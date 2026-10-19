-- Prove2me | Definitions.Def_QAlgorithms_Defs_RetainedStabilizerLearners
-- name    : QAlgorithms_Defs_RetainedStabilizerLearners
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:24:16.782411+00:00
-- url     : https://prove2.me/theorems/851c63f8-4ceb-4ccc-ab92-d850071444a0
-- title:
--   RetainedStabilizerLearners
-- statement:
--   RetainedStabilizerLearners
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\RetainedStabilizerLearners.lean

import Definitions.Def_QAlgorithms_Defs_AdaptiveMixedMeasurements
import Definitions.Def_QAlgorithms_Defs_StabilizerIdentification
noncomputable section

namespace QAlgorithms.StabilizerLearning

variable {n m d k b w M K N c out : ℕ}

/-- Elementary retained-register program, 2609.10974 pp.3,12–13,21–22.
Quantum/classical instructions are counted individually; partial measurements
retain all unmeasured wires. No instruction supplies another unknown copy. -/
inductive RetainedProgram (N c out : ℕ) where
  | halt (decode : BoolCircuit c out) (wellFormed : decode.WellFormed)
  | gate (g : GateApp htcxGateSet N) (next : RetainedProgram N c out)
  | measure (q : Fin N) (dst : Fin c) (next : Bool → RetainedProgram N c out)
  | coin (dst : Fin c) (next : Bool → RetainedProgram N c out)
  | setBit (dst : Fin c) (value : Bool) (next : RetainedProgram N c out)
  | boolean (op : BoolOp) (dst a b : Fin c) (next : RetainedProgram N c out)
  | branch (src : Fin c) (next : Bool → RetainedProgram N c out)

/-- Operational learner receiving t copies exactly once and clean ancillas,
2609.10974 pp.2–3,21. The final tableau is decoded by the frozen decoder. -/
structure RetainedCopyLearner (n : ℕ) where
  copies : ℕ
  ancillas : ℕ
  classicalBits : ℕ
  program : RetainedProgram (copies*n+ancillas) classicalBits (n*(2*n+2))

/-- Persistent Born/Lüders terminal law, 2609.10974 pp.3,21.
A fair coin splits the subnormalized input weight; no zero branch is divided. -/
def retainedProgramLaw {N c out : ℕ} :
    RetainedProgram N c out → Matrix (Qubits N) (Qubits N) ℂ →
      (Fin c → Bool) → (Fin out → Bool) → ℝ
  | .halt D _, rho, mem, result => if D.eval mem = result then rho.trace.re else 0
  | .gate g next, rho, mem, result =>
      retainedProgramLaw next (conjSuperop (embedOp g.gate.mat g.wires) rho) mem result
  | .measure q dst next, rho, mem, result => ∑ b : Bool,
      retainedProgramLaw (next b) (conjSuperop (qubitOp1 (measProj b) q) rho)
        (Function.update mem dst b) result
  | .coin dst next, rho, mem, result => (1/2 : ℝ) * ∑ b : Bool,
      retainedProgramLaw (next b) rho (Function.update mem dst b) result
  | .setBit dst b next, rho, mem, result =>
      retainedProgramLaw next rho (Function.update mem dst b) result
  | .boolean op dst a b next, rho, mem, result =>
      let value := match op with
        | .and => mem a && mem b
        | .or => mem a || mem b
        | .not => !mem a
      retainedProgramLaw next rho (Function.update mem dst value) result
  | .branch src next, rho, mem, result => retainedProgramLaw (next (mem src)) rho mem result

/-- Source learner's actual law on the persistent input copies,
2609.10974 pp.2–3. Initialization occurs once. -/
def retainedLearnerLaw {n : ℕ} (L : RetainedCopyLearner n)
    (psi : EuclideanSpace ℂ (Qubits n)) (hpsi : IsState psi)
    (result : Fin (n*(2*n+2)) → Bool) : ℝ :=
  retainedProgramLaw L.program
    (pureDensity (copiesInputState n L.copies L.ancillas psi)) (fun _ => false) result

/-- Worst executed elementary/classical instruction count,
2609.10974 pp.12–13,22. Giant unitaries and arbitrary classical maps
are not unit-cost commands. Both measurement/coin continuations are counted. -/
def retainedProgramTime {N c out : ℕ} : RetainedProgram N c out → ℕ
  | .halt D _ => D.size
  | .gate _ next => 1 + retainedProgramTime next
  | .measure _ _ next => 1 + max (retainedProgramTime (next false)) (retainedProgramTime (next true))
  | .coin _ next => 1 + max (retainedProgramTime (next false)) (retainedProgramTime (next true))
  | .setBit _ _ next => 1 + retainedProgramTime next
  | .boolean _ _ _ _ next => 1 + retainedProgramTime next
  | .branch _ next => 1 + max (retainedProgramTime (next false)) (retainedProgramTime (next true))

/-- Total retained-learner work includes one-time clean quantum and classical
initialization, 2609.10974 pp.12–13,21–22. Unknown copies are supplied once;
Clifford+T approximations contribute their actual elementary synthesis gates. -/
def RetainedCopyLearner.time {n : ℕ} (L : RetainedCopyLearner n) : ℕ :=
  L.ancillas + L.classicalBits + retainedProgramTime L.program

/-- Sanity check for the modeled source objects (arxiv-2609.10974v1, PDF pp.2,3,5,12,13,21,22). -/
example {N c out : ℕ} (D : BoolCircuit c out) (hD : D.WellFormed)
    (rho : Matrix (Qubits N) (Qubits N) ℂ) (mem : Fin c → Bool) :
    retainedProgramLaw (.halt D hD) rho mem (D.eval mem) = rho.trace.re := by
  simp [retainedProgramLaw]

/-- Sanity check for the modeled source objects (arxiv-2609.10974v1, PDF pp.2,3,5,12,13,21,22). -/
example {n : ℕ} (L : RetainedCopyLearner n) (h : L.copies = 0)
    (psi phi : EuclideanSpace ℂ (Qubits n)) (hpsi : IsState psi) (hphi : IsState phi)
    (result : Fin (n*(2*n+2)) → Bool) :
    retainedLearnerLaw L psi hpsi result = retainedLearnerLaw L phi hphi result := by
  have hs : copiesInputState n L.copies L.ancillas psi =
      copiesInputState n L.copies L.ancillas phi := by
    have he : (Finset.univ : Finset (Fin L.copies)) = ∅ := by
      ext i
      exact Fin.elim0 (Fin.cast h i)
    ext z
    simp [copiesInputState, he]
  simp only [retainedLearnerLaw, hs]

end QAlgorithms.StabilizerLearning


