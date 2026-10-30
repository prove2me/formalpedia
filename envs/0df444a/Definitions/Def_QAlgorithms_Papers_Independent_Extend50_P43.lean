-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P43
-- name    : QAlgorithms_Papers_Independent_Extend50_P43
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T20:57:34.874316+00:00
-- url     : https://prove2.me/theorems/dcb4b8a1-0f52-4d33-b165-58257f9cdddd
-- title:
--   Definitions for Programmable quantum gate arrays
-- statement:
--   The objects the formalized statements of *Programmable quantum gate arrays* (arXiv:quant-ph/9703032) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ExactPhaseEquivalent`: PDF p.2, Result: exact equality of operations modulo a global phase.
--   - `ImplementsProgramUnitary`: PDF p.1, Eqs.(1)–(3): one normalized program implements U exactly on all normalized data states. The residual program is initially allowed to vary with the data; its independence is a conclusion below.
--   - `orderedBellKet`: PDF p.2, Eqs.(12)–(13): ordered Bell kets on (A_i,B_i). Labels 0,1,2,3 mean Phi-plus, Phi-minus, Psi-plus, Psi-minus, respectively.
--   - `bellProduct`: PDF pp.2–3: the product Bell basis on all ordered pairs (A_i,B_i).
--   - `successOutcome`: PDF pp.2–3: the designated all-Phi-plus outcome. This flag is independent of the operation and the input state.
--   - `program`: PDF p.2, Eq.(11): the supplied 2m-qubit program on B,C is the constructed vector (I_B tensor U_C) Phi_m, using the frozen normalized EPR state.
--   - `contractBellOutcome`: PDF pp.2–3: the unnormalized C-register branch from measuring A,B in the product Bell basis. This is the Bell bra contraction, including its phase; it defines every outcome, including failures, without referring to U.
--   - `bellOutcomeProbability`: PDF pp.2–3: Born probability of a Bell outcome, computed from the branch.
--   - `normalizedBellOutput`: PDF p.3: normalized conditional C output. On a zero-probability branch this total function is zero; the success theorem proves strictly positive probability.
--   - `BellCircuit`: PDF pp.2–3, Fig.2: an instruction i is a two-qubit Bell measurement on the ordered pair (A_i,B_i), recording its four-valued outcome. A circuit is its actual instruction list; the C wires are the designated output. Each such primitive has a fixed constant-size elementary realization.
--   - `fixedProcessor`: PDF pp.2–3: the fixed processor measures each pair once, in wire order.
--   - `bellProjectorAt`: PDF p.2, Fig.2: the branch projector for one instruction, acting on A_i,B_i and as identity on the remaining wires, including C. This keeps the measured Bell state, so the full execution has the usual projective-measurement semantics.
--   - `processorBranch`: PDF pp.2–3: execute the instruction list on one recorded outcome path. The vector is subnormalized throughout; no free probability or cost field occurs.
--   - `regroupABC`: PDF p.3, systems A,B,C: regroup the frozen tensor coordinates to trace out A,B.
--   - `processorOutputDensity`: PDF p.3: the actual unnormalized output density on C of the listed processor. Its trace is the branch probability; the measured A,B registers are discarded.
--   - `ClassicalGate`: PDF pp.1,3: an arbitrary classical Boolean gate with a finite ordered input list and one output bit. Its function is unrestricted; this includes any maximum-fan-in-k gate set rather than only AND/OR/NOT.
--   - `ClassicalArray`: PDF pp.1,3: a classical programmable array with p program input bits, m data input bits, and m designated output wires. Gates are in topological order. Input wires are program first, then data; gate i creates wire p+m+i.
--   - `ClassicalWellFormed`: PDF pp.1,3: every gate reads an already defined wire and every output wire exists. This excludes the default getD value from all circuit evaluations.
--   - `HasFanInAtMost`: PDF p.3: maximum fan-in k bounds every actual gate occurrence.
--   - `classicalEval`: PDF pp.1,3: evaluate the fixed gates on program P and data d. Malformed wiring has a total default, excluded by ClassicalWellFormed.
--   - `ClassicalUniversal`: PDF pp.1,3: a classical universal array is one well-formed fixed circuit; only its program may depend on the selected function, and never on the data.
-- source:
--   Programmable quantum gate arrays, arXiv:quant-ph/9703032v1, https://arxiv.org/abs/quant-ph/9703032v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel

/-!
Statements from Nielsen and Chuang, *Programmable quantum gate arrays*,
arXiv:quant-ph/9703032v1, PDF pp.1–3. All new objects are local to this paper.
Program preparation is a supplied resource. For the probabilistic processor,
register C is the output, as explicitly permitted on p.3.
-/

namespace QAlgorithms.Papers.Independent.Extend50.P43

open scoped ComplexConjugate

noncomputable section

/-- PDF p.2, Result: exact equality of operations modulo a global phase. -/
def ExactPhaseEquivalent {m : ℕ}
    (U V : Matrix (Qubits m) (Qubits m) ℂ) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ U = z • V

/-- PDF p.1, Eqs.(1)–(3): one normalized program implements U exactly on
all normalized data states. The residual program is initially allowed to
vary with the data; its independence is a conclusion below. -/
def ImplementsProgramUnitary {m n : ℕ}
    (G : Matrix (Qubits m × Qubits n) (Qubits m × Qubits n) ℂ)
    (U : Matrix (Qubits m) (Qubits m) ℂ)
    (P : EuclideanSpace ℂ (Qubits n)) : Prop :=
  IsState P ∧ ∀ d : EuclideanSpace ℂ (Qubits m), IsState d →
    ∃ q : EuclideanSpace ℂ (Qubits n), IsState q ∧
      act G (tensorVec d P) = tensorVec (act U d) q

/-- Sanity: the phase relation identifies each matrix with itself. -/
example {m : ℕ} (U : Matrix (Qubits m) (Qubits m) ℂ) :
    ExactPhaseEquivalent U U := by
  exact ⟨1, by simp, by simp⟩

/-- Sanity: an identity array implements the identity with any normalized program. -/
example {m n : ℕ} (P : EuclideanSpace ℂ (Qubits n)) (hP : IsState P) :
    ImplementsProgramUnitary (1 : Matrix (Qubits m × Qubits n) (Qubits m × Qubits n) ℂ)
      (1 : Matrix (Qubits m) (Qubits m) ℂ) P := by
  refine ⟨hP, ?_⟩
  intro d hd
  exact ⟨P, hP, by simp [act]⟩

/-- PDF p.2, Eqs.(12)–(13): ordered Bell kets on (A_i,B_i).
Labels 0,1,2,3 mean Phi-plus, Phi-minus, Psi-plus, Psi-minus, respectively. -/
def orderedBellKet (r : Fin 4) : EuclideanSpace ℂ (Bool × Bool) :=
  WithLp.toLp 2 fun p =>
    let a : ℂ := ((Real.sqrt (2 : ℝ))⁻¹ : ℂ)
    match r.val with
    | 0 => if p.1 = p.2 then a else 0
    | 1 => if p.1 = p.2 then (if p.1 then -a else a) else 0
    | 2 => if p.1 ≠ p.2 then a else 0
    | _ => if p.1 ≠ p.2 then (if p.1 then -a else a) else 0

/-- PDF pp.2–3: the product Bell basis on all ordered pairs (A_i,B_i). -/
def bellProduct {m : ℕ} (o : Fin m → Fin 4) :
    EuclideanSpace ℂ (Qubits m × Qubits m) :=
  WithLp.toLp 2 fun p => ∏ i, orderedBellKet (o i) (p.1 i, p.2 i)

/-- PDF pp.2–3: the designated all-Phi-plus outcome. This flag is independent
of the operation and the input state. -/
def successOutcome (m : ℕ) : Fin m → Fin 4 := fun _ => 0

/-- PDF p.2, Eq.(11): the supplied 2m-qubit program on B,C is the constructed
vector (I_B tensor U_C) Phi_m, using the frozen normalized EPR state. -/
def program {m : ℕ} (U : Matrix (Qubits m) (Qubits m) ℂ) :
    EuclideanSpace ℂ (Qubits m × Qubits m) :=
  act (Matrix.kronecker (1 : Matrix (Qubits m) (Qubits m) ℂ) U) (maxEntangled m)

/-- PDF pp.2–3: the unnormalized C-register branch from measuring A,B in
the product Bell basis. This is the Bell bra contraction, including its phase;
it defines every outcome, including failures, without referring to U. -/
def contractBellOutcome {m : ℕ} (o : Fin m → Fin 4)
    (psi : EuclideanSpace ℂ (Qubits m × (Qubits m × Qubits m))) :
    EuclideanSpace ℂ (Qubits m) :=
  WithLp.toLp 2 fun c => ∑ a : Qubits m, ∑ b : Qubits m,
    conj (bellProduct o (a, b)) * psi (a, (b, c))

/-- PDF pp.2–3: Born probability of a Bell outcome, computed from the branch. -/
def bellOutcomeProbability {m : ℕ} (o : Fin m → Fin 4)
    (psi : EuclideanSpace ℂ (Qubits m × (Qubits m × Qubits m))) : ℝ :=
  ‖contractBellOutcome o psi‖ ^ 2

/-- PDF p.3: normalized conditional C output. On a zero-probability branch
this total function is zero; the success theorem proves strictly positive probability. -/
def normalizedBellOutput {m : ℕ} (o : Fin m → Fin 4)
    (psi : EuclideanSpace ℂ (Qubits m × (Qubits m × Qubits m))) :
    EuclideanSpace ℂ (Qubits m) :=
  ((Real.sqrt (bellOutcomeProbability o psi))⁻¹ : ℂ) • contractBellOutcome o psi

/-- Sanity: Phi-plus has the positive 00 amplitude; Psi-minus has negative 10 amplitude. -/
example : orderedBellKet 0 (false, false) = ((Real.sqrt (2 : ℝ))⁻¹ : ℂ) ∧
    orderedBellKet 3 (true, false) = -((Real.sqrt (2 : ℝ))⁻¹ : ℂ) := by
  simp [orderedBellKet]

/-- Sanity at the empty-register boundary: an empty Bell product has amplitude one. -/
example (o : Fin 0 → Fin 4) (a b : Qubits 0) : bellProduct o (a, b) = 1 := by
  simp [bellProduct]

/-- Sanity: a zero input has zero branch amplitude and probability. -/
example {m : ℕ} (o : Fin m → Fin 4) :
    contractBellOutcome o 0 = 0 ∧ bellOutcomeProbability o 0 = 0 := by
  have h : contractBellOutcome o 0 = 0 := by
    ext c
    simp [contractBellOutcome]
  exact ⟨h, by simp [bellOutcomeProbability, h]⟩

/-- PDF pp.2–3, Fig.2: an instruction i is a two-qubit Bell measurement
on the ordered pair (A_i,B_i), recording its four-valued outcome.
A circuit is its actual instruction list; the C wires are the designated output.
Each such primitive has a fixed constant-size elementary realization. -/
abbrev BellCircuit (m : ℕ) := List (Fin m)

/-- PDF pp.2–3: the fixed processor measures each pair once, in wire order. -/
def fixedProcessor (m : ℕ) : BellCircuit m := List.ofFn (fun i : Fin m => i)

/-- PDF p.2, Fig.2: the branch projector for one instruction, acting on A_i,B_i
and as identity on the remaining wires, including C. This keeps the measured
Bell state, so the full execution has the usual projective-measurement semantics. -/
def bellProjectorAt {m : ℕ} (i : Fin m) (r : Fin 4) :
    Matrix (Qubits m × (Qubits m × Qubits m))
      (Qubits m × (Qubits m × Qubits m)) ℂ :=
  open Classical in
  fun y z =>
    if y.2.2 = z.2.2 ∧
        (∀ j : Fin m, j ≠ i → y.1 j = z.1 j ∧ y.2.1 j = z.2.1 j) then
      orderedBellKet r (y.1 i, y.2.1 i) * conj (orderedBellKet r (z.1 i, z.2.1 i))
    else 0

/-- PDF pp.2–3: execute the instruction list on one recorded outcome path.
The vector is subnormalized throughout; no free probability or cost field occurs. -/
def processorBranch {m : ℕ} (circuit : BellCircuit m) (o : Fin m → Fin 4)
    (psi : EuclideanSpace ℂ (Qubits m × (Qubits m × Qubits m))) :
    EuclideanSpace ℂ (Qubits m × (Qubits m × Qubits m)) :=
  circuit.foldl (fun v i => act (bellProjectorAt i (o i)) v) psi

/-- PDF p.3, systems A,B,C: regroup the frozen tensor coordinates to trace out A,B. -/
def regroupABC {m : ℕ}
    (psi : EuclideanSpace ℂ (Qubits m × (Qubits m × Qubits m))) :
    EuclideanSpace ℂ ((Qubits m × Qubits m) × Qubits m) :=
  WithLp.toLp 2 fun p => psi (p.1.1, (p.1.2, p.2))

/-- PDF p.3: the actual unnormalized output density on C of the listed processor.
Its trace is the branch probability; the measured A,B registers are discarded. -/
def processorOutputDensity {m : ℕ} (circuit : BellCircuit m) (o : Fin m → Fin 4)
    (psi : EuclideanSpace ℂ (Qubits m × (Qubits m × Qubits m))) :
    Matrix (Qubits m) (Qubits m) ℂ :=
  traceLeft (pureDensity (regroupABC (processorBranch circuit o psi)))

/-- Sanity: no instructions leave the complete state unchanged. -/
example {m : ℕ} (o : Fin m → Fin 4)
    (psi : EuclideanSpace ℂ (Qubits m × (Qubits m × Qubits m))) :
    processorBranch [] o psi = psi := rfl

/-- Sanity: regrouping does not change any amplitude. -/
example {m : ℕ}
    (psi : EuclideanSpace ℂ (Qubits m × (Qubits m × Qubits m)))
    (a b c : Qubits m) : regroupABC psi ((a, b), c) = psi (a, (b, c)) := rfl

/-- Sanity at m=0: the fixed processor has an empty instruction list. -/
example : fixedProcessor 0 = [] := by simp [fixedProcessor]

/-- PDF pp.1,3: an arbitrary classical Boolean gate with a finite ordered
input list and one output bit. Its function is unrestricted; this includes
any maximum-fan-in-k gate set rather than only AND/OR/NOT. -/
structure ClassicalGate where
  arity : ℕ
  inputs : Fin arity → ℕ
  table : (Fin arity → Bool) → Bool

/-- PDF pp.1,3: a classical programmable array with p program input bits,
m data input bits, and m designated output wires. Gates are in topological
order. Input wires are program first, then data; gate i creates wire p+m+i. -/
structure ClassicalArray (m p : ℕ) where
  gates : List ClassicalGate
  outputs : Fin m → ℕ

/-- PDF pp.1,3: every gate reads an already defined wire and every output
wire exists. This excludes the default getD value from all circuit evaluations. -/
def ClassicalWellFormed {m p : ℕ} (circuit : ClassicalArray m p) : Prop :=
  (∀ i : Fin circuit.gates.length, ∀ j : Fin (circuit.gates.get i).arity,
    (circuit.gates.get i).inputs j < p + m + i.val) ∧
  ∀ j : Fin m, circuit.outputs j < p + m + circuit.gates.length

/-- PDF p.3: maximum fan-in k bounds every actual gate occurrence. -/
def HasFanInAtMost {m p : ℕ} (circuit : ClassicalArray m p) (k : ℕ) : Prop :=
  ∀ g ∈ circuit.gates, g.arity ≤ k

/-- PDF pp.1,3: evaluate the fixed gates on program P and data d.
Malformed wiring has a total default, excluded by ClassicalWellFormed. -/
def classicalEval {m p : ℕ} (circuit : ClassicalArray m p)
    (P : Qubits p) (d : Qubits m) : Qubits m :=
  let vals := circuit.gates.foldl
    (fun vals g => vals ++ [g.table (fun j => vals.getD (g.inputs j) false)])
    (List.ofFn (Fin.append P d))
  fun j => vals.getD (circuit.outputs j) false

/-- PDF pp.1,3: a classical universal array is one well-formed fixed circuit;
only its program may depend on the selected function, and never on the data. -/
def ClassicalUniversal {m p : ℕ} (circuit : ClassicalArray m p) : Prop :=
  ClassicalWellFormed circuit ∧
  ∀ f : Qubits m → Qubits m, ∃ P : Qubits p,
    ∀ d : Qubits m, classicalEval circuit P d = f d

/-- Sanity: a zero-gate array may output a program wire directly. Such
arrays are allowed in the model; universality, rather than an extra wiring
hypothesis, rules them out in the lower bound for nontrivial data. -/
example : classicalEval (⟨[], fun _ => 0⟩ : ClassicalArray 1 1)
    ![true] ![false] 0 = true := rfl

/-- Sanity: an arity-zero gate is a constant source, even with no available wires. -/
example : (ClassicalGate.mk 0 (fun i => Fin.elim0 i) (fun _ => true)).table
    (fun i => Fin.elim0 i) = true := rfl

end

end QAlgorithms.Papers.Independent.Extend50.P43


