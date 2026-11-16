-- Prove2me | Definitions.Def_PSPACEOracleSynth_Main_Supplement_Interaction
-- name    : PSPACEOracleSynth_Main_Supplement_Interaction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:26:28.617032+00:00
-- url     : https://prove2.me/theorems/93b73fea-28a3-4a2e-92ae-b8b7032ed2d6
-- title:
--   Entangled-input synthesis and pure-state verification
-- statement:
--   The verifier uses the published general-circuit round model, with private work, an acceptance flag, an output register and a message register. The prover chooses arbitrary finite persistent memory, an initial density matrix independent of input/reference, and a separate channel for each round. The input occupies the first input-sized segment of the verifier work register. The verifier description does not declare that occupied input size.
--
--   Interactive synthesis has one polynomial-time generator and polynomial verifier resources. For each $x,r$, one honest prover accepts with probability one on every supported input. For every pure entangled input and every prover accepted with probability at least $1/2$, the normalized accepted output is within trace distance $1/r$ of some completion on that input. The completion may depend on the input and prover. A pure-state verifier has no input, perfect honest acceptance, and the corresponding accepted-output error bound. The accepted joint state retains both message and prover memory.
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Definitions 2.10 and 7.3, pp. 14, 39

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Classes
import Definitions.Def_UnitaryQIPPSPACE_Verifier
import Definitions.Def_PSPACEOracleSynth_Main_Dilation

open QAlgorithms QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
open scoped Matrix ComplexOrder Kronecker
noncomputable section

attribute [local instance] Classical.propDecidable

namespace PSPACEOracleSynth.Main.Supplement

/-! Definitions 2.10 and 7.3, pp. 14, 39. Reuse the published general-circuit verifier
(private work, acceptance flag, output, message). T† is T^7, so its {H,T,CNOT}
rounds have exactly the computational power of G. Input occupancy is not part of its code. -/

abbrev Verifier := UnitaryQIPPSPACE.Verifier

/-- Arbitrary persistent private memory and a separate channel for every round.
The initial memory state is a separate argument, independent of the input/reference. -/
structure ProverMoves (m : ℕ) where
  memory : ℕ
  move : ℕ → Map (Bits m × Bits memory) (Bits m × Bits memory)
  channel : ∀ j, IsChannel (move j)

namespace Verifier

def layout (V : Verifier) : Bits V.dim ≃ Bits (V.w + 1 + V.o) × Bits V.m :=
  UnitaryQIPPSPACE.Bits.splitEquiv (V.w + 1 + V.o) V.m

/-- Final work, flag, output, message layout. -/
def wires (V : Verifier) (w : Bits V.w) (flag : Bool) (b : Bits V.o) (msg : Bits V.m) : Bits V.dim :=
  Fin.append (Fin.append (Fin.append w (fun _ : Fin 1 => flag)) b) msg

noncomputable def proverStep (V : Verifier) (P : ProverMoves V.m) (j : ℕ) :
    Map (Bits V.dim × Bits P.memory) (Bits V.dim × Bits P.memory) :=
  fun ρ u v =>
    P.move j (fun a b => ρ ((V.layout).symm ((V.layout u.1).1, a.1), a.2)
      ((V.layout).symm ((V.layout v.1).1, b.1), b.2))
      ((V.layout u.1).2, u.2) ((V.layout v.1).2, v.2)

/-- Run the round circuits, alternating with the prover, without resetting private memory. -/
noncomputable def interact (V : Verifier) (P : ProverMoves V.m)
    (ρ : Op (Bits V.dim × Bits P.memory)) : Op (Bits V.dim × Bits P.memory) :=
  (V.rounds.zipIdx).foldl (fun st cj =>
    let st' := withRef (cj.1.chan V.dim V.dim) st
    if cj.2 + 1 < V.rounds.length then V.proverStep P cj.2 st' else st') ρ

/-- Accepted output together with message and private memory; initialized verifier qubits
are zero except for the first a work wires holding ρ. Bad input occupancy is not used. -/
noncomputable def acceptedJoint (V : Verifier) (P : ProverMoves V.m) (a : ℕ)
    (τ : Op (Bits P.memory)) : Map (Bits a) (Bits V.o × (Bits V.m × Bits P.memory)) :=
  if h : a ≤ V.w then
    fun ρ =>
      let hdim : a ≤ V.dim := by dsimp [UnitaryQIPPSPACE.Verifier.dim]; omega
      let initial := (ancMat hdim * ρ * (ancMat hdim)ᴴ) ⊗ₖ τ
      let final := V.interact P initial
      fun u v => ∑ w : Bits V.w,
        final (V.wires w true u.1 u.2.1, u.2.2) (V.wires w true v.1 v.2.1, v.2.2)
  else fun _ => 0

noncomputable def accepted (V : Verifier) (P : ProverMoves V.m) (a : ℕ)
    (τ : Op (Bits P.memory)) : Map (Bits a) (Bits V.o) :=
  fun ρ => traceRight (V.acceptedJoint P a τ ρ)

/-- Definition 2.10 soundness, for every pure entangled input, including outside support.
The completion may depend on the input and on the prover. -/
def Sound {a b : ℕ} (V : Verifier) (U : PartialIso a b) (ε : ℝ) : Prop :=
  V.WF ∧ a ≤ V.w ∧ V.o = b ∧
    ∀ (P : ProverMoves V.m) (τ : Op (Bits P.memory)), IsDensityMatrix τ →
    ∀ (r : ℕ) (ψ : Bits a × Bits r → ℂ), UnitKet ψ →
      let Ω := withRef (V.accepted P a τ) (ket ψ)
      (1 : ℝ)/2 ≤ Ω.trace.re →
      ∃ Φ : Map (Bits a) (Bits V.o),
        (∃ h : V.o = b, Completion U
          (fun ρ => cast (congrArg (fun n => Op (Bits n)) h) (Φ ρ))) ∧
        dist (normalized Ω) (withRef Φ (ket ψ)) ≤ ε

/-- One honest prover and initial memory for every supported input. -/
def Complete {a b : ℕ} (V : Verifier) (U : PartialIso a b) : Prop :=
  ∃ (P : ProverMoves V.m) (τ : Op (Bits P.memory)), IsDensityMatrix τ ∧
    ∀ ψ : Bits a → ℂ, UnitKet ψ → U.projector.mulVec ψ = ψ →
      ((V.accepted P a τ) (ket ψ)).trace.re = 1

/-- Definition 7.3: perfect completeness, and threshold soundness for a pure target. -/
def StateVerifier (V : Verifier) (χ : Bits V.o → ℂ) (ε : ℝ) : Prop :=
  V.WF ∧ UnitKet χ ∧ 0 ≤ ε ∧
    (∃ (P : ProverMoves V.m) (τ : Op (Bits P.memory)), IsDensityMatrix τ ∧
      ((V.accepted P 0 τ) (ket (fun _ => (1 : ℂ)))).trace.re = 1) ∧
    ∀ (P : ProverMoves V.m) (τ : Op (Bits P.memory)), IsDensityMatrix τ →
      let Ω := (V.accepted P 0 τ) (ket (fun _ => (1 : ℂ)))
      (1 : ℝ)/2 ≤ Ω.trace.re → dist (normalized Ω) (ket χ) ≤ ε

end Verifier

/-- Definition 2.10. The verifier code fixes its output size but not the occupied input size. -/
def channelQIP : Set SynthProblem :=
  {U | ∃ V : Str → ℕ → Verifier,
    TimeUniform precisionIndex (fun xr => (V xr.1 xr.2).code) ∧
    (∃ p : Polynomial ℕ, ∀ x r,
      (V x r).dim + (V x r).size + (V x r).rounds.length ≤ p.eval (x.length+r)) ∧
    ∀ x r, 1 ≤ r → (V x r).Complete (U.target x) ∧
      (V x r).Sound (U.target x) (1/(r : ℝ))}

end PSPACEOracleSynth.Main.Supplement


