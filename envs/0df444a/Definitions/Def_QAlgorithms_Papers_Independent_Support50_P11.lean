-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11
-- name    : QAlgorithms_Papers_Independent_Support50_P11
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T19:01:22.872824+00:00
-- url     : https://prove2.me/theorems/e4ba3641-45e2-408d-8976-14cd8322dd82
-- title:
--   Definitions for On the power of PPT-preserving and non-signalling codes
-- statement:
--   The objects the formalized statements of *On the power of PPT-preserving and non-signalling codes* (arXiv:1406.7142) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `choiState`: PDF pp.3,9, (1),(52): normalized Choi state in reference,output order.
--   - `Loewner`: PDF pp.3,7: Loewner comparison; this is not entrywise matrix order.
--   - `NSBA`: PDF p.3, (7): non-signalling Bob to Alice on all operators.
--   - `NSAB`: PDF p.3, (8): non-signalling Alice to Bob on all operators.
--   - `PPTMap`: PDF p.3, (6): complete PPT preservation, equivalently CPTP after the two Bob transposes.
--   - `Horodecki`: PDF p.3: a Horodecki channel has a PPT Choi matrix.
--   - `IsClassicalSideChannel`: PDF p.5: a classical side channel is dephased at both ports.
--   - `forwardOp`: PDF pp.4--5, (9): actual encoder, one forward side-channel call, decoder. The middle coordinates explicitly move Bob's input next to the side-channel output.
--   - `eaOp`: PDF p.5: shared-state realization by two local CPTP operations.
--   - `CodeAssistance`: PDF pp.4--5: the operational and mathematical assistance classes.
--   - `InCodeClass`: PDF p.5: membership in an operational code class. Ancilla dimensions are arbitrary positive finite integers, chosen before any channel input.
--   - `IsForwardCode`: PDF p.4: a forward-assisted code is a CPTP bipartite operation non-signalling Bob to Alice.
--   - `link`: PDF p.4, (11)--(12): insert the noisy channel into the bipartite operation. This matrix-unit contraction is the source's full-transpose Choi link, not an ordinary serial composition or an adaptive use.
--   - `codeAverageInput`: PDF p.4, (13): average channel input on the maximally mixed sender input.
--   - `channelFidelity`: PDF p.4: normalized entanglement/channel fidelity, the accepted finite-register definition.
--   - `uniformClassicalSuccess`: PDF p.8: uniform computational-basis classical success probability.
--   - `optimalCodeFidelity`: PDF p.5, Definition 1: operational supremum of channel fidelities. For positive finite systems and a CPTP channel the feasible set is nonempty and bounded by one; the constrained optima are attained by Corollary 4.
--   - `optimalClassicalCodeFidelity`: PDF p.8, Definition 7: operational classical optimum over the same code class.
--   - `quantumCodeCapacity`: PDF p.5, (14): memoryless, parallel-block, vanishing-error capacity in qubits/use. Extended nonnegative suprema avoid junk values at unbounded sets.
--   - `zeroErrorCodeCapacity`: PDF p.5, (15): zero-error capacity, supremum over finite positive blocks and sizes.
--   - `flagsClass`: PDF pp.6--7: which of the two independently selectable constraints is imposed.
--   - `primalObjective`: PDF p.7, (31): full ordinary transpose of the unnormalized Choi matrix.
--   - `Primal`: PDF p.7, (32)--(35): exact primal constraints; all inequalities are Loewner.
--   - `ExpandedDualFeasible`: PDF p.7, (42)--(44): expanded dual, keeping both positive multipliers.
--   - `lagrangian`: PDF p.7, proof of Proposition 5: the unreduced Lagrangian on the PSD cone. The equality multipliers are free Hermitian W and real mu; rho is not normalized here.
--   - `relaxedBound`: PDF p.8, (48): Matthews--Wehner relaxation with a Loewner marginal inequality.
--   - `distillFidelity`: PDF p.9, (50): PPT distillation fidelity of a normalized bipartite state.
--   - `distillCapacity`: PDF p.9, (51): operational PPT distillable entanglement, in ebits/copy.
--   - `resourceSim`: PDF p.10, (53)--(56): Alice's local classical-output operation on input and her resource share, followed by Bob's local operation on the message and his share.
--   - `HasChoiSimulation`: PDF pp.9--10, Proposition 8(ii): exact single-copy Choi simulation by local operations and forward classical communication. It is an operational factorization.
--   - `classicalControlledUnitary`: PDF p.10: a classical control is measured, then the indicated unitary applied.
--   - `wernerHolevoChannel`: PDF p.10, (57)--(59): generalized Werner--Holevo channel, d>=2, alpha in [0,1].
--   - `epsilon3`: PDF p.10, (60): the real Levi-Civita symbol in the ordered basis 0,1,2.
--   - `HasAntidegradingDilation`: PDF p.10: an actual isometric dilation with a channel degrading environment to output.
--   - `wernerSector`: PDF pp.10,13: symmetric and antisymmetric projectors, selected by a Boolean.
--   - `sectorSum`: PDF p.13, (A1): E_j, with exactly j antisymmetric factors. Rows are (all inputs,all outputs).
--   - `bellSectorSum`: PDF p.14: Upsilon_i has exactly i normalized Bell projectors.
--   - `ansatz`: PDF pp.13--14, (A1): real sector coefficients, embedded into complex matrices.
--   - `coeffM`: PDF p.14, (A3): partial-transpose coefficients with zero-extended binomials. The explicit guard prevents truncated natural subtraction introducing extra terms.
--   - `coeffG`: PDF p.14: partial-trace coefficients g_j; the remaining identity acts on input.
--   - `lpObjective`: PDF p.14, (A4): essential factor d^n, including the endpoint convention 0^0=1.
--   - `WernerLPFeasible`: PDF p.14, (A5)--(A8): n+1 real variables with independently selectable NS/PPTp constraints.
--   - `exampleLambda`: PDF p.12, Example 9: corrected common 1/9 normalization of the printed Lambda.
--   - `measurementKet`: PDF p.12, Fig.7: Z- or X-basis ket a, selected by Bob's bit b.
--   - `bonusOperation`: PDF pp.12--13, Fig.7: the independently specified randomized measurement operation. Both outputs are diagonal, and Bob's independent uniform bit is the second output.
--   - `PerfectQubit`: PDF pp.12--13: an unassisted one-use perfect qubit transmission code for a side channel.
--   - `teleportWeyl`: PDF pp.14--15: generalized Pauli correction, with positive phase and shift X^a Z^b. The message c is identified with (a,b) by finProdFinEquiv.
--   - `bellKet`: PDF pp.14--15: the Bell measurement vectors (U_c tensor I)|phi>. This convention pairs with the correction U_c, not its inverse.
--   - `bellMeasure`: PDF pp.14--15: complete Bell measurement with a classical outcome.
--   - `teleportCode`: PDF pp.14--15: actual bipartite teleportation code, with one shared Bell state.
--   - `denseCode`: PDF pp.14--15: actual bipartite dense-coding code, with one shared Bell state.
--   - `dephasedPermutationTwirl`: PDF p.14, corrected (B1): input/output dephasing around permutation averaging. The printed permutation average alone does not remove quantum coherences.
--   - `fidelityDepolarizing`: PDF p.14: isotropic depolarizing channel parameterized by entanglement fidelity. Dimension one is handled separately; f is not the depolarizing mixing weight.
--   - `symmetricClassical`: PDF p.14: d-ary symmetric classical channel parameterized by success probability.
--   - `teleportConversion`: PDF p.15, (B6): fully specified CPTP teleportation conversion with corrected twirls.
--   - `denseConversion`: PDF p.15, (B8): fully specified CPTP dense-coding conversion with corrected twirls.
--   - `reconstructedCode`: PDF pp.6--7, (29),(36): the actual twirled bipartite operation reconstructed from rho,Lambda. Used only at K>=2; the scalar case of Theorem 3 is separate.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, https://arxiv.org/abs/1406.7142v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

/-!
Leung and Matthews, arXiv:1406.7142v2. All citations below are PDF pages.
Local coordinates always put Alice before Bob, and Choi reference before output.
The paper's suppressed permutations are written out in coordinates. Capacities
are operational suprema in the extended nonnegative reals, never entropy definitions.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P11

-- These are pinned accepted definitions, with no local copies or aliases.
open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)
open QAlgorithms.Papers.Independent.Information100.P21 (pt)
open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)
open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)
open QAlgorithms.Papers.Independent.Information100.P69 (replacer)
open QAlgorithms.Papers.Independent.Gap20.P19 (wernerIsometry)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF pp.3,9, (1),(52): normalized Choi state in reference,output order. -/
def choiState {I O : Type*} [Fintype I] [DecidableEq I] (N : Superop I O) :
    Matrix (I × O) (I × O) ℂ := (Fintype.card I : ℂ)⁻¹ • choi N

/-- PDF pp.3,7: Loewner comparison; this is not entrywise matrix order. -/
def Loewner {I : Type*} [Fintype I] (X Y : Matrix I I ℂ) : Prop :=
  (Y - X).PosSemidef

/-- PDF p.3, (7): non-signalling Bob to Alice on all operators. -/
def NSBA {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (Z : Superop (A × B) (C × D)) : Prop :=
  ∃ E : Superop A C, IsChannel E ∧ ∀ X, traceRight (Z X) = E (traceRight X)

/-- PDF p.3, (8): non-signalling Alice to Bob on all operators. -/
def NSAB {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (Z : Superop (A × B) (C × D)) : Prop :=
  ∃ Dmap : Superop B D, IsChannel Dmap ∧ ∀ X, traceLeft (Z X) = Dmap (traceLeft X)

/-- PDF p.3, (6): complete PPT preservation, equivalently CPTP after the two Bob transposes. -/
def PPTMap {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (Z : Superop (A × B) (C × D)) : Prop :=
  IsChannel Z ∧ IsChannel (fun X => pt (Z (pt X)))

/-- PDF p.3: a Horodecki channel has a PPT Choi matrix. -/
def Horodecki {I O : Type*} [Fintype I] [Fintype O] (N : Superop I O) : Prop :=
  IsChannel N ∧ (pt (choi N)).PosSemidef

/-- PDF p.5: a classical side channel is dephased at both ports. -/
def IsClassicalSideChannel {I O : Type*} [Fintype I] [Fintype O] (F : Superop I O) : Prop :=
  IsChannel F ∧ (∀ X, F (dephasing X) = F X) ∧ (∀ X, dephasing (F X) = F X)

/-- PDF pp.4--5, (9): actual encoder, one forward side-channel call, decoder.
The middle coordinates explicitly move Bob's input next to the side-channel output. -/
def forwardOp {A B I K Q R : Type} [Fintype A] [Fintype B]
    [Fintype Q] [Fintype R] [DecidableEq A] [DecidableEq B]
    [DecidableEq Q] [DecidableEq R]
    (E : Superop A (I × Q)) (F : Superop Q R) (D : Superop (R × B) K) :
    Superop (A × B) (I × K) :=
  fun X => idTensorSuperop D (idTensorSuperop (tensorAction F (fun Y : Matrix B B ℂ => Y))
    (fun (p q : I × (Q × B)) =>
      tensorAction E (fun Y : Matrix B B ℂ => Y) X ((p.1,p.2.1),p.2.2)
        ((q.1,q.2.1),q.2.2)))

/-- PDF p.5: shared-state realization by two local CPTP operations. -/
def eaOp {A B I K L R : Type} [Fintype A] [Fintype B] [Fintype L] [Fintype R]
    [DecidableEq A] [DecidableEq B] [DecidableEq L] [DecidableEq R]
    (sigma : Matrix (L × R) (L × R) ℂ)
    (E : Superop (A × L) I) (D : Superop (B × R) K) :
    Superop (A × B) (I × K) :=
  fun X => tensorAction E D (fun (p q : (A × L) × (B × R)) =>
    X (p.1.1,p.2.1) (q.1.1,q.2.1) * sigma (p.1.2,p.2.2) (q.1.2,q.2.2))

/-- PDF pp.4--5: the operational and mathematical assistance classes. -/
inductive CodeAssistance where
  | FA | UA | EA | FCA | FHA | NS | PPTp | both
  deriving DecidableEq

/-- PDF p.5: membership in an operational code class. Ancilla dimensions are arbitrary
positive finite integers, chosen before any channel input. -/
def InCodeClass {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (c : CodeAssistance)
    (Z : Superop (Fin K × O) (I × Fin K)) : Prop :=
  match c with
  | .FA => True
  | .UA => ∃ E : Superop (Fin K) I, ∃ D : Superop O (Fin K),
      IsChannel E ∧ IsChannel D ∧ Z = tensorAction E D
  | .EA => ∃ l r : ℕ, 0 < l ∧ 0 < r ∧
      ∃ sigma : Matrix (Fin l × Fin r) (Fin l × Fin r) ℂ,
      ∃ E : Superop (Fin K × Fin l) I, ∃ D : Superop (O × Fin r) (Fin K),
      IsDensityMatrix sigma ∧ IsChannel E ∧ IsChannel D ∧ Z = eaOp sigma E D
  | .FCA => ∃ q r : ℕ, 0 < q ∧ 0 < r ∧
      ∃ E : Superop (Fin K) (I × Fin q), ∃ F : Superop (Fin q) (Fin r),
      ∃ D : Superop (Fin r × O) (Fin K),
      IsChannel E ∧ IsClassicalSideChannel F ∧ IsChannel D ∧ Z = forwardOp E F D
  | .FHA => ∃ q r : ℕ, 0 < q ∧ 0 < r ∧
      ∃ E : Superop (Fin K) (I × Fin q), ∃ F : Superop (Fin q) (Fin r),
      ∃ D : Superop (Fin r × O) (Fin K),
      IsChannel E ∧ Horodecki F ∧ IsChannel D ∧ Z = forwardOp E F D
  | .NS => NSAB Z
  | .PPTp => PPTMap Z
  | .both => NSAB Z ∧ PPTMap Z

/-- PDF p.4: a forward-assisted code is a CPTP bipartite operation non-signalling Bob to Alice. -/
def IsForwardCode {I O : Type} [Fintype I] [Fintype O] (K : ℕ) (c : CodeAssistance)
    (Z : Superop (Fin K × O) (I × Fin K)) : Prop :=
  IsChannel Z ∧ NSBA Z ∧ InCodeClass K c Z

/-- PDF p.4, (11)--(12): insert the noisy channel into the bipartite operation.
This matrix-unit contraction is the source's full-transpose Choi link, not an
ordinary serial composition or an adaptive use. -/
def link {I O : Type*} [Fintype I] [Fintype O] (K : ℕ)
    (N : Superop I O) (Z : Superop (Fin K × O) (I × Fin K)) :
    Superop (Fin K) (Fin K) :=
  fun X b c => ∑ a, ∑ a2, ∑ i, ∑ j, ∑ beta, ∑ gamma,
    X a a2 * N (Matrix.single i j 1) beta gamma *
      Z (Matrix.single (a,beta) (a2,gamma) 1) (i,b) (j,c)

/-- PDF p.4, (13): average channel input on the maximally mixed sender input. -/
def codeAverageInput {I O : Type*} [Fintype O] (K : ℕ)
    (Z : Superop (Fin K × O) (I × Fin K)) : Matrix I I ℂ :=
  traceRight (Z (((K * Fintype.card O : ℕ) : ℂ)⁻¹ • 1))

/-- PDF p.4: normalized entanglement/channel fidelity, the accepted finite-register definition. -/
def channelFidelity (K : ℕ) (N : Superop (Fin K) (Fin K)) : ℝ :=
  if h : 0 < K then QuditFidelity.entanglementFidelity K h N else 0

/-- PDF p.8: uniform computational-basis classical success probability. -/
def uniformClassicalSuccess {I : Type*} [Fintype I] [DecidableEq I] (N : Superop I I) : ℝ :=
  (∑ i, (N (Matrix.single i i 1) i i).re) / Fintype.card I

/-- PDF p.5, Definition 1: operational supremum of channel fidelities. For positive
finite systems and a CPTP channel the feasible set is nonempty and bounded by one;
the constrained optima are attained by Corollary 4. -/
def optimalCodeFidelity {I O : Type} [Fintype I] [Fintype O] (c : CodeAssistance)
    (N : Superop I O) (K : ℕ) : ℝ :=
  sSup {f | ∃ Z, IsForwardCode K c Z ∧ f = channelFidelity K (link K N Z)}

/-- PDF p.8, Definition 7: operational classical optimum over the same code class. -/
def optimalClassicalCodeFidelity {I O : Type} [Fintype I] [Fintype O] (c : CodeAssistance)
    (N : Superop I O) (K : ℕ) : ℝ :=
  sSup {f | ∃ Z, IsForwardCode K c Z ∧ f = uniformClassicalSuccess (link K N Z)}

/-- PDF p.5, (14): memoryless, parallel-block, vanishing-error capacity in qubits/use.
Extended nonnegative suprema avoid junk values at unbounded sets. -/
def quantumCodeCapacity {I O : Type} [Fintype I] [Fintype O] (c : CodeAssistance)
    (N : Superop I O) : ℝ≥0∞ :=
  ⨆ r : NNReal, if Filter.Tendsto
    (fun n : ℕ => optimalCodeFidelity c (piSuperop (fun _ : Fin n => N))
      ⌊(2 : ℝ) ^ ((n : ℝ) * (r : ℝ))⌋₊)
    Filter.atTop (nhds 1) then (r : ℝ≥0∞) else 0

/-- PDF p.5, (15): zero-error capacity, supremum over finite positive blocks and sizes. -/
def zeroErrorCodeCapacity {I O : Type} [Fintype I] [Fintype O] (c : CodeAssistance)
    (N : Superop I O) : ℝ≥0∞ :=
  ⨆ n : ℕ+, ⨆ K : ℕ+, if optimalCodeFidelity c (piSuperop (fun _ : Fin (n : ℕ) => N)) K = 1
    then ENNReal.ofReal ((Real.log (K : ℝ) / Real.log 2) / (n : ℝ)) else 0

/-- PDF pp.6--7: which of the two independently selectable constraints is imposed. -/
def flagsClass (s p : Bool) : CodeAssistance :=
  if s then (if p then .both else .NS) else (if p then .PPTp else .FA)

/-- PDF p.7, (31): full ordinary transpose of the unnormalized Choi matrix. -/
def primalObjective {I O : Type*} [Fintype I] [Fintype O] (N : Superop I O)
    (L : Matrix (I × O) (I × O) ℂ) : ℝ := ((choi N).transpose * L).trace.re

/-- PDF p.7, (32)--(35): exact primal constraints; all inequalities are Loewner. -/
def Primal {I O : Type*} [Fintype I] [Fintype O] (K : ℕ) (s p : Bool)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) : Prop :=
  IsDensityMatrix rho ∧ L.PosSemidef ∧ Loewner L (Matrix.kronecker rho 1) ∧
  (s = true → traceLeft L = ((K : ℂ)^2)⁻¹ • 1) ∧
  (p = true → Loewner (-((K : ℂ)⁻¹ • Matrix.kronecker rho 1)) (pt L) ∧
    Loewner (pt L) ((K : ℂ)⁻¹ • Matrix.kronecker rho 1))

/-- PDF p.7, (42)--(44): expanded dual, keeping both positive multipliers. -/
def ExpandedDualFeasible {I O : Type*} [Fintype I] [Fintype O] (N : Superop I O)
    (K : ℕ) (s p : Bool) (mu : ℝ) (W : Matrix O O ℂ)
    (X Y V : Matrix (I × O) (I × O) ℂ) : Prop :=
  W.IsHermitian ∧ X.PosSemidef ∧ Y.PosSemidef ∧ V.PosSemidef ∧
  (s = false → W = 0) ∧ (p = false → Y = 0 ∧ V = 0) ∧
  Loewner ((choi N).transpose + pt (Y - V)) (X + Matrix.kronecker 1 W) ∧
  Loewner (traceRight (X + (K : ℂ)⁻¹ • (Y + V))) ((mu : ℂ) • 1)

/-- PDF p.7, proof of Proposition 5: the unreduced Lagrangian on the PSD cone.
The equality multipliers are free Hermitian W and real mu; rho is not normalized here. -/
def lagrangian {I O : Type*} [Fintype I] [Fintype O] (N : Superop I O)
    (K : ℕ) (mu : ℝ) (W : Matrix O O ℂ)
    (X Y V L : Matrix (I × O) (I × O) ℂ) (rho : Matrix I I ℂ) : ℝ :=
  primalObjective N L + (X * (Matrix.kronecker rho 1 - L)).trace.re +
    (Y * ((K : ℂ)⁻¹ • Matrix.kronecker rho 1 + pt L)).trace.re +
    (V * ((K : ℂ)⁻¹ • Matrix.kronecker rho 1 - pt L)).trace.re +
    (W * (((K : ℂ)^2)⁻¹ • 1 - traceLeft L)).trace.re + mu * (1 - rho.trace.re)

/-- PDF p.8, (48): Matthews--Wehner relaxation with a Loewner marginal inequality. -/
def relaxedBound {I O : Type*} [Fintype I] [Fintype O]
    (N : Superop I O) (M : ℕ) : ℝ :=
  sSup {v | ∃ rho : Matrix I I ℂ, ∃ L : Matrix (I × O) (I × O) ℂ,
    IsDensityMatrix rho ∧ L.PosSemidef ∧ Loewner L (Matrix.kronecker rho 1) ∧
    Loewner (traceLeft L) ((M : ℂ)⁻¹ • 1) ∧ v = primalObjective N L}

/-- Sanity: partial transpose is involutive on every operator, PDF p.3. -/
example {A B : Type*} (X : Matrix (A × B) (A × B) ℂ) : pt (pt X) = X := rfl

/-- Sanity: the identity qubit Choi coherence is unnormalized, PDF p.3, (5). -/
example : choi (fun X : Matrix (Fin 2) (Fin 2) ℂ => X) (0,0) (1,1) = 1 := by
  norm_num [choi, Matrix.single]

/-- Sanity: normalization divides the identity-qubit Choi coherence by two, PDF p.9. -/
example : choiState (fun X : Matrix (Fin 2) (Fin 2) ℂ => X) (0,0) (1,1) = 1 / 2 := by
  norm_num [choiState, choi, Matrix.single]

/-- Sanity: a scalar code has the selected class FA if neither constraint is imposed. -/
example : flagsClass false false = .FA := rfl

/-- PDF p.9, (50): PPT distillation fidelity of a normalized bipartite state. -/
def distillFidelity {A B : Type*} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) (K : ℕ) : ℝ :=
  if h : 0 < K then
    letI : Nonempty (Fin K) := ⟨⟨0,h⟩⟩
    sSup {f | ∃ Y : Superop (A × B) (Fin K × Fin K), PPTMap Y ∧
      f = effectProb (pureDensity (finiteMaxEntangled (Fin K))) (Y rho)}
  else 0

/-- PDF p.9, (51): operational PPT distillable entanglement, in ebits/copy. -/
def distillCapacity {A B : Type*} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ≥0∞ :=
  ⨆ r : NNReal, if Filter.Tendsto
    (fun n : ℕ => distillFidelity
      (fun p q : (Fin n → A) × (Fin n → B) =>
        ∏ k, rho (p.1 k,p.2 k) (q.1 k,q.2 k))
      ⌊(2 : ℝ) ^ ((n : ℝ) * (r : ℝ))⌋₊)
    Filter.atTop (nhds 1) then (r : ℝ≥0∞) else 0

/-- PDF p.10, (53)--(56): Alice's local classical-output operation on input and
her resource share, followed by Bob's local operation on the message and his share. -/
def resourceSim {A B I O C : Type*} [Fintype A] [Fintype I]
    (rho : Matrix (A × B) (A × B) ℂ) (M : Superop (I × A) C)
    (D : Superop (C × B) O) : Superop I O :=
  fun X => D (fun p q => M
    (fun u v => X u.1 v.1 * rho (u.2,p.2) (v.2,q.2)) p.1 q.1)

/-- PDF pp.9--10, Proposition 8(ii): exact single-copy Choi simulation by local
operations and forward classical communication. It is an operational factorization. -/
def HasChoiSimulation {I O : Type*} [Fintype I] [Fintype O] (N : Superop I O) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ M : Superop (I × I) (Fin m),
    ∃ D : Superop (Fin m × O) O, IsChannel M ∧ IsChannel D ∧
    (∀ X, dephasing (M X) = M X) ∧ ∀ X, resourceSim (choiState N) M D X = N X

/-- PDF p.10: a classical control is measured, then the indicated unitary applied. -/
def classicalControlledUnitary {C I : Type*} [Fintype C] [Fintype I]
    (U : C → Matrix I I ℂ) : Superop (C × I) I :=
  fun X => ∑ c, conjSuperop (U c) (fun i j => X (c,i) (c,j))

/-- PDF p.10, (57)--(59): generalized Werner--Holevo channel, d>=2, alpha in [0,1]. -/
def wernerHolevoChannel (d : ℕ) (alpha : ℝ) : Superop (Fin d) (Fin d) :=
  fun X => (((1 - alpha) / ((d : ℝ) + 1) : ℝ) : ℂ) • (X.trace • 1 + X.transpose) +
    ((alpha / ((d : ℝ) - 1) : ℝ) : ℂ) • (X.trace • 1 - X.transpose)

/-- PDF p.10, (60): the real Levi-Civita symbol in the ordered basis 0,1,2. -/
def epsilon3 (i j k : Fin 3) : ℝ :=
  if (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 1 ∧ j = 2 ∧ k = 0) ∨
      (i = 2 ∧ j = 0 ∧ k = 1) then 1
  else if (i = 0 ∧ j = 2 ∧ k = 1) ∨ (i = 2 ∧ j = 1 ∧ k = 0) ∨
      (i = 1 ∧ j = 0 ∧ k = 2) then -1 else 0

/-- PDF p.10: an actual isometric dilation with a channel degrading environment to output. -/
def HasAntidegradingDilation {I O : Type*} [Fintype I] [Fintype O] (N : Superop I O) : Prop :=
  ∃ e : ℕ, 0 < e ∧ ∃ V : Matrix (O × Fin e) I ℂ,
    Vᴴ * V = 1 ∧ (∀ X, N X = traceRight (V * X * Vᴴ)) ∧
    ∃ D : Superop (Fin e) O, IsChannel D ∧ ∀ X, N X = D (traceLeft (V * X * Vᴴ))

/-- PDF pp.10,13: symmetric and antisymmetric projectors, selected by a Boolean. -/
def wernerSector (d : ℕ) (anti : Bool) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (2 : ℂ)⁻¹ • (if anti then 1 - swapMatrix (I := Fin d) else 1 + swapMatrix (I := Fin d))

/-- PDF p.13, (A1): E_j, with exactly j antisymmetric factors. Rows are (all inputs,all outputs). -/
def sectorSum (d n j : ℕ) :
    Matrix ((Fin n → Fin d) × (Fin n → Fin d))
      ((Fin n → Fin d) × (Fin n → Fin d)) ℂ :=
  fun p q => ∑ t : Fin n → Bool,
    if (Finset.univ.filter (fun k => t k = true)).card = j then
      ∏ k, wernerSector d (t k) (p.1 k,p.2 k) (q.1 k,q.2 k) else 0

/-- PDF p.14: Upsilon_i has exactly i normalized Bell projectors. -/
def bellSectorSum (d n j : ℕ) (hd : 0 < d) :
    Matrix ((Fin n → Fin d) × (Fin n → Fin d))
      ((Fin n → Fin d) × (Fin n → Fin d)) ℂ :=
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let phi := pureDensity (finiteMaxEntangled (Fin d))
  fun p q => ∑ t : Fin n → Bool,
    if (Finset.univ.filter (fun k => t k = true)).card = j then
      ∏ k, (if t k then phi else 1 - phi) (p.1 k,p.2 k) (q.1 k,q.2 k) else 0

/-- PDF pp.13--14, (A1): real sector coefficients, embedded into complex matrices. -/
def ansatz (d n : ℕ) (x : Fin (n + 1) → ℝ) :=
  ∑ j : Fin (n + 1), (x j : ℂ) • sectorSum d n j

/-- PDF p.14, (A3): partial-transpose coefficients with zero-extended binomials.
The explicit guard prevents truncated natural subtraction introducing extra terms. -/
def coeffM (d n : ℕ) (i j : Fin (n + 1)) : ℝ :=
  (2 ^ n : ℝ)⁻¹ * ∑ k ∈ Finset.range (min i.val j.val + 1),
    if j.val - k ≤ n - i.val then
      (Nat.choose (n - i.val) (j.val - k) : ℝ) * (Nat.choose i.val k : ℝ) *
        (1 + (d : ℝ)) ^ (i.val - k) * (1 - (d : ℝ)) ^ k else 0

/-- PDF p.14: partial-trace coefficients g_j; the remaining identity acts on input. -/
def coeffG (d n : ℕ) (j : Fin (n + 1)) : ℝ :=
  (2 ^ n : ℝ)⁻¹ * Nat.choose n j.val * ((d : ℝ) + 1) ^ (n - j.val) *
    ((d : ℝ) - 1) ^ j.val

/-- PDF p.14, (A4): essential factor d^n, including the endpoint convention 0^0=1. -/
def lpObjective (d n : ℕ) (alpha : ℝ) (x : Fin (n + 1) → ℝ) : ℝ :=
  (d : ℝ)^n * ∑ j : Fin (n + 1), (Nat.choose n j.val : ℝ) *
    (1 - alpha) ^ (n - j.val) * alpha ^ j.val * x j

/-- PDF p.14, (A5)--(A8): n+1 real variables with independently selectable NS/PPTp constraints. -/
def WernerLPFeasible (d n K : ℕ) (s p : Bool) (x : Fin (n + 1) → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ ((d : ℝ)^n)⁻¹) ∧
  (s = true → (∑ j, coeffG d n j * x j) = ((K : ℝ)^2)⁻¹) ∧
  (p = true → ∀ i, -(((d : ℝ)^n)⁻¹ / K) ≤ (∑ j, coeffM d n i j * x j) ∧
    (∑ j, coeffM d n i j * x j) ≤ ((d : ℝ)^n)⁻¹ / K)

/-- PDF p.12, Example 9: corrected common 1/9 normalization of the printed Lambda. -/
def exampleLambda := ansatz 3 2 (fun j =>
  if j.val = 0 then (3 / 32 : ℝ) / 9 else if j.val = 1 then (7 / 32 : ℝ) / 9 else 1 / 9)

/-- PDF p.12, Fig.7: Z- or X-basis ket a, selected by Bob's bit b. -/
def measurementKet (b a i : Fin 2) : ℂ :=
  if b = 0 then (if i = a then 1 else 0)
  else ((if a = 1 ∧ i = 1 then -1 else 1 : ℝ) / Real.sqrt 2 : ℝ)

/-- PDF pp.12--13, Fig.7: the independently specified randomized measurement operation.
Both outputs are diagonal, and Bob's independent uniform bit is the second output. -/
def bonusOperation : Superop (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fun X u v => if u = v then (2 : ℂ)⁻¹ * ∑ b : Fin 2, ∑ a : Fin 2,
    if u.1.val = (a.val + u.2.val) % 2 then
      ∑ i : Fin 2, ∑ j : Fin 2,
        conj (measurementKet b a i) * X (i,b) (j,b) * measurementKet b a j
    else 0 else 0

/-- PDF pp.12--13: an unassisted one-use perfect qubit transmission code for a side channel. -/
def PerfectQubit {Q R : Type*} [Fintype Q] [Fintype R] (F : Superop Q R) : Prop :=
  ∃ E : Superop (Fin 2) Q, ∃ D : Superop R (Fin 2),
    IsChannel E ∧ IsChannel D ∧ ∀ X, D (F (E X)) = X

/-- Sanity: the orientation in (60) gives epsilon_012=+1 and epsilon_021=-1. -/
example : epsilon3 0 1 2 = 1 ∧ epsilon3 0 2 1 = -1 := by
  norm_num [epsilon3] <;> omega

/-- Sanity: Example 9's antisymmetric coefficient is 1/9, not one. -/
example : (fun j : Fin 3 => if j.val = 0 then (3 / 32 : ℝ) / 9
    else if j.val = 1 then (7 / 32 : ℝ) / 9 else 1 / 9) 2 = 1 / 9 := by norm_num

/-- PDF pp.14--15: generalized Pauli correction, with positive phase and shift X^a Z^b.
The message c is identified with (a,b) by finProdFinEquiv. -/
def teleportWeyl (d : ℕ) (c : Fin (d * d)) : Matrix (Fin d) (Fin d) ℂ :=
  let ab := (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).symm c
  fun i j => if i.val = (j.val + ab.1.val) % d then
    Complex.exp (((2 * Real.pi * (ab.2.val : ℝ) * j.val / d : ℝ) : ℂ) * Complex.I)
  else 0

/-- PDF pp.14--15: the Bell measurement vectors (U_c tensor I)|phi>.
This convention pairs with the correction U_c, not its inverse. -/
def bellKet (d : ℕ) (c : Fin (d * d)) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun p => teleportWeyl d c p.1 p.2 / (Real.sqrt d : ℂ))

/-- PDF pp.14--15: complete Bell measurement with a classical outcome. -/
def bellMeasure (d : ℕ) : Superop (Fin d × Fin d) (Fin (d * d)) :=
  fun X c e => if c = e then
    (pureDensity (bellKet d c) * X).trace else 0

/-- PDF pp.14--15: actual bipartite teleportation code, with one shared Bell state. -/
def teleportCode (d : ℕ) (hd : 0 < d) :
    Superop (Fin d × Fin (d * d)) (Fin (d * d) × Fin d) :=
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  eaOp (pureDensity (finiteMaxEntangled (Fin d))) (bellMeasure d) (classicalControlledUnitary (teleportWeyl d))

/-- PDF pp.14--15: actual bipartite dense-coding code, with one shared Bell state. -/
def denseCode (d : ℕ) (hd : 0 < d) :
    Superop (Fin (d * d) × Fin d) (Fin d × Fin (d * d)) :=
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  eaOp (pureDensity (finiteMaxEntangled (Fin d))) (classicalControlledUnitary (teleportWeyl d)) (bellMeasure d)

/-- PDF p.14, corrected (B1): input/output dephasing around permutation averaging.
The printed permutation average alone does not remove quantum coherences. -/
def dephasedPermutationTwirl (d : ℕ) (M : Superop (Fin d) (Fin d)) : Superop (Fin d) (Fin d) :=
  fun X => dephasing ((Nat.factorial d : ℂ)⁻¹ •
    ∑ pi : Equiv.Perm (Fin d), conjSuperop ((permutationMatrix pi)ᴴ)
      (M (conjSuperop (permutationMatrix pi) (dephasing X))))

/-- PDF p.14: isotropic depolarizing channel parameterized by entanglement fidelity.
Dimension one is handled separately; f is not the depolarizing mixing weight. -/
def fidelityDepolarizing (d : ℕ) (f : ℝ) : Superop (Fin d) (Fin d) :=
  if d = 1 then (fun X => X) else
    let a : ℝ := ((d : ℝ)^2 * f - 1) / ((d : ℝ)^2 - 1)
    fun X => (a : ℂ) • X + (((1 - a) / d : ℝ) : ℂ) • (X.trace • 1)

/-- PDF p.14: d-ary symmetric classical channel parameterized by success probability. -/
def symmetricClassical (d : ℕ) (p : ℝ) : Superop (Fin d) (Fin d) :=
  if d = 1 then dephasing else
    fun X i j => if i = j then (p : ℂ) * X i i +
      (((1 - p) / ((d : ℝ) - 1) : ℝ) : ℂ) * (∑ k, if k = i then 0 else X k k)
    else 0

/-- PDF p.15, (B6): fully specified CPTP teleportation conversion with corrected twirls. -/
def teleportConversion (d : ℕ) (hd : 0 < d)
    (M : Superop (Fin (d * d)) (Fin (d * d))) : Superop (Fin d) (Fin d) :=
  QuditFidelity.haarTwirl d hd (link d (dephasedPermutationTwirl (d * d) M) (teleportCode d hd))

/-- PDF p.15, (B8): fully specified CPTP dense-coding conversion with corrected twirls. -/
def denseConversion (d : ℕ) (hd : 0 < d)
    (N : Superop (Fin d) (Fin d)) : Superop (Fin (d * d)) (Fin (d * d)) :=
  dephasedPermutationTwirl (d * d) (link (d * d) (QuditFidelity.haarTwirl d hd N) (denseCode d hd))

/-- Sanity: the scalar isotropic channel is the identity, without division by d^2-1. -/
example (X : Matrix (Fin 1) (Fin 1) ℂ) : fidelityDepolarizing 1 1 X = X := by
  simp [fidelityDepolarizing]

/-- Sanity: the zero-outcome projection for Bob's b=0 is the computational ket. -/
example : measurementKet 0 0 0 = 1 ∧ measurementKet 0 0 1 = 0 := by
  norm_num [measurementKet]

section Statements

variable {I O : Type} [Fintype I] [Nonempty I] [Fintype O] [Nonempty O]

end Statements

/-- PDF pp.6--7, (29),(36): the actual twirled bipartite operation reconstructed
from rho,Lambda. Used only at K>=2; the scalar case of Theorem 3 is separate. -/
def reconstructedCode {I O : Type*} [Fintype I] [Fintype O] (K : ℕ) (hK : 0 < K)
    (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ) :
    Superop (Fin K × O) (I × Fin K) :=
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  let phi := pureDensity (finiteMaxEntangled (Fin K))
  let G := (((K : ℂ)^2 - 1)⁻¹) • (Matrix.kronecker rho 1 - L)
  fun X u v => ∑ a, ∑ a2, ∑ b, ∑ b2, X (a,b) (a2,b2) * (K : ℂ) *
    (phi (u.2,a) (v.2,a2) * L (u.1,b) (v.1,b2) +
      (1 - phi) (u.2,a) (v.2,a2) * G (u.1,b) (v.1,b2))

end QAlgorithms.Papers.Independent.Support50.P11


