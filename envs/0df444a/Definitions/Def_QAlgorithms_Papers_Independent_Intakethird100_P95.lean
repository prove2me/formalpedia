-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P95
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P95
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T09:22:57.48726+00:00
-- url     : https://prove2.me/theorems/b7ad1c5b-d3ff-493d-ba60-180a8924de08
-- title:
--   Definitions for Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose
-- statement:
--   The objects the formalized statements of *Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose* (arXiv:0801.4322) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `schmidtRenyi`: PDF p.2, equation (5): finite orders, with separate support and Shannon branches.
--   - `largestProbability`: PDF p.2, equation (5): maximum Schmidt probability. Its range is finite; normalization ensures it is nonempty and has a strictly positive maximum.
--   - `renyiInfinity`: PDF p.2, equation (5): the infinity order is a separate branch.
--   - `schmidtDensity`: PDF p.2, equation (1): the normalized Schmidt-form density when lam is a probability vector.
--   - `bobTransposeLinear`: PDF p.2, equation (4): complex-linear packaging of the accepted Bob partial transpose. The entry function is reused, rather than copied.
--   - `PPTChannel`: PDF p.2: CPTP and complete positivity of Gamma_out L Gamma_in. The accepted IsCompletelyPositive quantifies over every finite ancilla.
--   - `Reach`: PDF p.2: deterministic exact operational reachability, independently of all SDPs.
--   - `tensorSpectrum`: PDF p.3: tensor Schmidt probabilities. The empty tensor is the rank-one product state.
--   - `rhoPower`: PDF p.3: n copies, with all of Alice's copies grouped opposite all of Bob's.
--   - `ValidLengths`: PDF p.3, Definitions 1–2: positive block lengths tending to infinity.
--   - `RateLimit`: PDF p.3, Definitions 1–2: normalized log resource rank, independent of the protocols.
--   - `CostRates`: PDF p.3, Definition 2: achievable formation rates. Exact means equality at EVERY block; otherwise the trace norm error tends to zero.
--   - `DistillationRates`: PDF p.3, Definition 1: achievable distillation rates with zero error at every block in the exact case, and vanishing trace norm error otherwise.
--   - `pptEntanglementCost`: PDF p.3, Definition 2: operational infimum, retaining infinite values.
--   - `pptDistillableEntanglement`: PDF p.3, Definition 1: operational supremum, retaining infinite values.
--   - `PreparationFeasible`: PDF p.5, equation (14): one common Hermitian positive variable P in BOTH inequalities.
--   - `preparationValues`: PDF p.5, equation (14): objective set of the general mixed-state preparation SDP.
--   - `preparationValue`: PDF p.5, equation (14): infimum defined from the SDP, independently of reachability. Lemma 8 additionally asserts a minimum, excluding empty/unbounded default infima.
--   - `SymIndex`: PDF p.5: symmetric coordinates, one for each j ≤ i.
--   - `AntiIndex`: PDF p.5: antisymmetric coordinates, one for each j < i.
--   - `symmetricSchmidtProjector`: PDF p.5: sigma_ii is |ii><ii|; off diagonal symmetric projectors include 1/2.
--   - `antisymmetricSchmidtProjector`: PDF p.5: antisymmetric projectors include 1/2.
--   - `coordinateMatrix`: PDF pp.5–6, equations (20),(29): partially transposed coordinate matrix.
--   - `SchmidtPrimalFeasible`: PDF p.5, equation (20): the primal constraints.
--   - `schmidtPrimalObjective`: PDF p.5, equation (20): each real coordinate is counted once.
--   - `primalValues`: PDF p.5, equation (20): the set of feasible objective values.
--   - `primalValue`: PDF p.5, equation (20): T is defined independently as an SDP infimum; Proposition 9 records its attainment.
--   - `SchmidtDualFeasible`: PDF p.6, equation (29): upper bounds only, with no nonnegativity constraints on coordinates.
--   - `schmidtDualObjective`: PDF p.6, equation (28): dual objective with both weighted sums subtracted.
--   - `schmidtDualValues`: PDF p.6, equation (28): the dual's objective set.
--   - `rankOneValues`: PDF p.7, equation (36): rank EXACTLY one, without the spurious zero witness in (A3).
--   - `rankOneValue`: PDF p.7, Remark 14: supremum version of the restricted value; no assertion of attainment. Its nonemptiness and upper boundedness are conclusions of Remark 14 below.
--   - `IsUniformRank`: PDF pp.2,7,9: equality to Phi_K up to local unitaries and zero padding.
--   - `CatalyticPreparation`: PDF p.9, Theorem 21: exact, uncorrelated return of a finite maximally entangled catalyst.
--   - `faceQuadratic`: PDF p.11, (A4): the actual quadratic objective, with all diagonal terms in the second sum.
--   - `OnFace`: PDF pp.11–12: a point on the CLOSED face F_C; negative free coordinates are allowed.
--   - `FaceStationary`: PDF p.12, (A6): stationary for the restriction to the affine hull H_C and lying on F_C. The free-coordinate derivative of faceQuadratic is 2 / (K^2-1) times (sum_i x_i - K*x_j); this is not a constrained local extremum.
--   - `faceValue`: PDF p.12, (A7): stationary value; cast BEFORE subtraction. Under Lemma 23's hypotheses the denominator cannot vanish. Negative denominators are retained.
--   - `exampleSpectrum`: PDF p.4, Example 7: the displayed multiset, independent of its erroneous down-arrow label.
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, https://arxiv.org/abs/0801.4322v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

/-!
Matthews and Winter, arXiv:0801.4322v2. All page numbers are PDF pages.
Paper-specific finite-dimensional definitions are local to this paper; exact
accepted primitives are imported without local copies. They do not implement the
arbitrary-separable-space interfaces requested by the separate 2007.14270 paper.
Theorems 13 and 20 and Conjectures 19 and 22 are deferred in HARD.md.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder
open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P95

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact primitives from the pinned accepted library; no local aliases.
open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)
open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability)
open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)
open QAlgorithms.Papers.Independent.Information100.P19 (outer)
open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)
open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

/-- PDF p.2, equation (5): finite orders, with separate support and Shannon branches. -/
def schmidtRenyi {I : Type*} [Fintype I] (t : ℝ) (lam : I → ℝ) : ℝ :=
  if t = 0 then logTwo ((Finset.univ.filter fun i => lam i ≠ 0).card : ℝ)
  else if t = 1 then - ∑ i, lam i * logTwo (lam i)
  else logTwo (∑ i, Real.rpow (lam i) t) / (1 - t)

/-- PDF p.2, equation (5): maximum Schmidt probability. Its range is finite;
normalization ensures it is nonempty and has a strictly positive maximum. -/
def largestProbability {I : Type*} [Fintype I] (lam : I → ℝ) : ℝ :=
  sSup (Set.range lam)

/-- PDF p.2, equation (5): the infinity order is a separate branch. -/
def renyiInfinity {I : Type*} [Fintype I] (lam : I → ℝ) : ℝ :=
  - logTwo (largestProbability lam)

/-- PDF p.2, equation (1): the normalized Schmidt-form density when lam is a probability vector. -/
def schmidtDensity {I : Type*} (lam : I → ℝ) : Matrix (I × I) (I × I) ℂ :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then (Real.sqrt (lam p.1 * lam q.1) : ℂ) else 0

/-- PDF p.2, equation (4): complex-linear packaging of the accepted Bob partial
transpose. The entry function is reused, rather than copied. -/
def bobTransposeLinear {A B : Type*} :
    Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix (A × B) (A × B) ℂ where
  toFun := QAlgorithms.Papers.Independent.Information100.P04.gamma
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- PDF p.2: CPTP and complete positivity of Gamma_out L Gamma_in.
The accepted IsCompletelyPositive quantifies over every finite ancilla. -/
structure PPTChannel (A B C D : Type*) [Fintype A] [Fintype B]
    [Fintype C] [Fintype D] where
  map : Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix (C × D) (C × D) ℂ
  completelyPositive : QAlgorithms.Entanglement.IsCompletelyPositive map
  tracePreserving : ∀ X, (map X).trace = X.trace
  transposeCompletelyPositive :
    QAlgorithms.Entanglement.IsCompletelyPositive (bobTransposeLinear.comp (map.comp bobTransposeLinear))

/-- PDF p.2: deterministic exact operational reachability, independently of all SDPs. -/
def Reach {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (X : Matrix (A × B) (A × B) ℂ) (Y : Matrix (C × D) (C × D) ℂ) : Prop :=
  ∃ L : PPTChannel A B C D, L.map X = Y

/-- PDF p.3: tensor Schmidt probabilities. The empty tensor is the rank-one product state. -/
def tensorSpectrum {I : Type*} (lam : I → ℝ) (n : ℕ) : (Fin n → I) → ℝ :=
  fun x => ∏ j, lam (x j)

/-- PDF p.3: n copies, with all of Alice's copies grouped opposite all of Bob's. -/
def rhoPower {I : Type*} (lam : I → ℝ) (n : ℕ) := schmidtDensity (tensorSpectrum lam n)

/-- PDF p.3, Definitions 1–2: positive block lengths tending to infinity. -/
def ValidLengths (n K : ℕ → ℕ) : Prop :=
  (∀ j, 0 < n j) ∧ Tendsto n atTop atTop ∧ (∀ j, 0 < K j)

/-- PDF p.3, Definitions 1–2: normalized log resource rank, independent of the protocols. -/
def RateLimit (n K : ℕ → ℕ) (R : ℝ) : Prop :=
  Tendsto (fun j => logTwo (K j : ℝ) / (n j : ℝ)) atTop (nhds R)

/-- PDF p.3, Definition 2: achievable formation rates. Exact means equality at
EVERY block; otherwise the trace norm error tends to zero. -/
def CostRates {I : Type*} [Fintype I] (lam : I → ℝ) (zeroError : Bool) : Set EReal :=
  {r | ∃ R : ℝ, r = (R : EReal) ∧ ∃ n K : ℕ → ℕ,
    ValidLengths n K ∧ RateLimit n K R ∧
    ∃ L : (j : ℕ) → PPTChannel (Fin (K j)) (Fin (K j)) (Fin (n j) → I) (Fin (n j) → I),
      if zeroError then ∀ j, (L j).map (maximallyEntangledDensity (K j)) = rhoPower lam (n j)
      else Tendsto (fun j => QAlgorithms.traceNorm
        ((L j).map (maximallyEntangledDensity (K j)) - rhoPower lam (n j))) atTop (nhds 0)}

/-- PDF p.3, Definition 1: achievable distillation rates with zero error at every
block in the exact case, and vanishing trace norm error otherwise. -/
def DistillationRates {I : Type*} [Fintype I] (lam : I → ℝ) (zeroError : Bool) : Set EReal :=
  {r | ∃ R : ℝ, r = (R : EReal) ∧ ∃ n K : ℕ → ℕ,
    ValidLengths n K ∧ RateLimit n K R ∧
    ∃ L : (j : ℕ) → PPTChannel (Fin (n j) → I) (Fin (n j) → I) (Fin (K j)) (Fin (K j)),
      if zeroError then ∀ j, (L j).map (rhoPower lam (n j)) = maximallyEntangledDensity (K j)
      else Tendsto (fun j => QAlgorithms.traceNorm
        (maximallyEntangledDensity (K j) - (L j).map (rhoPower lam (n j)))) atTop (nhds 0)}

/-- PDF p.3, Definition 2: operational infimum, retaining infinite values. -/
def pptEntanglementCost {I : Type*} [Fintype I] (lam : I → ℝ) (zeroError : Bool) : EReal :=
  sInf (CostRates lam zeroError)

/-- PDF p.3, Definition 1: operational supremum, retaining infinite values. -/
def pptDistillableEntanglement {I : Type*} [Fintype I] (lam : I → ℝ) (zeroError : Bool) : EReal :=
  sSup (DistillationRates lam zeroError)

/-- PDF p.5, equation (14): one common Hermitian positive variable P in BOTH inequalities. -/
def PreparationFeasible {A B : Type*} [Fintype A] [Fintype B] (K : ℕ)
    (X P : Matrix (A × B) (A × B) ℂ) : Prop :=
  P.IsHermitian ∧ P.PosSemidef ∧
  Loewner ((-((K : ℝ) - 1) : ℂ) • bobTransposeLinear P) (bobTransposeLinear X) ∧
  Loewner (bobTransposeLinear X) (((K : ℝ) + 1 : ℂ) • bobTransposeLinear P)

/-- PDF p.5, equation (14): objective set of the general mixed-state preparation SDP. -/
def preparationValues {A B : Type*} [Fintype A] [Fintype B]
    (K : ℕ) (X : Matrix (A × B) (A × B) ℂ) : Set ℝ :=
  {v | ∃ P, PreparationFeasible K X P ∧ P.trace.re = v}

/-- PDF p.5, equation (14): infimum defined from the SDP, independently of reachability.
Lemma 8 additionally asserts a minimum, excluding empty/unbounded default infima. -/
def preparationValue {A B : Type*} [Fintype A] [Fintype B]
    (K : ℕ) (X : Matrix (A × B) (A × B) ℂ) : ℝ := sInf (preparationValues K X)

/-- PDF p.5: symmetric coordinates, one for each j ≤ i. -/
abbrev SymIndex (d : ℕ) := {p : Fin d × Fin d // p.2 ≤ p.1}

/-- PDF p.5: antisymmetric coordinates, one for each j < i. -/
abbrev AntiIndex (d : ℕ) := {p : Fin d × Fin d // p.2 < p.1}

/-- PDF p.5: sigma_ii is |ii><ii|; off diagonal symmetric projectors include 1/2. -/
def symmetricSchmidtProjector {d : ℕ} (i j : Fin d) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  if i = j then outer (WithLp.ofLp (QAlgorithms.ket (i, i)))
  else (1 / 2 : ℂ) • outer (WithLp.ofLp (QAlgorithms.ket (i, j)) + WithLp.ofLp (QAlgorithms.ket (j, i)))

/-- PDF p.5: antisymmetric projectors include 1/2. -/
def antisymmetricSchmidtProjector {d : ℕ} (i j : Fin d) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (1 / 2 : ℂ) • outer (WithLp.ofLp (QAlgorithms.ket (i, j)) - WithLp.ofLp (QAlgorithms.ket (j, i)))

/-- PDF pp.5–6, equations (20),(29): partially transposed coordinate matrix. -/
def coordinateMatrix {d : ℕ} (s : SymIndex d → ℝ) (a : AntiIndex d → ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (∑ p, (s p : ℂ) • bobTransposeLinear (symmetricSchmidtProjector p.val.1 p.val.2)) +
  ∑ p, (a p : ℂ) • bobTransposeLinear (antisymmetricSchmidtProjector p.val.1 p.val.2)

/-- PDF p.5, equation (20): the primal constraints. -/
def SchmidtPrimalFeasible {d : ℕ} (K : ℕ) (lam : Fin d → ℝ)
    (s : SymIndex d → ℝ) (a : AntiIndex d → ℝ) : Prop :=
  (∀ p, Real.sqrt (lam p.val.1 * lam p.val.2) / ((K : ℝ) + 1) ≤ s p) ∧
  (∀ p, Real.sqrt (lam p.val.1 * lam p.val.2) / ((K : ℝ) - 1) ≤ a p) ∧
  (coordinateMatrix s a).PosSemidef

/-- PDF p.5, equation (20): each real coordinate is counted once. -/
def schmidtPrimalObjective {d : ℕ} (s : SymIndex d → ℝ) (a : AntiIndex d → ℝ) : ℝ :=
  (∑ p, s p) + ∑ p, a p

/-- PDF p.5, equation (20): the set of feasible objective values. -/
def primalValues {d : ℕ} (K : ℕ) (lam : Fin d → ℝ) : Set ℝ :=
  {v | ∃ s a, SchmidtPrimalFeasible K lam s a ∧ schmidtPrimalObjective s a = v}

/-- PDF p.5, equation (20): T is defined independently as an SDP infimum;
Proposition 9 records its attainment. -/
def primalValue {d : ℕ} (K : ℕ) (lam : Fin d → ℝ) : ℝ := sInf (primalValues K lam)

/-- PDF p.6, equation (29): upper bounds only, with no nonnegativity constraints on coordinates. -/
def SchmidtDualFeasible {d : ℕ} (mu : SymIndex d → ℝ) (t : AntiIndex d → ℝ) : Prop :=
  (∀ p, mu p ≤ 1) ∧ (∀ p, t p ≤ 1) ∧ (coordinateMatrix mu t).PosSemidef

/-- PDF p.6, equation (28): dual objective with both weighted sums subtracted. -/
def schmidtDualObjective {d : ℕ} (K : ℕ) (lam : Fin d → ℝ)
    (mu : SymIndex d → ℝ) (t : AntiIndex d → ℝ) : ℝ :=
  ((K : ℝ) * Real.rpow 2 (schmidtRenyi (1 / 2) lam) - 1) / ((K : ℝ)^2 - 1) -
  ((∑ p, mu p * Real.sqrt (lam p.val.1 * lam p.val.2) / ((K : ℝ) + 1)) +
   ∑ p, t p * Real.sqrt (lam p.val.1 * lam p.val.2) / ((K : ℝ) - 1))

/-- PDF p.6, equation (28): the dual's objective set. -/
def schmidtDualValues {d : ℕ} (K : ℕ) (lam : Fin d → ℝ) : Set ℝ :=
  {v | ∃ mu t, SchmidtDualFeasible mu t ∧ schmidtDualObjective K lam mu t = v}

/-- PDF p.7, equation (36): rank EXACTLY one, without the spurious zero witness in (A3). -/
def rankOneValues {d : ℕ} (K : ℕ) (lam : Fin d → ℝ) : Set ℝ :=
  {v | ∃ mu t, SchmidtDualFeasible mu t ∧ (coordinateMatrix mu t).rank = 1 ∧
    schmidtDualObjective K lam mu t = v}

/-- PDF p.7, Remark 14: supremum version of the restricted value; no assertion
of attainment. Its nonemptiness and upper boundedness are conclusions of Remark 14 below. -/
def rankOneValue {d : ℕ} (K : ℕ) (lam : Fin d → ℝ) : ℝ := sSup (rankOneValues K lam)

/-- PDF pp.2,7,9: equality to Phi_K up to local unitaries and zero padding. -/
def IsUniformRank {I : Type*} [Fintype I] (lam : I → ℝ) (K : ℕ) : Prop :=
  (Finset.univ.filter fun i => lam i ≠ 0).card = K ∧
  ∀ i, lam i = 0 ∨ lam i = (K : ℝ)⁻¹

/-- PDF p.9, Theorem 21: exact, uncorrelated return of a finite maximally entangled catalyst. -/
def CatalyticPreparation {I : Type} [Fintype I] (K : ℕ) (lam : I → ℝ) : Prop :=
  ∃ C : ℕ, 2 ≤ C ∧ Reach (bipartiteTensor (maximallyEntangledDensity C) (maximallyEntangledDensity K))
    (bipartiteTensor (maximallyEntangledDensity C) (schmidtDensity lam))

/-- PDF p.11, (A4): the actual quadratic objective, with all diagonal terms in the second sum. -/
def faceQuadratic {d : ℕ} (K : ℕ) (x : Fin d → ℝ) : ℝ :=
  (∑ p : AntiIndex d, x p.val.1 * x p.val.2 / ((K : ℝ) - 1)) -
  ∑ p : SymIndex d, x p.val.1 * x p.val.2 / ((K : ℝ) + 1)

/-- PDF pp.11–12: a point on the CLOSED face F_C; negative free coordinates are allowed. -/
def OnFace {d : ℕ} (lam : Fin d → ℝ) (C : Finset (Fin d)) (x : Fin d → ℝ) : Prop :=
  (∀ i, |x i| ≤ Real.sqrt (lam i)) ∧ (∀ i ∈ C, x i = Real.sqrt (lam i))

/-- PDF p.12, (A6): stationary for the restriction to the affine hull H_C and
lying on F_C. The free-coordinate derivative of faceQuadratic is
2 / (K^2-1) times (sum_i x_i - K*x_j); this is not a constrained local extremum. -/
def FaceStationary {d : ℕ} (K : ℕ) (lam : Fin d → ℝ) (C : Finset (Fin d)) : Prop :=
  ∃ x : Fin d → ℝ, OnFace lam C x ∧
    ∀ j, j ∉ C → (∑ i, x i) - (K : ℝ) * x j = 0

/-- PDF p.12, (A7): stationary value; cast BEFORE subtraction. Under Lemma 23's
hypotheses the denominator cannot vanish. Negative denominators are retained. -/
def faceValue {d : ℕ} (K : ℕ) (lam : Fin d → ℝ) (C : Finset (Fin d)) : ℝ :=
  let D : ℝ := (K : ℝ) + (C.card : ℝ) - (d : ℝ)
  (K : ℝ) / (((K : ℝ)^2 - 1) * D) *
    ((∑ i ∈ C, Real.sqrt (lam i))^2 - D * ∑ i ∈ C, lam i)

/-- PDF p.4, Example 7: the displayed multiset, independent of its erroneous down-arrow label. -/
def exampleSpectrum : Fin 6 → ℝ := ![1/20, 1/20, 1/20, 4/20, 4/20, 9/20]

/-! Sanity examples for the complete local definitions (not theorem proofs). -/

example {A B : Type*} (X : Matrix (A × B) (A × B) ℂ) : bobTransposeLinear (bobTransposeLinear X) = X := rfl

example : bobTransposeLinear (fun p q : Fin 2 × Fin 2 =>
    if p = (0, 1) ∧ q = (1, 0) then (1 : ℂ) else 0) (0, 0) (1, 1) = 1 := by
  change (if ((0, 1) : Fin 2 × Fin 2) = (0, 1) ∧
    ((1, 0) : Fin 2 × Fin 2) = (1, 0) then (1 : ℂ) else 0) = 1
  simp

example : schmidtDensity (fun _ : Fin 1 => (1 : ℝ)) (0, 0) (0, 0) = 1 := by
  norm_num [schmidtDensity]

example {I : Type*} (lam : I → ℝ) (x : Fin 0 → I) : tensorSpectrum lam 0 x = 1 := by
  simp [tensorSpectrum]

example : maximallyEntangledDensity 2 (0, 0) (1, 1) = (1 / 2 : ℂ) := by
  norm_num [maximallyEntangledDensity]

example {A B C D : Type} (X : Matrix (A × B) (A × B) ℂ)
    (Y : Matrix (C × D) (C × D) ℂ) (a a' : A) (b b' : B) (c c' : C) (d d' : D) :
    bipartiteTensor X Y ((a,c),(b,d)) ((a',c'),(b',d')) =
      X (a,b) (a',b') * Y (c,d) (c',d') := rfl

example : symmetricSchmidtProjector (0 : Fin 2) 1 (0, 1) (1, 0) = (1 / 2 : ℂ) := by
  norm_num [symmetricSchmidtProjector, outer, QAlgorithms.ket, PiLp.ofLp_single, Pi.single_apply]

example : antisymmetricSchmidtProjector (0 : Fin 2) 1 (0, 1) (1, 0) = (-1 / 2 : ℂ) := by
  norm_num [antisymmetricSchmidtProjector, outer, QAlgorithms.ket, PiLp.ofLp_single, Pi.single_apply]

example : schmidtRenyi 1 (fun _ : Fin 1 => (1 : ℝ)) = 0 := by
  simp [schmidtRenyi, logTwo]

example : (∑ i, exampleSpectrum i) = 1 := by
  norm_num [exampleSpectrum, Fin.sum_univ_succ]

example {A B : Type*} [Fintype A] [Fintype B] (X P : Matrix (A × B) (A × B) ℂ) :
    PreparationFeasible 2 X P ↔ P.IsHermitian ∧ P.PosSemidef ∧
      Loewner ((-1 : ℂ) • bobTransposeLinear P) (bobTransposeLinear X) ∧
      Loewner (bobTransposeLinear X) ((3 : ℂ) • bobTransposeLinear P) := by
  norm_num [PreparationFeasible]

end QAlgorithms.Papers.Independent.Intakethird100.P95


