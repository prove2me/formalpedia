-- Prove2me | Definitions.Def_OAIQ075A000
-- name    : OAIQ075A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T07:54:35.889134+00:00
-- url     : https://prove2.me/theorems/0f6552ee-c70f-4812-b64d-2b8cc0c5d7a0
-- title:
--   Definitions bundle OAIQ075A000 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 314 declarations of OpenAI's Lean: 87 definitions, 8 inductive types or structures, 23 instances and 196 theorems. The definitions and types are `LinearIsometry.completion`, `LinearMap.extendOfIsometry`, `OAI.BoundedHochschild.CentralCorner.compressMap`, `OAI.BoundedHochschild.CentralCorner.extend`, `OAI.BoundedHochschild.CentralCorner.includeMap`, `OAI.BoundedHochschild.CentralCorner.restrict`, `OAI.BoundedHochschild.Cochain`, `OAI.BoundedHochschild.ExpectedEmbedding`, `OAI.BoundedHochschild.ExpectedEmbedding.extend`, `OAI.BoundedHochschild.ExpectedEmbedding.restrict`, `OAI.BoundedHochschild.GNSTendsto`, `OAI.BoundedHochschild.HasPreadjoint`, `OAI.BoundedHochschild.IsSupportProjection`, `OAI.BoundedHochschild.KadisonRingrose.CompletelyAdditive`, `OAI.BoundedHochschild.KadisonRingrose.FiniteAlgebra`, `OAI.BoundedHochschild.KadisonRingrose.FiniteCorner`, `OAI.BoundedHochschild.KadisonRingrose.HilbertDouble`, `OAI.BoundedHochschild.KadisonRingrose.HomogeneousTypeICorner`, `OAI.BoundedHochschild.KadisonRingrose.IsCentralSupport`, `OAI.BoundedHochschild.KadisonRingrose.IsInfinitePair`, `OAI.BoundedHochschild.KadisonRingrose.NoFiniteCentralSummand`, `OAI.BoundedHochschild.KadisonRingrose.OperatorFactorization`, `OAI.BoundedHochschild.KadisonRingrose.PositiveKernelHilbert`, `OAI.BoundedHochschild.KadisonRingrose.PositiveKernelPreSpace`, `OAI.BoundedHochschild.KadisonRingrose.ProperlyInfiniteProjection`, `OAI.BoundedHochschild.KadisonRingrose.StinespringPreSpace`, `OAI.BoundedHochschild.KadisonRingrose.StinespringSpace`, `OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso`, `OAI.BoundedHochschild.KadisonRingrose.algebraGram`, `OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso`, `OAI.BoundedHochschild.KadisonRingrose.columnTransition`, `OAI.BoundedHochschild.KadisonRingrose.composePartialIso`, `OAI.BoundedHochschild.KadisonRingrose.isometryColumn`, `OAI.BoundedHochschild.KadisonRingrose.kernelForm`, `OAI.BoundedHochschild.KadisonRingrose.kernelPreMap`, `OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns`, `OAI.BoundedHochschild.KadisonRingrose.nestedCornerEquiv`, `OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv`, `OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner`, `OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner` and 55 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundedHochschild_AbelianCentralSupport`, `BoundedHochschild_AbelianSupportEquivalence`, `BoundedHochschild_CentralHomotopy`, `BoundedHochschild_CentralPrimitives`, `BoundedHochschild_CentralSupportCuts`, `BoundedHochschild_CochainLimits`, `BoundedHochschild_Cochains`, `BoundedHochschild_CompleteAdditivity`, `BoundedHochschild_CompletelyBoundedFactorization`, `BoundedHochschild_Conditional`, `BoundedHochschild_CornerEquivalences`, `BoundedHochschild_Corners`, `BoundedHochschild_FiniteCentralDecomposition`, `BoundedHochschild_FiniteMoments`, `BoundedHochschild_FiniteProjectionEquivalence`, `BoundedHochschild_FiniteProjectionExtension`, `BoundedHochschild_Frames`, `BoundedHochschild_HarmonicSums`, `BoundedHochschild_IncrementalPatching`, `BoundedHochschild_InfiniteCentralReduction`, `BoundedHochschild_InfinitePairChains`, `BoundedHochschild_IsometryDefectColumns`, `BoundedHochschild_MatrixDilation`, `BoundedHochschild_MatrixSystems`, `BoundedHochschild_MonotoneLimits`, `BoundedHochschild_NormalModulus`, `BoundedHochschild_OperatorPrimitives`, `BoundedHochschild_PartialIsoCornerEquivalence`, `BoundedHochschild_PartialIsoProducts`, `BoundedHochschild_PartialIsometries`, `BoundedHochschild_PartialUnitaries`, `BoundedHochschild_PaulsenExtension`, `BoundedHochschild_PositiveKernelActions`, `BoundedHochschild_PositiveKernelMatrices`, `BoundedHochschild_PositiveKernelSpace`, `BoundedHochschild_PrimitiveAverages`, `BoundedHochschild_ProperlyInfiniteColumns`, `BoundedHochschild_ProperlyInfiniteCorners`, `BoundedHochschild_PublishedInputs`, `BoundedHochschild_SpectralProjections`, `BoundedHochschild_StarPreduals`, `BoundedHochschild_StinespringKernel`, `BoundedHochschild_StinespringLeftAction`, `BoundedHochschild_TraceExpectations`, `BoundedHochschild_TypeICentralPieces`, `BoundedHochschild_TypeIIDefinitions`, `BoundedHochschild_TypeIMatrixColumns`, `TracialCohomology_CornerComparison`, `TracialCohomology_CornerTraces`, `TracialCohomology_Corners`, `TracialCohomology_PartialRepresentations`, `TracialCohomology_PatchTraces`, `TracialCohomology_RepresentationLimits`, `TracialCohomology_TracialPrimitives`, `WeakInfiniteness_MatrixRepresentation`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A007`, `OAIQ075A008`, `OAIQ075A009`, `OAIQ075A010` and `OAIQ075A012`; the statement `OAI.BoundedHochschild.KadisonRingrose.factorization_of_complete_bound`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ075_KS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib d13f23b's `CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha`; ours is `norm_le_norm_of_nonneg_of_le ha hab`. -/
theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab
section X
variable {𝕜 𝕜₂ E Eₗ F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ] [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup Eₗ] [NormedSpace 𝕜 Eₗ] [NormedAddCommGroup F] [NormedSpace 𝕜₂ F] [CompleteSpace F]

/-- d13f23b's `LinearMap.extendOfIsometry`: a semilinear map into a complete space that agrees in norm
with a dense-range map `e` extends along `e` to a semilinear isometry. -/
noncomputable def _root_.LinearMap.extendOfIsometry (f : E →ₛₗ[σ] F) {e : E →ₗ[𝕜] Eₗ}
    (h_dense : DenseRange e) (h_norm : ∀ x, ‖f x‖ = ‖e x‖) : Eₗ →ₛₗᵢ[σ] F :=
  { toLinearMap := (f.extendOfNorm e).toLinearMap
    norm_map' := by
      intro x
      refine h_dense.induction_on x (isClosed_eq (by fun_prop) continuous_norm) ?_
      intro y
      have := LinearMap.extendOfNorm_eq (f := f) (e := e) h_dense ⟨1, by simp [h_norm]⟩ y
      simp only [ContinuousLinearMap.coe_coe, this, h_norm] }

omit [RingHomIsometric σ] in
theorem _root_.LinearMap.extendOfIsometry_eq (f : E →ₛₗ[σ] F) {e : E →ₗ[𝕜] Eₗ}
    (h_dense : DenseRange e) (h_norm : ∀ x, ‖f x‖ = ‖e x‖) (x : E) :
    f.extendOfIsometry h_dense h_norm (e x) = f x :=
  LinearMap.extendOfNorm_eq (f := f) (e := e) h_dense ⟨1, by simp [h_norm]⟩ x
end X
/-- d13f23b's `NonUnitalStarAlgHom.map_le_map_iff`: an injective ⋆-homomorphism of non-unital C⋆-algebras
reflects the order (Kadison similarity, oaiq-075). -/
theorem _root_.NonUnitalStarAlgHom.map_le_map_iff {F A B : Type*} [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] [PartialOrder A] [StarOrderedRing A] [PartialOrder B]
    [StarOrderedRing B] [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (φ : F) (hφ : Function.Injective φ) {a b : A} : φ a ≤ φ b ↔ a ≤ b := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← sub_nonneg] at h ⊢
    rw [← map_sub] at h
    generalize b - a = z at h
    have hsa : IsSelfAdjoint z := by
      apply hφ
      rw [map_star]
      exact IsSelfAdjoint.of_nonneg h
    let ψ := Unitization.starMap (φ : A →⋆ₙₐ[ℂ] B)
    have hψ : Function.Injective ψ := Unitization.starMap_injective hφ
    have hz : 0 ≤ (ψ (z : Unitization ℂ A)) := by
      rw [Unitization.starMap_inr]
      exact Unitization.inr_nonneg_iff.mpr h
    have hsa' : IsSelfAdjoint (z : Unitization ℂ A) := hsa.inr ℂ
    rw [← Unitization.inr_nonneg_iff]
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ hsa'] 
    intro x hx
    have := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (hsa'.map ψ)).mp hz
    rw [hsa'.map_spectrum_real ψ hψ] at this
    exact this x hx
  · exact OrderHomClass.mono φ h
/-- d13f23b's `LinearIsometry.completion`: a linear isometry extends to the completions
(Kadison similarity, oaiq-075). -/
noncomputable def _root_.LinearIsometry.completion {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →ₗᵢ[𝕜] F) :
    UniformSpace.Completion E →ₗᵢ[𝕜] UniformSpace.Completion F :=
  { toLinearMap := f.toContinuousLinearMap.completion.toLinearMap
    norm_map' := by
      intro x
      refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
      intro y
      simp }
@[simp]
theorem _root_.LinearIsometry.completion_apply_coe {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →ₗᵢ[𝕜] F) (x : E) : f.completion (x : UniformSpace.Completion E) = (f x : UniformSpace.Completion F) :=
  ContinuousLinearMap.completion_apply_coe f.toContinuousLinearMap x
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Cochains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded Hochschild cochains, last-input translation and averaging. -/

noncomputable section


namespace BoundedHochschild

abbrev Cochain (M : Type*) [NormedAddCommGroup M] [NormedSpace ℂ M] (n : ℕ) :=
  ContinuousMultilinearMap ℂ (fun _ : Fin n => M) M


section AlgebraicAveraging
variable {M : Type*} [NormedRing M] [NormedAlgebra ℂ M]


noncomputable def insertLast {n : ℕ} (f : Cochain M (n + 1)) (u : M) : Cochain M n :=
  ((ContinuousLinearMap.apply ℂ M) u).compContinuousMultilinearMap f.curryRight

@[simp] theorem insertLast_apply {n : ℕ} (f : Cochain M (n + 1)) (u : M)
    (v : Fin n → M) : insertLast f u v = f (Fin.snoc v u) := rfl

end AlgebraicAveraging

section CocycleIdentity
variable {M : Type*} [NormedRing M] [NormedAlgebra ℂ M]


noncomputable def rightMultiply {n : ℕ} (f : Cochain M n) (u : M) : Cochain M n :=
  ((ContinuousLinearMap.mul ℂ M).flip u).compContinuousMultilinearMap f

@[simp] theorem rightMultiply_apply {n : ℕ} (f : Cochain M n) (u : M)
    (v : Fin n → M) : rightMultiply f u v = f v * u := rfl

 
noncomputable def lastHomotopy {n : ℕ} (f : Cochain M (n + 1)) (u v : M) : Cochain M n :=
  rightMultiply (insertLast f u) v

@[simp] theorem lastHomotopy_apply {n : ℕ} (f : Cochain M (n + 1)) (u v : M)
    (x : Fin n → M) : lastHomotopy f u v x = f (Fin.snoc x u) * v := rfl

end CocycleIdentity

section UnitaryAveraging
variable {M : Type*} [CStarAlgebra M]

noncomputable def translateLast {n : ℕ} (f : Cochain M (n + 1)) (u : unitary M) :
    Cochain M (n + 1) :=
  rightMultiply
    (f.compContinuousLinearMap (fun i : Fin (n + 1) =>
      if i = Fin.last n then (ContinuousLinearMap.mul ℂ M).flip (u : M)
      else ContinuousLinearMap.id ℂ M)) (star (u : M))

@[simp] theorem translateLast_apply {n : ℕ} (f : Cochain M (n + 1)) (u : unitary M)
    (x : Fin (n + 1) → M) :
    translateLast f u x =
      f (Fin.snoc (fun i : Fin n => x i.castSucc) (x (Fin.last n) * u)) * star (u : M) := by
  change f (fun i => (if i = Fin.last n then (ContinuousLinearMap.mul ℂ M).flip (u : M)
    else ContinuousLinearMap.id ℂ M) (x i)) * star (u : M) = _
  congr 2
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem norm_translateLast_le {n : ℕ} (f : Cochain M (n + 1)) (u : unitary M) :
    ‖translateLast f u‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  rw [translateLast_apply]
  have hnorm (z : M) : ‖z * star (u : M)‖ = ‖z‖ :=
    CStarRing.norm_mul_coe_unitary z (star u)
  rw [hnorm]
  calc
    _ ≤ ‖f‖ * (∏ i : Fin n, ‖x i.castSucc‖) * ‖x (Fin.last n) * (u : M)‖ :=
      f.norm_map_snoc_le _ _
    _ = ‖f‖ * ∏ i, ‖x i‖ := by
      rw [CStarRing.norm_mul_coe_unitary, Fin.prod_univ_castSucc, mul_assoc]

@[simp] theorem translateLast_add {n : ℕ} (f g : Cochain M (n + 1)) (u : unitary M) :
    translateLast (f + g) u = translateLast f u + translateLast g u := by
  ext x
  simp [add_mul]

@[simp] theorem translateLast_smul {n : ℕ} (c : ℂ) (f : Cochain M (n + 1)) (u : unitary M) :
    translateLast (c • f) u = c • translateLast f u := by
  ext x
  simp

 
noncomputable def averageLast {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (f : Cochain M (n + 1)) : Cochain M (n + 1) :=
  ∑' j, (p j : ℂ) • translateLast f (u j)

theorem summable_averageLast {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ j, 0 ≤ p j) (hs : Summable p) (f : Cochain M (n + 1)) :
    Summable (fun j => (p j : ℂ) • translateLast f (u j)) := by
  refine (hs.mul_right ‖f‖).of_norm_bounded (fun j => ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp j)]
  exact mul_le_mul_of_nonneg_left (norm_translateLast_le _ _) (hp j)

theorem norm_averageLast_le {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1) (f : Cochain M (n + 1)) :
    ‖averageLast p u f‖ ≤ ‖f‖ := by
  have hbound (j : ℕ) : ‖(p j : ℂ) • translateLast f (u j)‖ ≤ p j * ‖f‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp j)]
    exact mul_le_mul_of_nonneg_left (norm_translateLast_le _ _) (hp j)
  simpa [averageLast] using tsum_of_norm_bounded (hs.mul_right ‖f‖) hbound

end UnitaryAveraging

end BoundedHochschild
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CentralHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Hochschild differential and homotopies for central idempotents. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

 
def centralCut {n : ℕ} (z : M) (f : Cochain M n) : Cochain M n :=
  f.compContinuousLinearMap (fun _ => ContinuousLinearMap.mul ℂ M z)

@[simp] lemma centralCut_apply {n : ℕ} (z : M) (f : Cochain M n) (v : Fin n → M) :
    centralCut z f v = f (fun i => z*v i) := rfl

lemma central_mul_assoc (z : M) (hz : ∀ a, z*a=a*z) (a b : M) :
    a*(z*b) = z*(a*b) := by rw [← mul_assoc, ← hz, mul_assoc]

lemma central_idempotent_mul (z : M) (hi : z*z=z) (hz : ∀ a, z*a=a*z) (a b : M) :
    (z*a)*(z*b) = z*(a*b) := by
  rw [mul_assoc, central_mul_assoc z hz, ← mul_assoc z z, hi]

end BoundedHochschild

 

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

def leftCoboundary {n : ℕ} (f : Cochain M n) : Cochain M (n+1) :=
  (((ContinuousLinearMap.compContinuousMultilinearMapL ℂ (fun _ : Fin n => M) M M).flip f).comp
    (ContinuousLinearMap.mul ℂ M)).uncurryLeft

@[simp] lemma leftCoboundary_apply {n : ℕ} (f : Cochain M n) (v : Fin (n+1) → M) :
    leftCoboundary f v = v 0 * f (fun i => v i.succ) := rfl

def rightCoboundary {n : ℕ} (f : Cochain M n) : Cochain M (n+1) :=
  ((ContinuousLinearMap.mul ℂ M).compContinuousMultilinearMap f).uncurryRight

@[simp] lemma rightCoboundary_apply {n : ℕ} (f : Cochain M n) (v : Fin (n+1) → M) :
    rightCoboundary f v = f (fun i => v i.castSucc) * v (Fin.last n) := rfl

end BoundedHochschild



open Filter Topology
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CochainLimits
attribute [-simp] _root_.OAI.BoundedHochschild.centralCut_apply _root_.OAI.BoundedHochschild.leftCoboundary_apply _root_.OAI.BoundedHochschild.rightCoboundary_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak-star cochain limits, averaging operators and preadjoints. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

 

def PredualTendsto (a : I → M) (l : Filter I) (b : M) : Prop :=
  ∀ z : X, Tendsto (fun i => e.symm (a i) z) l (𝓝 (e.symm b z))

lemma predual_tendsto_unique {a : I → M} {l : Filter I} [l.NeBot] {b c : M}
    (hb : PredualTendsto e a l b) (hc : PredualTendsto e a l c) : b = c := by
  apply e.symm.injective
  ext z
  exact tendsto_nhds_unique (hb z) (hc z)

lemma predual_tendsto_const (m : M) (l : Filter I) :
    PredualTendsto e (fun _ => m) l m := fun _ => tendsto_const_nhds

lemma predual_tendsto_add {a b : I → M} {l : Filter I} {c d : M}
    (ha : PredualTendsto e a l c) (hb : PredualTendsto e b l d) :
    PredualTendsto e (fun i => a i+b i) l (c+d) := by
  intro z
  simpa only [map_add,add_apply] using (ha z).add (hb z)

lemma predual_tendsto_smul {a : I → M} {l : Filter I} {b : M}
    (ha : PredualTendsto e a l b) (c : ℂ) :
    PredualTendsto e (fun i => c • a i) l (c • b) := by
  intro z
  simpa only [LinearIsometryEquiv.map_smulₛₗ,smul_apply,smul_eq_mul]
    using (ha z).const_mul (starRingEnd ℂ c)

lemma exists_predual_ultralimit (u : Ultrafilter I) (a : I → M) (C : ℝ)
    (hb : ∀ i, ‖a i‖ ≤ C) :
    ∃ b : M, ‖b‖ ≤ C ∧ PredualTendsto e a u b := by
  let j : I → WeakDual ℂ X := fun i => StrongDual.toWeakDual (e.symm (a i))
  have hmem : (u.map j : Filter (WeakDual ℂ X)) ≤
      𝓟 (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) C) := by
    rw [Ultrafilter.coe_map,Filter.map_le_iff_le_comap, Filter.comap_principal]
    apply Filter.le_principal_iff.mpr
    exact Filter.Eventually.of_forall fun i => by
      simpa [j,Metric.mem_closedBall] using hb i
  obtain ⟨b,hb',ht⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ X) C).ultrafilter_le_nhds (u.map j) hmem
  refine ⟨e (WeakDual.toStrongDual b),?_,?_⟩
  · simpa only [LinearIsometryEquiv.norm_map,Set.mem_preimage,
      Metric.mem_closedBall,dist_zero_right] using hb'
  · intro z
    have hjt : Tendsto j (u : Filter I) (𝓝 b) := by
      simpa only [Ultrafilter.coe_map, Filter.Tendsto] using ht
    have hz := (WeakDual.eval_continuous z).tendsto b |>.comp hjt
    change Tendsto (fun i => e.symm (a i) z) (u : Filter I) (𝓝 (b z)) at hz
    simpa only [LinearIsometryEquiv.symm_apply_apply, WeakDual.toStrongDual_apply] using hz



end BoundedHochschild

 

open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

@[simp] theorem translateLast_one {n : ℕ} (f : Cochain M (n+1)) :
    translateLast f 1 = f := by
  ext x
  simp only [translateLast_apply,Submonoid.coe_one,star_one,mul_one]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp] theorem translateLast_mul {n : ℕ} (f : Cochain M (n+1)) (u v : unitary M) :
    translateLast (translateLast f v) u = translateLast f (u*v) := by
  ext x
  simp only [translateLast_apply,Fin.snoc_last,Fin.snoc_castSucc,Submonoid.coe_mul,
    star_mul,mul_assoc]

noncomputable def averageLastCLM {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1) :
    Cochain M (n+1) →L[ℂ] Cochain M (n+1) :=
  LinearMap.mkContinuous
    { toFun := averageLast p u
      map_add' := fun f g => by
        simp only [averageLast,translateLast_add,smul_add]
        exact Summable.tsum_add (summable_averageLast p u hp hs.summable f)
          (summable_averageLast p u hp hs.summable g)
      map_smul' := fun c f => by
        simp only [averageLast,translateLast_smul,smul_comm (p _ : ℂ) c,
          tsum_const_smul'',RingHom.id_apply] }
    1 (fun f => by change ‖averageLast p u f‖ ≤ 1 * ‖f‖; simpa only [one_mul] using norm_averageLast_le p u hp hs f)

@[simp] theorem averageLastCLM_apply {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1) (f : Cochain M (n+1)) :
    averageLastCLM p u hp hs f = averageLast p u f := rfl



end BoundedHochschild

 

open Filter Topology
namespace BoundedHochschild
variable {M X I J : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma predual_tendsto_neg {a : I → M} {l : Filter I} {b : M}
    (h : PredualTendsto e a l b) : PredualTendsto e (fun i => -a i) l (-b) := by
  intro z
  simpa only [map_neg,neg_apply] using (h z).neg

lemma predual_tendsto_sub {a b : I → M} {l : Filter I} {c d : M}
    (ha : PredualTendsto e a l c) (hb : PredualTendsto e b l d) :
    PredualTendsto e (fun i => a i-b i) l (c-d) := by
  simpa only [sub_eq_add_neg] using predual_tendsto_add e ha (predual_tendsto_neg e hb)

lemma predual_norm_le {a : I → M} {l : Filter I} [l.NeBot] {b : M} (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ᶠ i in l, ‖a i‖ ≤ C) (h : PredualTendsto e a l b) : ‖b‖ ≤ C := by
  rw [← e.symm.norm_map b]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro z
  apply le_of_tendsto (h z).norm
  filter_upwards [ha] with i hi
  calc
    ‖e.symm (a i) z‖ ≤ ‖e.symm (a i)‖ * ‖z‖ := (e.symm (a i)).le_opNorm z
    _ ≤ C * ‖z‖ := mul_le_mul_of_nonneg_right (by simpa using hi) (norm_nonneg _)



def HasPreadjoint (L : M →L[ℂ] M) : Prop :=
  ∀ z : X, ∃ z' : X, ∀ a : M, e.symm (L a) z = e.symm a z'

lemma HasPreadjoint.tendsto {L : M →L[ℂ] M} (hL : HasPreadjoint e L)
    {a : I → M} {l : Filter I} {b : M} (h : PredualTendsto e a l b) :
    PredualTendsto e (fun i => L (a i)) l (L b) := by
  intro z
  obtain ⟨z',hz'⟩ := hL z
  simpa only [hz'] using h z'

end BoundedHochschild
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_HarmonicSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Harmonic sine estimates, Fourier windows, tracial Hilbert spaces and unitary power rigidity. -/

noncomputable section


namespace HochschildRigidity
open Finset


section FourierWindows
variable {L : ℕ} [NeZero L]

noncomputable def rootUnitary (j : ZMod L) : unitary ℂ :=
  ⟨ZMod.stdAddChar j, by
    rw [Unitary.mem_iff]
    simp only [Complex.star_def, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul,
      neg_add_cancel, add_neg_cancel, AddChar.map_zero_eq_one, and_self]⟩

@[simp] lemma rootUnitary_coe (j : ZMod L) :
    (rootUnitary j : ℂ) = ZMod.stdAddChar j := rfl

end FourierWindows

section TraceHilbertSpace
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ)
lemma preGNS_norm_mul_le (a b : A) :
    ‖τ.toPreGNS (a * b)‖ ≤ ‖a‖ * ‖τ.toPreGNS b‖ := by
  calc
    _ = ‖τ.leftMulMapPreGNS a (τ.toPreGNS b)‖ := rfl
    _ ≤ ‖τ.leftMulMapPreGNS a‖ * ‖τ.toPreGNS b‖ :=
      (τ.leftMulMapPreGNS a).le_opNorm _
    _ ≤ _ := by
      gcongr
      unfold PositiveLinearMap.leftMulMapPreGNS
      exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
lemma preGNS_norm_star (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a : A) :
    ‖τ.toPreGNS (star a)‖ = ‖τ.toPreGNS a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  push_cast
  simp only [τ.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS, star_star]
  exact htr _ _
lemma preGNS_norm_mul_right_le (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a b : A) :
    ‖τ.toPreGNS (a * b)‖ ≤ ‖b‖ * ‖τ.toPreGNS a‖ := by
  rw [← preGNS_norm_star τ htr, star_mul]
  exact (preGNS_norm_mul_le τ (star b) (star a)).trans_eq
    (by rw [norm_star, preGNS_norm_star τ htr])
lemma preGNS_norm_eq_zero_iff
    (hf : ∀ a : A, τ (star a * a) = 0 → a = 0) (a : A) :
    ‖τ.toPreGNS a‖ = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply hf
    simpa only [PositiveLinearMap.ofPreGNS_toPreGNS, h, Complex.ofReal_zero,
      zero_pow (by decide : 2 ≠ 0)] using (τ.preGNS_norm_sq (τ.toPreGNS a)).symm
  · rintro rfl
    simp

open Finset
open scoped BigOperators

end TraceHilbertSpace

end HochschildRigidity
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MatrixDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix dilations, tracial matrix algebras and bounded linear maps. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildMatrixDilation
noncomputable section
open scoped Matrix ComplexOrder
open Complex
variable {A : Type*} [CStarAlgebra A]

abbrev Mat (A : Type*) := CStarMatrix (Fin 2) (Fin 2) A

end
end HochschildMatrixDilation
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PrimitiveAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace preduals, primitives from averages and finite exactness. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

 

def TraceInPredual : Prop := ∃ z : X, ∀ x : M, τ x = star (e.symm x z)

end BoundedHochschild



open Filter Topology
open scoped ComplexOrder



open MeasureTheory Filter Topology
open scoped ENNReal



open MeasureTheory Filter Topology
open scoped ComplexOrder



open Filter Topology
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal cochains, bounded-ball continuity and primitive construction. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open Filter Topology
open scoped ComplexOrder



open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ)

def GNSTendsto (a : I → M) (l : Filter I) (b : M) : Prop :=
  Tendsto (fun i => ‖τ.toPreGNS (a i-b)‖) l (𝓝 0)

lemma GNSTendsto.const (b : M) (l : Filter I) : GNSTendsto τ (fun _ => b) l b := by
  simp only [GNSTendsto,sub_self,map_zero,norm_zero]
  exact tendsto_const_nhds

lemma GNSTendsto.add {a c : I → M} {l : Filter I} {b d : M}
    (ha : GNSTendsto τ a l b) (hc : GNSTendsto τ c l d) :
    GNSTendsto τ (fun i => a i+c i) l (b+d) := by
  apply squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) (by simpa only [add_zero] using Filter.Tendsto.add ha hc)
  rw [show a i+c i-(b+d)=(a i-b)+(c i-d) by abel,map_add]
  exact norm_add_le _ _

lemma GNSTendsto.neg {a : I → M} {l : Filter I} {b : M} (ha : GNSTendsto τ a l b) :
    GNSTendsto τ (fun i => -a i) l (-b) := by
  simpa only [GNSTendsto,neg_sub_neg,← neg_sub (a := b),map_neg,norm_neg] using ha

lemma GNSTendsto.sub {a c : I → M} {l : Filter I} {b d : M}
    (ha : GNSTendsto τ a l b) (hc : GNSTendsto τ c l d) :
    GNSTendsto τ (fun i => a i-c i) l (b-d) := by
  simpa only [sub_eq_add_neg] using ha.add τ (hc.neg τ)

lemma GNSTendsto.star (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    {a : I → M} {l : Filter I} {b : M} (ha : GNSTendsto τ a l b) :
    GNSTendsto τ (fun i => star (a i)) l (star b) := by
  simpa only [GNSTendsto,← star_sub,preGNS_norm_star τ htr] using ha

lemma GNSTendsto.mul (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    {a c : I → M} {l : Filter I} {b d : M}
    (ha : GNSTendsto τ a l b) (hc : GNSTendsto τ c l d)
    (C : ℝ) (hC : ∀ i, ‖a i‖ ≤ C) :
    GNSTendsto τ (fun i => a i*c i) l (b*d) := by
  have ht := (hc.const_mul C).add (ha.const_mul ‖d‖)
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) ht
  rw [show a i*c i-b*d=a i*(c i-d)+(a i-b)*d by noncomm_ring,map_add]
  exact (norm_add_le _ _).trans (add_le_add
    ((preGNS_norm_mul_le τ _ _).trans (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)))
    (preGNS_norm_mul_right_le τ htr _ _))

lemma GNSTendsto.unique (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)
    {a : I → M} {l : Filter I} [l.NeBot] {b c : M}
    (hb : GNSTendsto τ a l b) (hc : GNSTendsto τ a l c) : b=c := by
  have h : GNSTendsto τ (fun _ : I => (0:M)) l (b-c) := by
    simpa only [sub_self] using hb.sub τ hc
  have hz : ‖τ.toPreGNS (b-c)‖=0 := by
    have ht : Tendsto (fun _ : I => ‖τ.toPreGNS (b-c)‖) l (𝓝 0) := by
      simpa only [GNSTendsto,zero_sub,map_neg,norm_neg] using h
    exact tendsto_nhds_unique tendsto_const_nhds ht
  exact sub_eq_zero.mp ((preGNS_norm_eq_zero_iff τ hfaith _).mp hz)

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder



open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)

 

structure IsSupportProjection (a p : M) : Prop where
  proj : IsStarProjection p
  left : p*a=a
  right : a*p=a
  annihilate : ∀ x : M, a*x=0 → p*x=0

lemma IsSupportProjection.le_of_support {a p q : M} (hp : IsSupportProjection a p)
    (hq : IsStarProjection q) (haq : a*q=a) : p ≤ q := by
  apply (hp.proj.le_iff_mul_eq_left hq).mpr
  have hh := hp.annihilate (1-q) (by simp only [mul_sub,mul_one,haq,sub_self])
  simpa only [mul_sub,mul_one,sub_eq_zero,eq_comm] using hh

end BoundedHochschild
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CentralPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Central cut primitives and restriction through expected embeddings. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open Filter Topology



open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def centralOutput {n : ℕ} (p : M) (f : Cochain M n) : Cochain M n :=
  (ContinuousLinearMap.mul ℂ M p).compContinuousMultilinearMap f

@[simp] lemma centralOutput_apply {n : ℕ} (p : M) (f : Cochain M n) (x : Fin n → M) :
    centralOutput p f x=p*f x := rfl

end BoundedHochschild

 

open Filter Topology
namespace BoundedHochschild
variable {M N : Type*} [CStarAlgebra M] [CStarAlgebra N]

 

structure ExpectedEmbedding (N M : Type*) [CStarAlgebra N] [CStarAlgebra M] where
  includeMap : N →L[ℂ] M
  expectMap : M →L[ℂ] N
  include_mul : ∀ a b, includeMap (a*b)=includeMap a*includeMap b
  include_one : includeMap 1=1
  include_star : ∀ a, includeMap (star a)=star (includeMap a)
  include_norm : ∀ a, ‖includeMap a‖=‖a‖
  expect_norm : ∀ a, ‖expectMap a‖ ≤ ‖a‖
  retract : ∀ a, expectMap (includeMap a)=a
  left_module : ∀ a x, expectMap (includeMap a*x)=a*expectMap x
  right_module : ∀ x a, expectMap (x*includeMap a)=expectMap x*a

namespace ExpectedEmbedding
variable (E : ExpectedEmbedding N M)

def restrict {n : ℕ} (f : Cochain M n) : Cochain N n :=
  E.expectMap.compContinuousMultilinearMap (f.compContinuousLinearMap (fun _ => E.includeMap))

def extend {n : ℕ} (g : Cochain N n) : Cochain M n :=
  E.includeMap.compContinuousMultilinearMap (g.compContinuousLinearMap (fun _ => E.expectMap))

@[simp] lemma restrict_apply {n : ℕ} (f : Cochain M n) (x : Fin n → N) :
    E.restrict f x=E.expectMap (f (fun i => E.includeMap (x i))) := rfl
@[simp] lemma extend_apply {n : ℕ} (g : Cochain N n) (x : Fin n → M) :
    E.extend g x=E.includeMap (g (fun i => E.expectMap (x i))) := rfl

end ExpectedEmbedding
end BoundedHochschild
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TraceExpectations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace pairing norms, predual vectors and trace-preserving expectations. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder



open scoped ComplexOrder
namespace HochschildTraceNorm
open HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (htr : ∀ a b : A, τ (a*b)=τ (b*a))

def traceCLM : A →L[ℂ] ℂ where
  toLinearMap := τ.toLinearMap
  cont := map_continuous τ

@[simp] lemma traceCLM_apply (a : A) : traceCLM τ a=τ a := rfl

def tracePair (b : A) : A →L[ℂ] ℂ :=
  (traceCLM τ).comp (ContinuousLinearMap.mul ℂ A b)

@[simp] lemma tracePair_apply (b x : A) : tracePair τ b x=τ (b*x) := rfl

end HochschildTraceNorm

 

open scoped ComplexOrder
namespace BoundedHochschild
open HochschildTraceNorm
variable {N X : Type*} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N) (τ : N →ₚ[ℂ] ℂ)

omit [PartialOrder N] [StarOrderedRing N] in
lemma predual_vector_ext (z w : X) (h : ∀ a : N, e.symm a z=e.symm a w) : z=w := by
  apply (NormedSpace.inclusionInDoubleDualLi ℂ).injective
  ext f
  change f z=f w
  simpa only [e.symm_apply_apply] using h (e f)

variable (hL : ∀ b : N, HasPreadjoint e (ContinuousLinearMap.mul ℂ N b))
  (hτ : TraceInPredual e τ)

omit [StarOrderedRing N] in
include hL hτ in
lemma exists_trace_vector (b : N) : ∃ z : X, ∀ a : N, e.symm a z=star (τ (star b*a)) := by
  obtain ⟨z,hz⟩ := hτ
  obtain ⟨w,hw⟩ := hL (star b) z
  refine ⟨w,fun a => ?_⟩
  rw [hz,star_star,← hw]
  rfl

def traceVector (b : N) : X := Classical.choose (exists_trace_vector e τ hL hτ b)

omit [StarOrderedRing N] in
lemma traceVector_spec (b a : N) : e.symm a (traceVector e τ hL hτ b)=star (τ (star b*a)) :=
  Classical.choose_spec (exists_trace_vector e τ hL hτ b) a

def traceVectorLinear : N →ₗ[ℂ] X where
  toFun := traceVector e τ hL hτ
  map_add' b c := by
    apply predual_vector_ext e
    intro a
    simp only [map_add,traceVector_spec,star_add,add_mul]
  map_smul' r b := by
    apply predual_vector_ext e
    intro a
    simp only [traceVector_spec,map_smul,star_smul,smul_mul_assoc,star_star,RingHom.id_apply]

omit [StarOrderedRing N] in
@[simp] lemma traceVectorLinear_apply (b : N) :
    traceVectorLinear e τ hL hτ b=traceVector e τ hL hτ b := rfl

end BoundedHochschild

 

open scoped ComplexOrder



open scoped ComplexOrder



open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_StarPreduals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak-star continuity of the involution and its predual action. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open Filter Topology
open scoped ComplexOrder
namespace HochschildSakai
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma imag_square (a : M) (t : ℝ) :
    star (1+Complex.I • (t • a))*(1+Complex.I • (t • a))=
      1+t • (Complex.I • (a-star a))+(t^2) • (star a*a) := by
  have ht : star t=t := rfl
  have hi : star Complex.I = -Complex.I := by simp
  simp only [star_add,star_one,star_smul,ht,hi]
  simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm]
  simp only [smul_add,smul_sub,neg_smul]
  match_scalars <;> ring_nf
  all_goals simp

omit [PartialOrder M] [StarOrderedRing M] in
lemma norm_one_bound : ‖(1:M)‖ ≤ 1 := by
  nontriviality M
  simp

omit [PartialOrder M] [StarOrderedRing M] in
lemma norm_imag_add_sq (a : M) (ha : IsSelfAdjoint a) (t : ℝ) :
    ‖(1:M)+Complex.I • (t • a)‖^2 ≤ 1+t^2*‖a‖^2 := by
  rw [pow_two,← CStarRing.norm_star_mul_self,imag_square,ha.star_eq,sub_self,
    smul_zero,smul_zero,add_zero]
  calc
    ‖(1:M)+t^2 • (a*a)‖ ≤ ‖(1:M)‖+‖t^2 • (a*a)‖ := norm_add_le _ _
    _ ≤ 1+t^2*‖a‖^2 := by
      rw [norm_smul,Real.norm_of_nonneg (sq_nonneg _),ha.norm_mul_self]
      exact add_le_add (norm_one_bound (M := M)) le_rfl

lemma imag_linear_bound (a : M) (C : ℝ)
    (h : ∀ t : ℝ, ‖(1:M)+Complex.I • (t • a)‖^2 ≤ 1+t^2*C) (t : ℝ) :
    t • (Complex.I • (a-star a)) ≤ algebraMap ℝ M (t^2*C) := by
  have hn := CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := (1:M)+Complex.I • (t • a))
  have hh := hn.trans (algebraMap_mono M (h t))
  rw [imag_square] at hh
  have hp : 0 ≤ t^2 • (star a*a) := smul_nonneg (sq_nonneg _) (star_mul_self_nonneg a)
  have h := (le_add_of_nonneg_right hp).trans hh
  simpa only [map_add,map_one,add_le_add_iff_left] using h

 

theorem isSelfAdjoint_of_norm_imag_add (a : M) (C : ℝ)
    (h : ∀ t : ℝ, ‖(1:M)+Complex.I • (t • a)‖^2 ≤ 1+t^2*C) :
    IsSelfAdjoint a := by
  let b := Complex.I • (a-star a)
  have hb (t : ℝ) (ht : 0 < t) : b ≤ algebraMap ℝ M (t*C) := by
    have hh := imag_linear_bound a C h t
    have heq : algebraMap ℝ M (t^2*C)=t • algebraMap ℝ M (t*C) := by
      rw [Algebra.smul_def,← map_mul]
      congr 1
      ring
    rw [heq] at hh
    exact (smul_le_smul_iff_of_pos_left ht).mp hh
  have hnb (t : ℝ) (ht : 0 < t) : -b ≤ algebraMap ℝ M (t*C) := by
    have hh := imag_linear_bound a C h (-t)
    have heq : algebraMap ℝ M ((-t)^2*C)=t • algebraMap ℝ M (t*C) := by
      rw [Algebra.smul_def,← map_mul]
      congr 1
      ring
    rw [heq,neg_smul,← smul_neg] at hh
    exact (smul_le_smul_iff_of_pos_left ht).mp hh
  have hb0 : b ≤ 0 := by
    have ht : Tendsto (fun t : ℝ => algebraMap ℝ M (t*C)) (𝓝[>] 0) (𝓝 0) := by
      have ht : Tendsto (fun t : ℝ => t*C) (𝓝[>] 0) (𝓝 (0*C)) :=
        ((continuousAt_id (x := (0:ℝ))).mul_const C).tendsto.mono_left inf_le_left
      simpa only [zero_mul,map_zero,Function.comp_def] using
        (continuous_algebraMap ℝ M).continuousAt.tendsto.comp ht
    exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with t ht using hb t ht)
  have hn0 : -b ≤ 0 := by
    have ht : Tendsto (fun t : ℝ => algebraMap ℝ M (t*C)) (𝓝[>] 0) (𝓝 0) := by
      have ht : Tendsto (fun t : ℝ => t*C) (𝓝[>] 0) (𝓝 (0*C)) :=
        ((continuousAt_id (x := (0:ℝ))).mul_const C).tendsto.mono_left inf_le_left
      simpa only [zero_mul,map_zero,Function.comp_def] using
        (continuous_algebraMap ℝ M).continuousAt.tendsto.comp ht
    exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with t ht using hnb t ht)
  have hz : b=0 := le_antisymm hb0 (neg_nonpos.mp hn0)
  have ha : a-star a=0 := (smul_eq_zero.mp hz).resolve_left Complex.I_ne_zero
  exact (sub_eq_zero.mp ha).symm

end HochschildSakai

 

open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

 

theorem isSelfAdjoint_of_predual_tendsto {a : I → M} {l : Filter I} [l.NeBot]
    {b : M} (C : ℝ) (_hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (hsa : ∀ i, IsSelfAdjoint (a i)) (ht : PredualTendsto e a l b) :
    IsSelfAdjoint b := by
  let := CStarAlgebra.spectralOrder M
  let := CStarAlgebra.spectralOrderedRing M
  apply isSelfAdjoint_of_norm_imag_add b (C^2)
  intro t
  have htC : 0 ≤ 1+t^2*C^2 := by positivity
  have hnorm (i : I) : ‖(1:M)+Complex.I • (t • a i)‖ ≤ Real.sqrt (1+t^2*C^2) := by
    apply (Real.le_sqrt (norm_nonneg _) htC).mpr
    exact (norm_imag_add_sq (a i) (hsa i) t).trans (by
      gcongr
      exact ha i)
  have htw : PredualTendsto e (fun i => (1:M)+Complex.I • (t • a i)) l
      ((1:M)+Complex.I • (t • b)) := by
    simp only [← Complex.coe_smul]
    exact predual_tendsto_add e (predual_tendsto_const e 1 l)
      (predual_tendsto_smul e (predual_tendsto_smul e ht (t:ℂ)) Complex.I)
  exact (Real.le_sqrt (norm_nonneg _) htC).mp
    (predual_norm_le e _ (Real.sqrt_nonneg _) (Eventually.of_forall hnorm) htw)

lemma star_eq_of_sum_sub_selfAdjoint (a b : M)
    (hadd : IsSelfAdjoint (a+b)) (hsub : IsSelfAdjoint (Complex.I • (a-b))) :
    b=star a := by
  have h1 := hadd.star_eq
  have h2 := hsub.star_eq
  simp only [star_add] at h1
  have h3 : -(star a-star b)=a-b := by
    apply (smul_right_injective M Complex.I_ne_zero)
    simpa only [star_smul,star_sub,Complex.star_def,map_sub,map_id,Complex.conj_I,
      neg_smul,smul_neg] using h2
  have h4 : (2:ℂ) • (b-star a)=0 := by
    have h3' : star b-star a=a-b := by simpa only [neg_sub] using h3
    calc
      (2:ℂ) • (b-star a) = (a+b-(star a+star b)) - (a-b-(star b-star a)) := by module
      _ = 0 := by rw [h1,h3']; simp
  exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_left (by norm_num))

 

theorem predual_tendsto_star_bounded {a : I → M} {l : Filter I}
    {b : M} (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (ht : PredualTendsto e a l b) :
    PredualTendsto e (fun i => star (a i)) l (star b) := by
  intro z
  rw [Filter.tendsto_iff_ultrafilter]
  intro u hu
  have htu : PredualTendsto e a (u : Filter I) b := fun x => (ht x).mono_left hu
  obtain ⟨c,_,hc⟩ := exists_predual_ultralimit e u (fun i => star (a i)) C
    (fun i => by simpa only [norm_star] using ha i)
  have hadd : IsSelfAdjoint (b+c) :=
    isSelfAdjoint_of_predual_tendsto e (2*C) (by positivity)
      (fun i => (norm_add_le (a i) (star (a i))).trans (by
        simpa only [norm_star,two_mul] using add_le_add (ha i) (ha i)))
      (fun i => by simp only [IsSelfAdjoint,star_add,star_star,add_comm])
      (predual_tendsto_add e htu hc)
  have hsub : IsSelfAdjoint (Complex.I • (b-c)) :=
    isSelfAdjoint_of_predual_tendsto e (2*C) (by positivity)
      (fun i => by
        rw [norm_smul,Complex.norm_I,one_mul]
        exact (norm_sub_le (a i) (star (a i))).trans (by
          simpa only [norm_star,two_mul] using add_le_add (ha i) (ha i)))
      (fun i => by simp [IsSelfAdjoint,star_smul,Complex.conj_I,sub_eq_add_neg,add_comm])
      (predual_tendsto_smul e (predual_tendsto_sub e htu hc) Complex.I)
  have hc' := star_eq_of_sum_sub_selfAdjoint b c hadd hsub
  exact hc' ▸ hc z

end HochschildSakai

 

open Filter Topology
namespace HochschildSakai
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

 

theorem mem_predual_of_bounded_weak_continuity [CompleteSpace X]
    (F : StrongDual ℂ (StrongDual ℂ X))
    (hF : ∀ (a : Finset X → StrongDual ℂ X),
      (∀ s, ‖a s‖ ≤ 1) →
      (∀ x, Tendsto (fun s => a s x) atTop (𝓝 0)) →
      Tendsto (fun s => F (a s)) atTop (𝓝 0)) :
    ∃ x : X, ∀ f : StrongDual ℂ X, F f=f x := by
  classical
  let : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
  let : NormedAddCommGroup (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
  let j := NormedSpace.inclusionInDoubleDual ℂ X
  let j₀ : X →ₗ[ℂ] Module.Dual ℂ (StrongDual ℂ X) :=
    (ContinuousLinearMap.coeLM ℂ).comp j.toLinearMap
  have hsmall (ε : ℝ) (hε : 0 < ε) : ∃ s : Finset X,
      ∀ f : StrongDual ℂ X, ‖f‖ ≤ 1 → (∀ x ∈ s, f x=0) → ‖F f‖ ≤ ε := by
    by_contra h
    push Not at h
    choose a ha haz hFa using h
    have ha0 (x : X) : Tendsto (fun s => a s x) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      apply Filter.eventually_atTop.mpr
      refine ⟨{x},fun s hs => ?_⟩
      exact (haz s x (hs (Finset.mem_singleton_self x))).symm
    have hh := (hF a ha ha0).norm.eventually (gt_mem_nhds (show ‖(0:ℂ)‖ < ε by simpa only [norm_zero] using hε))
    obtain ⟨s,hs⟩ := hh.exists
    exact (not_lt_of_ge (le_of_lt hs)) (hFa s)
  have happ (ε : ℝ) (hε : 0 < ε) : ∃ x : X, ‖F-j x‖ ≤ ε := by
    obtain ⟨s,hs⟩ := hsmall ε hε
    let W : Submodule ℂ (Module.Dual ℂ (StrongDual ℂ X)) :=
      Submodule.span ℂ (j₀ '' (s : Set X))
    have hfin : (j₀ '' (s : Set X)).Finite := s.finite_toSet.image j₀
    let : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ hfin
    let K : Submodule ℂ (StrongDual ℂ X) := W.dualCoannihilator
    let : NormedAddCommGroup K := inferInstance
    let : NormedSpace ℂ K := inferInstance
    let FK : StrongDual ℂ K := F.comp K.subtypeL
    have hFK : ‖FK‖ ≤ ε := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
      intro f hf
      apply hs f hf.le
      intro x hx
      have hmem : j₀ x ∈ W := Submodule.subset_span ⟨x,hx,rfl⟩
      exact ((Submodule.mem_dualCoannihilator (Φ := W) f.val).mp f.property) (j₀ x) hmem
    obtain ⟨G,hG,hGn⟩ := _root_.exists_extension_norm_eq K FK
    have hmem : (F-G).toLinearMap ∈ W := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)]
      apply (Submodule.mem_dualAnnihilator _).mpr
      intro f hf
      change F f-G f=0
      exact sub_eq_zero.mpr (hG ⟨f,hf⟩).symm
    have hle : W ≤ LinearMap.range j₀ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x,_,rfl⟩
      exact ⟨x,rfl⟩
    obtain ⟨x,hx⟩ := hle hmem
    have hx' : j x=F-G := by
      ext f
      exact LinearMap.congr_fun hx f
    refine ⟨x,?_⟩
    rw [hx']
    calc
      ‖F-(F-G)‖ = ‖G‖ := congrArg norm (sub_sub_cancel F G)
      _ = ‖FK‖ := hGn
      _ ≤ ε := hFK

  have hclosed : IsClosed (Set.range j) :=
    (NormedSpace.inclusionInDoubleDualLi ℂ (E := X)).isometry.isClosedEmbedding.isClosed_range
  have hmem : F ∈ closure (Set.range j) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨x,hx⟩ := happ (ε/2) (half_pos hε)
    refine ⟨j x,⟨x,rfl⟩,?_⟩
    rw [dist_eq_norm]
    exact hx.trans_lt (half_lt_self hε)
  obtain ⟨x,hx⟩ := hclosed.closure_eq ▸ hmem
  exact ⟨x,fun f => by rw [← hx]; rfl⟩

end HochschildSakai

 

open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

 

theorem exists_star_predual_vector (z : X) :
    ∃ w : X, ∀ a : M, e.symm (star a) z = star (e.symm a w) := by
  let : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
  let L : StrongDual ℂ X →ₗ[ℂ] ℂ :=
    { toFun := fun f => star (e.symm (star (e f)) z)
      map_add' := by intro f g; simp
      map_smul' := by intro r f; simp [map_smulₛₗ] }
  have hb (f : StrongDual ℂ X) : ‖L f‖ ≤ ‖z‖ * ‖f‖ := by
    change ‖star (e.symm (star (e f)) z)‖ ≤ _
    rw [norm_star,mul_comm]
    simpa only [e.symm.norm_map,norm_star,e.norm_map] using
      (e.symm (star (e f))).le_opNorm z
  let F := L.mkContinuous ‖z‖ hb
  have hF (a : Finset X → StrongDual ℂ X) (ha : ∀ s, ‖a s‖ ≤ 1)
      (hta : ∀ x, Tendsto (fun s => a s x) atTop (𝓝 0)) :
      Tendsto (fun s => F (a s)) atTop (𝓝 0) := by
    have ht : PredualTendsto e (fun s => e (a s)) atTop 0 := by
      intro x
      simpa using hta x
    have hs := predual_tendsto_star_bounded e 1 zero_le_one
      (fun s => by simpa only [e.norm_map] using ha s) ht
    simpa [F,L] using (hs z).star
  obtain ⟨w,hw⟩ := mem_predual_of_bounded_weak_continuity F hF
  refine ⟨w,fun a => ?_⟩
  have hh := congrArg star (hw (e.symm a))
  simpa [F,L] using hh

 

theorem predual_tendsto_star {a : I → M} {l : Filter I} {b : M}
    (ha : PredualTendsto e a l b) :
    PredualTendsto e (fun i => star (a i)) l (star b) := by
  intro z
  obtain ⟨w,hw⟩ := exists_star_predual_vector e z
  simpa only [hw] using (ha w).star

end HochschildSakai
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MonotoneLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monotone weak-star limits and bounded GNS limits. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

 

theorem nonneg_of_bounded_predual_limit {a : I → M} {l : Filter I} [l.NeBot]
    {b : M} (C : ℝ) (hC : 0 ≤ C) (ha : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (hp : ∀ᶠ i in l, 0 ≤ a i) (ht : PredualTendsto e a l b) : 0 ≤ b := by
  have hs : PredualTendsto e (fun i => star (a i)) l b := by
    intro z
    apply (ht z).congr'
    filter_upwards [hp] with i hi
    rw [(IsSelfAdjoint.of_nonneg hi).star_eq]
  have hb : IsSelfAdjoint b := predual_tendsto_unique e (predual_tendsto_star e ht) hs
  let c := algebraMap ℝ M C
  have hc : 0 ≤ c := algebraMap_nonneg M hC
  have hac : ∀ᶠ i in l, ‖c-a i‖ ≤ C := by
    filter_upwards [ha,hp] with i hn hi
    have hai : a i ≤ c := (CStarAlgebra.norm_le_iff_le_algebraMap (a i) hC hi).mp hn
    exact (CStarAlgebra.norm_le_iff_le_algebraMap (c-a i) hC (sub_nonneg.mpr hai)).mpr
      (sub_le_self _ hi)
  have hbc : ‖c-b‖ ≤ C := predual_norm_le e C hC hac
    (predual_tendsto_sub e (predual_tendsto_const e c l) ht)
  have hsa : IsSelfAdjoint (c-b) := (IsSelfAdjoint.of_nonneg hc).sub hb
  have hle : c-b ≤ c := hsa.le_algebraMap_norm_self.trans (algebraMap_mono M hbc)
  exact le_of_add_le_add_left (show c+0 ≤ c+b by
    simpa only [add_zero] using sub_le_iff_le_add.mp hle)

 
theorem le_of_bounded_predual_limit {a : I → M} {l : Filter I} [l.NeBot]
    {b c : M} (C : ℝ) (hC : 0 ≤ C) (ha : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (hp : ∀ᶠ i in l, a i ≤ c) (ht : PredualTendsto e a l b) : b ≤ c := by
  apply sub_nonneg.mp
  apply nonneg_of_bounded_predual_limit e (‖c‖+C) (add_nonneg (norm_nonneg _) hC)
    ?_ (hp.mono fun _ hi => sub_nonneg.mpr hi)
    (predual_tendsto_sub e (predual_tendsto_const e c l) ht)
  filter_upwards [ha] with i hi
  exact (norm_sub_le c (a i)).trans (by gcongr)

theorem ge_of_bounded_predual_limit {a : I → M} {l : Filter I} [l.NeBot]
    {b c : M} (C : ℝ) (hC : 0 ≤ C) (ha : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (hp : ∀ᶠ i in l, c ≤ a i) (ht : PredualTendsto e a l b) : c ≤ b := by
  apply sub_nonneg.mp
  apply nonneg_of_bounded_predual_limit e (C+‖c‖) (add_nonneg hC (norm_nonneg _))
    ?_ (hp.mono fun _ hi => sub_nonneg.mpr hi)
    (predual_tendsto_sub e ht (predual_tendsto_const e c l))
  filter_upwards [ha] with i hi
  exact (norm_sub_le (a i) c).trans (by gcongr)

 

theorem exists_monotone_predual_limit [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (a : I → M) (hm : Monotone a) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ∃ b : M, ‖b‖ ≤ C ∧ IsLUB (Set.range a) b ∧ PredualTendsto e a atTop b := by
  let u : Ultrafilter I := Ultrafilter.of atTop
  have hu : (u : Filter I) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨b,hb,ht⟩ := exists_predual_ultralimit e u a C ha
  have hlu (v : Ultrafilter I) (hv : (v : Filter I) ≤ atTop) (c : M)
      (hc : PredualTendsto e a (v : Filter I) c) : IsLUB (Set.range a) c := by
    constructor
    · rintro _ ⟨i,rfl⟩
      apply ge_of_bounded_predual_limit e C hC (Eventually.of_forall ha) ?_ hc
      exact hv ((eventually_ge_atTop i).mono fun j hj => hm hj)
    · intro d hd
      apply le_of_bounded_predual_limit e C hC (Eventually.of_forall ha) ?_ hc
      exact Eventually.of_forall fun i => hd (Set.mem_range_self i)
  have hbL := hlu u hu b ht
  refine ⟨b,hb,hbL,fun z => ?_⟩
  rw [Filter.tendsto_iff_ultrafilter]
  intro v hv
  obtain ⟨c,_hc,hct⟩ := exists_predual_ultralimit e v a C ha
  have hcb : c=b := (hlu v hv c hct).unique hbL
  exact hcb ▸ hct z

end HochschildSakai

 

open Filter Topology



open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_SpectralProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support projections, power limits and density of projection spans. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open Filter Topology
open scoped ComplexOrder



open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma norm_add_smul_sq_of_star_mul_zero (x y : M) (hxy : star y*x=0) (t : ℝ) :
    ‖y+t • x‖^2 ≤ ‖y‖^2+t^2*‖x‖^2 := by
  have hyx : star x*y=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hxy
  rw [pow_two, ← CStarRing.norm_star_mul_self]
  have he : star (y+t • x)*(y+t • x)=star y*y+(t^2) • (star x*x) := by
    simp only [star_add,star_smul,star_trivial,add_mul,mul_add,mul_smul_comm,
      smul_mul_assoc,smul_smul,hxy,hyx,smul_zero,add_zero,zero_add,pow_two]
  rw [he]
  apply (norm_add_le _ _).trans_eq
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg t),
    CStarRing.norm_star_mul_self,CStarRing.norm_star_mul_self]
  ring

 

theorem projection_range_limit (p : M) (hp : IsStarProjection p)
    {a : I → M} {l : Filter I} [l.NeBot] {b : M}
    (C : ℝ) (_hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (hpa : ∀ i, p*a i=a i) (ht : PredualTendsto e a l b) : p*b=b := by
  let q := 1-p
  have hq : IsStarProjection q := hp.one_sub
  let y := q*b
  have hqy : q*y=y := by dsimp [y]; rw [← mul_assoc,hq.isIdempotentElem.eq]
  have hy (i : I) : star y*a i=0 := by
    have hqa : q*a i=0 := by dsimp [q]; rw [sub_mul,one_mul,hpa i,sub_self]
    dsimp [y]
    rw [star_mul,hq.isSelfAdjoint.star_eq,mul_assoc,hqa,mul_zero]
  have hbound (t : ℝ) : ‖y+t • b‖^2 ≤ ‖y‖^2+t^2*C^2 := by
    have hpos : 0 ≤ ‖y‖^2+t^2*C^2 := by positivity
    have hn (i : I) : ‖y+t • a i‖ ≤ Real.sqrt (‖y‖^2+t^2*C^2) := by
      apply (Real.le_sqrt (norm_nonneg _) hpos).mpr
      exact (norm_add_smul_sq_of_star_mul_zero (a i) y (hy i) t).trans (by gcongr; exact ha i)
    have ht' : PredualTendsto e (fun i => y+t • a i) l (y+t • b) := by
      simp only [← Complex.coe_smul]
      exact predual_tendsto_add e (predual_tendsto_const e y l) (predual_tendsto_smul e ht (t:ℂ))
    exact (Real.le_sqrt (norm_nonneg _) hpos).mp
      (predual_norm_le e _ (Real.sqrt_nonneg _) (Eventually.of_forall hn) ht')
  have hzero : ‖y‖=0 := by
    by_contra hy0
    have hyp : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy0)
    let t : ℝ := ‖y‖^2/(C^2+1)
    have ht0 : 0 < t := div_pos (sq_pos_of_pos hyp) (by positivity)
    have hlow : (1+t)*‖y‖ ≤ ‖y+t • b‖ := by
      calc
        (1+t)*‖y‖ = ‖(1+t) • y‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity)]
        _ = ‖q*(y+t • b)‖ := by rw [mul_add,mul_smul_comm,hqy]; congr 1; module
        _ ≤ ‖q‖*‖y+t • b‖ := norm_mul_le _ _
        _ ≤ 1*‖y+t • b‖ := by gcongr; exact hq.norm_le
        _ = ‖y+t • b‖ := one_mul _
    have hs := hbound t
    have hs' : ((1+t)*‖y‖)^2 ≤ ‖y+t • b‖^2 := by gcongr
    have hte : t*(C^2+1)=‖y‖^2 := by dsimp [t]; field_simp
    nlinarith [sq_nonneg (t*‖y‖)]
  have hqb : q*b=0 := norm_eq_zero.mp hzero
  dsimp [q] at hqb
  simpa only [sub_mul,one_mul,sub_eq_zero,eq_comm] using hqb

 

theorem predual_tendsto_projection_mul_bounded (p : M) (hp : IsStarProjection p)
    {a : I → M} {l : Filter I} {b : M}
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (ht : PredualTendsto e a l b) :
    PredualTendsto e (fun i => p*a i) l (p*b) := by
  intro z
  rw [Filter.tendsto_iff_ultrafilter]
  intro u hu
  have htu : PredualTendsto e a (u : Filter I) b := fun x => (ht x).mono_left hu
  have hpa (i : I) : ‖p*a i‖ ≤ C :=
    (norm_mul_le _ _).trans (by simpa using (mul_le_mul hp.norm_le (ha i) (norm_nonneg _) zero_le_one))
  obtain ⟨c,_,hc⟩ := exists_predual_ultralimit e u (fun i => p*a i) C hpa
  have hpc : p*c=c := projection_range_limit e p hp C hC hpa
    (fun i => by rw [← mul_assoc,hp.isIdempotentElem.eq]) hc
  have hq : IsStarProjection (1-p) := hp.one_sub
  have hqa (i : I) : ‖(1-p)*a i‖ ≤ C :=
    (norm_mul_le _ _).trans (by simpa using (mul_le_mul hq.norm_le (ha i) (norm_nonneg _) zero_le_one))
  have hqt : PredualTendsto e (fun i => (1-p)*a i) (u : Filter I) (b-c) := by
    simpa only [sub_mul,one_mul] using predual_tendsto_sub e htu hc
  have hqc := projection_range_limit e (1-p) hq C hC hqa
    (fun i => by rw [← mul_assoc,hq.isIdempotentElem.eq]) hqt
  have hcb : c=p*b := by
    rw [sub_mul,one_mul,mul_sub,hpc] at hqc
    have hh : p*b-c=0 := sub_eq_self.mp hqc
    exact (sub_eq_zero.mp hh).symm
  exact hcb ▸ hc z

 
theorem projection_mul_hasPreadjoint [CompleteSpace X] (p : M)
    (hp : IsStarProjection p) : HasPreadjoint e (ContinuousLinearMap.mul ℂ M p) := by
  intro z
  let : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
  let L : StrongDual ℂ X →ₗ[ℂ] ℂ :=
    { toFun := fun f => e.symm (p*e f) z
      map_add' := by intro f g; simp [mul_add]
      map_smul' := by intro r f; simp [map_smulₛₗ] }
  have hb (f : StrongDual ℂ X) : ‖L f‖ ≤ (‖p‖*‖z‖)*‖f‖ := by
    change ‖e.symm (p*e f) z‖ ≤ _
    calc
      _ ≤ ‖e.symm (p*e f)‖*‖z‖ := (e.symm (p*e f)).le_opNorm z
      _ = ‖p*e f‖*‖z‖ := by rw [e.symm.norm_map]
      _ ≤ (‖p‖*‖e f‖)*‖z‖ := by gcongr; exact norm_mul_le _ _
      _ = (‖p‖*‖z‖)*‖f‖ := by rw [e.norm_map]; ring
  let F := L.mkContinuous (‖p‖*‖z‖) hb
  have hF (a : Finset X → StrongDual ℂ X) (ha : ∀ s, ‖a s‖ ≤ 1)
      (hta : ∀ x, Tendsto (fun s => a s x) atTop (𝓝 0)) :
      Tendsto (fun s => F (a s)) atTop (𝓝 0) := by
    have ht : PredualTendsto e (fun s => e (a s)) atTop 0 := by
      intro x
      simpa using hta x
    have hh := predual_tendsto_projection_mul_bounded e p hp 1 zero_le_one
      (fun s => by simpa only [e.norm_map] using ha s) ht
    simpa [F,L] using hh z
  obtain ⟨w,hw⟩ := mem_predual_of_bounded_weak_continuity F hF
  refine ⟨w,fun a => ?_⟩
  simpa [F,L] using hw (e.symm a)

end HochschildSakai

 

open Filter Topology

namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma isGLB_of_antitone_predual_limit [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (a : I → M) (hm : Antitone a) {p : M} (ht : PredualTendsto e a atTop p)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) : IsGLB (Set.range a) p := by
  constructor
  · rintro _ ⟨i,rfl⟩
    apply le_of_bounded_predual_limit e C hC (Eventually.of_forall ha) ?_ ht
    exact (eventually_ge_atTop i).mono fun j hj => hm hj
  · intro d hd
    apply ge_of_bounded_predual_limit e C hC (Eventually.of_forall ha) ?_ ht
    exact Eventually.of_forall fun i => hd (Set.mem_range_self i)

lemma exists_antitone_predual_limit [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (a : I → M) (hm : Antitone a) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ∃ p : M, ‖p‖ ≤ C ∧ IsGLB (Set.range a) p ∧ PredualTendsto e a atTop p := by
  obtain ⟨b,hb,_,ht⟩ := exists_monotone_predual_limit e (fun i => -a i)
    (fun i j hij => neg_le_neg (hm hij)) C hC
    (fun i => by simpa only [norm_neg] using ha i)
  have ht' : PredualTendsto e a atTop (-b) := by
    simpa only [neg_neg] using predual_tendsto_neg e ht
  exact ⟨-b,by simpa only [norm_neg] using hb,
    isGLB_of_antitone_predual_limit e a hm ht' C hC ha,ht'⟩

lemma isGLB_star_conjugate {a : I → M} {p : M} (hp : IsGLB (Set.range a) p)
    (u : Mˣ) : IsGLB (Set.range (fun i => star (u:M)*a i*u)) (star (u:M)*p*u) := by
  constructor
  · rintro _ ⟨i,rfl⟩
    exact star_left_conjugate_le_conjugate (hp.1 (Set.mem_range_self i)) _
  · intro d hd
    have hx : star (↑(u⁻¹):M)*d*(↑(u⁻¹):M) ≤ p := by
      apply hp.2
      rintro _ ⟨i,rfl⟩
      have hh := star_left_conjugate_le_conjugate (hd (Set.mem_range_self i)) (↑(u⁻¹):M)
      simpa [← mul_assoc,← star_mul] using hh
    have hh := star_left_conjugate_le_conjugate hx (u:M)
    simpa [← mul_assoc,← star_mul] using hh

 

lemma le_of_positive_fixed (a b : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hba : b*a=a) : a ≤ b := by
  have hab : a*b=a := by
    simpa only [star_mul,(IsSelfAdjoint.of_nonneg ha0).star_eq,
      (IsSelfAdjoint.of_nonneg hb0).star_eq] using congrArg star hba
  have hcomm : Commute b (1-a) := by
    change b*(1-a)=(1-a)*b
    rw [mul_sub,sub_mul,mul_one,one_mul,hba,hab]
  have hh := hcomm.mul_nonneg hb0 (sub_nonneg.mpr ha1)
  simpa only [mul_sub,mul_one,hba,sub_nonneg] using hh

 

theorem power_limit_fixed (b p : M) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hp : IsGLB (Set.range (fun n : ℕ => b^n)) p)
    (ht : PredualTendsto e (fun n : ℕ => b^n) atTop p) : b*p=p := by
  have hbsa := IsSelfAdjoint.of_nonneg hb0
  have hnorm (n : ℕ) : ‖b^n‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (CStarAlgebra.pow_nonneg (a := b) hb0 n)).mpr
      (by simpa only [pow_zero] using CStarAlgebra.pow_antitone (ha₀ := hb0) (ha₁ := hb1) (Nat.zero_le n))
  have ht1 : PredualTendsto e (fun n : ℕ => b^(n+1)) atTop p :=
    fun z => (ht z).comp (tendsto_add_atTop_nat 1)
  have ht2 : PredualTendsto e (fun n : ℕ => b^(n+2)) atTop p :=
    fun z => (ht z).comp (tendsto_add_atTop_nat 2)
  have hconj (t : ℝ) (ht0 : 0 ≤ t) :
      (1+t • b)*p*(1+t • b)=(1+t)^2 • p := by
    let c : M := 1+t • b
    have hc0 : 1 ≤ c := le_add_of_nonneg_right (smul_nonneg ht0 hb0)
    have hcu : IsUnit c := CStarAlgebra.isUnit_of_le 1 hc0
    obtain ⟨u,hu⟩ := hcu
    have hcsa : IsSelfAdjoint c := (IsSelfAdjoint.of_nonneg (zero_le_one.trans hc0))
    have hgl : IsGLB (Set.range (fun n : ℕ => c*b^n*c)) (c*p*c) := by
      simpa only [hu,hcsa.star_eq] using isGLB_star_conjugate hp u
    have heq (n : ℕ) : c*b^n*c = b^n+(2*t) • b^(n+1)+(t^2) • b^(n+2) := by
      dsimp [c]
      rw [show n+2=(n+1)+1 by omega,pow_succ,pow_succ]
      simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,
        ← pow_succ',← pow_succ]
      module
    have htc : PredualTendsto e (fun n : ℕ => c*b^n*c) atTop ((1+t)^2 • p) := by
      have hh := predual_tendsto_add e
        (predual_tendsto_add e ht (predual_tendsto_smul e ht1 ((2*t:ℝ):ℂ)))
        (predual_tendsto_smul e ht2 ((t^2:ℝ):ℂ))
      simp only [Complex.coe_smul] at hh
      have he : p+(2*t) • p+t^2 • p=(1+t)^2 • p := by module
      simpa only [heq,he] using hh
    have hant : Antitone (fun n : ℕ => c*b^n*c) := by
      intro n m hnm
      simpa only [hcsa.star_eq] using
        star_left_conjugate_le_conjugate (CStarAlgebra.pow_antitone (ha₀ := hb0) (ha₁ := hb1) hnm) c
    have hbound (n : ℕ) : ‖c*b^n*c‖ ≤ ‖c‖^2 := by
      calc
        ‖c*b^n*c‖ ≤ (‖c‖*‖b^n‖)*‖c‖ := (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
        _ ≤ (‖c‖*1)*‖c‖ := by gcongr; exact hnorm n
        _ = ‖c‖^2 := by ring
    exact hgl.unique (isGLB_of_antitone_predual_limit e _ hant htc _ (sq_nonneg _) hbound)
  have h1 := hconj 1 zero_le_one
  have h2 := hconj 2 (by norm_num)
  have hppos : 0 ≤ p := hp.2 (by rintro _ ⟨n,rfl⟩; exact CStarAlgebra.pow_nonneg (a := b) hb0 n)
  have hpsa := IsSelfAdjoint.of_nonneg hppos
  have hbp : b*p*b=p := by
    have hid : (1+(2:ℝ) • b)*p*(1+(2:ℝ) • b) - (2:ℝ) • ((1+b)*p*(1+b)) =
        (2:ℝ) • (b*p*b) - p := by
      simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm]
      module
    have h1' : (1+b)*p*(1+b)=(4:ℝ) • p := by norm_num at h1 ⊢; exact h1
    have h2' : (1+(2:ℝ) • b)*p*(1+(2:ℝ) • b)=(9:ℝ) • p := by norm_num at h2 ⊢; exact h2
    rw [h1',h2'] at hid
    have hh : (2:ℝ) • (b*p*b-p)=0 := by
      calc
        _ = ((2:ℝ) • (b*p*b)-p)-((9:ℝ) • p-(2:ℝ) • ((4:ℝ) • p)) := by module
        _ = 0 := sub_eq_zero.mpr hid.symm
    exact sub_eq_zero.mp ((smul_eq_zero.mp hh).resolve_left (by norm_num))
  have hab : b*p+p*b=(2:ℝ) • p := by
    have h1' : (1+b)*p*(1+b)=(4:ℝ) • p := by norm_num at h1 ⊢; exact h1
    have he : (1+b)*p*(1+b)=p+(b*p+p*b)+b*p*b := by noncomm_ring
    rw [he,hbp] at h1'
    calc
      b*p+p*b = (p+(b*p+p*b)+p)-(2:ℝ) • p := by module
      _ = (4:ℝ) • p-(2:ℝ) • p := by rw [h1']
      _ = (2:ℝ) • p := by module
  have hz : (1-b)*p*(1-b)=0 := by
    have he : (1-b)*p*(1-b)=p-(b*p+p*b)+b*p*b := by noncomm_ring
    rw [he,hbp,hab]
    module
  let s := CFC.sqrt p
  have hs : s*s=p := CFC.sqrt_mul_sqrt_self p
  have hssa : star s=s := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)).star_eq
  have hx : s*(1-b)=0 := by
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    simpa only [star_mul,hssa,star_sub,star_one,hbsa.star_eq,mul_assoc,← hs] using hz
  have hpx : p*(1-b)=0 := by rw [← hs,mul_assoc,hx,mul_zero]
  have hxp : (1-b)*p=0 := by
    simpa only [star_mul,star_sub,star_one,hbsa.star_eq,hpsa.star_eq,star_zero]
      using congrArg star hpx
  simpa only [sub_mul,one_mul,sub_eq_zero,eq_comm] using hxp

 
theorem exists_power_projection (b : M) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∃ p : M, IsStarProjection p ∧ PredualTendsto e (fun n : ℕ => b^n) atTop p ∧
      b*p=p ∧ ∀ x : M, b*x=x → p*x=x := by
  have hbn (n : ℕ) : ‖b^n‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (CStarAlgebra.pow_nonneg (a := b) hb0 n)).mpr
      (by simpa only [pow_zero] using CStarAlgebra.pow_antitone (ha₀ := hb0) (ha₁ := hb1) (Nat.zero_le n))
  obtain ⟨p,_,hp,ht⟩ := exists_antitone_predual_limit e (fun n : ℕ => b^n)
    (CStarAlgebra.pow_antitone (ha₀ := hb0) (ha₁ := hb1)) 1 zero_le_one hbn
  have hp0 : 0 ≤ p := hp.2 (by rintro _ ⟨n,rfl⟩; exact CStarAlgebra.pow_nonneg (a := b) hb0 n)
  have hp1 : p ≤ 1 := by simpa only [pow_zero] using hp.1 (Set.mem_range_self 0)
  have hbp := power_limit_fixed e b p hb0 hb1 hp ht
  have hpsq : p*p ≤ p := by
    simpa only [pow_two,pow_one] using CStarAlgebra.pow_antitone (ha₀ := hp0) (ha₁ := hp1) (by omega : 1 ≤ 2)
  let q : M := p+(p-p*p)
  have hq0 : 0 ≤ q := add_nonneg hp0 (sub_nonneg.mpr hpsq)
  have hq1 : q ≤ 1 := by
    have hneg : 0 ≤ (1-p)*(1-p) := (IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hp1)).mul_self_nonneg
    have he : q=1-(1-p)*(1-p) := by dsimp [q]; noncomm_ring
    rw [he]
    exact sub_le_self _ hneg
  have hbq : b*q=q := by
    dsimp [q]
    rw [mul_add,mul_sub,← mul_assoc,hbp]
  have hpowq (n : ℕ) : b^n*q=q := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',mul_assoc,ih,hbq]
  have hqle : q ≤ p := hp.2 (by
    rintro _ ⟨n,rfl⟩
    exact le_of_positive_fixed q _ hq0 hq1 (CStarAlgebra.pow_nonneg (a := b) hb0 n) (hpowq n))
  have hpsq' : p ≤ p*p := sub_nonpos.mp (by
    simpa [q,add_assoc,add_comm,add_left_comm] using add_le_add_left hqle (-p))
  have hproj : IsStarProjection p := ⟨le_antisymm hpsq hpsq',(IsSelfAdjoint.of_nonneg hp0)⟩
  refine ⟨p,hproj,ht,hbp,?_⟩
  intro x hx
  let a : M := x*star x
  let r : ℝ := ‖a‖+1
  have hr : 0 < r := by dsimp [r]; positivity
  have ha0 : 0 ≤ a := mul_star_self_nonneg x
  have hca0 : 0 ≤ r⁻¹ • a := smul_nonneg (inv_nonneg.mpr hr.le) ha0
  have hcan : ‖r⁻¹ • a‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_one₀ hr).mpr (by dsimp [r]; linarith)
  have hca1 : r⁻¹ • a ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hca0).mp hcan
  have hba : b*(r⁻¹ • a)=r⁻¹ • a := by dsimp [a]; rw [mul_smul_comm,← mul_assoc,hx]
  have hbna (n : ℕ) : b^n*(r⁻¹ • a)=r⁻¹ • a := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',mul_assoc,ih,hba]
  have hcap : r⁻¹ • a ≤ p := hp.2 (by
    rintro _ ⟨n,rfl⟩
    exact le_of_positive_fixed _ _ hca0 hca1 (CStarAlgebra.pow_nonneg (a := b) hb0 n) (hbna n))
  have hpa : p*a=a := by
    have hh := congrArg (fun z : M => r • z)
      (hproj.mul_right_and_mul_left_of_nonneg_of_le hca0 hcap).2
    simpa only [mul_smul_comm,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using hh
  have hzero : (1-p)*x=0 := by
    apply (CStarRing.mul_star_self_eq_zero_iff _).mp
    rw [star_mul,star_sub,star_one,hproj.isSelfAdjoint.star_eq,← mul_assoc,
      mul_assoc (1-p) x (star x)]
    change ((1-p)*a)*(1-p)=0
    rw [sub_mul,one_mul,hpa,sub_self,zero_mul]
  simpa only [sub_mul,one_mul,sub_eq_zero,eq_comm] using hzero

lemma exists_support_contraction (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ p : M, IsSupportProjection a p ∧
      PredualTendsto e (fun n : ℕ => 1-(1-a)^n) atTop p := by
  obtain ⟨q,hq,ht,hbq,hqx⟩ := exists_power_projection e (1-a)
    (sub_nonneg.mpr ha1) (sub_le_self _ ha0)
  have haq : a*q=0 := by
    have hh := hbq
    rw [sub_mul,one_mul] at hh
    exact sub_eq_self.mp hh
  have hqa : q*a=0 := by
    simpa only [star_mul,hq.isSelfAdjoint.star_eq,(IsSelfAdjoint.of_nonneg ha0).star_eq,star_zero]
      using congrArg Star.star haq
  refine ⟨1-q,⟨hq.one_sub,?_,?_,?_⟩,?_⟩
  · simp only [sub_mul,one_mul,hqa,sub_zero]
  · simp only [mul_sub,mul_one,haq,sub_zero]
  · intro x hx
    have hbx : (1-a)*x=x := by simp only [sub_mul,one_mul,hx,sub_zero]
    simp only [sub_mul,one_mul,hqx x hbx,sub_self]
  · exact predual_tendsto_sub e (predual_tendsto_const e 1 (atTop : Filter ℕ)) ht

include e in
 

theorem exists_support_projection (a : M) (ha : 0 ≤ a) :
    ∃ p : M, IsSupportProjection a p := by
  let r : ℝ := ‖a‖+1
  have hr : 0 < r := by dsimp [r]; positivity
  have hi : 0 < r⁻¹ := inv_pos.mpr hr
  have hn : ‖r⁻¹ • a‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hi]
    exact (inv_mul_le_one₀ hr).mpr (by dsimp [r]; linarith)
  have hsa : 0 ≤ r⁻¹ • a := smul_nonneg hi.le ha
  obtain ⟨p,hp,_⟩ := exists_support_contraction e (r⁻¹ • a) hsa
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hsa).mp hn)
  refine ⟨p,hp.proj,?_,?_,?_⟩
  · have hh := congrArg (fun z : M => r • z) hp.left
    simpa only [mul_smul_comm,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using hh
  · have hh := congrArg (fun z : M => r • z) hp.right
    simpa only [smul_mul_assoc,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using hh
  · intro x hx
    apply hp.annihilate x
    simp only [smul_mul_assoc,hx,smul_zero]

include e in
 

theorem exists_dyadic_projection (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ p : M, IsStarProjection p ∧ 0 ≤ (2:ℝ) • a-p ∧ (2:ℝ) • a-p ≤ 1 := by
  let b : M := a-(1/2:ℝ) • (1:M)
  let c : M := b⁺
  let d : M := b⁻
  have hbsa : IsSelfAdjoint b := (IsSelfAdjoint.of_nonneg ha0).sub
    (IsSelfAdjoint.of_nonneg (smul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) zero_le_one))
  have hb : c-d=b := CFC.posPart_sub_negPart b hbsa
  have hc0 : 0 ≤ c := CFC.posPart_nonneg b
  have hd0 : 0 ≤ d := CFC.negPart_nonneg b
  obtain ⟨p,hp⟩ := exists_support_projection e c hc0
  have hpd : p*d=0 := hp.annihilate d (CFC.posPart_mul_negPart b)
  have hdp : d*p=0 := by
    simpa only [star_mul,(IsSelfAdjoint.of_nonneg hd0).star_eq,
      hp.proj.isSelfAdjoint.star_eq,star_zero] using congrArg star hpd
  have hcp : b*p=c := by rw [← hb,sub_mul,hp.right,hdp,sub_zero]
  have hpc : p*b=c := by rw [← hb,mul_sub,hp.left,hpd,sub_zero]
  have hac : Commute a p := by
    change a*p=p*a
    have hh := hcp.trans hpc.symm
    dsimp [b] at hh
    simpa only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,
      sub_left_inj] using hh
  have har : 0 ≤ a*(1-p) :=
    (show Commute a (1-p) from (Commute.one_right a).sub_right hac).mul_nonneg ha0
      (sub_nonneg.mpr hp.proj.le_one)
  have hal : 0 ≤ (1-a)*p :=
    ((Commute.one_left p).sub_left hac).mul_nonneg (sub_nonneg.mpr ha1) hp.proj.nonneg
  have hpa : a*p=c+(1/2:ℝ) • p := by
    dsimp [b] at hcp
    rw [sub_mul,smul_mul_assoc,one_mul] at hcp
    exact sub_eq_iff_eq_add.mp hcp
  have hlow : 0 ≤ a-(1/2:ℝ) • p := by
    have he : a-(1/2:ℝ) • p=c+a*(1-p) := by
      rw [mul_sub,mul_one,hpa]
      module
    rw [he]
    exact add_nonneg hc0 har
  have hhigh : 0 ≤ (1/2:ℝ) • (1:M)-(a-(1/2:ℝ) • p) := by
    have he : (1/2:ℝ) • (1:M)-(a-(1/2:ℝ) • p)=(1-a)*p+d := by
      rw [sub_mul,one_mul,hpa]
      have haa : a=c-d+(1/2:ℝ) • (1:M) := by
        exact (sub_eq_iff_eq_add.mp hb.symm)
      conv_lhs => rw [haa]
      module
    rw [he]
    exact add_nonneg hal hd0
  refine ⟨p,hp.proj,?_,?_⟩
  · have hh := smul_nonneg (by norm_num : (0:ℝ) ≤ 2) hlow
    convert hh using 1; module
  · apply sub_nonneg.mp
    have hh := smul_nonneg (by norm_num : (0:ℝ) ≤ 2) hhigh
    convert hh using 1; module

include e in
 

theorem dual_zero_of_projection_zero (F : StrongDual ℂ M)
    (hF : ∀ p : M, IsStarProjection p → F p=0) : F=0 := by
  have hbound : ∀ n : ℕ, ∀ a : M, 0 ≤ a → a ≤ 1 → ‖F a‖ ≤ (1/2:ℝ)^n * ‖F‖ := by
    intro n
    induction n with
    | zero =>
      intro a ha0 ha1
      simpa only [pow_zero,one_mul] using (F.le_opNorm a).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          ((CStarAlgebra.norm_le_one_iff_of_nonneg _ ha0).mpr ha1))
    | succ n ih =>
      intro a ha0 ha1
      obtain ⟨p,hp,h0,h1⟩ := exists_dyadic_projection e a ha0 ha1
      have hh := ih ((2:ℝ) • a-p) h0 h1
      have he : F ((2:ℝ) • a-p)=(2:ℝ) • F a := by
        simp only [map_sub, ← Complex.coe_smul, map_smul, hF p hp, sub_zero]
      rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
      rw [pow_succ]
      nlinarith
  have hz (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : F a=0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have ht : Tendsto (fun n : ℕ => (1/2:ℝ)^n * ‖F‖) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
          (by norm_num : (1/2:ℝ)<1)).mul_const ‖F‖
    exact ge_of_tendsto ht (Eventually.of_forall fun n => hbound n a ha0 ha1)
  have hpos (a : M) (ha : 0 ≤ a) : F a=0 := by
    let r : ℝ := ‖a‖+1
    have hr : 0 < r := by dsimp [r]; positivity
    have hc0 : 0 ≤ r⁻¹ • a := smul_nonneg (inv_nonneg.mpr hr.le) ha
    have hcn : ‖r⁻¹ • a‖ ≤ 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
      exact (inv_mul_le_one₀ hr).mpr (by dsimp [r]; linarith)
    have hh := hz (r⁻¹ • a) hc0 ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hc0).mp hcn)
    simp only [← Complex.coe_smul, map_smul] at hh
    exact (smul_eq_zero.mp hh).resolve_left (by exact_mod_cast inv_ne_zero hr.ne')
  have hker : (⊤ : Submodule ℂ M) ≤ F.ker := by
    rw [← CStarAlgebra.span_nonneg]
    exact Submodule.span_le.mpr hpos
  ext a
  exact hker (Submodule.mem_top)

end HochschildSakai
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_OperatorPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitives on operator algebras and polar partial isometries. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
namespace BoundedHochschild
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 
def rankOneColumn (φ : StrongDual ℂ E) : E →L[ℂ] (E →L[ℂ] E) :=
  ContinuousLinearMap.smulRightL ℂ E E φ

@[simp] lemma rankOneColumn_apply (φ : StrongDual ℂ E) (x y : E) :
    rankOneColumn φ x y = φ y • x := rfl



def columnEvaluate (φ : StrongDual ℂ E) (x : E) :
    ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) →L[ℂ] (E →L[ℂ] E) :=
  (ContinuousLinearMap.compL ℂ E (E →L[ℂ] E) E ((ContinuousLinearMap.apply ℂ E) x)).comp
    ((ContinuousLinearMap.compL ℂ E (E →L[ℂ] E) (E →L[ℂ] E)).flip (rankOneColumn φ))

@[simp] lemma columnEvaluate_apply (φ : StrongDual ℂ E) (x y : E)
    (F : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) :
    columnEvaluate φ x F y = F (rankOneColumn φ y) x := rfl

 
def operatorHomotopy (φ : StrongDual ℂ E) (x : E) {n : ℕ}
    (f : Cochain (E →L[ℂ] E) (n+1)) : Cochain (E →L[ℂ] E) n :=
  (columnEvaluate φ x).compContinuousMultilinearMap f.curryRight

@[simp] lemma operatorHomotopy_apply (φ : StrongDual ℂ E) (x y : E) {n : ℕ}
    (f : Cochain (E →L[ℂ] E) (n+1)) (v : Fin n → (E →L[ℂ] E)) :
    operatorHomotopy φ x f v y = f (Fin.snoc v (rankOneColumn φ y)) x := rfl

end BoundedHochschild

 

open Filter Topology
namespace HochschildPolar
open BoundedHochschild HochschildSakai
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

omit [PartialOrder M] [StarOrderedRing M] in
lemma support_right_annihilate {a p : M} (hp : IsSupportProjection a p)
    (ha : IsSelfAdjoint a) {x : M} (hx : x*a=0) : x*p=0 := by
  have hh := hp.annihilate (star x) (by
    simpa only [star_mul,ha.star_eq,star_zero] using congrArg star hx)
  simpa only [star_mul,star_star,hp.proj.isSelfAdjoint.star_eq,star_zero]
    using congrArg star hh

end HochschildPolar
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialIsometries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial isometries and comparison of equal-trace projections. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped ComplexOrder
namespace HochschildComparison
variable {M : Type*} [CStarAlgebra M]

structure PartialIso (M : Type*) [CStarAlgebra M] where
  val : M
  mul_star_mul : val * star val * val = val

namespace PartialIso
instance instCoe : Coe (PartialIso M) M := ⟨val⟩
@[ext] lemma ext {v w : PartialIso M} (h : (v : M) = w) : v = w := by
  cases v; cases w; congr

def initial (v : PartialIso M) : M := star (v : M) * v
def final (v : PartialIso M) : M := (v : M) * star (v : M)
lemma mul_initial (v : PartialIso M) : (v : M) * v.initial = v := by
  simpa only [initial, ← mul_assoc] using v.mul_star_mul
lemma final_mul (v : PartialIso M) : v.final * (v : M) = v := v.mul_star_mul
lemma initial_proj (v : PartialIso M) : IsStarProjection v.initial := by
  refine ⟨?_, IsSelfAdjoint.star_mul_self _⟩
  change (star (v : M) * v) * (star (v : M) * v) = star (v : M) * v
  calc
    _ = star (v : M) * ((v : M) * star (v : M) * v) := by simp only [mul_assoc]
    _ = _ := by rw [v.mul_star_mul]
lemma final_proj (v : PartialIso M) : IsStarProjection v.final := by
  refine ⟨?_, IsSelfAdjoint.mul_star_self _⟩
  change ((v : M) * star (v : M)) * ((v : M) * star (v : M)) = (v : M) * star (v : M)
  calc
    _ = ((v : M) * star (v : M) * v) * star (v : M) := by simp only [mul_assoc]
    _ = _ := by rw [v.mul_star_mul]

variable [PartialOrder M]

instance instLE : LE (PartialIso M) := ⟨fun v w => v.initial ≤ w.initial ∧ (w : M) * v.initial = v⟩
variable [StarOrderedRing M]

instance instZero : Zero (PartialIso M) := ⟨⟨0, by simp⟩⟩
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma coe_zero : ((0 : PartialIso M) : M) = 0 := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma initial_zero : (0 : PartialIso M).initial = 0 := by simp [initial]
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma final_zero : (0 : PartialIso M).final = 0 := by simp [final]

section
omit [PartialOrder M] [StarOrderedRing M]

lemma star_mul_eq_zero_of_final_orthogonal {v w : PartialIso M}
    (h : v.final*w.final=0) : star (v : M)*w=0 := by
  have hv : star (v : M)*v.final=star (v : M) := by
    simpa only [star_mul,star_star,v.final_proj.isSelfAdjoint.star_eq]
      using congrArg star v.final_mul
  calc
    star (v : M)*w = (star (v : M)*v.final)*(w.final*(w : M)) := by
      rw [hv,w.final_mul]
    _ = star (v : M)*(v.final*w.final)*(w : M) := by simp only [mul_assoc]
    _ = 0 := by rw [h,mul_zero,zero_mul]

lemma mul_star_eq_zero_of_initial_orthogonal {v w : PartialIso M}
    (h : v.initial*w.initial=0) : (v : M)*star (w : M)=0 := by
  have hw : w.initial*star (w : M)=star (w : M) := by
    simpa only [star_mul,star_star,w.initial_proj.isSelfAdjoint.star_eq]
      using congrArg star w.mul_initial
  calc
    (v : M)*star (w : M) = ((v : M)*v.initial)*(w.initial*star (w : M)) := by
      rw [v.mul_initial,hw]
    _ = (v : M)*(v.initial*w.initial)*star (w : M) := by simp only [mul_assoc]
    _ = 0 := by rw [h,mul_zero,zero_mul]

lemma orthogonal_initial_symm {v w : PartialIso M} (h : v.initial*w.initial=0) :
    w.initial*v.initial=0 := by
  simpa only [star_mul,v.initial_proj.isSelfAdjoint.star_eq,
    w.initial_proj.isSelfAdjoint.star_eq,star_zero] using congrArg star h
lemma orthogonal_final_symm {v w : PartialIso M} (h : v.final*w.final=0) :
    w.final*v.final=0 := by
  simpa only [star_mul,v.final_proj.isSelfAdjoint.star_eq,
    w.final_proj.isSelfAdjoint.star_eq,star_zero] using congrArg star h

def orthogonalSum (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : PartialIso M where
  val := (v : M)+w
  mul_star_mul := by
    have hab := mul_star_eq_zero_of_initial_orthogonal hi
    have hba := mul_star_eq_zero_of_initial_orthogonal (orthogonal_initial_symm hi)
    have hab' := star_mul_eq_zero_of_final_orthogonal hf
    have hba' := star_mul_eq_zero_of_final_orthogonal (orthogonal_final_symm hf)
    simp only [star_add,mul_add,add_mul,hab,hba,zero_add,add_zero]
    rw [v.mul_star_mul,w.mul_star_mul,mul_assoc,mul_assoc,hab',hba',mul_zero,mul_zero]
    abel

lemma orthogonalSum_initial (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : (orthogonalSum v w hi hf).initial=v.initial+w.initial := by
  change star ((v : M)+w)*((v : M)+w)=_
  simp only [star_add,mul_add,add_mul,star_mul_eq_zero_of_final_orthogonal hf,
    star_mul_eq_zero_of_final_orthogonal (orthogonal_final_symm hf),zero_add,add_zero,initial]
lemma orthogonalSum_final (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : (orthogonalSum v w hi hf).final=v.final+w.final := by
  change ((v : M)+w)*star ((v : M)+w)=_
  simp only [star_add,mul_add,add_mul,mul_star_eq_zero_of_initial_orthogonal hi,
    mul_star_eq_zero_of_initial_orthogonal (orthogonal_initial_symm hi),zero_add,add_zero,final]
end

end PartialIso
end HochschildComparison

 

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialUnitaries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial unitaries, ordered limits and trace estimates. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildComparison
open BoundedHochschild
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

abbrev PartialUnitary (M : Type*) [CStarAlgebra M] :=
  {v : PartialIso M // v.final = v.initial}
namespace PartialUnitary
instance instCoe : Coe (PartialUnitary M) M := ⟨fun v => v.val.val⟩
section
omit [PartialOrder M] [StarOrderedRing M]

@[ext] lemma ext {v w : PartialUnitary M} (h : (v : M)=w) : v=w :=
  Subtype.ext (PartialIso.ext h)
abbrev support (v : PartialUnitary M) : M := v.val.initial
instance instZero : Zero (PartialUnitary M) := ⟨⟨0,by simp [PartialIso.final,PartialIso.initial]⟩⟩
@[simp] lemma coe_zero : ((0 : PartialUnitary M) : M)=0 := rfl
@[simp] lemma support_zero : (0 : PartialUnitary M).support=0 := by simp [support,PartialIso.initial]
end

section
omit [PartialOrder M] [StarOrderedRing M]

def orthogonalSum (v w : PartialUnitary M) (h : v.support*w.support=0) : PartialUnitary M :=
  ⟨PartialIso.orthogonalSum v.val w.val h (by simpa only [v.property,w.property] using h), by
    rw [PartialIso.orthogonalSum_final,PartialIso.orthogonalSum_initial,v.property,w.property]⟩
@[simp] lemma coe_orthogonalSum (v w : PartialUnitary M) (h : v.support*w.support=0) :
    ((v.orthogonalSum w h : PartialUnitary M) : M)=(v : M)+w := rfl
end

end PartialUnitary
end HochschildComparison

 

 

open Filter Topology
open scoped ComplexOrder







open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MatrixSystems
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix systems, expectations and rational projection approximation. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)


structure MatrixSystem (M : Type*) [Ring M] [StarRing M] (n : ℕ) where
  entry : Fin n → Fin n → M
  star_entry : ∀ i j, star (entry i j)=entry j i
  entry_mul : ∀ i j k l, entry i j*entry k l=if j=k then entry i l else 0
  sum_diagonal : ∑ i, entry i i=1

end HochschildMatrixSystems

 

 

 

open scoped ComplexOrder







open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Corners
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral corners, corner preduals and factor structure. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def corner (p : M) (hp : IsStarProjection p) : NonUnitalStarSubalgebra ℂ M where
  carrier := {a | p*a=a ∧ a*p=a}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    exact ⟨by rw [mul_add,ha,hb],by rw [add_mul,ha',hb']⟩
  mul_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    exact ⟨by rw [← mul_assoc,ha],by rw [mul_assoc,hb']⟩
  smul_mem' := by
    intro c a ha
    exact ⟨by rw [mul_smul_comm,ha.1],by rw [smul_mul_assoc,ha.2]⟩
  star_mem' := by
    intro a ha
    exact ⟨by simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star ha.2,
      by simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star ha.1⟩

instance corner_closed (p : M) (hp : IsStarProjection p) : IsClosed (corner p hp : Set M) := by
  exact (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

omit [PartialOrder M] [StarOrderedRing M] in
lemma self_mem_corner {p : M} (hp : IsStarProjection p) : p ∈ corner p hp :=
  ⟨hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩

end HochschildCorners

 

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (p : M) (hp : IsStarProjection p)

abbrev Corner := corner p hp

instance cornerOne : One (Corner p hp) := ⟨⟨p,self_mem_corner hp⟩⟩
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma corner_coe_one : ((1 : Corner p hp):M)=p := rfl

instance cornerRing : Ring (Corner p hp) where
  one_mul a := Subtype.ext a.property.1
  mul_one a := Subtype.ext a.property.2
  natCast := fun n => ⟨n • p,(corner p hp).nsmul_mem (self_mem_corner hp) n⟩
  natCast_zero := Subtype.ext (zero_nsmul _)
  natCast_succ n := Subtype.ext (succ_nsmul _ _)
  intCast := fun z => ⟨z • p,(corner p hp).toNonUnitalSubring.toAddSubgroup.zsmul_mem (self_mem_corner hp) z⟩
  intCast_ofNat n := Subtype.ext (natCast_zsmul _ _)
  intCast_negSucc n := Subtype.ext (negSucc_zsmul _ _)

instance cornerAlgebra : Algebra ℂ (Corner p hp) where
  algebraMap :=
    { toFun := fun c => c • (1 : Corner p hp)
      map_zero' := zero_smul _ _
      map_one' := one_smul _ _
      map_add' := fun _ _ => add_smul _ _ _
      map_mul' := fun c d => by
        ext
        change (c*d) • p=(c • p)*(d • p)
        rw [smul_mul_smul_comm,hp.isIdempotentElem.eq] }
  commutes' c a := by
    ext
    change (c • p)*(a:M)=(a:M)*(c • p)
    rw [smul_mul_assoc,mul_smul_comm,a.property.1,a.property.2]
  smul_def' c a := by
    ext
    change c • (a:M)=(c • p)*(a:M)
    rw [smul_mul_assoc,a.property.1]

instance cornerNormedRing : NormedRing (Corner p hp) where
  dist_eq a b := by
    change dist (a:M) (b:M)=‖-(a:M)+(b:M)‖
    rw [dist_comm,dist_eq_norm,sub_eq_add_neg,add_comm]
  norm_mul_le a b := norm_mul_le (a:M) (b:M)
instance cornerNormedAlgebra : NormedAlgebra ℂ (Corner p hp) where
  norm_smul_le c a := norm_smul_le c (a:M)
instance cornerCStarAlgebra : CStarAlgebra (Corner p hp) where

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma corner_coe_mul (a b : Corner p hp) : ((a*b : Corner p hp):M)=(a:M)*(b:M) := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma corner_coe_star (a : Corner p hp) : ((star a : Corner p hp):M)=star (a:M) := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma corner_coe_smul (c : ℂ) (a : Corner p hp) : ((c • a : Corner p hp):M)=c • (a:M) := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma corner_coe_zero : ((0 : Corner p hp):M)=0 := rfl

end HochschildCorners

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (p : M) (hp : IsStarProjection p)

omit [PartialOrder M] [StarOrderedRing M] in
lemma corner_projection_coe {q : Corner p hp} (hq : IsStarProjection q) :
    IsStarProjection (q:M) := ⟨congrArg (fun a : Corner p hp => (a:M)) hq.isIdempotentElem.eq,
      congrArg (fun a : Corner p hp => (a:M)) hq.isSelfAdjoint.star_eq⟩

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

def cornerTrace : Corner p hp →ₚ[ℂ] ℂ where
  toLinearMap := ((τ p).re : ℂ)⁻¹ • (τ.toLinearMap.comp (corner p hp).subtype)
  monotone' := fun _ _ h => mul_le_mul_of_nonneg_left (τ.monotone h)
    (inv_nonneg.mpr (Complex.zero_le_real.mpr
      (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).1))

@[simp] lemma cornerTrace_apply (a : Corner p hp) :
    cornerTrace p hp τ a = ((τ p).re : ℂ)⁻¹ * τ (a:M) := rfl

end HochschildCorners

 

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_IncrementalPatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner partial unitaries, incremental moment estimates and unitary completion. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildSakai HochschildCorners HochschildComparison
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (q : M) (hq : IsStarProjection q)

def ofCornerUnitary (u : unitary (Corner q hq)) : PartialUnitary M :=
  ⟨⟨((u : Corner q hq):M),by
    have hh := congrArg (fun a : Corner q hq => (a : M)) (Unitary.coe_mul_star_self u)
    change ((u : Corner q hq):M)*star ((u : Corner q hq):M)=q at hh
    rw [hh]
    exact (u : Corner q hq).property.1⟩,by
      have hl := congrArg (fun a : Corner q hq => (a : M)) (Unitary.coe_mul_star_self u)
      have hr := congrArg (fun a : Corner q hq => (a : M)) (Unitary.coe_star_mul_self u)
      exact hl.trans hr.symm⟩
@[simp] lemma ofCornerUnitary_coe (u : unitary (Corner q hq)) :
    ((ofCornerUnitary q hq u : PartialUnitary M):M)=((u : Corner q hq):M) := rfl
@[simp] lemma ofCornerUnitary_support (u : unitary (Corner q hq)) :
    (ofCornerUnitary q hq u).support=q := by
  exact congrArg (fun a : Corner q hq => (a : M)) (Unitary.coe_star_mul_self u)

end HochschildPatching

 

 

 

open scoped ComplexOrder







open Filter Topology
open scoped ComplexOrder





open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small unitary moments, reindexing and simultaneous moment sequences. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
universe u v
variable {M : Type u} [CStarAlgebra M]

def asPartialUnitary (u : unitary M) : PartialUnitary M :=
  ⟨⟨(u:M),by rw [u.property.2,one_mul]⟩,by
    change (u:M)*star (u:M)=star (u:M)*(u:M)
    exact u.property.2.trans u.property.1.symm⟩
@[simp] lemma asPartialUnitary_coe (u : unitary M) : ((asPartialUnitary u : PartialUnitary M):M)=(u:M) := rfl

end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder







open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TypeIIDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Central projections and the finite type-II condition. -/

noncomputable section

open scoped ComplexOrder
namespace FinitePathMain

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def CentralProjection (p : M) : Prop :=
  IsStarProjection p ∧ ∀ a : M, Commute p a

def AbelianProjection (p : M) : Prop :=
  IsStarProjection p ∧ ∀ a b : M, Commute (p * a * p) (p * b * p)

end FinitePathMain

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Frames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal frames of partial isometries and maximal frame construction. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace PartialIso

def ofProjection (p : M) (hp : IsStarProjection p) : PartialIso M :=
  ⟨p,by rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq,hp.isIdempotentElem.eq]⟩
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma ofProjection_coe (p : M) (hp : IsStarProjection p) :
    ((ofProjection p hp : PartialIso M):M)=p := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma ofProjection_initial (p : M) (hp : IsStarProjection p) :
    (ofProjection p hp).initial=p := by simp only [initial,ofProjection_coe,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma ofProjection_final (p : M) (hp : IsStarProjection p) :
    (ofProjection p hp).final=p := by simp only [final,ofProjection_coe,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]

lemma restrict_square (v : PartialIso M) {p : M} (hp : IsStarProjection p)
    (hpv : p ≤ v.initial) : star ((v:M)*p)*((v:M)*p)=p := by
  calc
    star ((v:M)*p)*((v:M)*p) = p*v.initial*p := by
      simp only [star_mul,hp.isSelfAdjoint.star_eq,initial,mul_assoc]
    _ = p := by rw [(hp.le_iff_mul_eq_left v.initial_proj).mp hpv,hp.isIdempotentElem.eq]

def restrict (v : PartialIso M) {p : M} (hp : IsStarProjection p)
    (hpv : p ≤ v.initial) : PartialIso M :=
  ⟨(v:M)*p,by rw [mul_assoc,restrict_square v hp hpv,mul_assoc,hp.isIdempotentElem.eq]⟩
@[simp] lemma restrict_coe (v : PartialIso M) {p : M} (hp : IsStarProjection p)
    (hpv : p ≤ v.initial) : ((v.restrict hp hpv : PartialIso M):M)=(v:M)*p := rfl
@[simp] lemma restrict_initial (v : PartialIso M) {p : M} (hp : IsStarProjection p)
    (hpv : p ≤ v.initial) : (v.restrict hp hpv).initial=p := restrict_square v hp hpv
end PartialIso

structure Frame (M : Type*) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] (n : ℕ) where
  part : Fin (n+1) → PartialIso M
  common : ∀ i, (part i).initial=(part 0).initial
  anchor : (part 0 : M)=(part 0).initial
  orthogonal : ∀ i j, i ≠ j → (part i).final*(part j).final=0

namespace Frame
variable {n : ℕ}
@[ext] lemma ext {v w : Frame M n} (h : ∀ i, v.part i=w.part i) : v=w := by
  have he := funext h
  cases v; cases w; congr

instance instZero : Zero (Frame M n) := ⟨⟨fun _ => 0,fun _ => rfl,by simp,by intros; simp⟩⟩
@[simp] lemma zero_part (i : Fin (n+1)) : (0:Frame M n).part i=0 := rfl

end Frame
end HochschildComparison

open Filter Topology
open scoped ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PublishedInputs
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero
attribute [-simp] _root_.OAI.HochschildPatching.ofCornerUnitary_coe _root_.OAI.HochschildPatching.ofCornerUnitary_support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BoundedHochschild
namespace CentralCorner

open HochschildCorners

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, p * a = a * p)

/-- The inclusion of a corner into its ambient algebra. -/
def includeMap : Corner p hp →L[ℂ] M :=
  (corner p hp).toNonUnitalSubalgebra.toSubmodule.subtypeL

/-- Compression to a central corner, which is an algebra homomorphism. -/
def compressMap : M →L[ℂ] Corner p hp :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨p * a, by
        constructor
        · rw [← mul_assoc, hp.isIdempotentElem.eq]
        · calc
            (p * a) * p = p * (a * p) := mul_assoc _ _ _
            _ = p * (p * a) := by rw [← hc a]
            _ = p * a := by rw [← mul_assoc, hp.isIdempotentElem.eq]⟩
      map_add' := fun a b => Subtype.ext (mul_add p a b)
      map_smul' := fun c a => Subtype.ext (by
        change p * (c • a) = c • (p * a)
        rw [mul_smul_comm]) }
    1 (fun a => by
      change ‖p * a‖ ≤ 1 * ‖a‖
      exact (norm_mul_le p a).trans (mul_le_mul_of_nonneg_right hp.norm_le (norm_nonneg a)))

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma includeMap_apply (a : Corner p hp) : includeMap p hp a = (a : M) := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma compressMap_coe (a : M) :
    (compressMap p hp hc a : M) = p * a := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma compressMap_includeMap (a : Corner p hp) :
    compressMap p hp hc (includeMap p hp a) = a := Subtype.ext a.property.1

/-- Restrict inputs to a central corner and compress the output. -/
def restrict {n : ℕ} (f : Cochain M n) : Cochain (Corner p hp) n :=
  (compressMap p hp hc).compContinuousMultilinearMap
    (f.compContinuousLinearMap (fun _ => includeMap p hp))

/-- Pull a corner cochain back along central compression. -/
def extend {n : ℕ} (g : Cochain (Corner p hp) n) : Cochain M n :=
  (includeMap p hp).compContinuousMultilinearMap
    (g.compContinuousLinearMap (fun _ => compressMap p hp hc))

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma restrict_apply {n : ℕ} (f : Cochain M n) (x : Fin n → Corner p hp) :
    restrict p hp hc f x = compressMap p hp hc (f (fun i => (x i : M))) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma extend_apply {n : ℕ} (g : Cochain (Corner p hp) n) (x : Fin n → M) :
    extend p hp hc g x = (g (fun i => compressMap p hp hc (x i)) : M) := rfl

end CentralCorner
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_CornerComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner comparison for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder

open Filter Topology
open scoped ComplexOrder
namespace PopaCorners
open BoundedHochschild HochschildRigidity
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

structure CornerIso (p q : M) where
  val : M
  init_proj : IsStarProjection (star val*val)
  absorb : val*(star val*val)=val
  init_le : star val*val ≤ p
  final_le : val*star val ≤ q

namespace CornerIso
variable {p q : M}
instance instCoeOut : CoeOut (CornerIso p q) M := ⟨CornerIso.val⟩

omit [StarOrderedRing M] in
@[ext] theorem ext {v w : CornerIso p q} (h : (v:M)=(w:M)) : v=w := by
  cases v; cases w; cases h; rfl

def initial (v : CornerIso p q) : M := star (v:M)*(v:M)

end CornerIso
end PopaCorners

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_Corners
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corners for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaCorner
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {p : M} (hp : IsStarProjection p)

def algebra : NonUnitalStarSubalgebra ℂ M where
  carrier := {a | p*a=a ∧ a*p=a}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    change p*(a+b)=a+b ∧ (a+b)*p=a+b
    simp only [mul_add,add_mul,ha,ha',hb,hb',and_self]
  mul_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    change p*(a*b)=a*b ∧ (a*b)*p=a*b
    constructor
    · rw [←mul_assoc,ha]
    · rw [mul_assoc,hb']
  smul_mem' := by
    rintro c a ⟨ha,ha'⟩
    change p*(c • a)=c • a ∧ (c • a)*p=c • a
    simp only [mul_smul_comm,smul_mul_assoc,ha,ha',and_self]
  star_mem' := by
    rintro a ⟨ha,ha'⟩
    constructor
    · simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star ha'
    · simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star ha

instance algebra_closed : IsClosed (algebra hp : Set M) :=
  (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

instance instOne : One (algebra hp) := ⟨⟨p,hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩⟩
instance instRing : Ring (algebra hp) where
  __ := (inferInstance : NonUnitalRing (algebra hp))
  one_mul a := Subtype.ext a.property.1
  mul_one a := Subtype.ext a.property.2

instance instAlgebra : Algebra ℂ (algebra hp) := Algebra.ofModule
  (fun c a b => smul_mul_assoc c a b) (fun c a b => by rw [mul_smul_comm])

def incl : algebra hp →⋆ₙₐ[ℂ] M where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma coe_one : ((1 : algebra hp):M)=p := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma incl_apply (a : algebra hp) : incl hp a=(a:M) := rfl

end PopaCorner

open Filter Topology
open scoped ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_PartialRepresentations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial representations for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
variable (G M : Type*) [Group G] [CStarAlgebra M]

structure Rep where
  val : G → M
  mul : ∀ g h, val (g*h)=val g*val h
  inv : ∀ g, val g⁻¹=star (val g)

namespace Rep
variable {G M} [PartialOrder M] [StarOrderedRing M]

instance instCoeFunForall : CoeFun (Rep G M) (fun _ => G → M) := ⟨Rep.val⟩
def support (v : Rep G M) : M := v 1

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma support_mul (v : Rep G M) (g : G) : v.support*v g=v g := by
  rw [support,←v.mul,one_mul]
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma mul_support (v : Rep G M) (g : G) : v g*v.support=v g := by
  rw [support,←v.mul,mul_one]
omit [PartialOrder M] [StarOrderedRing M] in
lemma support_projection (v : Rep G M) : IsStarProjection v.support := by
  constructor
  · exact v.support_mul 1
  · simpa only [IsSelfAdjoint,support,inv_one] using (v.inv 1).symm
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma star_mul_self (v : Rep G M) (g : G) : star (v g)*v g=v.support := by
  rw [←v.inv,←v.mul,inv_mul_cancel,support]
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma mul_star_self (v : Rep G M) (g : G) : v g*star (v g)=v.support := by
  rw [←v.inv,←v.mul,mul_inv_cancel,support]

def add (v w : Rep G M) (hvw : v.support*w.support=0) : Rep G M where
  val g := v g+w g
  mul g h := by
    have hfg : w.support*v.support=0 := by
      have hh := congrArg star hvw
      simpa only [star_mul,v.support_projection.isSelfAdjoint.star_eq,
        w.support_projection.isSelfAdjoint.star_eq,star_zero] using hh
    have hvw' : v g*w h=0 := by
      calc
        v g*w h = (v g*v.support)*(w.support*w h) := by rw [v.mul_support,w.support_mul]
        _ = v g*(v.support*w.support)*w h := by simp only [mul_assoc]
        _ = 0 := by rw [hvw,mul_zero,zero_mul]
    have hwv : w g*v h=0 := by
      calc
        w g*v h = (w g*w.support)*(v.support*v h) := by rw [w.mul_support,v.support_mul]
        _ = w g*(w.support*v.support)*v h := by simp only [mul_assoc]
        _ = 0 := by rw [hfg,mul_zero,zero_mul]
    simp only [v.mul,w.mul,add_mul,mul_add,hvw',hwv,zero_add,add_zero]
  inv g := by simp only [v.inv,w.inv,star_add]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma add_apply (v w : Rep G M) (hvw) (g : G) : add v w hvw g=v g+w g := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma add_support (v w : Rep G M) (hvw) : (add v w hvw).support=v.support+w.support := rfl
end Rep
end PopaPatching

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_RepresentationLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Representation limits for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaPatching.Rep
open BoundedHochschild HochschildRigidity PopaCorners
variable {G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
@[ext] lemma ext {v w : Rep G M} (h : ∀ g, v g=w g) : v=w := by
  cases v; cases w; simp_all [Rep.mk.injEq,funext_iff]

def toCorner (v : Rep G M) (g : G) : CornerIso (1:M) 1 where
  val := v g
  init_proj := by rw [v.star_mul_self]; exact v.support_projection
  absorb := by rw [v.star_mul_self,v.mul_support]
  init_le := by rw [v.star_mul_self]; exact v.support_projection.le_one
  final_le := by rw [v.mul_star_self]; exact v.support_projection.le_one

@[simp] lemma toCorner_val (v : Rep G M) (g : G) : (toCorner v g : M)=v g := rfl
@[simp] lemma toCorner_initial (v : Rep G M) (g : G) : (toCorner v g).initial=v.support :=
  v.star_mul_self g
end PopaPatching.Rep

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_CornerTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner traces for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {p : M} (hp : IsStarProjection p) (τ : M →ₚ[ℂ] ℂ)

def trace : algebra hp →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀
  ((((τ p).re⁻¹ : ℝ) : ℂ) • τ.toLinearMap.comp (algebra hp).toNonUnitalSubalgebra.toSubmodule.subtype) (by
    intro a ha
    change 0 ≤ (((τ p).re⁻¹ : ℝ) : ℂ)*τ (a:M)
    apply mul_nonneg
    · exact Complex.nonneg_iff.mpr ⟨inv_nonneg.mpr
        (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).1,rfl⟩
    · exact τ.map_nonneg ha)

@[simp] lemma trace_apply (a : algebra hp) :
    trace hp τ a=(((τ p).re⁻¹ : ℝ) : ℂ)*τ (a:M) := rfl

end PopaCorner

open scoped ComplexOrder

open scoped ComplexOrder

open scoped ComplexOrder

open scoped ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_PatchTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Patch traces for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
open BoundedHochschild HochschildRigidity
variable {G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace Rep

def inCorner (v : Rep G M) {p : M} (hp : IsStarProjection p) (hv : v.support=p) :
    G →* PopaCorner.algebra hp where
  toFun g := ⟨v g,by
    change p*v g=v g ∧ v g*p=v g
    rw [←hv]
    exact ⟨v.support_mul g,v.mul_support g⟩⟩
  map_one' := Subtype.ext hv
  map_mul' g h := Subtype.ext (v.mul g h)

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma inCorner_coe (v : Rep G M) {p : M} (hp : IsStarProjection p) (hv) (g) :
    ((inCorner v hp hv g : PopaCorner.algebra hp):M)=v g := rfl

end Rep

end PopaPatching

open scoped ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_TracialPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tracial primitives for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder

open Filter Topology
open scoped ComplexOrder

open Filter Topology
open scoped ComplexOrder

open scoped ComplexOrder
namespace PopaTypeII
open BoundedHochschild PopaCorner PopaCorners
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def AbelianProjection {p : M} (hp : IsStarProjection p) : Prop :=
  ∀ a b : algebra hp, Commute a b

end PopaTypeII

open scoped ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Conditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners
open scoped ComplexOrder

universe u

/-- The finite condition used in the von Neumann type decomposition. -/
def FiniteAlgebra (N : Type u) [CStarAlgebra N] : Prop :=
  ∀ v : N, star v * v = 1 → v * star v = 1

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CornerEquivalences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Structural transport for actual corners and algebra equivalences

Nested corners flatten to the corresponding ambient corner. Type I corners
and the absence of a type I central part are invariant under an actual star
algebra equivalence. These facts are algebraic and require no trace.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners

section Nested
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- A corner within a corner is the corner of its ambient projection. -/
def nestedCornerEquiv {p : M} (hp : IsStarProjection p)
    (q : Corner p hp) (hq : IsStarProjection q) :
    Corner q hq ≃⋆ₐ[ℂ] Corner (q : M) (corner_projection_coe p hp hq) where
  toFun a := ⟨((a : Corner p hp) : M),
    congrArg Subtype.val a.property.1, congrArg Subtype.val a.property.2⟩
  invFun b := ⟨⟨(b : M), by
      constructor
      · calc
          p * (b : M) = p * ((q : M) * (b : M)) := by rw [b.property.1]
          _ = (b : M) := by rw [← mul_assoc, q.property.1, b.property.1]
      · calc
          (b : M) * p = ((b : M) * (q : M)) * p := by rw [b.property.2]
          _ = (b : M) := by rw [mul_assoc, q.property.2, b.property.2]⟩,
    Subtype.ext b.property.1, Subtype.ext b.property.2⟩
  left_inv a := Subtype.ext (Subtype.ext rfl)
  right_inv b := Subtype.ext rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma nestedCornerEquiv_apply {p : M} (hp : IsStarProjection p)
    (q : Corner p hp) (hq : IsStarProjection q) (a : Corner q hq) :
    ((nestedCornerEquiv hp q hq a : Corner (q : M) (corner_projection_coe p hp hq)) : M) =
      ((a : Corner p hp) : M) := rfl

end Nested

section Transport
variable {M N : Type*} [CStarAlgebra M] [CStarAlgebra N]
  [PartialOrder M] [StarOrderedRing M] [PartialOrder N] [StarOrderedRing N]

/-- An algebra equivalence induces an equivalence between corresponding corners. -/
def popaCornerEquiv (φ : M ≃⋆ₐ[ℂ] N) {p : M} (hp : IsStarProjection p) :
    PopaCorner.algebra hp ≃⋆ₐ[ℂ] PopaCorner.algebra (hp.map φ) where
  toFun a := ⟨φ (a : M), by
    constructor
    · change φ p * φ (a : M) = φ (a : M)
      rw [← map_mul, a.property.1]
    · change φ (a : M) * φ p = φ (a : M)
      rw [← map_mul, a.property.2]⟩
  invFun b := ⟨φ.symm (b : N), by
    constructor
    · apply φ.injective
      change φ (p * φ.symm (b : N)) = φ (φ.symm (b : N))
      rw [map_mul, φ.apply_symm_apply]
      exact b.property.1
    · apply φ.injective
      change φ (φ.symm (b : N) * p) = φ (φ.symm (b : N))
      rw [map_mul, φ.apply_symm_apply]
      exact b.property.2⟩
  left_inv a := Subtype.ext (φ.symm_apply_apply (a : M))
  right_inv b := Subtype.ext (φ.apply_symm_apply (b : N))
  map_add' a b := Subtype.ext (map_add φ (a : M) (b : M))
  map_mul' a b := Subtype.ext (map_mul φ (a : M) (b : M))
  map_smul' c a := Subtype.ext (map_smul φ c (a : M))
  map_star' a := Subtype.ext (map_star φ (a : M))

/-- Abelianness of a projection is transported by a star algebra equivalence. -/
lemma abelianProjection_map_equiv (φ : M ≃⋆ₐ[ℂ] N) {p : M}
    (hp : IsStarProjection p) (hab : PopaTypeII.AbelianProjection hp) :
    PopaTypeII.AbelianProjection (hp.map φ) := by
  let E := popaCornerEquiv φ hp
  intro a b
  simpa only [E.apply_symm_apply] using (hab (E.symm a) (E.symm b)).map E

end Transport

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialIsoCornerEquivalence
attribute [-simp] _root_.OAI.HochschildComparison.Frame.zero_part _root_.OAI.HochschildComparison.PartialIso.ofProjection_coe _root_.OAI.HochschildComparison.PartialIso.ofProjection_final _root_.OAI.HochschildComparison.PartialIso.ofProjection_initial _root_.OAI.HochschildComparison.PartialIso.restrict_coe _root_.OAI.HochschildComparison.PartialIso.restrict_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Equivalence of corners joined by a partial isometry

Conjugation by a partial isometry identifies its initial and final corners as
actual star algebras. In particular abelianness passes between these corners
and to smaller projections.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- Conjugation identifies the initial and final corners of a partial isometry. -/
def partialIsoCornerEquiv (v : PartialIso M) :
    PopaCorner.algebra v.initial_proj ≃⋆ₐ[ℂ] PopaCorner.algebra v.final_proj where
  toFun a := ⟨(v : M) * (a : M) * star (v : M), by
    constructor
    · rw [← mul_assoc, ← mul_assoc, v.final_mul]
    · have hs : star (v : M) * v.final = star (v : M) := by
        simpa only [star_mul, star_star, v.final_proj.isSelfAdjoint.star_eq] using
          congrArg star v.final_mul
      change ((v : M) * (a : M) * star (v : M)) * v.final = _
      rw [mul_assoc, hs]⟩
  invFun b := ⟨star (v : M) * (b : M) * (v : M), by
    constructor
    · have hs : v.initial * star (v : M) = star (v : M) := by
        simpa only [star_mul, star_star, v.initial_proj.isSelfAdjoint.star_eq] using
          congrArg star v.mul_initial
      change v.initial * (star (v : M) * (b : M) * (v : M)) = _
      rw [← mul_assoc, ← mul_assoc, hs]
    · rw [mul_assoc, v.mul_initial]⟩
  left_inv a := by
    apply Subtype.ext
    change star (v : M) * ((v : M) * (a : M) * star (v : M)) * (v : M) = (a : M)
    calc
      _ = v.initial * (a : M) * v.initial := by simp only [PartialIso.initial, mul_assoc]
      _ = (a : M) := by rw [a.property.1, a.property.2]
  right_inv b := by
    apply Subtype.ext
    change (v : M) * (star (v : M) * (b : M) * (v : M)) * star (v : M) = (b : M)
    calc
      _ = v.final * (b : M) * v.final := by simp only [PartialIso.final, mul_assoc]
      _ = (b : M) := by rw [b.property.1, b.property.2]
  map_add' a b := by
    apply Subtype.ext
    change (v : M) * ((a : M) + (b : M)) * star (v : M) =
      (v : M) * (a : M) * star (v : M) + (v : M) * (b : M) * star (v : M)
    simp only [mul_add, add_mul]
  map_mul' a b := by
    apply Subtype.ext
    change (v : M) * ((a : M) * (b : M)) * star (v : M) =
      ((v : M) * (a : M) * star (v : M)) * ((v : M) * (b : M) * star (v : M))
    symm
    calc
      _ = (v : M) * ((a : M) * v.initial * (b : M)) * star (v : M) := by
        simp only [PartialIso.initial, mul_assoc]
      _ = _ := by rw [a.property.2]
  map_smul' c a := by
    apply Subtype.ext
    change (v : M) * (c • (a : M)) * star (v : M) =
      c • ((v : M) * (a : M) * star (v : M))
    simp only [mul_smul_comm, smul_mul_assoc]
  map_star' a := by
    apply Subtype.ext
    change (v : M) * star (a : M) * star (v : M) =
      star ((v : M) * (a : M) * star (v : M))
    simp only [star_mul, star_star, mul_assoc]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma partialIsoCornerEquiv_apply (v : PartialIso M)
    (a : PopaCorner.algebra v.initial_proj) :
    (partialIsoCornerEquiv v a : M) = (v : M) * (a : M) * star (v : M) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
/-- Equivalent projections have simultaneously abelian corners. -/
lemma abelianProjection_partialIso (v : PartialIso M)
    (hab : PopaTypeII.AbelianProjection v.initial_proj) :
    PopaTypeII.AbelianProjection v.final_proj := by
  let E := partialIsoCornerEquiv v
  intro a b
  simpa only [E.apply_symm_apply] using (hab (E.symm a) (E.symm b)).map E

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_AbelianCentralSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Central support and comparison of abelian projections for type I reduction. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The central support of a projection, expressed by its central annihilators. -/
def IsCentralSupport (p z : M) : Prop :=
  CentralProjection z ∧ p ≤ z ∧
    ∀ c : M, CentralProjection c → c * p = 0 → c * z = 0

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteCentralDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The maximal finite central cut, constructed without an assumed trace. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Finiteness of a corner, expressed in the ambient algebra. -/
def FiniteCorner (p : M) : Prop :=
  ∀ a : M, p * a = a → a * p = a → star a * a = p → a * star a = p

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteProjectionEquivalence
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unitary equivalence of finite projections

In a finite von Neumann algebra a partial isometry extends to a unitary.
The proof uses trace-free central comparison of the complementary projections
and finiteness of central corners. No scalar trace is used.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison FinitePathMain

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def adjointPartialIso (v : PartialIso M) : PartialIso M :=
  ⟨star (v : M), by
    simpa only [star_mul, star_star, mul_assoc] using congrArg star v.mul_star_mul⟩

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma adjointPartialIso_initial (v : PartialIso M) :
    (adjointPartialIso v).initial = v.final := by simp [adjointPartialIso, PartialIso.initial, PartialIso.final]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma adjointPartialIso_final (v : PartialIso M) :
    (adjointPartialIso v).final = v.initial := by simp [adjointPartialIso, PartialIso.initial, PartialIso.final]

/-- Restrict a partial isometry to a central summand. -/
def centralCutPartialIso (z : M) (hz : IsStarProjection z)
    (hc : ∀ a : M, z * a = a * z) (v : PartialIso M) : PartialIso M where
  val := z * (v : M)
  mul_star_mul := by
    have hstar : star (z * (v : M)) = z * star (v : M) := by
      rw [star_mul, hz.isSelfAdjoint.star_eq, hc]
    rw [hstar, central_idempotent_mul z hz.isIdempotentElem.eq hc,
      central_idempotent_mul z hz.isIdempotentElem.eq hc, v.mul_star_mul]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma centralCutPartialIso_initial (z : M) (hz : IsStarProjection z)
    (hc : ∀ a : M, z * a = a * z) (v : PartialIso M) :
    (centralCutPartialIso z hz hc v).initial = z * v.initial := by
  change star (z * (v : M)) * (z * (v : M)) = z * (star (v : M) * v)
  rw [star_mul, hz.isSelfAdjoint.star_eq, ← hc (star (v : M)),
    central_idempotent_mul z hz.isIdempotentElem.eq hc]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma centralCutPartialIso_final (z : M) (hz : IsStarProjection z)
    (hc : ∀ a : M, z * a = a * z) (v : PartialIso M) :
    (centralCutPartialIso z hz hc v).final = z * v.final := by
  change (z * (v : M)) * star (z * (v : M)) = z * ((v : M) * star (v : M))
  rw [star_mul, hz.isSelfAdjoint.star_eq, ← hc (star (v : M)),
    central_idempotent_mul z hz.isIdempotentElem.eq hc]

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_AbelianSupportEquivalence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Abelian projections with the same central support are equivalent. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_initial_zero_iff_final_zero (v : PartialIso M)
    {c : M} (hc : ∀ a : M, c * a = a * c) :
    c * v.initial = 0 ↔ c * v.final = 0 := by
  have hf (w : PartialIso M) (hi : c * w.initial = 0) : c * w.final = 0 := by
    have hv : c * (w : M) = 0 := by
      calc
        _ = c * ((w : M) * w.initial) := by rw [w.mul_initial]
        _ = (w : M) * (c * w.initial) := by rw [← mul_assoc, hc, mul_assoc]
        _ = 0 := by rw [hi, mul_zero]
    change c * ((w : M) * star (w : M)) = 0
    rw [← mul_assoc, hv, zero_mul]
  exact ⟨hf v, fun h => by simpa using hf (adjointPartialIso v) (by simpa using h)⟩

lemma IsCentralSupport.partialIso (v : PartialIso M) {z : M}
    (h : IsCentralSupport v.initial z) : IsCentralSupport v.final z := by
  have hzv : z * (v : M) = v := by
    calc
      _ = z * ((v : M) * v.initial) := by rw [v.mul_initial]
      _ = (v : M) * (z * v.initial) := by rw [← mul_assoc, (h.1.2 (v : M)).eq, mul_assoc]
      _ = v := by rw [(v.initial_proj.le_iff_mul_eq_right h.1.1).mp h.2.1, v.mul_initial]
  refine ⟨h.1, (v.final_proj.le_iff_mul_eq_right h.1.1).mpr ?_, ?_⟩
  · change z * ((v : M) * star (v : M)) = _
    rw [← mul_assoc, hzv]
    rfl
  · intro c hc hc0
    exact h.2.2 c hc ((central_initial_zero_iff_final_zero v (fun a => (hc.2 a).eq)).mpr hc0)

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CentralSupportCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Central cuts of projection supports. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma IsCentralSupport.eq_zero_iff {p z : M} (hp : IsStarProjection p)
    (h : IsCentralSupport p z) : p = 0 ↔ z = 0 := by
  constructor
  · intro hp0
    have hz := h.2.2 1 ⟨IsStarProjection.one M, fun _ => Commute.one_left _⟩ (by simp [hp0])
    simpa only [one_mul] using hz
  · intro hz0
    exact le_antisymm (hz0 ▸ h.2.1) hp.nonneg

lemma IsCentralSupport.centralCut {p t z : M} (hp : IsStarProjection p)
    (h : IsCentralSupport p t) (hz : CentralProjection z) :
    IsCentralSupport (z * p) (z * t) := by
  have hzp := hz.1.mul hp (hz.2 p)
  have hzt : CentralProjection (z * t) :=
    ⟨hz.1.mul h.1.1 (hz.2 t), fun a => (hz.2 a).mul_left (h.1.2 a)⟩
  refine ⟨hzt, (hzp.le_iff_mul_eq_left hzt.1).mpr ?_, ?_⟩
  · calc
      z * p * (z * t) = z * (p * t) :=
        central_idempotent_mul z hz.1.isIdempotentElem.eq (fun a => (hz.2 a).eq) p t
      _ = z * p := by rw [(hp.le_iff_mul_eq_left h.1.1).mp h.2.1]
  · intro c hc hcp
    have hcz : CentralProjection (c * z) :=
      ⟨hc.1.mul hz.1 (hc.2 z), fun a => (hc.2 a).mul_left (hz.2 a)⟩
    have hh := h.2.2 (c * z) hcz (by simpa only [mul_assoc] using hcp)
    simpa only [mul_assoc] using hh

lemma IsCentralSupport.centralCut_one {p z : M} (hp : IsStarProjection p)
    (h : IsCentralSupport p 1) (hz : CentralProjection z) :
    IsCentralSupport (z * p) z := by
  simpa only [mul_one] using h.centralCut hp hz

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteProjectionExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Extension of embeddings in finite corners

A partial embedding into a finite projection extends whenever an embedding
of the larger initial projection exists. This is the cancellation step used
in Ringrose, *Lectures on the trace in a finite von Neumann algebra*, Lemma 5.1.
The construction uses only the predual and finiteness, not a trace.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison HochschildCorners

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma partialIso_left_support {q : M} (hq : IsStarProjection q)
    (v : PartialIso M) (hv : v.final ≤ q) : q * (v : M) = v := by
  calc
    q * (v : M) = q * (v.final * (v : M)) := by rw [v.final_mul]
    _ = (v : M) := by
      rw [← mul_assoc, (v.final_proj.le_iff_mul_eq_right hq).mp hv, v.final_mul]

lemma partialIso_right_support {q : M} (hq : IsStarProjection q)
    (v : PartialIso M) (hv : v.initial ≤ q) : (v : M) * q = v := by
  calc
    (v : M) * q = ((v : M) * v.initial) * q := by rw [v.mul_initial]
    _ = (v : M) := by
      rw [mul_assoc, (v.initial_proj.le_iff_mul_eq_left hq).mp hv, v.mul_initial]

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialIsoProducts
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Products of composable partial isometries and comparison of complements. -/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma partialIso_product_initial (v w : PartialIso M) (h : w.final ≤ v.initial) :
    star ((v : M) * w) * ((v : M) * w) = w.initial := by
  calc
    _ = star (w : M) * (v.initial * (w : M)) := by
      simp only [star_mul, PartialIso.initial, mul_assoc]
    _ = w.initial := by rw [partialIso_left_support v.initial_proj w h]; rfl

/-- Compose two partial isometries when the final support of the second lies
in the initial support of the first. -/
def composePartialIso (v w : PartialIso M) (h : w.final ≤ v.initial) : PartialIso M :=
  ⟨(v : M) * w, by
    rw [mul_assoc, partialIso_product_initial v w h, mul_assoc, w.mul_initial]⟩

@[simp] lemma composePartialIso_initial (v w : PartialIso M) (h : w.final ≤ v.initial) :
    (composePartialIso v w h).initial = w.initial := partialIso_product_initial v w h

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CompleteAdditivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete additivity on orthogonal projections

This is the complete-additivity condition of Ringrose, Section 4 (Takesaki's
normality criterion), expressed through the net of finite partial sums.
-/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Preservation of arbitrary orthogonal projection sums. The index universe
need only contain the set of projections of the algebra. -/
def CompletelyAdditive (F : StrongDual ℂ M) : Prop :=
  ∀ (I : Type u) (p : I → M), (∀ i, IsStarProjection (p i)) →
    (∀ i j, i ≠ j → p i * p j = 0) →
    ∀ P : M, IsStarProjection P → (∀ i, p i ≤ P) →
      (∀ r : M, IsStarProjection r → (∀ i, p i ≤ r) → P ≤ r) →
      Tendsto (fun s : Finset I => ∑ i ∈ s, F (p i)) atTop (𝓝 (F P))

omit [StarOrderedRing M] in
lemma CompletelyAdditive.sub {F G : StrongDual ℂ M} (hF : CompletelyAdditive F)
    (hG : CompletelyAdditive G) : CompletelyAdditive (F - G) := by
  classical
  intro I p hp ho P hP hu hl
  simpa only [sub_apply, Finset.sum_sub_distrib] using
    (hF I p hp ho P hP hu hl).sub (hG I p hp ho P hP hu hl)

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.WeakInfiniteness_MatrixRepresentation
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace

namespace WeakPureInfiniteness

section MatrixOperators

variable {n H : Type*} [Fintype n]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def matrixOperator (M : CStarMatrix n n (H →L[ℂ] H)) :
    (PiLp 2 (fun _ : n => H)) →L[ℂ] (PiLp 2 (fun _ : n => H)) :=
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => H)
  e.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun i => ∑ j, (M i j).comp (ContinuousLinearMap.proj j)).comp
      e.toContinuousLinearMap)

omit [CompleteSpace H] in
@[simp]

lemma matrixOperator_apply (M : CStarMatrix n n (H →L[ℂ] H))
    (x : PiLp 2 (fun _ : n => H)) (i : n) :
    matrixOperator M x i = ∑ j, M i j (x j) := by
  simp [matrixOperator]

omit [CompleteSpace H] in
lemma matrixOperator_add (M N : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (M + N) = matrixOperator M + matrixOperator N := by
  ext x i
  simp [Finset.sum_add_distrib]

omit [CompleteSpace H] in
lemma matrixOperator_smul (c : ℂ) (M : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (c • M) = c • matrixOperator M := by
  ext x i
  simp [Finset.smul_sum]

omit [CompleteSpace H] in
lemma matrixOperator_zero : matrixOperator (0 : CStarMatrix n n (H →L[ℂ] H)) = 0 := by
  ext x i
  simp

omit [CompleteSpace H] in
lemma matrixOperator_mul (M N : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (M * N) = matrixOperator M * matrixOperator N := by
  ext x i
  simp only [matrixOperator_apply, CStarMatrix.mul_apply, sum_apply,
    mul_apply_eq_comp, map_sum]
  exact Finset.sum_comm

lemma matrixOperator_star (M : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (star M) = star (matrixOperator M) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply, matrixOperator_apply, sum_inner, inner_sum,
    CStarMatrix.star_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
  exact Finset.sum_comm

noncomputable def matrixOperatorHom : CStarMatrix n n (H →L[ℂ] H) →⋆ₙₐ[ℂ]
    ((PiLp 2 (fun _ : n => H)) →L[ℂ] (PiLp 2 (fun _ : n => H))) where
  toFun := matrixOperator
  map_zero' := matrixOperator_zero
  map_add' := matrixOperator_add
  map_smul' := matrixOperator_smul
  map_mul' := matrixOperator_mul
  map_star' := matrixOperator_star

end MatrixOperators

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveKernelMatrices
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive finite Gram matrices and the coefficient inequality needed for
the Hilbert-space construction of completely positive maps. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype I]

/-- The Gram matrix of a finite family in the algebra. -/
def algebraGram (a : I → M) : CStarMatrix I I M := fun i j => star (a i) * a j

lemma algebraGram_nonneg (a : I → M) : 0 ≤ algebraGram a := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h =>
    have hz : algebraGram a = 0 := by ext i; exact isEmptyElim i
    rw [hz]
  | inr h =>
    let i₀ : I := Classical.choice h
    let R : CStarMatrix I I M := fun i j => if i = i₀ then a j else 0
    have heq : star R * R = algebraGram a := by
      ext i j
      change (∑ k, star (if k = i₀ then a i else 0) *
        (if k = i₀ then a j else 0)) = star (a i) * a j
      simp
    rw [← heq]
    exact star_mul_self_nonneg R

/-- Positivity of operator matrices implies positivity of their finite
quadratic forms, with arbitrary Hilbert-space vectors. -/
lemma operatorMatrix_quadratic_nonneg
    (A : CStarMatrix I I (H →L[ℂ] H)) (hA : 0 ≤ A) (ξ : I → H) :
    0 ≤ ∑ i, ∑ j, inner ℂ (ξ i) (A i j (ξ j)) := by
  have h := map_nonneg (WeakPureInfiniteness.matrixOperatorHom (n := I) (H := H)) hA
  have hi := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp h).inner_nonneg_right
    (WithLp.toLp 2 ξ)
  change 0 ≤ inner ℂ (WithLp.toLp 2 ξ)
    (WeakPureInfiniteness.matrixOperator A (WithLp.toLp 2 ξ)) at hi
  simpa only [PiLp.inner_apply, WeakPureInfiniteness.matrixOperator_apply,
    PiLp.toLp_apply, inner_sum] using hi

/-- A completely positive map produces positive finite coefficient kernels. -/
lemma completelyPositive_kernel_nonneg
    (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : I → M) (ξ : I → H) :
    0 ≤ ∑ i, ∑ j, inner ℂ (ξ i) (φ (star (a i) * a j) (ξ j)) := by
  exact operatorMatrix_quadratic_nonneg _
    (φ.map_cstarMatrix_nonneg (algebraGram a) (algebraGram_nonneg a)) ξ

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveKernelSpace
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Hilbert-space construction for a positive scalar kernel, specialized
later to the coefficient kernel of a completely positive map. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {I : Type*}

/-- The finite coefficient pairing of a scalar kernel. -/
def kernelForm (K : Matrix I I ℂ) (x y : I →₀ ℂ) : ℂ :=
  x.sum fun i a => y.sum fun j b => star a * K i j * b

lemma kernelForm_conj_symm (K : Matrix I I ℂ) (hK : K.IsHermitian) (x y : I →₀ ℂ) :
    star (kernelForm K y x) = kernelForm K x y := by
  classical
  simp only [kernelForm, Finsupp.sum, star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hK.apply i j]
  ring

lemma kernelForm_add_left (K : Matrix I I ℂ) (x y z : I →₀ ℂ) :
    kernelForm K (x + y) z = kernelForm K x z + kernelForm K y z := by
  classical
  unfold kernelForm
  apply Finsupp.sum_add_index'
  · intro i
    simp
  · intro i a b
    simp only [star_add, add_mul, Finsupp.sum, Finset.sum_add_distrib]

lemma kernelForm_smul_left (K : Matrix I I ℂ) (x y : I →₀ ℂ) (r : ℂ) :
    kernelForm K (r • x) y = star r * kernelForm K x y := by
  classical
  unfold kernelForm
  rw [Finsupp.sum_smul_index (by intro i; simp)]
  simp only [star_mul, mul_assoc, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma kernelForm_nonneg (K : Matrix I I ℂ) (hK : K.PosSemidef) (x : I →₀ ℂ) :
    0 ≤ kernelForm K x x := hK.2 x

/-- A type copy keeps the kernel seminorm separate from any norm on the free
coefficient space. Its completion automatically removes the null vectors. -/
def PositiveKernelPreSpace (K : Matrix I I ℂ) (_hK : K.PosSemidef) : Type _ := I →₀ ℂ

instance kernelPreAddCommGroup (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    AddCommGroup (PositiveKernelPreSpace K hK) := inferInstanceAs (AddCommGroup (I →₀ ℂ))

instance kernelPreModule (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    Module ℂ (PositiveKernelPreSpace K hK) := inferInstanceAs (Module ℂ (I →₀ ℂ))

abbrev positiveKernelCore (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    PreInnerProductSpace.Core ℂ (PositiveKernelPreSpace K hK) where
  inner := kernelForm K
  conj_inner_symm x y := kernelForm_conj_symm K hK.1 x y
  re_inner_nonneg x := (kernelForm_nonneg K hK x).1
  add_left := kernelForm_add_left K
  smul_left := kernelForm_smul_left K

instance kernelPreSeminormedAddCommGroup (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    SeminormedAddCommGroup (PositiveKernelPreSpace K hK) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := positiveKernelCore K hK)

instance kernelPreInnerProductSpace (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    InnerProductSpace ℂ (PositiveKernelPreSpace K hK) :=
  InnerProductSpace.ofCore (positiveKernelCore K hK)

/-- The separated Hilbert completion of the finite kernel vectors. -/
abbrev PositiveKernelHilbert (K : Matrix I I ℂ) (hK : K.PosSemidef) :=
  UniformSpace.Completion (PositiveKernelPreSpace K hK)

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_StinespringKernel
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive scalar kernel of an operator-valued completely positive map.
No normality or separability assumption is required. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma completelyPositive_star (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : M) :
    φ (star a) = star (φ a) := by
  obtain ⟨x, hx, _, rfl⟩ := CStarAlgebra.exists_sum_four_nonneg a
  have hxstar (i : Fin 4) : star (x i) = x i := (IsSelfAdjoint.of_nonneg (hx i)).star_eq
  have hystar (i : Fin 4) : star (φ (x i)) = φ (x i) :=
    (IsSelfAdjoint.of_nonneg (map_nonneg φ (hx i))).star_eq
  simp only [star_sum, star_smul, map_sum, map_smul, hxstar, hystar]

/-- The coefficient kernel on formal algebra-vector pairs. -/
def stinespringKernel (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    Matrix (M × H) (M × H) ℂ :=
  fun p q => inner ℂ p.2 (φ (star p.1 * q.1) q.2)

lemma stinespringKernel_hermitian (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    (stinespringKernel φ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  change star (inner ℂ q.2 (φ (star q.1 * p.1) p.2)) =
    inner ℂ p.2 (φ (star p.1 * q.1) q.2)
  rw [← starRingEnd_apply, inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right]
  rw [← ContinuousLinearMap.star_eq_adjoint, ← completelyPositive_star]
  simp only [star_mul, star_star]

lemma kernelForm_coefficients {J : Type*}
    (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : J → M) (ξ : J → H) (x : J →₀ ℂ) :
    kernelForm (fun i j => inner ℂ (ξ i) (φ (star (a i) * a j) (ξ j))) x x =
      ∑ i : x.support, ∑ j : x.support,
        inner ℂ (x i • ξ i) (φ (star (a i) * a j) (x j • ξ j)) := by
  classical
  unfold kernelForm
  rw [Finsupp.sum, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finsupp.sum, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [inner_smul_left, map_smul, inner_smul_right, starRingEnd_apply]
  ring

/-- Complete positivity makes all finite formal-vector norms nonnegative
in this construction. -/
theorem stinespringKernel_positive (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    (stinespringKernel φ).PosSemidef := by
  classical
  refine ⟨stinespringKernel_hermitian φ, ?_⟩
  intro x
  change 0 ≤ kernelForm (fun p q : M × H =>
    inner ℂ p.2 (φ (star p.1 * q.1) q.2)) x x
  rw [kernelForm_coefficients]
  exact completelyPositive_kernel_nonneg φ
    (fun i : x.support => i.val.1) (fun i : x.support => x i • i.val.2)

/-- The auxiliary Hilbert space of a completely positive map. -/
abbrev StinespringSpace (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :=
  PositiveKernelHilbert (stinespringKernel φ) (stinespringKernel_positive φ)

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveKernelActions
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of finite kernel vectors and the corresponding bounded maps
on their pre-Hilbert spaces. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {I : Type*}

lemma kernelForm_mapDomain_left (K : Matrix I I ℂ) (f : I → I) (x y : I →₀ ℂ) :
    kernelForm K (Finsupp.mapDomain f x) y = kernelForm (fun i j => K (f i) j) x y := by
  classical
  unfold kernelForm
  rw [Finsupp.sum_mapDomain_index]
  · intro i
    simp
  · intro i a b
    simp only [star_add, add_mul, Finsupp.sum, Finset.sum_add_distrib]

lemma kernelForm_mapDomain_right (K : Matrix I I ℂ) (f : I → I) (x y : I →₀ ℂ) :
    kernelForm K x (Finsupp.mapDomain f y) = kernelForm (fun i j => K i (f j)) x y := by
  classical
  unfold kernelForm
  apply Finsupp.sum_congr
  intro i hi
  rw [Finsupp.sum_mapDomain_index]
  · intro j
    simp
  · intro j a b
    exact mul_add _ _ _

lemma kernelForm_mapDomain (K : Matrix I I ℂ) (f : I → I) (x y : I →₀ ℂ) :
    kernelForm K (Finsupp.mapDomain f x) (Finsupp.mapDomain f y) =
      kernelForm (fun i j => K (f i) (f j)) x y := by
  rw [kernelForm_mapDomain_left]
  exact kernelForm_mapDomain_right (K := (fun i j => K (f i) j)) f x y

lemma kernelPre_norm_sq (K : Matrix I I ℂ) (hK : K.PosSemidef)
    (x : PositiveKernelPreSpace K hK) : ‖x‖ ^ 2 = (kernelForm K x x).re :=
  norm_sq_eq_re_inner (𝕜 := ℂ) x

/-- A map of labels bounded for the kernel quadratic form induces a bounded
linear map on the finite kernel vectors. -/
def kernelPreMap (K : Matrix I I ℂ) (hK : K.PosSemidef) (f : I → I)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x : I →₀ ℂ, (kernelForm (fun i j => K (f i) (f j)) x x).re ≤
      C ^ 2 * (kernelForm K x x).re) :
    PositiveKernelPreSpace K hK →L[ℂ] PositiveKernelPreSpace K hK :=
  let L : PositiveKernelPreSpace K hK →ₗ[ℂ] PositiveKernelPreSpace K hK :=
    { toFun := Finsupp.mapDomain f
      map_add' _ _ := Finsupp.mapDomain_add
      map_smul' r x := Finsupp.mapDomain_smul r x }
  L.mkContinuous C (fun x => by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
    rw [mul_pow, kernelPre_norm_sq K hK, kernelPre_norm_sq K hK]
    change (kernelForm K (Finsupp.mapDomain f x) (Finsupp.mapDomain f x)).re ≤
      C ^ 2 * (kernelForm K x x).re
    exact (congrArg Complex.re (kernelForm_mapDomain K f
      (show I →₀ ℂ from x) (show I →₀ ℂ from x))).trans_le (hf x))

@[simp] lemma kernelPreMap_apply (K : Matrix I I ℂ) (hK : K.PosSemidef) (f : I → I)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x : I →₀ ℂ, (kernelForm (fun i j => K (f i) (f j)) x x).re ≤
      C ^ 2 * (kernelForm K x x).re) (x : PositiveKernelPreSpace K hK) :
    kernelPreMap K hK f C hC hf x = Finsupp.mapDomain f x := rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_StinespringLeftAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Left multiplication on the auxiliary positive-kernel Hilbert space. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev StinespringPreSpace (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :=
  PositiveKernelPreSpace (stinespringKernel φ) (stinespringKernel_positive φ)

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_IsometryDefectColumns
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Orthogonal columns from an isometry defect

A nonunitary isometry supplies countably many equivalent, orthogonal defect
projections. This is an algebraic ingredient of the properly infinite case.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M]

lemma isometry_pow_initial {v : M} (hv : star v * v = 1) (n : ℕ) :
    star (v ^ n) * v ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, star_mul]
      calc
        _ = star v * (star (v ^ n) * v ^ n) * v := by simp only [mul_assoc]
        _ = 1 := by rw [ih, mul_one, hv]

lemma isometry_column_initial {v p : M} (hv : star v * v = 1)
    (hp : IsStarProjection p) (n : ℕ) :
    star (v ^ n * p) * (v ^ n * p) = p := by
  rw [star_mul, hp.isSelfAdjoint.star_eq]
  calc
    _ = p * (star (v ^ n) * v ^ n) * p := by simp only [mul_assoc]
    _ = p := by rw [isometry_pow_initial hv, mul_one, hp.isIdempotentElem.eq]

def isometryColumn (v : M) (hv : star v * v = 1) (p : M)
    (hp : IsStarProjection p) (n : ℕ) : PartialIso M :=
  ⟨v ^ n * p, by
    rw [mul_assoc, isometry_column_initial hv hp, mul_assoc, hp.isIdempotentElem.eq]⟩

@[simp] lemma isometryColumn_initial (v : M) (hv : star v * v = 1) (p : M)
    (hp : IsStarProjection p) (n : ℕ) :
    (isometryColumn v hv p hp n).initial = p := isometry_column_initial hv hp n

@[simp] lemma isometryColumn_coe (v : M) (hv : star v * v = 1) (p : M)
    (hp : IsStarProjection p) (n : ℕ) :
    (isometryColumn v hv p hp n : M) = v ^ n * p := rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ProperlyInfiniteColumns
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Properly infinite projections from orthogonal columns

Countably many equivalent orthogonal projections split into even and odd
columns. The resulting operators are actual partial isometries in the algebra.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- A projection admits two orthogonal copies of itself inside itself. -/
def ProperlyInfiniteProjection (p : M) : Prop :=
  ∃ v w : PartialIso M, v.initial = p ∧ w.initial = p ∧
    v.final ≤ p ∧ w.final ≤ p ∧ v.final * w.final = 0

omit [PartialOrder M] [StarOrderedRing M] in
lemma column_transition_initial (v w : PartialIso M) (h : v.initial = w.initial) :
    star ((v : M) * star (w : M)) * ((v : M) * star (w : M)) = w.final := by
  calc
    _ = (w : M) * v.initial * star (w : M) := by
      simp only [star_mul, star_star, PartialIso.initial, mul_assoc]
    _ = w.final := by rw [h, w.mul_initial]; rfl

def columnTransition (v w : PartialIso M) (h : v.initial = w.initial) : PartialIso M :=
  ⟨(v : M) * star (w : M), by
    rw [mul_assoc, column_transition_initial v w h]
    have hw : star (w : M) * w.final = star (w : M) := by
      simpa only [star_mul, star_star, w.final_proj.isSelfAdjoint.star_eq] using
        congrArg star w.final_mul
    rw [mul_assoc, hw]⟩

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma columnTransition_initial (v w : PartialIso M) (h) :
    (columnTransition v w h).initial = w.final := column_transition_initial v w h

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma columnTransition_final (v w : PartialIso M) (h) :
    (columnTransition v w h).final = v.final := by
  change ((v : M) * star (w : M)) * star ((v : M) * star (w : M)) = _
  rw [star_mul, star_star]
  calc
    _ = (v : M) * w.initial * star (v : M) := by simp only [PartialIso.initial, mul_assoc]
    _ = v.final := by rw [← h, v.mul_initial]; rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TypeIMatrixColumns
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso_final _root_.OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso_final _root_.OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.composePartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_initial _root_.OAI.HochschildComparison.Frame.zero_part _root_.OAI.HochschildComparison.PartialIso.ofProjection_coe _root_.OAI.HochschildComparison.PartialIso.ofProjection_final _root_.OAI.HochschildComparison.PartialIso.ofProjection_initial _root_.OAI.HochschildComparison.PartialIso.restrict_coe _root_.OAI.HochschildComparison.PartialIso.restrict_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Homogeneous matrix systems from equivalent orthogonal abelian projections. -/

noncomputable section

open scoped BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison HochschildMatrixSystems

variable {M : Type*} [CStarAlgebra M] {n : ℕ} {p : M}

def matrixSystemOfColumns (v : Fin n → PartialIso M)
    (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0)
    (hs : ∑ i, (v i).final = 1) : MatrixSystem M n where
  entry i j := (v i : M) * star (v j : M)
  star_entry i j := by simp only [star_mul, star_star]
  entry_mul i j k l := by
    classical
    by_cases h : j = k
    · subst k
      rw [ite_eq_left rfl]
      calc
        _ = (v i : M) * (v j).initial * star (v l : M) := by
          simp only [PartialIso.initial, mul_assoc]
        _ = (v i : M) * (v i).initial * star (v l : M) := by rw [hi, hi]
        _ = _ := by rw [(v i).mul_initial]
    · rw [ite_eq_right h]
      calc
        _ = (v i : M) * (star (v j : M) * (v k : M)) * star (v l : M) := by
          simp only [mul_assoc]
        _ = 0 := by rw [PartialIso.star_mul_eq_zero_of_final_orthogonal (ho j k h),
          mul_zero, zero_mul]
  sum_diagonal := hs

@[simp] lemma matrixSystemOfColumns_diagonal (v : Fin n → PartialIso M)
    (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0)
    (hs : ∑ i, (v i).final = 1) (i : Fin n) :
    (matrixSystemOfColumns v hi ho hs).entry i i = (v i).final := rfl

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TypeICentralPieces
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.composePartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete finite homogeneous central corners and their matrix columns. -/

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners HochschildComparison HochschildMatrixSystems FinitePathMain

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def HomogeneousTypeICorner (z : M) : Prop :=
  ∃ (hz : IsStarProjection z) (n : ℕ) (E : MatrixSystem (Corner z hz) n) (i : Fin n),
    AbelianProjection (E.entry i i)

def partialIsoInCorner {z : M} (hz : IsStarProjection z) (v : PartialIso M)
    (hi : v.initial ≤ z) (hf : v.final ≤ z) : PartialIso (Corner z hz) where
  val := ⟨(v : M), partialIso_left_support hz v hf, partialIso_right_support hz v hi⟩
  mul_star_mul := Subtype.ext v.mul_star_mul

@[simp] lemma partialIsoInCorner_initial {z : M} (hz : IsStarProjection z)
    (v : PartialIso M) (hi : v.initial ≤ z) (hf : v.final ≤ z) :
    ((partialIsoInCorner hz v hi hf).initial : M) = v.initial := rfl

@[simp] lemma partialIsoInCorner_final {z : M} (hz : IsStarProjection z)
    (v : PartialIso M) (hi : v.initial ≤ z) (hf : v.final ≤ z) :
    ((partialIsoInCorner hz v hi hf).final : M) = v.final := rfl

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_InfiniteCentralReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The remaining properly infinite input

The finite case is proved. The maximal finite central cut reduces the
classical vanishing input to algebras with no nonzero finite central summand,
the properly infinite case of Christensen--Effros--Sinclair (1987), as
recorded in Christensen--Pop--Sinclair--Smith (2003), p. 636, equation (1.1).
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners

universe u

def NoFiniteCentralSummand (M : Type u) [CStarAlgebra M]
    [PartialOrder M] [StarOrderedRing M] : Prop :=
  ∀ (p : M) (hp : IsStarProjection p), (∀ a : M, p * a = a * p) →
    FiniteAlgebra (Corner p hp) → p = 0

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ProperlyInfiniteCorners
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner transport and finiteness obstructions for properly infinite projections. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison HochschildCorners FinitePathMain

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def partialIsoFromCorner {p : M} (hp : IsStarProjection p)
    (v : PartialIso (Corner p hp)) : PartialIso M :=
  ⟨((v : Corner p hp) : M), congrArg Subtype.val v.mul_star_mul⟩

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma partialIsoFromCorner_initial {p : M} (hp : IsStarProjection p)
    (v : PartialIso (Corner p hp)) :
    (partialIsoFromCorner hp v).initial = ((v.initial : Corner p hp) : M) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma partialIsoFromCorner_final {p : M} (hp : IsStarProjection p)
    (v : PartialIso (Corner p hp)) :
    (partialIsoFromCorner hp v).final = ((v.final : Corner p hp) : M) := rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_InfinitePairChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Increasing chains of pairs implementing properly infinite projections. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Two embeddings of a common projection into orthogonal subprojections. -/
def IsInfinitePair (a : PartialIso M × PartialIso M) : Prop :=
  a.1.initial = a.2.initial ∧ a.1.final ≤ a.1.initial ∧
    a.2.final ≤ a.1.initial ∧ a.1.final * a.2.final = 0

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PaulsenExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend the two-by-two operator-system map into operators on the doubled
Hilbert space, using the proved positive extension theorem. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev HilbertDouble (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  PiLp 2 (fun _ : Fin 2 => H)

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CompletelyBoundedFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Factor a completely contractive map through an actual star representation. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

universe u v
variable {A : Type u} {H : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure OperatorFactorization (T : A →ₗ[ℂ] (H →L[ℂ] H)) (C : ℝ) where
  K : Type (max u v)
  [normed : NormedAddCommGroup K]
  [innerSpace : InnerProductSpace ℂ K]
  [complete : CompleteSpace K]
  representation : A →⋆ₐ[ℂ] (K →L[ℂ] K)
  leftMap : H →L[ℂ] K
  rightMap : H →L[ℂ] K
  bound : ‖leftMap‖ * ‖rightMap‖ ≤ C
  factorization : ∀ a, T a = leftMap.adjoint.comp ((representation a).comp rightMap)

attribute [instance] OperatorFactorization.normed OperatorFactorization.innerSpace
  OperatorFactorization.complete

end BoundedHochschild.KadisonRingrose

end

end OAI
end


