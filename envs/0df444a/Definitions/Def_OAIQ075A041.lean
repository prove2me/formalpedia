-- Prove2me | Definitions.Def_OAIQ075A041
-- name    : OAIQ075A041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T11:01:49.608195+00:00
-- url     : https://prove2.me/theorems/ca60816b-84f5-49b6-84b0-78fe1118658e
-- title:
--   Definitions bundle OAIQ075A041 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 1 definition and 8 theorems. The definitions and types are `OAI.KadisonSimilarity.publishedSeparableModel_of_central_factors`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`KadisonSimilarity_FreeProduct_FiniteFactorFreeness`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/FiniteFactorFreeness.lean), [`KadisonSimilarity_FreeProduct_MatrixSourceFreeness`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/MatrixSourceFreeness.lean), [`KadisonSimilarity_FreeProduct_NormalInclusionFreeness`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/NormalInclusionFreeness.lean), [`KadisonSimilarity_FreeProduct_TracialInclusionFreeness`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialInclusionFreeness.lean), [`KadisonSimilarity_Representation_CentralFactorAssembly`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/CentralFactorAssembly.lean), [`KadisonSimilarity_Tracial_SourceAllMoments`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/SourceAllMoments.lean), [`KadisonSimilarity_Tracial_SourceConstantMoments`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/SourceConstantMoments.lean).
--
--   **Imports.** It imports the bundle `OAIQ075A040` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.KadisonSimilarity.publishedUniformInputs`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A040

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceAllMoments
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All mixed words from a countable ambient family vanish for a sequence
of source unitaries in the tracial ultrapower. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial
open UltrapowerBridge (TracialRepresentation)
open HochschildComparison HochschildPatching HochschildUltrapower BoundedHochschild
open TracialUltrapower Filter Topology
open scoped ComplexOrder BoundedContinuousFunction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

local instance allMomentAmbientClosed_rb0c165_1 : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
attribute [local instance] OAI.KadisonSimilarity.allMomentSourceClosed
include hfactor hdiff hirr in
theorem exists_source_quotient_unitary_all_moments
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    {I : Type*} [Countable I] [Nonempty I]
    (A : I → (ℕ →ᵇ M.toStarSubalgebra)) (hA : ∀ i n, ‖A i n‖ ≤ 1) :
    ∃ u : ℕ → unitary R.toStarSubalgebra,
      AllQuotientMoments (B := M.toStarSubalgebra) (vectorPositiveFunctional M υ.vector) υ.trace_one ω υ.trace_mul_comm
        A (fun n => mapUnitary (coordinateInclusion hRM) (u n)) := by
  classical
  let τ := vectorPositiveFunctional M υ.vector
  let h1 : τ 1 = 1 := υ.trace_one
  let tr : ∀ a b, τ (a * b) = τ (b * a) := υ.trace_mul_comm
  let : Inhabited I := ⟨Classical.arbitrary I⟩
  let : Encodable I := Encodable.ofCountable I
  let f : ℕ → I := fun n => (Encodable.decode (α := I) n).getD default
  have hf (i : I) : f (Encodable.encode i) = i := by simp [f]
  obtain ⟨u, hu⟩ := exists_source_quotient_unitary_moments υ hRM hfactor hdiff hirr ω hω
    (A ∘ f) (fun i n => hA (f i) n)
  refine ⟨u, fun K a l hl => ?_⟩
  let C : ℕ → Ultrapower (A := M.toStarSubalgebra) τ h1 ω tr := fun n => quotientHom (A := M.toStarSubalgebra) τ h1 ω tr (A (f n)) -
    quotientTrace (A := M.toStarSubalgebra) τ h1 ω tr (quotientHom (A := M.toStarSubalgebra) τ h1 ω tr (A (f n))) • 1
  have hz := all_finite_words (quotientTrace (A := M.toStarSubalgebra) τ h1 ω tr) C
    (quotientUnitary (M := M.toStarSubalgebra) τ h1 ω tr (fun n => mapUnitary (coordinateInclusion hRM) (u n)))
    hu K (a.map Encodable.encode) (l.map (mapAtom Encodable.encode id))
    (admissibleTail_map Encodable.encode id l hl)
  rw [mixedEval_map C Encodable.encode id (fun _ => rfl)] at hz
  have hc : C ∘ Encodable.encode = fun i => quotientHom (A := M.toStarSubalgebra) τ h1 ω tr (A i) -
      quotientTrace (A := M.toStarSubalgebra) τ h1 ω tr (quotientHom (A := M.toStarSubalgebra) τ h1 ω tr (A i)) • 1 := by
    funext i
    simp only [Function.comp_apply, C, hf]
  rw [hc] at hz
  exact hz

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceConstantMoments
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prescribed-source unitaries annihilate all centered constant mixed moments. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial
open UltrapowerBridge (TracialRepresentation)
open HochschildComparison HochschildPatching HochschildUltrapower BoundedHochschild
open TracialUltrapower Filter Topology
open scoped ComplexOrder BoundedContinuousFunction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

local instance constantMomentAmbientClosed_rb0c165_1 : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
attribute [local instance] OAI.KadisonSimilarity.constantMomentSourceClosed
include hfactor hdiff hirr in
theorem exists_source_constant_integer_moments
    [TopologicalSpace.SeparableSpace (vectorPositiveFunctional M υ.vector).GNS]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop) :
    ∃ u : ℕ → unitary R.toStarSubalgebra,
      ConstantIntegerMoments (B := M.toStarSubalgebra)
        (vectorPositiveFunctional M υ.vector) υ.trace_one ω υ.trace_mul_comm
        (fun n => mapUnitary (coordinateInclusion hRM) (u n)) := by
  let τ := vectorPositiveFunctional M υ.vector
  obtain ⟨d, hd, hdense⟩ := exists_trace_dense_contractions τ
  obtain ⟨u, hu⟩ := exists_source_quotient_unitary_all_moments υ hRM hfactor hdiff hirr ω hω
    (fun i => BoundedContinuousFunction.const ℕ (d i)) (fun i _ => hd i)
  exact ⟨u, constantIntegerMoments_of_dense τ υ.trace_one ω υ.trace_mul_comm
    d hd hdense (fun n => mapUnitary (coordinateInclusion hRM) (u n)) hu⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialInclusionFreeness
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prescribed-source freeness for an abstract normal tracial inclusion. -/

noncomputable section
namespace KadisonSimilarity
open Generator Generator.Tracial
open UltrapowerBridge (TracialRepresentation)
open HochschildPatching HochschildUltrapower
open scoped ComplexOrder

universe u
variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {φ : A →⋆ₐ[ℂ] B} {τ : B →ₚ[ℂ] ℂ}

namespace TracialInclusionModel
variable (F : TracialInclusionModel φ τ)

attribute [local instance] OAI.KadisonSimilarity.TracialInclusionModel.modelMomentAmbientClosed
attribute [local instance] OAI.KadisonSimilarity.TracialInclusionModel.modelMomentSourceClosed
include F in
omit [PartialOrder A] [StarOrderedRing A] in
theorem exists_source_moments [TopologicalSpace.SeparableSpace τ.GNS]
    (h1 : τ 1 = 1) (tr : ∀ a b, τ (a * b) = τ (b * a))
    (hfactor : ∀ c : A, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (hirr : ∀ c : B, (∀ a : A, φ a * c = c * φ a) → ∃ z : ℂ, c = z • 1)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.atTop) :
    ∃ u : ℕ → unitary A,
      ConstantIntegerMoments τ h1 ω tr (fun n => mapUnitary φ (u n)) := by
  let τF := vectorPositiveFunctional F.M F.representation.vector
  let : TopologicalSpace.SeparableSpace τF.GNS :=
    gns_separable_of_trace_equiv τ τF F.ambientEquiv F.trace_eq
  obtain ⟨v, hv⟩ := exists_source_constant_integer_moments F.representation F.le
    (F.source_factor hfactor) (F.source_diffuse hdiff) (F.source_irreducible hirr) ω hω
  let u : ℕ → unitary A := fun n => mapUnitary F.sourceEquiv.symm.toStarAlgHom (v n)
  have he (n : ℕ) : mapUnitary F.ambientEquiv.toStarAlgHom (mapUnitary φ (u n)) =
      mapUnitary (coordinateInclusion F.le) (v n) := by
    apply Subtype.ext
    change F.ambientEquiv (φ (F.sourceEquiv.symm (v n : F.N.toStarSubalgebra))) =
      coordinateInclusion F.le (v n : F.N.toStarSubalgebra)
    rw [← F.compatible, F.sourceEquiv.apply_symm_apply]
  refine ⟨u, constantIntegerMoments_of_map τ τF h1 F.representation.trace_one ω tr
    F.representation.trace_mul_comm F.ambientEquiv.toStarAlgHom F.trace_eq
    (fun n => mapUnitary φ (u n)) ?_⟩
  simpa only [he] using hv

end TracialInclusionModel

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_NormalInclusionFreeness
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The free-position specialization from normal trace models and closed
source trace balls. No predual construction for a matrix algebra is needed. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial HochschildPatching HochschildUltrapower
open scoped ComplexOrder

universe u
variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem popa1995_of_normal_traces
    (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
    [TopologicalSpace.SeparableSpace τB.GNS]
    (hclosed : ∀ C : ℝ, IsClosed (gnsTracialVector τA '' Metric.closedBall (0 : A) C))
    (h1A : τA 1 = 1) (h1B : τB 1 = 1)
    (trA : ∀ a b, τA (a * b) = τA (b * a))
    (trB : ∀ a b, τB (a * b) = τB (b * a))
    (hfB : ∀ a, τB (star a * a) = 0 → a = 0) (hnB : HasNormalGNS τB)
    (ψ : A →⋆ₐ[ℂ] B) (hi : Function.Injective ψ)
    (ht : ∀ a, τB (ψ a) = τA a)
    (hfactor : ∀ c : A, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (hirr : ∀ c : B, (∀ a : A, ψ a * c = c * ψ a) → ∃ z : ℂ, c = z • 1)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    {D : Type*} [CStarAlgebra D] (ρ : D →⋆ₐ[ℂ] A) :
    Popa1995ConjugateFreenessInput τA τB h1A h1B ω trA trB ψ ht hω ρ := by
  obtain ⟨F⟩ := exists_tracialInclusionModel_of_trace_balls τA τB hclosed h1B trB hfB hnB ψ hi ht
  obtain ⟨v, hv⟩ := F.exists_source_moments h1B trB hfactor hdiff hirr ω
    (hω.trans_eq Nat.cofinite_eq_atTop)
  exact popaConjugateFreeness_of_constant_moments τA τB h1A h1B ω trA trB ψ ht hω ρ v hv

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_MatrixSourceFreeness
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved prescribed-source freeness theorem supplies every finite
matrix amplification required by the finite-factor estimate. -/

noncomputable section
namespace KadisonSimilarity
open UltrapowerBridge
open scoped ComplexOrder

universe u
variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem finiteFactorFreeCornerInputs_of_normal_tower
    (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
    [TopologicalSpace.SeparableSpace τB.GNS]
    (hA : τA 1 = 1) (hB : τB 1 = 1)
    (trA : ∀ a b, τA (a * b) = τA (b * a))
    (trB : ∀ a b, τB (a * b) = τB (b * a))
    (hfA : ∀ a, τA (star a * a) = 0 → a = 0)
    (hfB : ∀ a, τB (star a * a) = 0 → a = 0)
    (hnA : HasNormalGNS τA) (hnB : HasNormalGNS τB)
    (φ : A →⋆ₐ[ℂ] B) (hi : Function.Injective φ)
    (ht : ∀ a, τB (φ a) = τA a)
    (hirr : ∀ c : B, (∀ a : A, φ a * c = c * φ a) → ∃ z : ℂ, c = z • 1)
    {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
    (M : NestedTracialMatrices (A := I) τA.toLinearMap (gnsTracialVector τA))
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite) :
    FiniteFactorFreeCornerInputs τA τB hA hB ω trA trB φ ht hω := by
  refine ⟨fun n _ => ?_⟩
  let := matrix_gns_separable τB n
  have hcenter : ∀ c : A, (∀ a : A, c * a = a * c) →
      ∃ z : ℂ, c = algebraMap ℂ A z := by
    intro c hc
    obtain ⟨z, hz⟩ := (gnsTracialGeometry τA trA).scalar_center_of_matrix_tower M
      (gnsTracialVector_injective τA hfA) c (fun a => (hc a).symm)
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  have hfactor : ∀ X : CStarMatrix (Fin n) (Fin n) A,
      (∀ Y, Y * X = X * Y) → ∃ z : ℂ, X = z • 1 := by
    intro X hX
    have hid (Y : CStarMatrix (Fin n) (Fin n) A) :
        matrixEntryHom (StarAlgHom.id ℂ A) Y = Y := by
      ext i j
      rfl
    obtain ⟨z, hz⟩ := scalar_of_matrix_relative_commutant (StarAlgHom.id ℂ A)
      hcenter X (fun Y => by rw [hid]; exact (hX Y).symm)
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  have hirrn : ∀ X : CStarMatrix (Fin n) (Fin n) B,
      (∀ Y, matrixEntryHom φ Y * X = X * matrixEntryHom φ Y) →
      ∃ z : ℂ, X = z • 1 := by
    intro X hX
    obtain ⟨z, hz⟩ := scalar_of_matrix_relative_commutant φ
      (fun c hc => by
        obtain ⟨z, hz⟩ := hirr c (fun a => (hc a).symm)
        exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩)
      X (fun Y => (hX Y).symm)
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  exact popa1995_of_normal_traces (normalizedMatrixTrace τA n) (normalizedMatrixTrace τB n)
    (matrix_trace_balls_closed τA _ hnA n hA trA hfA)
    (normalizedMatrixTrace_one τA hA) (normalizedMatrixTrace_one τB hB)
    (normalizedMatrixTrace_tracial τA trA) (normalizedMatrixTrace_tracial τB trB)
    (normalizedMatrixTrace_faithful τB hfB) (matrix_gns_normal_range τB _ hnB n)
    (matrixEntryHom φ) (matrixEntryHom_injective φ hi)
    (normalizedMatrixTrace_entryHom τA τB φ ht) hfactor
    (matrix_diffuse_of_tower τA hA trA hfA M hnA hsize n) hirrn ω hω (matrixDiagonalHom n)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FiniteFactorFreeness
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed irreducible matrix source supplies the free position
required by every separably acting finite factor. -/

noncomputable section
namespace KadisonSimilarity
open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : VonNeumannAlgebra H} [TopologicalSpace.SeparableSpace H]

namespace FiniteFactorPresentation
variable (F : FiniteFactorPresentation P)

theorem freePosition (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite) :
    F.FreePosition ω hω := by
  let : Nontrivial F.N.toStarSubalgebra :=
    nontrivial_of_ne (F.equivalence 0) (F.equivalence 1) (fun h => by
      have he : (0 : P.toStarSubalgebra) = 1 := F.equivalence.injective h
      have ht := congrArg F.traceData.trace he
      rw [map_zero, F.traceData.one] at ht
      exact zero_ne_one ht)
  let : ∀ n, Nonempty (Fin (F.source.stages n).size) :=
    fun n => ⟨⟨0, (F.source.stages n).positive⟩⟩
  let : TopologicalSpace.SeparableSpace F.traceData.trace.GNS :=
    gns_separable_of_predual (concretePredualEquiv P) F.traceData.trace F.traceData.normal_predual
  apply finiteFactorFreeCornerInputs_of_normal_tower
    (generatedMatrixTrace F.source.stages F.representation) F.traceData.trace
    (generatedMatrixTrace_one F.source.stages F.representation) F.traceData.one
    (generatedMatrixTrace_tracial F.source.stages F.representation) F.traceData.tracial
    (generatedMatrixTrace_faithful F.source.stages F.representation) F.traceData.faithful
    (generatedMatrixTrace_normal F.source.stages F.representation) F.normal
    F.inclusion ?_ F.trace_inclusion ?_
    (concreteNestedTracialMatrices F.source.stages F.source.monotone F.representation)
    (matrix_stage_sizes_tendsto F.source.stages F.source.monotone F.source.source_factor.diffuse)
    ω hω
  · exact F.equivalence.symm.injective.comp
      (StarSubalgebra.inclusion_injective (FiniteMatrixStage.generated_le F.source.stages))
  · intro c hc
    have hcomm (a : FiniteMatrixStage.generated F.source.stages) :
        a.val * (F.equivalence c).val = (F.equivalence c).val * a.val := by
      have h := congrArg F.equivalence (hc a)
      change F.equivalence (F.inclusion a * c) = F.equivalence (c * F.inclusion a) at h
      rw [map_mul, map_mul] at h
      have ha : F.equivalence (F.inclusion a) = StarSubalgebra.inclusion
          (FiniteMatrixStage.generated_le F.source.stages) a :=
        F.equivalence.apply_symm_apply _
      rw [ha] at h
      exact congrArg Subtype.val h
    obtain ⟨z, hz⟩ := F.source.irreducible (F.equivalence c) hcomm
    refine ⟨z, F.equivalence.injective ?_⟩
    change F.equivalence c = F.equivalence (z • 1)
    rw [map_smul, map_one]
    exact hz

end FiniteFactorPresentation

/-- The three structural factor alternatives have local free-position data. -/
theorem publishedFactorCases [Nontrivial H]
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c) :
    PublishedFactorCasesInput P := by
  apply publishedFactorCases_of_free_position P hfactor
  intro F
  obtain ⟨ω, hω⟩ := Ultrafilter.exists_le (Filter.cofinite : Filter ℕ)
  exact ⟨ω, hω, F.freePosition ω hω⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CentralFactorAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The factor alternatives are proved, including zero Hilbert fibers.
Only the central decomposition itself remains a structural input here. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] (P : VonNeumannAlgebra H)

theorem publishedFactorCases_of_scalar_center
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c) :
    PublishedFactorCasesInput P := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · let := hs
    let σ : Matrix (Fin 1) (Fin 1) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H) := {
      toFun := fun _ => 0
      map_zero' := rfl
      map_add' := fun _ _ => by simp
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ => by simp
      commutes' := fun _ => Subsingleton.elim _ _
      map_star' := fun _ => by simp }
    exact Or.inr (Or.inr ⟨{
      size := 1
      size_ne_zero := by decide
      inclusion := σ
      mem := fun _ => P.zero_mem
      surjective := fun T _ => ⟨0, Subsingleton.elim _ _⟩ }⟩)
  · let := hn
    exact publishedFactorCases hfactor

variable {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type u) [∀ a, NormedAddCommGroup (K a)]
  [∀ a, InnerProductSpace ℂ (K a)] [∀ a, CompleteSpace (K a)]
  [∀ a, TopologicalSpace.SeparableSpace (K a)]

/-- A central decomposition into actual factors suffices; no factor model
or free-position hypothesis is required from the decomposition theorem. -/
def publishedSeparableModel_of_central_factors
    (D : CentralDecompositionData μ K P)
    (hfactor : ∀ᵐ a ∂μ, ∀ x : (D.algebra a).toStarSubalgebra,
      (∀ y, x * y = y * x) →
        ∃ z : ℂ, x = algebraMap ℂ (D.algebra a).toStarSubalgebra z) :
    PublishedSeparableModel P where
  Ω := Ω
  measure := μ
  K := K
  decomposition := D
  cases := hfactor.mono fun a ha => publishedFactorCases_of_scalar_center (D.algebra a) ha

end KadisonSimilarity

end

end OAI
end


