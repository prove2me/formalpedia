-- Prove2me | Definitions.Def_OAIQ075A039
-- name    : OAIQ075A039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:47:44.02337+00:00
-- url     : https://prove2.me/theorems/e4d2ee75-75ed-4b6b-9424-5ec8a1889cc0
-- title:
--   Definitions bundle OAIQ075A039 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`KadisonSimilarity_Tracial_FiniteFactorPresentation`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/FiniteFactorPresentation.lean), [`KadisonSimilarity_Tracial_SourceCornerQuantization`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/SourceCornerQuantization.lean), [`KadisonSimilarity_Tracial_SourceIncrementalPatching`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/SourceIncrementalPatching.lean).
--
--   **Imports.** It imports the bundle `OAIQ075A038` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ075A040`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A038

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FiniteFactorPresentation
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite diffuse branch has a constructed normal trace and an actual
irreducible matrix source. Its sole remaining local input is Popa freeness. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open BoundedHochschild.KadisonRingrose
open scoped ComplexOrder

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

attribute [instance] FiniteFactorPresentation.normed FiniteFactorPresentation.innerProduct
  FiniteFactorPresentation.complete

attribute [local instance] OAI.KadisonSimilarity.finitePresentationClosed
theorem exists_finiteFactorPresentation [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    (hP : IsII1Factor P.toStarSubalgebra) : Nonempty (FiniteFactorPresentation P) := by
  obtain ⟨τ, hnormal, h1, htr, hf, hn⟩ := exists_faithful_normal_trace P hP.finite
    (fun a ha => hP.factor a (fun b => (ha b).symm))
  obtain ⟨F, _, hmono, _, hII, _, hirr⟩ := exists_gns_irreducible_matrix_subfactor
    (concretePredualEquiv P) τ h1 htr hf hnormal hP.factor hP.diffuse
  exact ⟨{
    traceData := {
      trace := τ
      normal_predual := hnormal
      one := h1
      tracial := htr
      faithful := hf }
    K := τ.GNS
    N := representationVonNeumannAlgebra τ.gnsStarAlgHom
    representation := normalGNSRepresentation τ h1 htr hf hn
    equivalence := normalGNSEquivalence τ htr hf hn
    trace_equivalence := normalGNSRepresentation_trace τ h1 htr hf hn
    source := {
      stages := F
      monotone := hmono
      source_factor := hII
      irreducible := hirr } }⟩

/-- Factor classification and the normal matrix presentation reduce the
finite diffuse case to prescribed-source free position. -/
theorem publishedFactorCases_of_free_position [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c)
    (hfree : ∀ F : FiniteFactorPresentation P,
      ∃ (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite), F.FreePosition ω hω) :
    PublishedFactorCasesInput P := by
  rcases factor_structural_cases P hfactor with hfinite | hinfinite | hmatrix
  · obtain ⟨F⟩ := exists_finiteFactorPresentation P hfinite
    obtain ⟨ω, hω, hF⟩ := hfree F
    exact Or.inl ⟨F.model ω hω hF⟩
  · exact Or.inr (Or.inl hinfinite)
  · exact Or.inr (Or.inr hmatrix)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceCornerQuantization
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local quantization inside every nonzero corner of the prescribed source. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open HochschildCorners
open scoped ComplexOrder

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hNM : N ≤ M)

local instance sourceCornerAmbientClosed_ra7ef65_1 : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
attribute [local instance] OAI.KadisonSimilarity.sourceCornerSourceClosed
/-- Centered coefficients in the normalized corner admit small source projections. -/
theorem exists_source_corner_compression
    (hfactor : ∀ c : N.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra, coordinateInclusion hNM a * c =
        c * coordinateInclusion hNM a) → ∃ z : ℂ, c = z • 1)
    (p : N.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0)
    {I : Type*} [Fintype I]
    (x : I → Corner (coordinateInclusion hNM p) (hp.map (coordinateInclusion hNM)))
    (hx : ∀ i, cornerTrace (coordinateInclusion hNM p)
      (hp.map (coordinateInclusion hNM)) (vectorPositiveFunctional M υ.vector) (x i) = 0)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ q : Corner p hp, IsStarProjection q ∧ q ≠ 0 ∧
      (cornerTrace (coordinateInclusion hNM p) (hp.map (coordinateInclusion hNM))
        (vectorPositiveFunctional M υ.vector) (sourceCornerHom (coordinateInclusion hNM) p hp q)).re < η ∧
      ∀ i, ‖(cornerTrace (coordinateInclusion hNM p) (hp.map (coordinateInclusion hNM))
        (vectorPositiveFunctional M υ.vector)).toPreGNS
          (sourceCornerHom (coordinateInclusion hNM) p hp q * x i *
            sourceCornerHom (coordinateInclusion hNM) p hp q)‖ ^ 2 <
        δ * (cornerTrace (coordinateInclusion hNM p) (hp.map (coordinateInclusion hNM))
          (vectorPositiveFunctional M υ.vector) (sourceCornerHom (coordinateInclusion hNM) p hp q)).re := by
  let φ := coordinateInclusion hNM
  let τN := vectorPositiveFunctional N υ.vector
  let τM := vectorPositiveFunctional M υ.vector
  let pM := φ p
  have hpM : IsStarProjection pM := hp.map φ
  have hpM0 : pM ≠ 0 := fun h => hp0
    (Subtype.ext (congrArg (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H)) h))
  have hfM (a : M.toStarSubalgebra) (ha : τM (star a * a) = 0) : a = 0 := by
    apply υ.separating a
    exact inner_self_eq_zero.mp ((baseVector_inner_trace υ a a).trans ha)
  let ρN := cornerTrace p hp τN
  let ρM := cornerTrace pM hpM τM
  let ψ := sourceCornerHom φ p hp
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : Corner pM hpM => c.val.val) hab
  let : Nontrivial (Corner p hp) := nontrivial_of_ne (1 : Corner p hp) 0
    (fun h => hp0 (congrArg (fun a : Corner p hp => (a : N.toStarSubalgebra)) h))
  exact exists_relative_compression_of_predual
    (cornerPredualEquiv p hp (concretePredualEquiv N))
    (cornerPredualEquiv pM hpM (concretePredualEquiv M)) ρN ρM
    (cornerTrace_normal p hp _ τN (vectorPositiveFunctional_normal N υ.vector))
    (cornerTrace_normal pM hpM _ τM (vectorPositiveFunctional_normal M υ.vector))
    (cornerTrace_one pM hpM τM hfM hpM0)
    (cornerTrace_tracial pM hpM τM υ.trace_mul_comm)
    (cornerTrace_faithful pM hpM τM hfM hpM0) ψ hψ (fun _ => rfl)
    (source_corner_factor υ hNM hfactor hdiff p hp hp0)
    (source_corner_diffuse hdiff p hp)
    (source_corner_irreducible υ hNM hirr p hp) x hx hδ hη

set_option maxHeartbeats 1600000 in
/-- Every nonzero source corner admits relative compression, with the
normalization expressed using the original ambient trace. -/
theorem exists_source_relative_small_corner
    (hfactor : ∀ c : N.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra, coordinateInclusion hNM a * c =
        c * coordinateInclusion hNM a) → ∃ z : ℂ, c = z • 1)
    (p : N.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0)
    {I : Type*} [Fintype I] (x : I → M.toStarSubalgebra)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≤ p ∧ q ≠ 0 ∧
      (υ.trace (coordinateInclusion hNM q)).re < η ∧
      ∀ i, ‖(vectorPositiveFunctional M υ.vector).toPreGNS
        (coordinateInclusion hNM q * x i * coordinateInclusion hNM q -
          (((υ.trace (coordinateInclusion hNM p)).re : ℂ)⁻¹ *
            υ.trace (coordinateInclusion hNM p * x i * coordinateInclusion hNM p)) •
              coordinateInclusion hNM q)‖ ^ 2 <
        δ * (υ.trace (coordinateInclusion hNM q)).re := by
  let φ := coordinateInclusion hNM
  let τM := vectorPositiveFunctional M υ.vector
  let pM := φ p
  have hpM : IsStarProjection pM := hp.map φ
  have hpM0 : pM ≠ 0 := fun h => hp0
    (Subtype.ext (congrArg (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H)) h))
  have hfM (a : M.toStarSubalgebra) (ha : τM (star a * a) = 0) : a = 0 := by
    apply υ.separating a
    exact inner_self_eq_zero.mp ((baseVector_inner_trace υ a a).trans ha)
  let ρM := cornerTrace pM hpM τM
  let ψ := sourceCornerHom φ p hp
  let y : I → Corner pM hpM := fun i => ⟨pM * x i * pM, compress_mem_corner hpM (x i)⟩
  let z : I → Corner pM hpM := fun i => y i - ρM (y i) • 1
  have hρ1 : ρM 1 = 1 := cornerTrace_one pM hpM τM hfM hpM0
  have hz (i : I) : ρM (z i) = 0 := by
    simp only [z, map_sub, map_smul, hρ1, smul_eq_mul, mul_one, sub_self]
  have htp : 0 < (τM pM).re := HochschildDiffuse.projection_trace_pos τM hfM hpM hpM0
  obtain ⟨q, hq, hq0, hqt, hqz⟩ := exists_source_corner_compression υ hNM
    hfactor hdiff hirr p hp hp0 z hz hδ (div_pos hη htp)
  have hqN := corner_projection_coe p hp hq
  have hqp := corner_projection_le p hp hq
  refine ⟨q, hqN, hqp, (fun h => hq0 (Subtype.ext h)), ?_, ?_⟩
  · exact original_trace_lt_of_corner pM hpM τM htp hqt
  · intro i
    have he := sourceCorner_compressed_eq hNM p hp q hq (x i) (ρM (y i))
    have hh := original_norm_bound_of_corner pM hpM τM htp (hqz i)
    change ((ψ q * z i * ψ q : Corner pM hpM) : M.toStarSubalgebra) = _ at he
    rw [he] at hh
    exact hh

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceIncrementalPatching
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incremental moment patches chosen inside a prescribed irreducible source. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open HochschildComparison HochschildPatching BoundedHochschild
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

set_option maxHeartbeats 1600000 in
include hfactor hdiff hirr in
/-- The mixed-word patch is an extension in the source algebra, even though
all coefficients and estimates belong to the larger ambient algebra. -/
theorem exists_source_incremental_patch {I : Type*} [Fintype I]
    (F : I → M.toStarSubalgebra)
    (hF : ∀ i, ‖F i‖ ≤ 1) (hFτ : ∀ i, υ.trace (F i) = 0)
    {K N : ℕ} (hK : 0 < K) {b : ℝ → ℝ} (v : PartialUnitary R.toStarSubalgebra)
    (hb : 0 ≤ b ((υ.trace (coordinateInclusion hRM v.support)).re))
    (hv : MomentBound F (vectorPositiveFunctional M υ.vector) (K := K) (N := N) b
      (SourcePartialUnitary.map (coordinateInclusion hRM) v))
    (hs : (υ.trace (coordinateInclusion hRM v.support)).re < 1)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ w : PartialUnitary R.toStarSubalgebra, ∃ h : v.support * w.support = 0,
      0 < (υ.trace (coordinateInclusion hRM w.support)).re ∧
      (υ.trace (coordinateInclusion hRM w.support)).re < η ∧
      ∀ a : BoundedWord I K N, admissibleTail a.2.val →
        ‖υ.trace (mixedEval F
          (SourcePartialUnitary.map (coordinateInclusion hRM) (v.orthogonalSum w h))
          a.1 a.2.val)‖ ≤ b ((υ.trace (coordinateInclusion hRM v.support)).re) +
          ((N : ℝ) * ε + (N : ℝ)^2 *
            (ε + 2 * b ((υ.trace (coordinateInclusion hRM v.support)).re) /
              (1 - (υ.trace (coordinateInclusion hRM v.support)).re))) *
            (υ.trace (coordinateInclusion hRM w.support)).re := by
  let φ := coordinateInclusion hRM
  let τ := vectorPositiveFunctional M υ.vector
  let V := SourcePartialUnitary.map φ v
  have hVs : V.support = φ v.support := SourcePartialUnitary.support_map φ v
  have hφp : φ (1 - v.support) = 1 - V.support := by rw [map_sub, map_one, hVs]
  have hpt : (τ (φ (1 - v.support))).re = 1 - (υ.trace (φ v.support)).re := by
    rw [map_sub, map_one]
    change (υ.trace (1 - φ v.support)).re = _
    rw [trace_sub, υ.trace_one, Complex.sub_re, Complex.one_re]
  have hp : 0 < (τ (1 - V.support)).re := by rw [← hφp, hpt]; linarith
  have hp0 : 1 - v.support ≠ 0 := by
    intro he
    have ht : 0 < (τ (φ (1 - v.support))).re := by rwa [hφp]
    rw [he, map_zero, map_zero, Complex.zero_re] at ht
    exact lt_irrefl _ ht
  obtain ⟨q, hq, hqv, hq0, hqt, hqsmall⟩ := exists_source_relative_small_corner
    υ hRM hfactor hdiff hirr (1 - v.support) v.support_proj.one_sub hp0
    (fun a : BoundedWord I K N => mixedEval F V a.1 a.2.val) (sq_pos_of_pos hε) hη
  obtain ⟨w, hw, hweak⟩ := exists_source_partial_unitary_weak_powers
    υ hRM hfactor hdiff q hq hq0 (linearCoeff F V (K := K) (N := N)) linearPower hε
  have horth : v.support * w.support = 0 := by
    rw [hw]
    have hh := (hq.le_iff_mul_eq_right v.support_proj.one_sub).mp hqv
    rw [sub_mul, one_mul, sub_eq_self] at hh
    exact hh
  let W := SourcePartialUnitary.map φ w
  have hWs : W.support = φ q := by rw [SourcePartialUnitary.support_map, hw]
  have horthM : V.support * W.support = 0 := by
    rw [hVs, SourcePartialUnitary.support_map, ← map_mul, horth, map_zero]
  have hwpos : 0 < (υ.trace (φ w.support)).re := by
    rw [hw]
    exact HochschildDiffuse.projection_trace_pos τ
      (fun a ha => υ.separating a (inner_self_eq_zero.mp ((baseVector_inner_trace υ a a).trans ha)))
      (hq.map φ) (fun h => hq0 (Subtype.ext (congrArg
        (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H)) h)))
  refine ⟨w, horth, hwpos, by rwa [hw], fun a ha => ?_⟩
  have hsmall : ∀ z : BoundedWord I K N,
      ‖τ.toPreGNS (W.support * mixedEval F V z.1 z.2.val * W.support -
        residualScalar τ V (mixedEval F V z.1 z.2.val) • W.support)‖ ≤
        ε * ‖τ.toPreGNS W.support‖ := by
    intro z
    rw [hWs]
    apply le_of_sq_le_sq _ (mul_nonneg hε.le (norm_nonneg _))
    rw [mul_pow, projection_gns_sq τ (hq.map φ)]
    apply le_of_lt
    change ‖τ.toPreGNS (φ q * mixedEval F V z.1 z.2.val * φ q -
      residualScalar τ V (mixedEval F V z.1 z.2.val) • φ q)‖ ^ 2 < ε ^ 2 * (τ (φ q)).re
    rw [residualScalar, ← hφp]
    exact hqsmall z
  have hlin := linear_trace_bound F τ υ.trace_mul_comm V W a.1 a.2.val a.2.property
    (ε * (τ W.support).re) (fun j => by
      rw [hWs]
      rw [show W.power (linearPower j) = φ (w.power (linearPower j)) from
        SourcePartialUnitary.power_map φ w (linearPower j)]
      change ‖υ.trace (linearCoeff F V j * φ (w.power (linearPower j)))‖ ≤
        ε * (υ.trace (φ q)).re
      exact (hweak j).le)
  have hquad := quadratic_trace_bound F τ υ.trace_mul_comm V W horthM hK hF hFτ
    hb hv hp ε hsmall a.1 a.2.val a.2.property ha
  have hh := mixedEval_patch_bound F τ V W horthM a.1 a.2.val a.2.property
    (mul_nonneg hε.le hwpos.le)
    (mul_nonneg (add_nonneg hε.le (div_nonneg (mul_nonneg (by norm_num) hb) hp.le)) hwpos.le)
    hlin hquad
  have hpt' : (τ (1 - V.support)).re = 1 - (υ.trace (φ v.support)).re := by
    rw [← hφp, hpt]
  rw [hpt'] at hh
  rw [SourcePartialUnitary.map_orthogonalSum]
  change ‖τ (mixedEval F (V.orthogonalSum W horthM) a.1 a.2.val)‖ ≤ _
  calc
    _ ≤ ‖τ (mixedEval F V a.1 a.2.val)‖ + (N : ℝ) * (ε * (τ W.support).re) +
        (N : ℝ)^2 * ((ε + 2 * b ((υ.trace (φ v.support)).re) /
          (1 - (υ.trace (φ v.support)).re)) * (τ W.support).re) := hh
    _ ≤ b ((υ.trace (φ v.support)).re) + (N : ℝ) * (ε * (τ W.support).re) +
        (N : ℝ)^2 * ((ε + 2 * b ((υ.trace (φ v.support)).re) /
          (1 - (υ.trace (φ v.support)).re)) * (τ W.support).re) :=
      add_le_add (add_le_add (hv a ha) le_rfl) le_rfl
    _ = _ := by
      rw [SourcePartialUnitary.support_map]
      change b ((υ.trace (φ v.support)).re) + (N : ℝ) * (ε * (υ.trace (φ w.support)).re) +
        (N : ℝ)^2 * ((ε + 2 * b ((υ.trace (φ v.support)).re) /
          (1 - (υ.trace (φ v.support)).re)) * (υ.trace (φ w.support)).re) = _
      ring

end KadisonSimilarity

end

end OAI
end


