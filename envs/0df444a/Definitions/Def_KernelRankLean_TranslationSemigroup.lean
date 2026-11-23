-- Prove2me | Definitions.Def_KernelRankLean_TranslationSemigroup
-- name    : KernelRankLean_TranslationSemigroup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T02:04:34.61554+00:00
-- url     : https://prove2.me/theorems/a9bbf634-92a7-4bef-9f7f-d5ac9c982d12
-- title:
--   Translation Semigroup
-- statement:
--   Definitions and structural lemmas for Translation Semigroup, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/TranslationSemigroup.lean

import Definitions.Def_ImportCompatibility_Normability
import Definitions.Def_KernelRankLean_Translations
import Definitions.Def_KernelRankLean_Semigroup
import Definitions.Def_KernelRankLean_Complexification
import Theorems.Thm_KernelRank_IsSumOfProducts_comp
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_isNormableSpace_of_finiteDimensional
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero


set_option autoImplicit true
open NNReal
namespace KernelRank
variable {𝕜 : Type*} [Field 𝕜]
noncomputable def shift (t : ℝ≥0) : (ℝ≥0 → 𝕜) →ₗ[𝕜] (ℝ≥0 → 𝕜) :=
  LinearMap.funLeft 𝕜 𝕜 (· + t)
lemma shift_apply (t : ℝ≥0) (g : ℝ≥0 → 𝕜) (u : ℝ≥0) : shift t g u = g (u + t) := rfl
variable (φ : ℝ → 𝕜)
lemma translate_mem_translateSpan (s : ℝ≥0) :
    (fun u : ℝ≥0 => φ (u + s)) ∈ translateSpan φ :=
  Submodule.subset_span ⟨s, rfl⟩
lemma shift_mem_translateSpan (t : ℝ≥0) {g : ℝ≥0 → 𝕜} (hg : g ∈ translateSpan φ) :
    shift t g ∈ translateSpan φ := by
  have : translateSpan φ ≤ (translateSpan φ).comap (shift t) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨s, rfl⟩
    refine Submodule.subset_span ⟨s + t, funext fun u => ?_⟩
    simp only [shift_apply, NNReal.coe_add]
    congr 1
    ring
  exact this hg
noncomputable def shiftW (t : ℝ≥0) : translateSpan φ →ₗ[𝕜] translateSpan φ :=
  (shift t).restrict fun _ hg => shift_mem_translateSpan φ t hg
noncomputable def initialProfile : translateSpan φ := ⟨_, translate_mem_translateSpan φ 0⟩
section Complex
variable (ψ : ℝ → ℂ) [FiniteDimensional ℂ (translateSpan ψ)]
noncomputable abbrev translateNormedAddCommGroup : NormedAddCommGroup (translateSpan ψ) := by
  let : IsNormableSpace ℂ (translateSpan ψ) := isNormableSpace_of_finiteDimensional
  let : SeminormedAddCommGroup (translateSpan ψ) :=
    IsNormableSpace.toSeminormedAddCommGroup ℂ _
  exact NormedAddCommGroup.ofSeparation fun g hg =>
    (Metric.inseparable_iff.mpr (by simpa only [dist_zero_right] using hg)).eq
noncomputable abbrev translateNormedSpace :
    letI := translateNormedAddCommGroup ψ
    NormedSpace ℂ (translateSpan ψ) := by
  let : IsNormableSpace ℂ (translateSpan ψ) := isNormableSpace_of_finiteDimensional
  exact IsNormableSpace.toNormedSpace ℂ _
noncomputable abbrev translateUniformSpace : UniformSpace (translateSpan ψ) :=
  (translateNormedAddCommGroup ψ).toUniformSpace
attribute [local instance] translateNormedAddCommGroup translateNormedSpace translateUniformSpace
noncomputable abbrev translateCompleteSpace :
    letI := translateNormedAddCommGroup ψ
    letI := translateNormedSpace ψ
    CompleteSpace (translateSpan ψ) := FiniteDimensional.complete ℂ _
attribute [local instance] translateCompleteSpace
noncomputable def shiftCLM (t : ℝ) : translateSpan ψ →L[ℂ] translateSpan ψ :=
  (shiftW ψ t.toNNReal).toContinuousLinearMap
noncomputable def evalW (u : ℝ≥0) : translateSpan ψ →L[ℂ] ℂ :=
  ((LinearMap.proj u).comp (translateSpan ψ).subtype).toContinuousLinearMap
end Complex
end KernelRank


