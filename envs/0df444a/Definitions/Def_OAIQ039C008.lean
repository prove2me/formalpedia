-- Prove2me | Definitions.Def_OAIQ039C008
-- name    : OAIQ039C008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:12:50.354171+00:00
-- url     : https://prove2.me/theorems/57a61ae3-3c5c-4e3a-84dc-c64fb45cec63
-- title:
--   Definitions bundle OAIQ039C008 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 44 declarations of OpenAI's Lean: 14 definitions, 2 instances and 28 theorems. The definitions and types are `OAI.Kadison.DenseRationalStar.denseRationalStarNormedAlgebra`, `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections`, `OAI.Kadison.FactorCorner.IsFactor`, `OAI.Kadison.FactorCorner.supportSpace`, `OAI.Kadison.FejerTest.powerAverage`, `OAI.Kadison.FejerTest.testPolynomial`, `OAI.Kadison.FiniteTest.realTrace`, `OAI.Kadison.OperatorAmplification.matrixAlgebraDensityDecidableEq`, `OAI.Kadison.Polar.absToInitial`, `OAI.Kadison.Polar.initial`, `OAI.Kadison.Polar.initialMap`, `OAI.Kadison.Polar.leftSupport`, `OAI.Kadison.Polar.partialIsometry`, `OAI.Kadison.ProjectionChains.TraceCut`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_DecomposableAlgebra`, `Commutator_DenseRationalStar`, `Commutator_DiffuseProjection`, `Commutator_EquivariantBicommutant`, `Commutator_FactorCorner`, `Commutator_FejerTest`, `Commutator_FiniteTestPatching`, `Commutator_KaplanskyFull`, `Commutator_MainMatrix`, `Commutator_MatrixAlgebraDensity`, `Commutator_PolarDecomposition`, `Commutator_PolarSupport`, `Commutator_ProjectionChains`, `Commutator_ScalarField`, `Commutator_WeakOperatorAlgebra`.
--
--   **Imports.** It imports the published bundle `Def_UniformCommutator`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C023`, `OAIQ039C024`, `OAIQ039C025`, `OAIQ039C026`, `OAIQ039C029`, `OAIQ039C030` and `OAIQ039C031`; the statements `OAI.Kadison.AtomicFactor.exists_decomposition`, `OAI.Kadison.CornerPhase.exists_relative_corner_phase`, `OAI.Kadison.CornerSymmetrization.bound_small_projection`, `OAI.Kadison.CornerTransport.finite_small_corner_bound`, `OAI.Kadison.Decomposable.matrix_commutator_bound_of_countable_factor_fields`, `OAI.Kadison.Decomposable.matrix_commutator_bound_of_factor_fields`, `OAI.Kadison.GeneratedMatrixBicommutant.factor`, `OAI.Kadison.MatrixDiffuse.noMinimal_of_matrix_stages`, `OAI.Kadison.NormalRepresentation.finite_standard_compression_bound`, `OAI.Kadison.NormalRepresentation.separable_traced_factor_bound`, `OAI.Kadison.PartialIsometryOrder.finite_factor_unitary_subequivalence`, `OAI.Kadison.PartialIsometryOrder.maximal_family_spans_of_full_support`, `OAI.Kadison.PartialIsometryOrder.nonfinite_two_isometries`, `OAI.Kadison.TraceDimension.faithful`, `OAI.Kadison.uniform_commutator_atomic_factor`, `OAI.Kadison.uniform_commutator_nonfinite_factor` and `OAI.Kadison.uniform_commutator_separable_factor`; the proofs of `OAI_Kadison_Decomposable_uniform_commutator_in_central_spectral_model`, `OAI_Kadison_Decomposable_uniform_commutator_in_factor_model`, `OAI.Kadison.EquivariantBicommutant.bicommutant_range`, `OAI.Kadison.IntertwinerCompression.pullback_matrix_commutator_norm_le`, `OAI.Kadison.uniform_commutator_nonfinite_factor` and `OAI.Kadison.uniform_commutator_of_isometries`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_UniformCommutator

section
-- module Solutions.OAIQ039_CM.Commutator_DecomposableAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma sub_measurable (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ) (ξ : H) :
    AEStronglyMeasurable (fun a => (T a-S a) ξ) μ := (hT ξ).sub (hS ξ)

lemma sub_bound (T S : Ω → H →L[ℂ] H) {b c : ℝ}
    (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖ ≤ c) :
    ∀ᵐ a ∂μ,‖T a-S a‖≤b+c := by
  filter_upwards [hb,hc] with a ha hb
  exact (norm_sub_le _ _).trans (add_le_add ha hb)

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WeakOperatorAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

open Filter

namespace Kadison.WeakOperatorLimit

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {l : Filter ι} [l.NeBot] {T : ι → H →L[ℂ] H} {W : H →L[ℂ] H}

variable (hlim : ∀ x y, Tendsto (fun i => inner ℂ (T i x) y) l (𝓝 (inner ℂ (W x) y)))

include hlim

omit [CompleteSpace H] in
lemma right_eq (A B : H →L[ℂ] H) (h : ∀ᶠ i in l, T i*A=B) : W*A=B := by
  ext x
  apply ext_inner_right ℂ
  intro y
  exact tendsto_nhds_unique (hlim (A x) y) (tendsto_const_nhds.congr' (by
    filter_upwards [h] with i hi
    exact congrArg (fun U : H →L[ℂ] H => inner ℂ (U x) y) hi.symm))

end Kadison.WeakOperatorLimit

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter ContinuousLinearMapWOT

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.ProjectionChains

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) →ₚ[ℂ] ℂ)

variable (e : H →L[ℂ] H) (t : ℝ)

abbrev TraceCut := {p : H →L[ℂ] H // p∈M ∧ IsStarProjection p ∧ p≤e ∧ (τ p).re≤t}

end Kadison.ProjectionChains

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DiffuseProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.DiffuseProjection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def HasNoMinimalProjections (M : VonNeumannAlgebra H) : Prop :=
  ∀ p∈M, IsStarProjection p → p≠0 →
    ∃ q∈M, IsStarProjection q ∧ q≠0 ∧ q≠p ∧ q≤p

variable (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) →ₚ[ℂ] ℂ)

variable (hM : HasNoMinimalProjections M)

include hM

lemma exists_half {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p) (hpn : p≠0) :
    ∃ q∈M, IsStarProjection q ∧ q≠0 ∧ q≤p ∧ (τ q).re≤(τ p).re/2 := by
  obtain ⟨q,hqM,hq,hqn,hqp,hqle⟩ := hM p hpM hp hpn
  by_cases hsmall : (τ q).re≤(τ p).re/2
  · exact ⟨q,hqM,hq,hqn,hqle,hsmall⟩
  · have hr : IsStarProjection (p-q) := hq.sub_of_mul_eq_left hp
      ((hq.le_iff_mul_eq_left hp).mp hqle)
    refine ⟨p-q,M.sub_mem hpM hqM,hr,?_,?_,?_⟩
    · exact fun h => hqp (sub_eq_zero.mp h).symm
    · exact sub_le_self p hq.nonneg
    · rw [map_sub,Complex.sub_re]
      linarith

lemma exists_geometric {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p) (hpn : p≠0)
    (n : ℕ) : ∃ q∈M, IsStarProjection q ∧ q≠0 ∧ q≤p ∧ (τ q).re≤(1/2:ℝ)^n*(τ p).re := by
  induction n with
  | zero => exact ⟨p,hpM,hp,hpn,le_rfl,by simp⟩
  | succ n ih =>
    obtain ⟨q,hqM,hq,hqn,hqle,hqtrace⟩ := ih
    obtain ⟨r,hrM,hr,hrn,hrle,hrtrace⟩ := exists_half M τ hM hqM hq hqn
    refine ⟨r,hrM,hr,hrn,hrle.trans hqle,?_⟩
    rw [pow_succ]
    nlinarith

theorem exists_small {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p) (hpn : p≠0)
    {ε : ℝ} (hε : 0<ε) : ∃ q∈M, IsStarProjection q ∧ q≠0 ∧ q≤p ∧ (τ q).re<ε := by
  have hlim : Tendsto (fun n : ℕ => (1/2:ℝ)^n*(τ p).re) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num)).mul_const (τ p).re
  obtain ⟨n,hn⟩ := (hlim.eventually_lt_const hε).exists
  obtain ⟨q,hqM,hq,hqn,hqle,hqtrace⟩ := exists_geometric M τ hM hpM hp hpn n
  exact ⟨q,hqM,hq,hqn,hqle,hqtrace.trans_lt hn⟩

end Kadison.DiffuseProjection

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PolarDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma norm_abs_apply (T : H →L[ℂ] H) (x : H) : ‖CFC.abs T x‖=‖T x‖ := by
  have hs : star (CFC.abs T)=CFC.abs T := (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg T)).star_eq
  have he : inner ℂ (CFC.abs T x) (CFC.abs T x)=inner ℂ (T x) (T x) := by
    rw [←ContinuousLinearMap.adjoint_inner_right,←ContinuousLinearMap.star_eq_adjoint,hs]
    change inner ℂ x ((CFC.abs T*CFC.abs T) x)=_
    rw [CFC.abs_mul_abs,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  have hn : ‖CFC.abs T x‖^2=‖T x‖^2 := by
    rw [@norm_sq_eq_re_inner ℂ H _ _,@norm_sq_eq_re_inner ℂ H _ _]
    exact congrArg RCLike.re he
  nlinarith [norm_nonneg (CFC.abs T x),norm_nonneg (T x)]

def initial (T : H →L[ℂ] H) : Submodule ℂ H :=
  (LinearMap.range (CFC.abs T).toLinearMap).topologicalClosure

instance instCompleteSpaceSubtypeMemSubmoduleComplexInitial (T : H →L[ℂ] H) : CompleteSpace (initial T) :=
  (LinearMap.range (CFC.abs T).toLinearMap).isClosed_topologicalClosure.completeSpace_coe

def absToInitial (T : H →L[ℂ] H) : H →ₗ[ℂ] initial T :=
  (CFC.abs T).toLinearMap.codRestrict (initial T) (fun x =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x))

lemma absToInitial_dense (T : H →L[ℂ] H) : DenseRange (absToInitial T) := by
  let inc : LinearMap.range (CFC.abs T).toLinearMap → initial T :=
    fun x => ⟨x.val,Submodule.le_topologicalClosure _ x.property⟩
  have hi : DenseRange inc := by
    change DenseRange (Set.inclusion (Submodule.le_topologicalClosure _))
    apply (denseRange_inclusion_iff _).2
    exact fun _ h => h
  have hs : Function.Surjective (CFC.abs T).toLinearMap.rangeRestrict := by
    rintro ⟨y,x,rfl⟩
    exact ⟨x,rfl⟩
  exact hi.comp hs.denseRange (continuous_inclusion (Submodule.le_topologicalClosure _))

def initialMap (T : H →L[ℂ] H) : initial T →L[ℂ] H :=
  T.toLinearMap.extendOfNorm (absToInitial T)

lemma initialMap_abs (T : H →L[ℂ] H) (x : H) :
    initialMap T (absToInitial T x)=T x := by
  apply LinearMap.extendOfNorm_eq (absToInitial_dense T)
  refine ⟨1,fun x => ?_⟩
  change ‖T x‖≤1*‖CFC.abs T x‖
  rw [one_mul,norm_abs_apply]

lemma initialMap_norm (T : H →L[ℂ] H) (x : initial T) : ‖initialMap T x‖=‖x‖ := by
  refine (absToInitial_dense T).induction_on x
    (isClosed_eq (initialMap T).continuous.norm continuous_norm) ?_
  intro y
  rw [initialMap_abs]
  exact (norm_abs_apply T y).symm

def partialIsometry (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (initialMap T).comp (initial T).orthogonalProjectionOnto

lemma partialIsometry_mem (T : H →L[ℂ] H) (x : initial T) :
    partialIsometry T x=initialMap T x := by
  exact congrArg (initialMap T)
    (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x)

lemma factorization (T : H →L[ℂ] H) : partialIsometry T*CFC.abs T=T := by
  ext x
  change partialIsometry T (absToInitial T x)=T x
  rw [partialIsometry_mem,initialMap_abs]

lemma initialMap_adjoint_comp (T : H →L[ℂ] H) :
    (initialMap T).adjoint.comp (initialMap T)=1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (initialMap_norm T)

lemma partialIsometry_initial (T : H →L[ℂ] H) :
    star (partialIsometry T)*partialIsometry T=(initial T).starProjection := by
  change (partialIsometry T).adjoint.comp (partialIsometry T)=_
  rw [partialIsometry,ContinuousLinearMap.adjoint_comp,Submodule.adjoint_orthogonalProjectionOnto,
    ContinuousLinearMap.comp_assoc,←ContinuousLinearMap.comp_assoc (initialMap T).adjoint,
    initialMap_adjoint_comp]
  simp only [ContinuousLinearMap.one_def,ContinuousLinearMap.id_comp]
  rfl

lemma partialIsometry_mul_initial (T : H →L[ℂ] H) :
    partialIsometry T*(initial T).starProjection=partialIsometry T := by
  ext x
  change initialMap T ((initial T).orthogonalProjectionOnto ((initial T).starProjection x))=_
  rw [Submodule.starProjection_apply,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  rfl

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PolarSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def leftSupport (T : H →L[ℂ] H) : H →L[ℂ] H :=
  partialIsometry T*star (partialIsometry T)

lemma partialIsometry_triple (T : H →L[ℂ] H) :
    partialIsometry T*star (partialIsometry T)*partialIsometry T=partialIsometry T := by
  rw [mul_assoc,partialIsometry_initial,partialIsometry_mul_initial]

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FactorCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.FactorCorner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def supportSpace (M : VonNeumannAlgebra H) (e : H →L[ℂ] H) : Submodule ℂ H :=
  (Submodule.span ℂ {x | ∃ a∈M, ∃ ξ : H, a (e ξ)=x}).topologicalClosure

instance instCompleteSpaceSubtypeMemSubmoduleComplexSupportSpace (M : VonNeumannAlgebra H) (e : H →L[ℂ] H) : CompleteSpace (supportSpace M e) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

lemma generator_mem (M : VonNeumannAlgebra H) (e : H →L[ℂ] H)
    {a : H →L[ℂ] H} (ha : a∈M) (ξ : H) : a (e ξ)∈supportSpace M e :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a,ha,ξ,rfl⟩)

lemma supportSpace_invariant (M : VonNeumannAlgebra H) (e B : H →L[ℂ] H)
    (hB : ∀ a∈M, ∀ ξ : H, B (a (e ξ))∈supportSpace M e) :
    ∀ x∈supportSpace M e, B x∈supportSpace M e := by
  intro x hx
  apply closure_minimal (t := {x | B x∈supportSpace M e}) ?_
    ((Submodule.isClosed_topologicalClosure _).preimage B.continuous) hx
  exact (Submodule.span_le.mpr (by rintro y ⟨a,ha,ξ,rfl⟩; exact hB a ha ξ) :
    Submodule.span ℂ {x | ∃ a∈M, ∃ ξ : H, a (e ξ)=x} ≤ (supportSpace M e).comap B.toLinearMap)

lemma invariant_of_mem (M : VonNeumannAlgebra H) (e : H →L[ℂ] H)
    {B : H →L[ℂ] H} (hB : B∈M) :
    ∀ x∈supportSpace M e, B x∈supportSpace M e := by
  apply supportSpace_invariant
  intro a ha ξ
  exact generator_mem M e (M.mul_mem hB ha) ξ

lemma invariant_of_commutant (M : VonNeumannAlgebra H) {e B : H →L[ℂ] H}
    (he : e∈M) (hB : B∈Set.centralizer (M : Set (H →L[ℂ] H))) :
    ∀ x∈supportSpace M e, B x∈supportSpace M e := by
  apply supportSpace_invariant
  intro a ha ξ
  have hba : B*a=a*B := (hB a ha).symm
  have hbe : B*e=e*B := (hB e he).symm
  change B (a (e ξ))∈supportSpace M e
  rw [show B (a (e ξ))=a (B (e ξ)) from congrArg (fun T : H →L[ℂ] H => T (e ξ)) hba,
    show B (e ξ)=e (B ξ) from congrArg (fun T : H →L[ℂ] H => T ξ) hbe]
  exact generator_mem M e ha (B ξ)

def IsFactor (M : VonNeumannAlgebra H) : Prop :=
  ∀ z∈M, z∈Set.centralizer (M : Set (H →L[ℂ] H)) → ∃ c : ℂ, z=c • (1 : H →L[ℂ] H)

end Kadison.FactorCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixAlgebraDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι]

local instance matrixAlgebraDensityDecidableEq : DecidableEq ι := Classical.decEq ι

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.Kaplansky

open OperatorAmplification

local instance instDecidableEqFinOfNatNat_solutions_r76dd7d_1 : DecidableEq (Fin 2) := Classical.decEq (Fin 2)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma star_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) {a : H →L[ℂ] H}
    (ha : a∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    star a∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  let B := StarSubalgebra.centralizer ℂ ((StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H))) : Set (H →L[ℂ] H))
  have he : (B : Set (H →L[ℂ] H))=Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
    simp only [B,StarSubalgebra.coe_centralizer_centralizer,StarMemClass.star_coe_eq,Set.union_self]
  have hm : a∈B := by
    change a∈(B : Set (H →L[ℂ] H))
    rw [he]
    exact ha
  rw [←he]
  exact B.star_mem' hm

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DenseRationalStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

namespace Kadison.DenseRationalStar

variable (A : Type*) [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]

local instance denseRationalStarNormedAlgebra : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℂ A

local instance denseRationalStarStarModule : StarModule ℚ A where
  star_smul r a := by
    change star ((r:ℂ) • a)=((star r:ℚ):ℂ) • star a
    simp

end Kadison.DenseRationalStar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EquivariantBicommutant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.EquivariantBicommutant

variable {A B : Type*} [Monoid A] [Monoid B]

lemma mem_centralizer_image (e : A ≃* B) (s : Set A) (x : A) :
    e x∈Set.centralizer (e '' s) ↔ x∈Set.centralizer s := by
  constructor
  · intro h y hy
    apply e.injective
    simpa only [map_mul] using h (e y) ⟨y,hy,rfl⟩
  · rintro h _ ⟨y,hy,rfl⟩
    simpa only [map_mul] using congrArg e (h y hy)

lemma centralizer_image (e : A ≃* B) (s : Set A) :
    Set.centralizer (e '' s)=e '' Set.centralizer s := by
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    apply (mem_centralizer_image e s (e.symm x)).mp
    simpa only [e.apply_symm_apply] using hx
  · rintro ⟨y,hy,rfl⟩
    exact (mem_centralizer_image e s y).mpr hy

lemma bicommutant_image (e : A ≃* B) (s : Set A) :
    Set.centralizer (Set.centralizer (e '' s))=e '' Set.centralizer (Set.centralizer s) := by
  rw [centralizer_image,centralizer_image]

end Kadison.EquivariantBicommutant

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FejerTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.FejerTest

variable {A : Type*} [CStarAlgebra A]

def powerAverage (w : A) (m : ℕ) : A :=
  ((m : ℂ)⁻¹) • ∑ i ∈ Finset.range m, w^i

def testPolynomial (w : A) (m : ℕ) : A :=
  star (powerAverage w m) * powerAverage w m - ((m : ℂ)⁻¹) • (1 : A)

end Kadison.FejerTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTestPatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.FiniteTest

section ActualGNS

open scoped ComplexOrder

open UniformSpace

variable {A I J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype I] [LinearOrder I] [Fintype J]

variable (τ : A →ₚ[ℂ] ℂ)

def realTrace : A →ₗ[ℝ] ℝ :=
  Complex.reCLM.toLinearMap.comp (τ.toLinearMap.restrictScalars ℝ)

end ActualGNS

end Kadison.FiniteTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MainMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

universe u

open scoped InnerProductSpace BigOperators ComplexOrder

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
@[simp] lemma matrixOperator_apply (h : ℕ) (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K))
    (x : PiLp 2 (fun _ : Fin h => K)) (i : Fin h) : matrixOperator h X x i=∑ j,X i j (x j) := by
  simp [matrixOperator]

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ScalarField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma smul_measurable (z : ℂ) (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ) :
    ∀ ξ,AEStronglyMeasurable (fun a => (z • T a) ξ) μ := fun ξ => (hm ξ).const_smul z

lemma smul_field_bound (z : ℂ) (T : Ω → H →L[ℂ] H)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) : ∀ᵐ a ∂μ,‖z • T a‖≤‖z‖*b := by
  filter_upwards [hb] with a ha
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left ha (norm_nonneg z)

end Kadison.Decomposable

end

end
end

end OAI
end


