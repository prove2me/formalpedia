-- Prove2me | Definitions.Def_OAIQ039C005
-- name    : OAIQ039C005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:11:38.50985+00:00
-- url     : https://prove2.me/theorems/d02a1d43-a426-452a-8326-3e7875fbfdc2
-- title:
--   Definitions bundle OAIQ039C005 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 13 definitions, 2 instances and 12 theorems. The definitions and types are `OAI.Kadison.CyclicSpatial.delta`, `OAI.Kadison.CyclicSpatial.instNormedAddCommGroupContinuousLinearMapComplexIdSubtypeMemSubmodule_solutions`, `OAI.Kadison.CyclicSpatial.instNormedAddCommGroupContinuousLinearMapComplexIdSubtypeMemSubmodule_solutions_1`, `OAI.Kadison.CyclicSpatial.instNormedSpaceComplexContinuousLinearMapIdSubtypeMemSubmodule_solutions_1`, `OAI.Kadison.CyclicSpectral.complexify`, `OAI.Kadison.CyclicSpectral.gelfandRepresentation`, `OAI.Kadison.CyclicSpectral.measure`, `OAI.Kadison.CyclicSpectral.normSqFunction`, `OAI.Kadison.CyclicSpectral.orbitMap`, `OAI.Kadison.CyclicSpectral.spectrumSpace`, `OAI.Kadison.CyclicSpectral.vectorFunctional`, `OAI.Kadison.DihedralCorner.wave`, `OAI.Kadison.ReducingRepresentation.restrict`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CyclicGelfandModel`, `Commutator_CyclicImplementationUnconditional`, `Commutator_CyclicSpatialImplementation`, `Commutator_CyclicSpectralMeasure`, `Commutator_CyclicSpectralNorm`, `Commutator_CyclicSpectralUnitary`, `Commutator_DecomposableOperator`, `Commutator_HankelAlgebra`, `Commutator_ReducingRepresentation`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C022`, `OAIQ039C023` and `OAIQ039C030`; the statements `OAI.Kadison.CyclicSpatial.exists_cyclic_intertwiner` and `OAI_Kadison_Decomposable_uniform_commutator_in_factor_model`; the proofs of `OAI.Kadison.CyclicSpatial.exists_embedded_cyclic_intertwiner` and `OAI_Kadison_uniform_commutator_of_two_isometries`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicSpectralMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory

open scoped ComplexOrder InnerProductSpace CompactlySupported

namespace Kadison.CyclicSpectral

variable {Ω H : Type*} [TopologicalSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def complexify (f : C_c(Ω,ℝ)) : C(Ω,ℂ) :=
  ⟨fun x => (f x:ℂ),Complex.continuous_ofReal.comp f.continuous⟩

lemma complexify_add (f g : C_c(Ω,ℝ)) : complexify (f+g)=complexify f+complexify g := by
  ext x
  simp [complexify]

lemma complexify_smul (r : ℝ) (f : C_c(Ω,ℝ)) : complexify (r•f)=(r:ℂ)•complexify f := by
  ext x
  simp [complexify]

lemma complexify_sub (f g : C_c(Ω,ℝ)) : complexify (f-g)=complexify f-complexify g := by
  ext x
  simp [complexify]

lemma complexify_nonneg {f : C_c(Ω,ℝ)} (hf : 0≤f) : 0 ≤ complexify f := by
  intro x
  exact Complex.zero_le_real.mpr (hf x)

def vectorFunctional (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : C_c(Ω,ℝ) →ₚ[ℝ] ℝ where
  toFun f := (inner ℂ ξ (ρ (complexify f) ξ)).re
  map_add' f g := by simp [complexify_add]
  map_smul' r f := by
    rw [complexify_smul,map_smul]
    simp
  monotone' := by
    intro f g hfg
    have hp : 0≤ρ (complexify (g-f)) := map_nonneg ρ (complexify_nonneg (sub_nonneg.mpr hfg))
    have hi := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hp).re_inner_nonneg_right ξ
    simpa [complexify_sub,inner_sub_right,sub_nonneg] using hi

variable [T2Space Ω] [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]

def measure (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : Measure Ω :=
  RealRMK.rieszMeasure (vectorFunctional ρ ξ)

instance measure_regular (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    (measure ρ ξ).Regular := inferInstanceAs (RealRMK.rieszMeasure (vectorFunctional ρ ξ)).Regular

instance measure_finite (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    IsFiniteMeasure (measure ρ ξ) := inferInstance

lemma integral_real (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (f : C_c(Ω,ℝ)) :
    ∫ x,f x ∂measure ρ ξ=(inner ℂ ξ (ρ (complexify f) ξ)).re :=
  RealRMK.integral_rieszMeasure (vectorFunctional ρ ξ) f

end Kadison.CyclicSpectral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicSpectralNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory

open scoped ComplexOrder InnerProductSpace CompactlySupported ComplexConjugate

namespace Kadison.CyclicSpectral

variable {Ω H : Type*} [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def normSqFunction (f : C(Ω,ℂ)) : C_c(Ω,ℝ) :=
  CompactlySupportedContinuousMap.continuousMapEquiv
    ⟨fun x => Complex.normSq (f x),Complex.continuous_normSq.comp f.continuous⟩

omit [T2Space Ω] [MeasurableSpace Ω] [BorelSpace Ω] in
lemma complexify_normSq (f : C(Ω,ℂ)) : complexify (normSqFunction f)=star f*f := by
  ext x
  change (Complex.normSq (f x):ℂ)=star (f x)*f x
  simp [Complex.normSq_eq_conj_mul_self]

lemma representation_norm_integral (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (f : C(Ω,ℂ)) :
    ‖ρ f ξ‖^2=∫ x,Complex.normSq (f x) ∂measure ρ ξ := by
  have hi := integral_real ρ ξ (normSqFunction f)
  rw [complexify_normSq,map_mul,map_star] at hi
  change (∫ x,Complex.normSq (f x) ∂measure ρ ξ)=
    (inner ℂ ξ ((ρ f).adjoint (ρ f ξ))).re at hi
  rw [ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K] at hi
  change (∫ x,Complex.normSq (f x) ∂measure ρ ξ)=
    ((Complex.ofReal ‖ρ f ξ‖)^2).re at hi
  rw [←Complex.ofReal_pow, Complex.ofReal_re] at hi
  exact hi.symm

end Kadison.CyclicSpectral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DecomposableOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology ComplexOrder InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma measurable_apply_simple (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ) (f : SimpleFunc Ω H) :
    AEStronglyMeasurable (fun a => T a (f a)) μ := by
  classical
  induction f with
  | const c => exact hm c
  | @pcw f g s hs hf hg =>
    convert AEStronglyMeasurable.piecewise hs hf.restrict hg.restrict using 1
    all_goals try with_reducible_and_instances rfl
    funext a
    change T a (if a∈s then f a else g a)=(if a∈s then T a (f a) else T a (g a))
    split_ifs <;> rfl

lemma measurable_apply (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {f : Ω → H} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun a => T a (f a)) μ := by
  obtain ⟨s,hs⟩ := hf.stronglyMeasurable_mk
  apply aestronglyMeasurable_of_tendsto_ae atTop (fun n => measurable_apply_simple μ T hm (s n))
  filter_upwards [hf.ae_eq_mk] with a ha
  rw [ha]
  exact (T a).continuous.continuousAt.tendsto.comp (hs a)

lemma memLp_apply (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (f : Lp H 2 μ) :
    MemLp (fun a => T a (f a)) 2 μ := by
  apply (Lp.memLp f).of_le_mul (measurable_apply μ T hm (Lp.aestronglyMeasurable f))
  filter_upwards [hb] with a ha
  exact ((T a).le_opNorm (f a)).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicSpectralUnitary
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

namespace Kadison.CyclicSpectral

variable {Ω H : Type*} [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def orbitMap (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : C(Ω,ℂ) →ₗ[ℂ] H where
  toFun f := ρ f ξ
  map_add' f g := by simp
  map_smul' z f := by simp

end Kadison.CyclicSpectral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicGelfandModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory

open scoped Topology

namespace Kadison.CyclicSpectral

variable {A H : Type*} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev spectrumSpace := WeakDual.characterSpace ℂ A

variable [MeasurableSpace (spectrumSpace (A:=A))] [BorelSpace (spectrumSpace (A:=A))]

def gelfandRepresentation (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    C(spectrumSpace (A:=A),ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  ρ.comp (gelfandStarTransform A).symm.toStarAlgHom

end Kadison.CyclicSpectral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ReducingRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.ReducingRepresentation

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H), x∈K → σ a x∈K)

def restrict : A →⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun a := (σ a).restrict (hinv a)
  map_one' := by ext x; change σ 1 (x:H)=x; simp
  map_mul' a b := by ext x; change σ (a*b) (x:H)=σ a (σ b x); rw [map_mul]; rfl
  map_add' a b := by ext x; change σ (a+b) (x:H)=σ a x+σ b x; rw [map_add]; rfl
  map_zero' := by ext x; change σ 0 (x:H)=0; simp
  commutes' c := by
    ext x
    change σ (algebraMap ℂ A c) (x:H)=c • (x:H)
    simp only [Algebra.algebraMap_eq_smul_one,map_smul,map_one,smul_apply,one_apply_eq_self]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y:H) (σ (star a) (x:H)) = inner ℂ y (((σ a).restrict (hinv a)).adjoint x)
    rw [adjoint_inner_right]
    change inner ℂ (y:H) (σ (star a) (x:H))=inner ℂ (σ a (y:H)) (x:H)
    rw [map_star,star_eq_adjoint,adjoint_inner_right]

@[simp] lemma restrict_apply (a : A) (x : K) :
    (restrict σ K hinv a x:H)=σ a x := rfl

end Kadison.ReducingRepresentation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicSpatialImplementation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.CyclicSpatial

open ReducingRepresentation

variable {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι]

local instance instDecidableEq_solutions_re02800_1 : DecidableEq ι := Classical.decEq ι
variable (lam : A →⋆ₐ[ℂ] (H →L[ℂ] H))
  (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H), x∈K → lam a x∈K)

local instance instNormedAddCommGroupContinuousLinearMapComplexIdSubtypeMemSubmodule_solutions : NormedAddCommGroup (K →L[ℂ] H) := ContinuousLinearMap.toNormedAddCommGroup

local instance instNormedSpaceComplexContinuousLinearMapIdSubtypeMemSubmodule_solutions_re02800_1 : NormedSpace ℂ (K →L[ℂ] H) := ContinuousLinearMap.toNormedSpace
def delta (G : K →L[ℂ] H) : A →L[ℂ] (K →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun a := G.comp (restrict lam K hinv a)-(lam a).comp G
      map_add' a b := by simp [map_add,ContinuousLinearMap.comp_add,
        ContinuousLinearMap.add_comp,add_sub_add_comm]
      map_smul' z a := by simp [map_smul,ContinuousLinearMap.smul_comp,smul_sub] }
    (2*‖G‖) (by
      intro a
      change ‖G.comp (restrict lam K hinv a)-(lam a).comp G‖≤(2*‖G‖)*‖a‖
      calc
        _ ≤ ‖G.comp (restrict lam K hinv a)‖+‖(lam a).comp G‖ := norm_sub_le _ _
        _ ≤ ‖G‖*‖restrict lam K hinv a‖+‖lam a‖*‖G‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
        _ ≤ ‖G‖*‖a‖+‖a‖*‖G‖ := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le (restrict lam K hinv) a) (norm_nonneg G))
            (mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le lam a) (norm_nonneg G))
        _ = (2*‖G‖)*‖a‖ := by ring)

@[simp] lemma delta_apply (G : K →L[ℂ] H) (a : A) :
    delta lam K hinv G a=G.comp (restrict lam K hinv a)-(lam a).comp G := rfl

end Kadison.CyclicSpatial

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicImplementationUnconditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.CyclicSpatial

open ReducingRepresentation

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (lam : A →⋆ₐ[ℂ] (H →L[ℂ] H))
  (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H), x∈K → lam a x∈K)

local instance instNormedAddCommGroupContinuousLinearMapComplexIdSubtypeMemSubmodule_solutions_1 : NormedAddCommGroup (K →L[ℂ] H) := ContinuousLinearMap.toNormedAddCommGroup

local instance instNormedSpaceComplexContinuousLinearMapIdSubtypeMemSubmodule_solutions_1 : NormedSpace ℂ (K →L[ℂ] H) := ContinuousLinearMap.toNormedSpace

end Kadison.CyclicSpatial

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HankelAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.DihedralCorner

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

variable (u d : unitary A)

def wave (n : ℤ) : A := (u^n : unitary A)

end Kadison.DihedralCorner

end

end
end

end OAI
end


