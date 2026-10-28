-- Prove2me | Definitions.Def_OAIQ068A010
-- name    : OAIQ068A010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:40:37.524391+00:00
-- url     : https://prove2.me/theorems/208466d8-5ca6-4755-8a17-9dbc770803c8
-- title:
--   Definitions bundle OAIQ068A010 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 61 declarations of OpenAI's Lean: 29 definitions, 4 instances and 28 theorems. The definitions and types are `OAI.PiExponentJets.W22.HomogeneousPrimeStep`, `OAI.PiExponentJets.W22.MinimalParentsBelow`, `OAI.PiExponentJets.W22.actualLocalLength`, `OAI.PiExponentJets.W22.cyclicFactorEquiv`, `OAI.PiExponentJets.W22.dehomogenize`, `OAI.PiExponentJets.W22.globalParentCutSum`, `OAI.PiExponentJets.W22.homogenize`, `OAI.PiExponentJets.W22.localPrimeTowerEquiv`, `OAI.PiExponentJets.W22.localizedCyclicFactorEquiv`, `OAI.PiExponentJets.W22.localizedMinimalPrimesEquiv`, `OAI.PiExponentJets.W22.parameterCombination`, `OAI.PiExponentJets.W22.primeLocalizedCyclicFactorEquiv`, `OAI.PiExponentJets.W22.subquotientEquivImage`, `OAI.PiExponentJets.W24.polynomialPrefix`, `OAI.PiExponentJets.W24.powerPrefixPolynomial`, `OAI.PiExponentJets.W24.quotientDegreeFiltration`, `OAI.PiExponentJets.W24.quotientPrimeResidueAlgEquiv`, `OAI.PiExponentJets.W24.surjective_prime_residueAlgEquiv`, `OAI.PiExponentJets.W25.quotientDegreeProjection`, `OAI.PiExponentJets.W28.LocalIntersection.cokernelEquivCut`, `OAI.PiExponentJets.W28.LocalIntersection.colonQuotientEquivKernel`, `OAI.PiExponentJets.W28.LocalIntersection.cutEuler`, `OAI.PiExponentJets.W28.LocalIntersection.minimalPrimeCutSum`, `OAI.PiExponentJets.W28.LocalIntersection.quotientMinimalPrimesEquiv`, `OAI.PiExponentJets.W28.LocalIntersection.quotientMul`, `OAI.PiExponentJets.W28.LocalIntersection.scalarCokernelEquiv`, `OAI.PiExponentSiegel.W08.renameQuotientEquiv`, `OAI.PiExponentSiegel.W17.ConeLocalLength.AffineRing`, `OAI.PiExponentSiegel.W17.ConeLocalLength.ConeRing`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Cohomology_FiniteCoverCohomology`, `PiExponent_Cohomology_LocalIntersectionEulerFiltration`, `PiExponent_Geometry_NormalizationGrowth`, `PiExponent_LocalAlgebra_ColonHilbertStep`, `PiExponent_LocalAlgebra_ConeLocalLength`, `PiExponent_LocalAlgebra_CumulativeHilbertSections`, `PiExponent_LocalAlgebra_CyclicPrimeFactor`, `PiExponent_LocalAlgebra_LocalIntersectionLength`, `PiExponent_LocalAlgebra_LocalIntersectionPrimeFactors`, `PiExponent_LocalAlgebra_LocalIntersectionQuotientTransport`, `PiExponent_LocalAlgebra_LocalIntersectionTransport`, `PiExponent_LocalAlgebra_LocalPrimeTower`, `PiExponent_LocalAlgebra_LocalizedCyclicFactor`, `PiExponent_LocalAlgebra_LocalizedMinimalPrimeFamily`, `PiExponent_LocalAlgebra_LocalizedOneCutPropagation`, `PiExponent_LocalAlgebra_NaturalMultiplicityPropagation`, `PiExponent_LocalAlgebra_ParameterCombinations`, `PiExponent_LocalAlgebra_PositiveDimensionalHilbert`, `PiExponent_LocalAlgebra_PrimeCutBudget`, `PiExponent_LocalAlgebra_QuotientPrimeResidueBasis`, `PiExponent_LocalAlgebra_RegularPrefixes`, `PiExponent_LocalAlgebra_SubquotientLength`, `PiExponent_Polynomials_CoordinateQuotientGrading`, `PiExponent_Polynomials_HomogeneousIdealStep`, `PiExponent_Polynomials_HomogeneousPrimeFiltration`, `PiExponent_Polynomials_HomogeneousQuotientDimension`, `PiExponent_Polynomials_Homogenization`, `PiExponent_Polynomials_PolynomialCumulative`, `PiExponent_Polynomials_PolynomialPrimeDimension`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A015`, `OAIQ068A018` and `OAIQ068A019`; the statements `OAI_PiExponentJets_W22_localized_onecut_parent_recurrence`, `OAI.PiExponentJets.W22.localized_onecut_parent_recurrence_q68`, `OAI_PiExponentJets_W28_LocalIntersection_regular_ring_onecut_length`, `OAI.PiExponentJets.W28.LocalIntersection.regular_ring_onecut_length_q68`, `OAI_PiExponent_AdmissibleBlowupGeometry_uniform_curve_margin_of_affine_curve_data` and `OAI_PiExponent_GlobalReesRecoveryComparison_eventually_ordinaryMap_app_bijective`; the proofs of `OAI_PiExponentJets_W22_localized_cyclic_filtration_length`, `OAI.PiExponentJets.W22.localized_cyclic_filtration_length_q68`, `OAI_PiExponentJets_W22_localized_onecut_parent_recurrence`, `OAI.PiExponentJets.W22.localized_onecut_parent_recurrence_q68`, `OAI_PiExponent_localIsolatedBezout` and `OAI.PiExponent.localIsolatedBezout_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_FiniteCoverCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace ModuleGrothendieck
open CategoryTheory CategoryTheory.Limits
universe u
variable {C : Type u} [Category.{u} C] (R₀ : Cᵒᵖ ⥤ RingCat.{u})

instance presheafHasSeparator : HasSeparator (PresheafOfModules.{u} R₀) :=
  ⟨⟨∐ (yoneda ⋙ PresheafOfModules.free R₀).obj,
    (PresheafOfModules.freeYoneda.isSeparating R₀).isSeparator_coproduct⟩⟩

end ModuleGrothendieck

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CyclicPrimeFactor
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

variable {R : Type*} [CommRing R]

noncomputable def cyclicFactorEquiv (I : Ideal R) (f : R) :
    (R ⧸ I.colon {f}) ≃ₗ[R]
      (↥(I ⊔ Ideal.span {f}) ⧸ I.submoduleOf (I ⊔ Ideal.span {f})) := by
  let J : Ideal R := I ⊔ Ideal.span {f}
  have hfJ : f ∈ J := (show Ideal.span {f} ≤ J from le_sup_right)
    (Ideal.subset_span (by simp))
  let F : R →ₗ[R] J ⧸ I.submoduleOf J :=
    (I.submoduleOf J).mkQ.comp (LinearMap.toSpanSingleton R J ⟨f, hfJ⟩)
  have hker : LinearMap.ker F = I.colon {f} := by
    ext a
    change ((Submodule.Quotient.mk (a • (⟨f, hfJ⟩ : J)) : J ⧸ I.submoduleOf J) = 0) ↔
      a ∈ I.colon {f}
    rw [Submodule.Quotient.mk_eq_zero]
    change a * f ∈ I ↔ a ∈ I.colon {f}
    simp only [Submodule.mem_colon_singleton, smul_eq_mul]
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨x, rfl⟩ := (I.submoduleOf J).mkQ_surjective y
    have hx : (x : R) ∈ Ideal.span {f} ⊔ I := by
      simpa only [J, sup_comm] using x.property
    obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp hx
    refine ⟨a, ?_⟩
    change (Submodule.Quotient.mk (a • (⟨f, hfJ⟩ : J)) : J ⧸ I.submoduleOf J) =
      Submodule.Quotient.mk x
    rw [Submodule.Quotient.eq]
    change a * f - (x : R) ∈ I
    rw [← hab]
    simpa only [sub_add_eq_sub_sub, sub_self, zero_sub] using I.neg_mem hb
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (F.quotKerEquivOfSurjective hsurj)

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_SubquotientLength
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

noncomputable def subquotientEquivImage (A B : Submodule R M) :
    (B ⧸ A.submoduleOf B) ≃ₗ[R] B.map A.mkQ := by
  let F : B →ₗ[R] M ⧸ A := A.mkQ.comp B.subtype
  have hker : LinearMap.ker F = A.submoduleOf B := by
    simp only [F, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.submoduleOf]
  have hrange : LinearMap.range F = B.map A.mkQ := by
    simp only [F, LinearMap.range_comp, Submodule.range_subtype]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (F.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalIntersectionLength
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

def quotientMul (I : Ideal A) (x : A) : (A ⧸ I) →ₗ[A] (A ⧸ I) :=
  x • LinearMap.id

@[simp] theorem quotientMul_apply (I : Ideal A) (x : A) (y : A ⧸ I) :
    quotientMul I x y = x • y := rfl

@[simp] theorem quotientMul_mk (I : Ideal A) (x a : A) :
    quotientMul I x (I.mkQ a) = I.mkQ (a * x) := by
  change x • I.mkQ a = I.mkQ (a * x)
  calc
    x • I.mkQ a = I.mkQ (x • a) := (I.mkQ.map_smul x a).symm
    _ = I.mkQ (a * x) := by rw [smul_eq_mul, mul_comm]

theorem quotientMul_kernel (I : Ideal A) (x : A) :
    LinearMap.ker (quotientMul I x) = Submodule.map I.mkQ (I.colon {x}) := by
  ext y
  constructor
  · intro hy
    obtain ⟨a, rfl⟩ := I.mkQ_surjective y
    have ha : a * x ∈ I := by
      have hz : quotientMul I x (I.mkQ a) = 0 := hy
      rw [quotientMul_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
      exact hz
    refine ⟨a, ?_, rfl⟩
    change a ∈ I.colon {x}
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using ha
  · rintro ⟨a, ha, rfl⟩
    change a ∈ I.colon {x} at ha
    change quotientMul I x (I.mkQ a) = 0
    rw [quotientMul_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using ha

noncomputable def colonQuotientEquivKernel (I : Ideal A) (x : A) :
    ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) ≃ₗ[A]
      LinearMap.ker (quotientMul I x) :=
  (W22.subquotientEquivImage I (I.colon {x})).trans
    (LinearEquiv.ofEq _ _ (quotientMul_kernel I x).symm)

theorem quotientMul_range (I : Ideal A) (x : A) :
    LinearMap.range (quotientMul I x) = Submodule.map I.mkQ (Ideal.span {x}) := by
  have hcomp : (quotientMul I x).comp I.mkQ =
      I.mkQ.comp (LinearMap.toSpanSingleton A A x) := by
    apply LinearMap.ext
    intro a
    change quotientMul I x (I.mkQ a) = I.mkQ (a * x)
    exact quotientMul_mk I x a
  have hr := congrArg LinearMap.range hcomp
  simpa only [LinearMap.range_comp, Submodule.range_mkQ, Submodule.map_top,
    LinearMap.range_toSpanSingleton] using hr

noncomputable def cokernelEquivCut (I : Ideal A) (x : A) :
    ((A ⧸ I) ⧸ LinearMap.range (quotientMul I x)) ≃ₗ[A]
      A ⧸ (I ⊔ Ideal.span {x}) :=
  (Submodule.quotEquivOfEq _ _ (quotientMul_range I x)).trans
    (Submodule.quotientQuotientEquivQuotientSup I (Ideal.span {x}))

end PiExponentJets.W28.LocalIntersection

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalIntersectionTransport
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A M N : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

theorem map_scalar_kernel (e : M ≃ₗ[A] N) (x : A) :
    (LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M))).map e.toLinearMap =
      LinearMap.ker (x • (LinearMap.id : N →ₗ[A] N)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change x • e z = 0
    change x • z = 0 at hz
    rw [← map_smul, hz, map_zero]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change x • e.symm y = 0
    change x • y = 0 at hy
    rw [← map_smul, hy, map_zero]

theorem map_scalar_range (e : M ≃ₗ[A] N) (x : A) :
    (LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))).map e.toLinearMap =
      LinearMap.range (x • (LinearMap.id : N →ₗ[A] N)) := by
  ext y
  constructor
  · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
    refine ⟨e w, ?_⟩
    change x • e w = e (x • w)
    exact (map_smul e x w).symm
  · rintro ⟨z, rfl⟩
    refine ⟨x • e.symm z, ⟨e.symm z, rfl⟩, ?_⟩
    change e (x • e.symm z) = x • z
    rw [map_smul, e.apply_symm_apply]

noncomputable def scalarCokernelEquiv (e : M ≃ₗ[A] N) (x : A) :
    (M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))) ≃ₗ[A]
      (N ⧸ LinearMap.range (x • (LinearMap.id : N →ₗ[A] N))) :=
  Submodule.Quotient.equiv _ _ e (map_scalar_range e x)

end PiExponentJets.W28.LocalIntersection

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalizedCyclicFactor
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

variable {R : Type*} [CommRing R]

theorem map_colon_singleton_localization
    (S : Submonoid R) (L : Type*) [CommRing L] [Algebra R L] [IsLocalization S L]
    (I : Ideal R) (f : R) :
    (I.colon {f}).map (algebraMap R L) =
      (I.map (algebraMap R L)).colon {algebraMap R L f} := by
  apply (IsLocalization.orderEmbedding S L).injective
  ext a
  change algebraMap R L a ∈ (I.colon {f}).map (algebraMap R L) ↔
    algebraMap R L a ∈ (I.map (algebraMap R L)).colon {algebraMap R L f}
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul,
    IsLocalization.algebraMap_mem_map_algebraMap_iff S L, mul_assoc]

noncomputable def localizedCyclicFactorEquiv
    (S : Submonoid R) (L : Type*) [CommRing L] [Algebra R L] [IsLocalization S L]
    (I : Ideal R) (f : R) :
    (L ⧸ (I.colon {f}).map (algebraMap R L)) ≃ₗ[L]
      (((I ⊔ Ideal.span {f}).map (algebraMap R L)) ⧸
        (I.map (algebraMap R L)).submoduleOf
          ((I ⊔ Ideal.span {f}).map (algebraMap R L))) := by
  rw [map_colon_singleton_localization S L, Ideal.map_sup,
    Ideal.map_span, Set.image_singleton]
  exact cyclicFactorEquiv (I.map (algebraMap R L)) (algebraMap R L f)

noncomputable def primeLocalizedCyclicFactorEquiv
    (Q : Ideal R) [Q.IsPrime] (I : Ideal R) (f : R) :
    (Localization.AtPrime Q ⧸ (I.colon {f}).map
      (algebraMap R (Localization.AtPrime Q))) ≃ₗ[Localization.AtPrime Q]
      (((I ⊔ Ideal.span {f}).map (algebraMap R (Localization.AtPrime Q))) ⧸
        (I.map (algebraMap R (Localization.AtPrime Q))).submoduleOf
          ((I ⊔ Ideal.span {f}).map (algebraMap R (Localization.AtPrime Q)))) :=
  localizedCyclicFactorEquiv Q.primeCompl (Localization.AtPrime Q) I f

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_LocalIntersectionEulerFiltration
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators

variable {A : Type*} [CommRing A]

noncomputable def cutEuler (I : Ideal A) (x : A) : ℤ :=
  ((Module.length A (A ⧸ (I ⊔ Ideal.span {x}))).toNat : ℤ) -
    (Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x}))).toNat

@[simp] theorem cutEuler_top (x : A) : cutEuler (⊤ : Ideal A) x = 0 := by
  simp [cutEuler, Module.length_eq_zero]

end PiExponentJets.W28.LocalIntersection

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_NormalizationGrowth
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

open MvPolynomial

variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def quotientDegreeFiltration (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Submodule k (MvPolynomial σ k ⧸ I) :=
  (restrictTotalDegree σ k n).map (Ideal.Quotient.mkₐ k I).toLinearMap

noncomputable instance quotientDegreeFiltration_finite (I : Ideal (MvPolynomial σ k))
    (n : ℕ) : Module.Finite k (quotientDegreeFiltration I n) := by
  unfold quotientDegreeFiltration
  infer_instance

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousIdealStep
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

theorem homogeneous_mem_step_decomposition
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d n : ℕ} (f p : MvPolynomial σ k)
    (hf : f.IsHomogeneous d) (hp : p.IsHomogeneous (n + d))
    (hmem : p ∈ Ideal.span {f} ⊔ I) :
    ∃ a : MvPolynomial σ k, a.IsHomogeneous n ∧ p - a * f ∈ I := by
  obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp hmem
  let aₙ := DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ k) a n
  refine ⟨aₙ.1, aₙ.2, ?_⟩
  have hproj := congrArg
    (GradedRing.proj (MvPolynomial.homogeneousSubmodule σ k) (n + d)) hab
  rw [map_add, GradedRing.proj_apply, GradedRing.proj_apply,
    GradedRing.proj_apply,
    DirectSum.coe_decompose_mul_add_of_right_mem
      (MvPolynomial.homogeneousSubmodule σ k) hf,
    DirectSum.decompose_of_mem_same (MvPolynomial.homogeneousSubmodule σ k) hp] at hproj
  have hb' := (Ideal.IsHomogeneous.mem_iff
    (MvPolynomial.homogeneousSubmodule σ k) hI).mp hb (n + d)
  have heq : p - aₙ.1 * f =
      (DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ k) b (n + d) :
        MvPolynomial σ k) := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [aₙ, add_comm] using hproj.symm
  rw [heq]
  exact hb'

theorem homogeneous_mem_step_of_degree_lt
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d n : ℕ} (f p : MvPolynomial σ k)
    (hf : f.IsHomogeneous d) (hp : p.IsHomogeneous n) (hnd : n < d)
    (hmem : p ∈ Ideal.span {f} ⊔ I) : p ∈ I := by
  obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp hmem
  have hproj := congrArg
    (GradedRing.proj (MvPolynomial.homogeneousSubmodule σ k) n) hab
  rw [map_add, GradedRing.proj_apply, GradedRing.proj_apply,
    GradedRing.proj_apply,
    DirectSum.coe_decompose_mul_of_right_mem_of_not_le
      (MvPolynomial.homogeneousSubmodule σ k) hf (Nat.not_le_of_lt hnd),
    zero_add,
    DirectSum.decompose_of_mem_same (MvPolynomial.homogeneousSubmodule σ k) hp] at hproj
  rw [← hproj]
  exact (Ideal.IsHomogeneous.mem_iff
    (MvPolynomial.homogeneousSubmodule σ k) hI).mp hb n

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ColonHilbertStep
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem ideal_le_colon_singleton (I : Ideal (MvPolynomial σ k))
    (f : MvPolynomial σ k) : I ≤ I.colon {f} := by
  intro p hp
  apply Submodule.mem_colon_singleton.mpr
  simpa only [smul_eq_mul] using I.mul_mem_right f hp

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ConeLocalLength
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSiegel.W17.ConeLocalLength

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

variable (k σ : Type*) [CommRing k]

abbrev AffineRing := MvPolynomial σ k
abbrev ConeRing := MvPolynomial (Option σ) k

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousQuotientDimension
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.W25

open MvPolynomial
open PiExponentJets.W64
open DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

def quotientDegreeProjection (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (n : ℕ) :
    (MvPolynomial σ k ⧸ I) →ₗ[k] (MvPolynomial σ k ⧸ I) :=
  (I.restrictScalars k).liftQ
    ((Ideal.Quotient.mkₐ k I).toLinearMap.comp
      (GradedAlgebra.proj (MvPolynomial.homogeneousSubmodule σ k) n)) (by
    intro p hp
    change Ideal.Quotient.mk I
      (GradedAlgebra.proj (MvPolynomial.homogeneousSubmodule σ k) n p) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (Ideal.IsHomogeneous.mem_iff
      (MvPolynomial.homogeneousSubmodule σ k) hI).mp hp n)

@[simp] theorem quotientDegreeProjection_mk (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (n : ℕ)
    (p : MvPolynomial σ k) :
    quotientDegreeProjection I hI n (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk I
        (GradedAlgebra.proj (MvPolynomial.homogeneousSubmodule σ k) n p) := rfl

end PiExponentJets.W25

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CumulativeHilbertSections
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.W25

open MvPolynomial DirectSum
open PiExponentJets.W24 PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

theorem restrictTotalDegree_eq_iSup_homogeneous (n : ℕ) :
    restrictTotalDegree σ k n =
      ⨆ j : Fin (n + 1), homogeneousSubmodule σ k j.val := by
  classical
  apply le_antisymm
  · intro p hp
    have hpdegree : p.totalDegree ≤ n := (mem_restrictTotalDegree σ _ _).mp hp
    have hsum : (∑ j ∈ Finset.range (p.totalDegree + 1), homogeneousComponent j p) ∈
        ⨆ j : Fin (n + 1), homogeneousSubmodule σ k j.val := by
      apply Submodule.sum_mem
      intro j hj
      have hjdegree : j ≤ n :=
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hpdegree
      exact (le_iSup (fun a : Fin (n + 1) => homogeneousSubmodule σ k a.val)
        ⟨j, Nat.lt_succ_of_le hjdegree⟩) (homogeneousComponent_mem j p)
    simpa only [sum_homogeneousComponent] using hsum
  · apply iSup_le
    intro j p hp
    apply (mem_restrictTotalDegree σ _ _).mpr
    exact (show p.IsHomogeneous j.val from hp).totalDegree_le.trans
      (Nat.le_of_lt_succ j.isLt)

end PiExponentJets.W25

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalIntersectionPrimeFactors
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A : Type*} [CommRing A]

noncomputable def minimalPrimeCutSum [IsNoetherianRing A]
    (I : Ideal A) (x : A) : ℕ∞ := by
  classical
  letI : Fintype I.minimalPrimes :=
    (I.finite_minimalPrimes_of_isNoetherianRing A).fintype
  exact ∑ P : I.minimalPrimes,
    letI : P.val.IsPrime := P.property.1.1
    Module.length (Localization.AtPrime P.val)
      (Localization.AtPrime P.val ⧸
        I.map (algebraMap A (Localization.AtPrime P.val))) *
      Module.length A (A ⧸ (P.val ⊔ Ideal.span {x}))

end PiExponentJets.W28.LocalIntersection

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalIntersectionQuotientTransport
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A : Type*} [CommRing A]

noncomputable def quotientMinimalPrimesEquiv (I : Ideal A) :
    minimalPrimes (A ⧸ I) ≃ I.minimalPrimes := by
  classical
  let f : minimalPrimes (A ⧸ I) → I.minimalPrimes := fun Q =>
    ⟨Q.val.comap (Ideal.Quotient.mk I), by
      rw [I.minimalPrimes_eq_comap]
      exact ⟨Q.val, Q.property, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro Q R h
    apply Subtype.ext
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    exact congrArg Subtype.val h
  · intro P
    have hmem : P.val ∈ Ideal.comap (Ideal.Quotient.mk I) '' minimalPrimes (A ⧸ I) :=
      Eq.mp (congrArg (fun S : Set (Ideal A) => P.val ∈ S) I.minimalPrimes_eq_comap) P.property
    obtain ⟨Q, hQ, hQP⟩ := hmem
    exact ⟨⟨Q, hQ⟩, Subtype.ext hQP⟩

@[simp] theorem quotientMinimalPrimesEquiv_apply (I : Ideal A)
    (Q : minimalPrimes (A ⧸ I)) :
    (quotientMinimalPrimesEquiv I Q).val = Q.val.comap (Ideal.Quotient.mk I) := rfl

end PiExponentJets.W28.LocalIntersection

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalPrimeTower
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

variable {A : Type*} [CommRing A]

noncomputable def localPrimeTowerEquiv
    (Q : Ideal A) [Q.IsPrime] (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] :
    Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q))) ≃ₐ[A]
      Localization.AtPrime p :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization Q.primeCompl p

@[simp] theorem localPrimeTowerEquiv_algebraMap
    (Q : Ideal A) [Q.IsPrime] (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] (a : A) :
    localPrimeTowerEquiv Q p
      (algebraMap A (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q)))) a) =
      algebraMap A (Localization.AtPrime p) a :=
  (localPrimeTowerEquiv Q p).commutes a

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalizedMinimalPrimeFamily
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

variable {A : Type*} [CommRing A]

def MinimalParentsBelow (I Q : Ideal A) := {P : Ideal A // P ∈ I.minimalPrimes ∧ P ≤ Q}

noncomputable instance minimalParentsBelow_fintype [IsNoetherianRing A] (I Q : Ideal A) :
    Fintype (MinimalParentsBelow I Q) := by
  have hfinite : {P : Ideal A | P ∈ I.minimalPrimes ∧ P ≤ Q}.Finite :=
    (I.finite_minimalPrimes_of_isNoetherianRing A).subset (fun _ h => h.1)
  exact hfinite.fintype

instance instIsPrimeValIdealAndMemSetMinimalPrimesLe_solutions {I Q : Ideal A} (P : MinimalParentsBelow I Q) : P.val.IsPrime := P.property.1.1.1

noncomputable def localizedMinimalPrimesEquiv (I Q : Ideal A) [Q.IsPrime] :
    (I.map (algebraMap A (Localization.AtPrime Q))).minimalPrimes ≃ MinimalParentsBelow I Q := by
  classical
  let L := Localization.AtPrime Q
  let e := IsLocalization.AtPrime.orderIsoOfPrime L Q
  let f : (I.map (algebraMap A L)).minimalPrimes → MinimalParentsBelow I Q := fun p =>
    ⟨p.val.comap (algebraMap A L), by
      have hmin : p.val.comap (algebraMap A L) ∈ I.minimalPrimes :=
        (Set.ext_iff.mp (IsLocalization.minimalPrimes_map Q.primeCompl L I) p.val).mp p.property
      exact ⟨hmin, (e ⟨p.val, p.property.1.1⟩).property.2⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q h
    apply Subtype.ext
    apply (IsLocalization.orderEmbedding Q.primeCompl L).injective
    exact congrArg Subtype.val h
  · intro P
    let p := e.symm ⟨P.val, P.property.1.1.1, P.property.2⟩
    have heq : p.val.comap (algebraMap A L) = P.val :=
      congrArg Subtype.val (e.apply_symm_apply ⟨P.val, P.property.1.1.1, P.property.2⟩)
    have hp : p.val ∈ (I.map (algebraMap A L)).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map Q.primeCompl L I]
      change p.val.comap (algebraMap A L) ∈ I.minimalPrimes
      rw [heq]
      exact P.property.1
    exact ⟨⟨p.val, hp⟩, Subtype.ext heq⟩

@[simp] theorem localizedMinimalPrimesEquiv_apply
    (I Q : Ideal A) [Q.IsPrime]
    (p : (I.map (algebraMap A (Localization.AtPrime Q))).minimalPrimes) :
    (localizedMinimalPrimesEquiv I Q p).val =
      p.val.comap (algebraMap A (Localization.AtPrime Q)) := rfl

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalizedOneCutPropagation
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W28.LocalIntersection
open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

noncomputable def globalParentCutSum (I Q : Ideal A) [Q.IsPrime] (x : A) : ℕ∞ :=
  ∑ P : MinimalParentsBelow I Q,
    Module.length (Localization.AtPrime P.val)
      (Localization.AtPrime P.val ⧸ I.map (algebraMap A (Localization.AtPrime P.val))) *
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ (P.val ⊔ Ideal.span {x}).map
        (algebraMap A (Localization.AtPrime Q)))

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_Homogenization
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators
open MvPolynomial

variable {k σ : Type*} [CommRing k]

noncomputable def dehomogenize : MvPolynomial (Option σ) k →+* MvPolynomial σ k :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun o : Option σ => o.elim 1 MvPolynomial.X)

@[simp] theorem dehomogenize_X_none :
    dehomogenize (MvPolynomial.X none : MvPolynomial (Option σ) k) = 1 := by
  simp [dehomogenize]

@[simp] theorem dehomogenize_rename (p : MvPolynomial σ k) :
    dehomogenize (MvPolynomial.rename some p) = p := by
  change MvPolynomial.eval₂Hom MvPolynomial.C
    (fun o : Option σ => o.elim 1 MvPolynomial.X) (MvPolynomial.rename some p) = p
  rw [MvPolynomial.eval₂Hom_rename]
  change MvPolynomial.eval₂ MvPolynomial.C MvPolynomial.X p = p
  exact MvPolynomial.eval₂_eta p

noncomputable def homogenize (p : MvPolynomial σ k) : MvPolynomial (Option σ) k :=
  ∑ i ∈ Finset.range (p.totalDegree + 1),
    MvPolynomial.rename some (MvPolynomial.homogeneousComponent i p) *
      MvPolynomial.X none ^ (p.totalDegree - i)

@[simp] theorem dehomogenize_homogenize (p : MvPolynomial σ k) :
    dehomogenize (homogenize p) = p := by
  simp only [homogenize, map_sum, map_mul, map_pow, dehomogenize_rename,
    dehomogenize_X_none, one_pow, mul_one]
  exact MvPolynomial.sum_homogeneousComponent p

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularPrefixes
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegel.W20

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem prefixIdeal_homogeneous
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i)) (n : ℕ) :
    (Ideal.ofList (rs.take n)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k) := by
  apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule σ k)
  intro f hf
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_mem_take hf)
  exact ⟨degrees ⟨i, hi⟩, hhom ⟨i, hi⟩⟩

end PiExponentSiegel.W20

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PositiveDimensionalHilbert
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem map_int_invOneSubPow (r : ℕ) :
    PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.invOneSubPow ℤ r).val =
      (PowerSeries.invOneSubPow ℚ r).val := by
  cases r with
  | zero => simp [PowerSeries.invOneSubPow_zero]
  | succ r =>
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
      PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
    ext n
    simp [PowerSeries.coeff_map]

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_CoordinateQuotientGrading
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PiExponentSiegel.W08

section

open MvPolynomial

variable {k σ τ : Type*} [Field k]

theorem homogeneous_ideal_map_of_degree_preserving
    (f : MvPolynomial σ k →ₐ[k] MvPolynomial τ k)
    (hf : ∀ n (p : MvPolynomial σ k), p.IsHomogeneous n → (f p).IsHomogeneous n)
    (J : Ideal (MvPolynomial σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    (J.map f.toRingHom).IsHomogeneous (MvPolynomial.homogeneousSubmodule τ k) := by
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists (MvPolynomial.homogeneousSubmodule σ k) J).mp hJ
  rw [hS, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro q ⟨p, ⟨z, hz, rfl⟩, rfl⟩
  obtain ⟨n, hn⟩ := z.property
  exact ⟨n, hf n z hn⟩

end

variable {k σ τ : Type*} [Field k]

noncomputable def renameQuotientEquiv (e : σ ≃ τ) (J : Ideal (MvPolynomial σ k)) :
    (MvPolynomial σ k ⧸ J) ≃ₐ[k]
      (MvPolynomial τ k ⧸ J.map (MvPolynomial.rename e).toRingHom) :=
  Ideal.quotientEquivAlg J _ (MvPolynomial.renameEquiv k e) rfl

theorem renameImageIdeal_homogeneous (e : σ ≃ τ) (J : Ideal (MvPolynomial σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    (J.map (MvPolynomial.rename e).toRingHom).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule τ k) :=
  homogeneous_ideal_map_of_degree_preserving (MvPolynomial.rename e)
    (fun _ _ hp => hp.rename_isHomogeneous) J hJ

end PiExponentSiegel.W08

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousPrimeFiltration
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

def HomogeneousPrimeStep (I J : Ideal (MvPolynomial σ k)) : Prop :=
  I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) ∧
    ∃ (d : ℕ) (f : MvPolynomial σ k), f.IsHomogeneous d ∧ f ∉ I ∧
      (I.colon {f}).IsPrime ∧ J = I ⊔ Ideal.span {f}

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialCumulative
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

open Polynomial Finset

noncomputable def powerPrefixPolynomial (d : ℕ) : Polynomial ℚ :=
  C ((d + 1 : ℚ)⁻¹) * (Polynomial.bernoulli (d + 1) - C (_root_.bernoulli (d + 1)))

noncomputable def polynomialPrefix (p : Polynomial ℚ) : Polynomial ℚ :=
  ∑ i ∈ range (p.natDegree + 1), C (p.coeff i) * powerPrefixPolynomial i

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrimeCutBudget
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ τ : Type*} [Field k] [Fintype σ] [Fintype τ]

noncomputable def actualLocalLength (I Q : Ideal (MvPolynomial σ k)) [Q.IsPrime] : ℕ :=
  (Module.length (Localization.AtPrime Q)
    (Localization.AtPrime Q ⧸ I.map
      (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q)))).toNat

omit [Fintype σ] in
theorem primeCut_isHomogeneous
    (P : Ideal (MvPolynomial σ k))
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) :
    (Ideal.span {f} ⊔ P).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  have hsingle : (Ideal.span {f}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
    apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule σ k)
    intro x hx
    have hxf : x = f := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨d, hf⟩
  exact hsingle.sup hP

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_NaturalMultiplicityPropagation
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {k σ : Type u} [Field k] [Fintype σ]

omit [Fintype σ] in
theorem cut_ideal_homogeneous
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (x : MvPolynomial σ k) (hx : x.IsHomogeneous d) :
    (I ⊔ Ideal.span {x}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  simpa only [sup_comm] using primeCut_isHomogeneous I hI x hx

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ParameterCombinations
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators

variable {k σ ι : Type*} [CommRing k]

noncomputable def parameterCombination (s : Finset ι) (c : ι → k)
    (f : ι → MvPolynomial σ k) : MvPolynomial σ k :=
  ∑ i ∈ s, MvPolynomial.C (c i) * f i

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_QuotientPrimeResidueBasis
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.W24

section Surjective

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

def surjective_prime_residueAlgEquiv
    (f : A →ₐ[k] B) (hf : Function.Surjective f)
    (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime]
    (hPQ : P = Q.comap f.toRingHom) : P.ResidueField ≃ₐ[k] Q.ResidueField :=
  AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ P Q f hPQ)
    ((RingHom.surjectiveOnStalks_of_surjective hf).residueFieldMap_bijective P Q hPQ)

@[simp] theorem surjective_prime_residueAlgEquiv_algebraMap
    (f : A →ₐ[k] B) (hf : Function.Surjective f)
    (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime]
    (hPQ : P = Q.comap f.toRingHom) (a : A) :
    surjective_prime_residueAlgEquiv f hf P Q hPQ (algebraMap A P.ResidueField a) =
      algebraMap B Q.ResidueField (f a) :=
  Ideal.ResidueField.map_algebraMap P Q f.toRingHom hPQ a

end Surjective

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

theorem quotient_prime_comap (P Q : Ideal A) (hPQ : P ≤ Q) :
    (Q.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = Q := by
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  change Q ⊔ RingHom.ker (Ideal.Quotient.mk P) = Q
  rw [Ideal.mk_ker, sup_eq_left.mpr hPQ]

def quotientPrimeResidueAlgEquiv
    (P Q : Ideal A) [Q.IsPrime] (hPQ : P ≤ Q) :
    letI : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hPQ)
    Q.ResidueField ≃ₐ[k] (Q.map (Ideal.Quotient.mk P)).ResidueField := by
  letI : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hPQ)
  exact surjective_prime_residueAlgEquiv (Ideal.Quotient.mkₐ k P)
    Ideal.Quotient.mk_surjective Q (Q.map (Ideal.Quotient.mk P))
    (quotient_prime_comap P Q hPQ).symm

end PiExponentJets.W24

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialPrimeDimension
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.W24

section Equivalence
variable {A B : Type*} [CommRing A] [CommRing B]

local instance imagePrime_isPrime (e : A ≃+* B) (Q : Ideal A) [Q.IsPrime] :
    (Q.map e.toRingHom).IsPrime := Ideal.map_isPrime_of_equiv e

end Equivalence


end PiExponentJets.W24

end

end OAI
end


