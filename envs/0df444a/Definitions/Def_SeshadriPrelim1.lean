-- Prove2me | Definitions.Def_SeshadriPrelim1
-- name    : SeshadriPrelim1
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T14:32:14.061385+00:00
-- url     : https://prove2.me/theorems/ef16e136-1254-47eb-b59c-8125ea033f2f
-- title:
--   Maximal Seshadri constants: supporting development, part 1
-- statement:
--   Part 1 of 6 of the supporting Lean development for the maximal Seshadri constants theorem. It holds the definitions that the statements of the published child theorems refer to, in source order, together with the proved lemmas that their bodies and type class instances rely on. No result is assumed: every lemma here has a proof. Source modules: `Analytic.ConvergentSeries`, `Bertini.LinearForms`, `Cohomology.AffineDenominators`, `Cohomology.Injectives`, `Geometry.SmoothAffineRefinement`, `Jets.PolynomialJets`, `Sheaves.LineBundleCoherent`. The compatibility block restates for this Mathlib some names available in the upstream Mathlib: `PresheafOfModulesOfCommRing` abbreviations, `TensorProduct.inductionOn`, `MvPolynomial.monomial_mul_monomial`, and `ite_eq_left`, `ite_eq_right`, `dite_eq_left`, `dite_eq_right` in namespace `OAI`, and it adds `@[simp]` to the `Pi.lift_π`, `Sigma.ι_desc`, `prod` and `coprod` projection lemmas.
--
--   **Formalization Note** Definitions of this development carry proof fields, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/AlgebraicGeometry/Seshadri` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`. Edits for the port: in `AdicInjective.fg_uniform_exponent`, `obtain ⟨s, hs⟩ := IsCompactElement.exists_finset_of_le_iSup` becomes `obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup (Submodule R M)`; in `Geometry.freeUnitIso`, `rw [Sigma.ι_comp_desc_assoc]` becomes `rw [Sigma.ι_desc_assoc]`.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants

set_option linter.all false


noncomputable abbrev PresheafOfModulesOfCommRing.monoidalCategory :=
  @PresheafOfModules.monoidalCategory
noncomputable abbrev PresheafOfModulesOfCommRing.Monoidal.tensorHom :=
  @PresheafOfModules.Monoidal.tensorHom

noncomputable abbrev PresheafOfModulesOfCommRing.symmetricCategory :=
  @PresheafOfModules.symmetricCategory

open scoped TensorProduct in
@[elab_as_elim]
protected theorem TensorProduct.inductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add

attribute [simp] CategoryTheory.Limits.Pi.lift_π CategoryTheory.Limits.Pi.lift_π_assoc
  CategoryTheory.Limits.Sigma.ι_desc CategoryTheory.Limits.Sigma.ι_desc_assoc
  CategoryTheory.Limits.prod.lift_fst CategoryTheory.Limits.prod.lift_fst_assoc
  CategoryTheory.Limits.prod.lift_snd CategoryTheory.Limits.prod.lift_snd_assoc
  CategoryTheory.Limits.coprod.inl_desc CategoryTheory.Limits.coprod.inl_desc_assoc
  CategoryTheory.Limits.coprod.inr_desc CategoryTheory.Limits.coprod.inr_desc_assoc

theorem MvPolynomial.monomial_mul_monomial {σ R : Type*} [CommSemiring R] {s s' : σ →₀ ℕ} {a b : R} :
    MvPolynomial.monomial s a * MvPolynomial.monomial s' b = MvPolynomial.monomial (s + s') (a * b) :=
  MvPolynomial.monomial_mul

namespace OAI

theorem ite_eq_left {α : Sort*} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort*} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort*} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α}
    (h : c) : dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort*} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α}
    (h : ¬c) : dite c a b = b h := dif_neg h

end OAI

namespace OAI
end OAI
namespace OAI.MaximalSeshadri
end OAI.MaximalSeshadri
namespace OAI.MaximalSeshadri.ActualInterpolation
end OAI.MaximalSeshadri.ActualInterpolation
namespace OAI.MaximalSeshadri.AdicInjective
end OAI.MaximalSeshadri.AdicInjective
namespace OAI.MaximalSeshadri.AffineBlowup
end OAI.MaximalSeshadri.AffineBlowup
namespace OAI.MaximalSeshadri.AffineCohomology
end OAI.MaximalSeshadri.AffineCohomology
namespace OAI.MaximalSeshadri.AffineDenominators
end OAI.MaximalSeshadri.AffineDenominators
namespace OAI.MaximalSeshadri.AffineSchemeCohomology
end OAI.MaximalSeshadri.AffineSchemeCohomology
namespace OAI.MaximalSeshadri.AlgebraicJets
end OAI.MaximalSeshadri.AlgebraicJets
namespace OAI.MaximalSeshadri.AnalyticCoordinates
end OAI.MaximalSeshadri.AnalyticCoordinates
namespace OAI.MaximalSeshadri.AnalyticNode
end OAI.MaximalSeshadri.AnalyticNode
namespace OAI.MaximalSeshadri.Bertini
end OAI.MaximalSeshadri.Bertini
namespace OAI.MaximalSeshadri.BertiniIntegral
end OAI.MaximalSeshadri.BertiniIntegral
namespace OAI.MaximalSeshadri.BlowupGluing
end OAI.MaximalSeshadri.BlowupGluing
namespace OAI.MaximalSeshadri.BlowupLift
end OAI.MaximalSeshadri.BlowupLift
namespace OAI.MaximalSeshadri.CartierSequence
end OAI.MaximalSeshadri.CartierSequence
namespace OAI.MaximalSeshadri.ClosedPushforward
end OAI.MaximalSeshadri.ClosedPushforward
namespace OAI.MaximalSeshadri.Cohomology
end OAI.MaximalSeshadri.Cohomology
namespace OAI.MaximalSeshadri.EtaleDimension
end OAI.MaximalSeshadri.EtaleDimension
namespace OAI.MaximalSeshadri.EulerNumerics
end OAI.MaximalSeshadri.EulerNumerics
namespace OAI.MaximalSeshadri.ExtCokernel
end OAI.MaximalSeshadri.ExtCokernel
namespace OAI.MaximalSeshadri.ExtSectionComparison
end OAI.MaximalSeshadri.ExtSectionComparison
namespace OAI.MaximalSeshadri.FiniteCoverCohomology
end OAI.MaximalSeshadri.FiniteCoverCohomology
namespace OAI.MaximalSeshadri.FinitePointBlowup
end OAI.MaximalSeshadri.FinitePointBlowup
namespace OAI.MaximalSeshadri.FiniteSupport
end OAI.MaximalSeshadri.FiniteSupport
namespace OAI.MaximalSeshadri.FlasqueCohomology
end OAI.MaximalSeshadri.FlasqueCohomology
namespace OAI.MaximalSeshadri.FlatContraction
end OAI.MaximalSeshadri.FlatContraction
namespace OAI.MaximalSeshadri.FormalAdic
end OAI.MaximalSeshadri.FormalAdic
namespace OAI.MaximalSeshadri.FormalCoordinates
end OAI.MaximalSeshadri.FormalCoordinates
namespace OAI.MaximalSeshadri.FrameBertini
end OAI.MaximalSeshadri.FrameBertini
namespace OAI.MaximalSeshadri.Frames
end OAI.MaximalSeshadri.Frames
namespace OAI.MaximalSeshadri.FreeOpenUnit
end OAI.MaximalSeshadri.FreeOpenUnit
namespace OAI.MaximalSeshadri.Geometry
end OAI.MaximalSeshadri.Geometry
namespace OAI.MaximalSeshadri.Geometry.BaseSections
end OAI.MaximalSeshadri.Geometry.BaseSections
namespace OAI.MaximalSeshadri.Hartogs
end OAI.MaximalSeshadri.Hartogs
namespace OAI.MaximalSeshadri.IdealModule
end OAI.MaximalSeshadri.IdealModule
namespace OAI.MaximalSeshadri.IdealPullback
end OAI.MaximalSeshadri.IdealPullback
namespace OAI.MaximalSeshadri.InjectiveRange
end OAI.MaximalSeshadri.InjectiveRange
namespace OAI.MaximalSeshadri.Interpolation
end OAI.MaximalSeshadri.Interpolation
namespace OAI.MaximalSeshadri.IntersectionLength
end OAI.MaximalSeshadri.IntersectionLength
namespace OAI.MaximalSeshadri.InvertibleLocal
end OAI.MaximalSeshadri.InvertibleLocal
namespace OAI.MaximalSeshadri.LaurentCech
end OAI.MaximalSeshadri.LaurentCech
namespace OAI.MaximalSeshadri.LaurentLattices
end OAI.MaximalSeshadri.LaurentLattices
namespace OAI.MaximalSeshadri.LaurentPlane
end OAI.MaximalSeshadri.LaurentPlane
namespace OAI.MaximalSeshadri.LaurentTails
end OAI.MaximalSeshadri.LaurentTails
namespace OAI.MaximalSeshadri.LineClosedUnit
end OAI.MaximalSeshadri.LineClosedUnit
namespace OAI.MaximalSeshadri.LinearBertini
end OAI.MaximalSeshadri.LinearBertini
namespace OAI.MaximalSeshadri.LocalComparison
end OAI.MaximalSeshadri.LocalComparison
namespace OAI.MaximalSeshadri.LocalCurve
end OAI.MaximalSeshadri.LocalCurve
namespace OAI.MaximalSeshadri.ModuleFlasque
end OAI.MaximalSeshadri.ModuleFlasque
namespace OAI.MaximalSeshadri.ModuleGrothendieck
end OAI.MaximalSeshadri.ModuleGrothendieck
namespace OAI.MaximalSeshadri.ModuleLocal
end OAI.MaximalSeshadri.ModuleLocal
namespace OAI.MaximalSeshadri.ModuleMayerVietoris
end OAI.MaximalSeshadri.ModuleMayerVietoris
namespace OAI.MaximalSeshadri.ModulePresheaf
end OAI.MaximalSeshadri.ModulePresheaf
namespace OAI.MaximalSeshadri.ModuleSheafExact
end OAI.MaximalSeshadri.ModuleSheafExact
namespace OAI.MaximalSeshadri.NefNumerics
end OAI.MaximalSeshadri.NefNumerics
namespace OAI.MaximalSeshadri.NodalLocal
end OAI.MaximalSeshadri.NodalLocal
namespace OAI.MaximalSeshadri.OpenBaseChange
end OAI.MaximalSeshadri.OpenBaseChange
namespace OAI.MaximalSeshadri.PlaneBlowup
end OAI.MaximalSeshadri.PlaneBlowup
namespace OAI.MaximalSeshadri.PlaneCech
end OAI.MaximalSeshadri.PlaneCech
namespace OAI.MaximalSeshadri.PointBlowup
end OAI.MaximalSeshadri.PointBlowup
namespace OAI.MaximalSeshadri.PointCoordinates
end OAI.MaximalSeshadri.PointCoordinates
namespace OAI.MaximalSeshadri.PrincipalSequence
end OAI.MaximalSeshadri.PrincipalSequence
namespace OAI.MaximalSeshadri.ProjBase
end OAI.MaximalSeshadri.ProjBase
namespace OAI.MaximalSeshadri.Projective
end OAI.MaximalSeshadri.Projective
namespace OAI.MaximalSeshadri.ProjectiveBertini
end OAI.MaximalSeshadri.ProjectiveBertini
namespace OAI.MaximalSeshadri.ProjectiveGeometry
end OAI.MaximalSeshadri.ProjectiveGeometry
namespace OAI.MaximalSeshadri.PullbackTensor
end OAI.MaximalSeshadri.PullbackTensor
namespace OAI.MaximalSeshadri.PushforwardTensor
end OAI.MaximalSeshadri.PushforwardTensor
namespace OAI.MaximalSeshadri.QuadraticJets
end OAI.MaximalSeshadri.QuadraticJets
namespace OAI.MaximalSeshadri.ReesGrading
end OAI.MaximalSeshadri.ReesGrading
namespace OAI.MaximalSeshadri.RestrictionCohomology
end OAI.MaximalSeshadri.RestrictionCohomology
namespace OAI.MaximalSeshadri.RestrictionExact
end OAI.MaximalSeshadri.RestrictionExact
namespace OAI.MaximalSeshadri.SchematicExt
end OAI.MaximalSeshadri.SchematicExt
namespace OAI.MaximalSeshadri.SchemeBertini
end OAI.MaximalSeshadri.SchemeBertini
namespace OAI.MaximalSeshadri.SectionOpens
end OAI.MaximalSeshadri.SectionOpens
namespace OAI.MaximalSeshadri.SpecMaps
end OAI.MaximalSeshadri.SpecMaps
namespace OAI.MaximalSeshadri.Tensor
end OAI.MaximalSeshadri.Tensor
namespace OAI.MaximalSeshadri.TensorLocalization
end OAI.MaximalSeshadri.TensorLocalization
namespace OAI.MaximalSeshadri.TensorPure
end OAI.MaximalSeshadri.TensorPure
namespace OAI.MaximalSeshadri.TildeExact
end OAI.MaximalSeshadri.TildeExact
namespace OAI.MaximalSeshadri.TildeFlasque
end OAI.MaximalSeshadri.TildeFlasque
namespace OAI.MaximalSeshadri.UnitEndomorphism
end OAI.MaximalSeshadri.UnitEndomorphism
section
namespace OAI

section
noncomputable section

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}

def openScalars (g : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) : K →+* Γ(X, U) :=
  (g.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

end
end MaximalSeshadri.ProjectiveBertini

end
end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R] [IsDomain R]

end

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped nonZeroDivisors
open MvPolynomial
variable {R σ : Type*} [CommRing R] [Fintype σ]

def homogeneousLinearForm (v : σ → R) : MvPolynomial σ R :=
  ∑ i, C (v i) * X i

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped nonZeroDivisors
open MvPolynomial
variable {R σ : Type*} [CommRing R] [Fintype σ]

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped nonZeroDivisors
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {R σ : Type*} [CommRing R] [IsDomain R] [Fintype σ]

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct nonZeroDivisors

end
end MaximalSeshadri.BertiniIntegral

end

end OAI
end

section
namespace OAI

section
noncomputable section

section
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

def freeUnitIso {C : Type} [Category.{0} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{0}) [HasColimits (SheafOfModules R)] :
    SheafOfModules.free (R := R) PUnit.{1} ≅ SheafOfModules.unit R := by
  change (∐ fun _ : PUnit.{1} => SheafOfModules.unit R) ≅ SheafOfModules.unit R
  refine
    { hom := Sigma.desc (fun _ => 𝟙 _)
      inv := Sigma.ι (fun _ : PUnit.{1} => SheafOfModules.unit R) PUnit.unit
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  ·
    apply Sigma.hom_ext
    intro i
    cases i
    rw [Sigma.ι_desc_assoc]
    change 𝟙 (SheafOfModules.unit R) ≫
      Sigma.ι (fun _ : PUnit.{1} => SheafOfModules.unit R) PUnit.unit =
      Sigma.ι (fun _ : PUnit.{1} => SheafOfModules.unit R) PUnit.unit ≫
        𝟙 (∐ fun _ : PUnit.{1} => SheafOfModules.unit R)
    simp only [Category.id_comp, Category.comp_id]
  · simp

variable {X : Scheme.{0}}

def overFrame {M : X.Modules} {U : X.Opens}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e ≪≫
      (Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm)

variable {C : Type} [Category.{0} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{0}} [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat]

def frameGenerators {M : SheafOfModules R} (e : M ≅ SheafOfModules.unit R) :
    M.GeneratingSections where
  I := PUnit.{1}
  s := M.freeHomEquiv ((freeUnitIso R).hom ≫ e.inv)
  epi := by
    rw [Equiv.symm_apply_apply]
    infer_instance

instance frameGenerators_finite {M : SheafOfModules R}
    (e : M ≅ SheafOfModules.unit R) : (frameGenerators e).IsFiniteType where
  finite := inferInstanceAs (Finite PUnit.{1})

instance frameGenerators_isIso {M : SheafOfModules R}
    (e : M ≅ SheafOfModules.unit R) : IsIso (frameGenerators e).π := by
  change IsIso ((M.freeHomEquiv (I := PUnit.{1})).symm
    (M.freeHomEquiv ((freeUnitIso R).hom ≫ e.inv)))
  rw [Equiv.symm_apply_apply]
  infer_instance

def LineBundle.localGenerators (L : LineBundle X) : L.sheaf.LocalGeneratorsData where
  I := X
  X x := (L.locallyRankOne x).choose
  coversTop := by
    rw [Opens.coversTop_iff, IsOpenCover]
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, (L.locallyRankOne x).choose_spec.1⟩
  generators x := frameGenerators (overFrame (L.locallyRankOne x).choose_spec.2.some)

instance LineBundle.localGenerators_locallyFree (L : LineBundle X) :
    L.localGenerators.IsLocallyFreeData where
  isIso _x := frameGenerators_isIso _

instance LineBundle.locallyFree (L : LineBundle X) : L.sheaf.IsLocallyFree :=
  L.localGenerators.isLocallyFree

instance LineBundle.quasicoherent (L : LineBundle X) : L.sheaf.IsQuasicoherent :=
  L.localGenerators.quasiCoherentData.isQuasicoherent

end
end MaximalSeshadri.Geometry
end

end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.AdicInjective
noncomputable section
universe u v
variable {R : Type u} [CommRing R]
variable (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

def adicTorsion : Submodule R M :=
  ⨆ n : ℕ, Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R)

lemma torsion_mono : Monotone (fun n : ℕ => Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R)) :=
  fun a b hab => Submodule.torsionBySet_le_torsionBySet_pow a b hab I

lemma mem_adicTorsion (x : M) : x ∈ adicTorsion I M ↔
    ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0 := by
  rw [adicTorsion, Submodule.mem_iSup_of_directed _ (torsion_mono I M).directed_le]
  simp only [Submodule.mem_torsionBySet_iff, Subtype.forall, SetLike.mem_coe]

lemma fg_uniform_exponent (N : Submodule R M) (hN : N.FG)
    (h : N ≤ adicTorsion I M) :
    ∃ n : ℕ, N ≤ Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R) := by
  classical
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup (Submodule R M)
    ((Submodule.fg_iff_compact N).mp hN)
    (fun n : ℕ => Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R)) h
  refine ⟨s.sup id, hs.trans (iSup_le fun n => iSup_le fun hn => ?_)⟩
  exact torsion_mono I M (Finset.le_sup (f := id) hn)

lemma exists_power_inf_le [IsNoetherianRing R] (J : Ideal R) (n : ℕ) :
    ∃ m : ℕ, I ^ m ⊓ J ≤ I ^ n * J := by
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (M := R) J
  refine ⟨k+n, ?_⟩
  have h := hk (k+n) (Nat.le_add_right _ _)
  simp only [Ideal.smul_eq_mul, Ideal.mul_top, Nat.add_sub_cancel_left] at h
  rw [h]
  exact Ideal.mul_mono le_rfl inf_le_right

theorem adicTorsion_injective [IsNoetherianRing R] [Small.{v} R]
    [Module.Injective R M] : Module.Injective R (adicTorsion I M) := by
  apply Module.Baer.injective
  intro J g
  let g₀ : J →ₗ[R] M := (adicTorsion I M).subtype.comp g
  have hg₀ : g₀.range ≤ adicTorsion I M := by
    rintro x ⟨y, rfl⟩
    exact (g y).property
  obtain ⟨n, hn⟩ := fg_uniform_exponent I M g₀.range (Submodule.fg_range g₀) hg₀
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R M J R
    J.subtype Subtype.val_injective g₀
  have hj : ∀ x : J, h x = g₀ x := fun x => LinearMap.congr_fun hh x
  have hzero : I ^ n * J ≤ h.ker := by
    apply Ideal.mul_le.mpr
    intro a ha b hb
    change h (a * b) = 0
    rw [← smul_eq_mul, h.map_smul, hj ⟨b, hb⟩]
    exact (Submodule.mem_torsionBySet_iff _ _).mp (hn (LinearMap.mem_range_self g₀ ⟨b,hb⟩)) ⟨a,ha⟩
  obtain ⟨m, hm⟩ := exists_power_inf_le I J n
  let f : R →ₗ.[R] M := ⟨J, g₀⟩
  let z : R →ₗ.[R] M := ⟨I ^ m, 0⟩
  have hz : ∀ (x : f.domain) (y : z.domain), (x : R) = y → f x = z y := by
    intro x y hxy
    change g₀ x = 0
    rw [← hj x]
    exact hzero (hm ⟨hxy ▸ y.property, x.property⟩)
  let F := f.sup z hz
  obtain ⟨H, hH⟩ := Module.Injective.extension_property R M F.domain R
    F.domain.subtype Subtype.val_injective F.toFun
  have HF : ∀ x : F.domain, H x = F x := fun x => LinearMap.congr_fun hH x
  have HJ : ∀ x : J, H x = g₀ x := by
    intro x
    rw [HF ⟨x, (show J ≤ J ⊔ I ^ m from le_sup_left) x.property⟩]
    exact ((f.left_le_sup z hz).2 (x := x) (y := ⟨x, (show J ≤ J ⊔ I ^ m from le_sup_left) x.property⟩) rfl).symm
  have HI : ∀ a ∈ I ^ m, H a = 0 := by
    intro a ha
    rw [HF ⟨a, (show I ^ m ≤ J ⊔ I ^ m from le_sup_right) ha⟩]
    exact ((f.right_le_sup z hz).2 (x := ⟨a,ha⟩) (y := ⟨a,(show I ^ m ≤ J ⊔ I ^ m from le_sup_right) ha⟩) rfl).symm
  have Hmem : ∀ a, H a ∈ adicTorsion I M := by
    intro a
    apply (mem_adicTorsion I M _).mpr
    refine ⟨m, fun b hb => ?_⟩
    rw [← H.map_smul]
    exact HI (b * a) ((I ^ m).mul_mem_right a hb)
  refine ⟨H.codRestrict (adicTorsion I M) Hmem, ?_⟩
  intro x hx
  apply Subtype.ext
  exact HJ ⟨x,hx⟩

end
end MaximalSeshadri.AdicInjective

namespace MaximalSeshadri.InjectiveRange
noncomputable section
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Small.{v} R]
variable {N : Type w} [AddCommGroup N] [Module R N] [Small.{w} R]

omit [Small.{w} R] in

lemma injective_of_retract [Module.Injective R M]
    (i : N →ₗ[R] M) (p : M →ₗ[R] N) (h : p.comp i = LinearMap.id) :
    Module.Injective R N := by
  apply Module.Baer.injective
  intro J g
  obtain ⟨f, hf⟩ := Module.Baer.of_injective (R := R) (Q := M) inferInstance J (i.comp g)
  refine ⟨p.comp f, fun x hx => ?_⟩
  change p (f x) = g ⟨x,hx⟩
  rw [hf x hx]
  exact LinearMap.congr_fun h (g ⟨x,hx⟩)

omit [Small.{w} R] in
lemma range_injective (r : M →ₗ[R] N) [Module.Injective R M]
    [Module.Injective R r.ker] : Module.Injective R r.range := by
  obtain ⟨p, hp⟩ := Module.Injective.extension_property R r.ker r.ker M
    r.ker.subtype Subtype.val_injective LinearMap.id
  let f : M →ₗ[R] M := LinearMap.id - r.ker.subtype.comp p
  have hf : r.ker ≤ f.ker := by
    intro x hx
    change x - (p x : M) = 0
    have hpx := LinearMap.congr_fun hp ⟨x,hx⟩
    exact sub_eq_zero.mpr (congrArg Subtype.val hpx).symm
  let i : r.range →ₗ[R] M := (r.ker.liftQ f hf).comp r.quotKerEquivRange.symm.toLinearMap
  apply injective_of_retract i r.rangeRestrict
  ext y
  rcases y with ⟨y,hy⟩
  obtain ⟨x,rfl⟩ := hy
  change r ((r.ker.liftQ f hf) (r.quotKerEquivRange.symm ⟨r x, LinearMap.mem_range_self r x⟩)) = r x
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  change r (x - (p x : M)) = r x
  rw [map_sub, (p x).property, sub_zero]

lemma surjective_of_torsion_cokernel (I : Ideal R) (r : M →ₗ[R] N)
    [Module.Injective R M] [Module.Injective R r.ker]
    (hc : ∀ y : N, ∃ n : ℕ, ∀ a ∈ I ^ n, a • y ∈ r.range)
    (ht : ∀ y : N, (∃ n : ℕ, ∀ a ∈ I ^ n, a • y = 0) → y = 0) :
    Function.Surjective r := by
  let : Module.Injective R r.range := range_injective r
  obtain ⟨p, hp⟩ := Module.Injective.extension_property R r.range r.range N
    r.range.subtype Subtype.val_injective LinearMap.id
  intro y
  suffices h : y = (p y : N) from h ▸ (p y).property
  apply sub_eq_zero.mp
  apply ht
  obtain ⟨n, hn⟩ := hc y
  refine ⟨n, fun a ha => ?_⟩
  rw [smul_sub]
  have h := congrArg Subtype.val (LinearMap.congr_fun hp ⟨a • y, hn a ha⟩)
  change (p (a • y) : N) = a • y at h
  rw [map_smul] at h
  exact sub_eq_zero.mpr h.symm

end
end MaximalSeshadri.InjectiveRange

noncomputable section
universe u
open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
open PrimeSpectrum

end
end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section
section
noncomputable section
universe u
open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
open PrimeSpectrum
namespace MaximalSeshadri.AffineDenominators
variable {R : CommRingCat.{u}} (M : (Spec R).Modules)

private def basicOpen (element : R) : (Spec R).Opens := PrimeSpectrum.basicOpen element

private lemma basicOpen_mul (left right : R) :
    basicOpen (left * right) = basicOpen left ⊓ basicOpen right :=
  PrimeSpectrum.basicOpen_mul left right

private lemma basicOpen_mul_le_left (left right : R) :
    basicOpen (left * right) ≤ basicOpen left :=
  PrimeSpectrum.basicOpen_mul_le_left left right

private lemma basicOpen_mul_le_right (left right : R) :
    basicOpen (left * right) ≤ basicOpen right :=
  PrimeSpectrum.basicOpen_mul_le_right left right

private lemma moduleIsSheaf :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology (Spec R)) M.presheaf :=
  M.isSheaf

structure Aux (V : (Spec R).Opens) where
  existence (f : R) (hf : basicOpen f ≤ V) (s : Γ(M, basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, V)), M.presheaf.map (homOfLE hf).op t = f ^ n • s
  uniqueness (f : R) (hf : basicOpen f ≤ V) (t : Γ(M, V)) :
    M.presheaf.map (.op <| homOfLE hf) t = (0 : Γ(M, basicOpen f)) →
    ∃ (n : ℕ), f ^ n • t = 0

lemma Aux.of_le {M : (Spec R).Modules} {V : (Spec R).Opens} (g : R) (hg : basicOpen g ≤ V)
    (hV : Aux M V) :
    Aux M (basicOpen g) where
  existence f hfg s := by
    obtain ⟨n, t, ht⟩ := hV.existence f (le_trans hfg hg) s
    use n, M.presheaf.map (homOfLE hg).op t
    simp [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, ht]
  uniqueness f hfg t ht := by
    obtain ⟨n, t', ht'⟩ := hV.existence g hg t
    obtain ⟨m, hm⟩ := hV.uniqueness _ (le_trans hfg hg) t' <| by
      rw [← homOfLE_comp hfg hg, op_comp, M.presheaf.map_comp_apply, ht', M.map_smul_Spec, ht]
      simp
    refine ⟨m, ((M.isSMulRegular_of_le_basicOpen (U := basicOpen g) (f := g)
      le_rfl).pow n).right_eq_zero_of_smul ?_⟩
    simp [smul_comm, ← ht', ← M.map_smul_Spec, hm]

lemma Aux.of_eq_iSup_basicOpen {M : (Spec R).Modules} (V : (Spec R).Opens)
    {ι : Type*} [Finite ι] (g : ι → R) (hg : V = ⨆ i, basicOpen (g i))
    (h₁ : ∀ (i : ι), Aux M (basicOpen (g i))) :
    Aux M V := by
  have h₂ (i j : ι) : Aux M (basicOpen (g i * g j)) :=
    .of_le _ (basicOpen_mul_le_left _ _) (h₁ i)
  have hgle (i : ι) : basicOpen (g i) ≤ V := by rw [hg]; exact le_iSup_of_le _ le_rfl
  have hug (i : ι) (m : ℕ) :
      IsUnit (algebraMap R (Module.End R Γ(M, basicOpen (g i))) (g i ^ m)) := by
    rw [map_pow]
    exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (g i) le_rfl).pow m

  refine ⟨fun f hf s ↦ ?_, fun f hf t hs ↦ ?_⟩
  · have hfgi (i : ι) : basicOpen (f * g i) ≤ basicOpen (g i) := basicOpen_mul_le_right f (g i)
    let s' (i : ι) : Γ(M, basicOpen (f * g i)) :=
      M.presheaf.map (homOfLE <| basicOpen_mul_le_left f (g i)).op s

    obtain ⟨N, t, ht⟩ : ∃ (N : ℕ) (t : ∀ i, Γ(M, basicOpen (g i))),
        ∀ i, f ^ N • s' i = M.presheaf.map (homOfLE (basicOpen_mul_le_right f (g i))).op (t i) := by
      have (i : ι) : ∃ (n : ℕ) (t : Γ(M, basicOpen (g i))),
          f ^ n • s' i = M.presheaf.map (homOfLE (hfgi i)).op t := by
        obtain ⟨n, t', ht'⟩ := (h₁ i).existence (f * g i) (hfgi i) (s' i)
        rw [mul_pow, mul_smul, smul_comm] at ht'
        obtain ⟨ψ, hψ⟩ := IsUnit.exists_right_inv (hug i n)
        use n, ψ t'
        apply (M.isSMulRegular_of_le_basicOpen (U := basicOpen (f * g i))
          (basicOpen_mul_le_right f (g i))).pow n
        dsimp
        rw [← ht', ← Scheme.Modules.map_smul_Spec]
        congr 1
        exact congr($hψ t').symm
      choose n t' ht' using this
      have (i : ι) : n i ≤ ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have hN (i : ι) : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by grind
      refine ⟨⨆ i, n i, fun i ↦ f ^ ((⨆ i, n i) - n i) • t' i, fun i ↦ ?_⟩
      conv_lhs => rw [hN i]
      rw [pow_add, mul_smul, ht', M.map_smul_Spec]

    obtain ⟨K, hK⟩ : ∃ (K : ℕ), ∀ (i j : ι),
        M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (f ^ K • t i) =
          M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (f ^ K • t j) := by
      have (i j : ι) : ∃ (m : ℕ),
          M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (f ^ m • t i) =
            M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (f ^ m • t j) := by
        have := (h₂ i j).uniqueness (f * (g i * g j)) (basicOpen_mul_le_right _ _)
          (M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (t i) -
            M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (t j)) ?_
        · obtain ⟨m, hm⟩ := this
          use m
          apply (M.isSMulRegular_of_le_basicOpen (U := basicOpen (g i * g j))
            (f := g i * g j) le_rfl).pow m
          simpa [M.map_smul_Spec _ (f ^ m), ← mul_smul, ← mul_smul, ← mul_pow, ← mul_comm f,
            smul_sub, sub_eq_zero] using hm
        · have hfgigi : basicOpen (f * (g i * g j)) ≤ basicOpen (f * g i) := by
            rw [← mul_assoc]
            exact basicOpen_mul_le_left _ _
          have hfgigj : basicOpen (f * (g i * g j)) ≤ basicOpen (f * g j) := by
            rw [mul_comm (g i) (g j), ← mul_assoc]
            exact basicOpen_mul_le_left _ _
          rw [map_sub, ← M.presheaf.map_comp_apply, ← op_comp, ← M.presheaf.map_comp_apply,
            ← op_comp, homOfLE_comp, homOfLE_comp, ← homOfLE_comp hfgigi (hfgi i),
            ← homOfLE_comp hfgigj (hfgi j), op_comp, M.presheaf.map_comp_apply, ← ht i,
            M.map_smul_Spec, ← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, op_comp,
            M.presheaf.map_comp_apply, ← ht j, M.map_smul_Spec, ← M.presheaf.map_comp_apply,
            ← op_comp, homOfLE_comp]
          simp
      choose m hm using this
      let K := ⨆ i, ⨆ j, m i j
      refine ⟨K, fun i j ↦ ?_⟩
      have : m i j ≤ K :=
        le_ciSup_of_le (Finite.bddAbove_range _) i (le_ciSup (Finite.bddAbove_range _) _)
      have : K = (K - m i j) + m i j := by lia
      rw [this, pow_add, mul_smul, mul_smul, M.map_smul_Spec, M.map_smul_Spec _ (f ^ (K - m i j)),
        hm i j]

    refine ⟨N + K, ?_⟩
    have := TopCat.Sheaf.existsUnique_gluing' ⟨_, moduleIsSheaf M⟩ (fun i ↦ basicOpen (g i)) V
      (fun i ↦ homOfLE (by rw [hg]; exact le_iSup_of_le _ le_rfl)) (by simp [hg])
      (fun i ↦ f ^ K • t i) ?_
    · obtain ⟨a, ha, -⟩ := this
      use a
      refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, moduleIsSheaf M⟩ (fun i ↦ basicOpen (f * g i)) _
          (fun i ↦ homOfLE (basicOpen_mul_le_left f (g i))) ?_ _ _ ?_
      · rw [left_eq_inf.mpr hf, hg, inf_iSup_eq]
        simp_rw [basicOpen_mul]
        exact le_rfl
      · intro i
        rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp (basicOpen_mul_le_right _ _) (hgle i), op_comp, M.presheaf.map_comp_apply,
          M.map_smul_Spec, ha, M.map_smul_Spec, pow_add, mul_smul, smul_comm, ht i]
    · intro i j
      have : Function.Injective (M.presheaf.map (eqToHom <| (basicOpen_mul (g i) (g j))).op) :=
        ConcreteCategory.injective_of_mono_of_preservesPullback _
      apply this
      dsimp [Opens.infLELeft, Opens.infLERight]
      simp_rw [← M.presheaf.map_comp_apply, ← op_comp, eqToHom_comp_homOfLE]
      exact hK i j
  · have (i : ι) : ∃ (n : ℕ), M.presheaf.map (homOfLE (hgle i)).op (f ^ n • t) = 0 := by
      have := (h₁ i).uniqueness (f * g i) (basicOpen_mul_le_right f (g i))
        (M.presheaf.map (homOfLE (hgle i)).op t) ?_
      · obtain ⟨n, hn⟩ := this
        use n
        rw [mul_pow, mul_comm, mul_smul, ← Scheme.Modules.map_smul_Spec] at hn
        exact ((M.isSMulRegular_of_le_basicOpen (U := basicOpen (g i))
          (f := g i) le_rfl).pow n).right_eq_zero_of_smul hn
      · rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp ((basicOpen_mul_le_left f (g i))) hf, op_comp, M.presheaf.map_comp_apply]
        simp [hs]
    choose n hn using this
    use ⨆ i, n i
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, moduleIsSheaf M⟩ (fun i ↦ basicOpen (g i)) _
      (fun i ↦ homOfLE (by rw [hg]; exact le_iSup_of_le _ le_rfl))
    · simp [hg]
    · intro i
      have : n i ≤ ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by lia
      rw [this, pow_add, mul_smul, Scheme.Modules.map_smul_Spec, hn i]
      simp

lemma isLocalizing_iff_aux (M : (Spec R).Modules) :
    IsLocalizing (modulesSpecToSheaf.obj M) ↔ Aux M ⊤ := by
  let φ (f : R) := ((modulesSpecToSheaf.obj M).obj.map (basicOpen f).leTop.op).hom
  refine ⟨fun h ↦ ?_, fun h f ↦ IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_⟩
  · have hf (f : R) : IsLocalizedModule.Away f (φ f) := h f
    refine ⟨fun f hle s ↦ ?_, fun f hle s hs ↦ ?_⟩
    · obtain ⟨n, y, hy⟩ := (hf f).surj _ _ s
      use n, y, hy.symm
    · obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers f) (φ f)).mp hs
      use n, hn
  · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl
  · intro x
    obtain ⟨n, t, ht⟩ := h.existence f le_top x
    use n, t, ht.symm
  · intro x hx
    obtain ⟨n, hn⟩ := h.uniqueness _ _ _ hx
    use n, hn

theorem aux_of_isCompact (V : (Spec R).Opens) (hV : IsCompact (V : Set (Spec R)))
    (h : IsLocalizing (modulesSpecToSheaf.obj M)) : Aux M V := by
  obtain ⟨ι, hι, g, hg⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact V hV
  let := hι
  exact Aux.of_eq_iSup_basicOpen V g hg (fun i =>
    Aux.of_le (g i) le_top ((isLocalizing_iff_aux M).mp h))

variable {M}

def res (U V : (Spec R).Opens) (h : U ≤ V) : Γ(M,V) →ₗ[R] Γ(M,U) :=
  ((modulesSpecToSheaf.obj M).obj.map (homOfLE h).op).hom

lemma res_comp {U V W : (Spec R).Opens} (h : U ≤ V) (k : V ≤ W) (s : Γ(M,W)) :
    res U V h (M := M) (res V W k s) = res U W (h.trans k) s := by
  exact (M.presheaf.map_comp_apply (homOfLE k).op (homOfLE h).op s).symm

lemma eq_zero_of_cover {ι : Type*} (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, basicOpen (g i)) (s : Γ(M,U))
    (h : ∀ i, res (basicOpen (g i)) U (hU ▸ le_iSup_of_le i le_rfl) s = 0) : s = 0 := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, moduleIsSheaf M⟩ (fun i => basicOpen (g i)) U
    (fun i => homOfLE (hU ▸ le_iSup_of_le i le_rfl)) (by rw [hU])
  intro i
  change res (basicOpen (g i)) U _ s = res (basicOpen (g i)) U _ 0
  rw [map_zero]
  exact h i

lemma power_in_ideal_of_generator_powers {ι : Type*} [Finite ι]
    (g : ι → R) (J : Ideal R) (h : ∀ i, ∃ n : ℕ, g i ^ n ∈ J) :
    ∃ n : ℕ, Ideal.span (Set.range g) ^ n ≤ J := by
  apply Ideal.exists_pow_le_of_le_radical_of_fg
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact h i
  · exact Submodule.fg_span (Set.finite_range g)

lemma kernel_is_torsion {ι : Type*} [Finite ι] (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, basicOpen (g i))
    (hloc : IsLocalizing (modulesSpecToSheaf.obj M)) (s : Γ(M,⊤))
    (hs : res U ⊤ le_top s = 0) :
    ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n, a • s = 0 := by
  let J : Ideal R := (LinearMap.toSpanSingleton R Γ(M,⊤) s).ker
  have hgen : ∀ i, ∃ n : ℕ, g i ^ n ∈ J := by
    intro i
    apply ((isLocalizing_iff_aux M).mp hloc).uniqueness (g i) le_top s
    change res (basicOpen (g i)) ⊤ le_top s = 0
    rw [← res_comp (hU ▸ le_iSup_of_le i le_rfl) le_top, hs, map_zero]
  obtain ⟨n,hn⟩ := power_in_ideal_of_generator_powers g J hgen
  exact ⟨n,fun a ha => hn ha⟩

lemma torsion_free {ι : Type*} (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, basicOpen (g i)) (s : Γ(M,U))
    (hs : ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n, a • s = 0) : s = 0 := by
  obtain ⟨n,hn⟩ := hs
  apply eq_zero_of_cover g U hU s
  intro i
  have hm : g i ^ n ∈ Ideal.span (Set.range g) ^ n :=
    Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) n
  have h := congrArg (res (basicOpen (g i)) U (hU ▸ le_iSup_of_le i le_rfl)) (hn _ hm)
  rw [map_smul, map_zero] at h
  exact ((M.isSMulRegular_of_le_basicOpen (U := basicOpen (g i))
    (f := g i) le_rfl).pow n).right_eq_zero_of_smul h

lemma torsion_in_kernel {ι : Type*} (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, basicOpen (g i)) (s : Γ(M,⊤))
    (hs : ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n, a • s = 0) :
    res U ⊤ le_top s = 0 := by
  apply torsion_free g U hU
  obtain ⟨n,hn⟩ := hs
  refine ⟨n,fun a ha => ?_⟩
  rw [← map_smul, hn a ha, map_zero]

lemma cokernel_is_torsion {ι : Type*} [Finite ι] (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, basicOpen (g i)) (hU' : IsCompact (U : Set (Spec R)))
    (hloc : IsLocalizing (modulesSpecToSheaf.obj M)) (s : Γ(M,U)) :
    ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n,
      a • s ∈ (res U ⊤ le_top (M := M)).range := by
  let J : Ideal R := (res U ⊤ le_top (M := M)).range.comap
    (LinearMap.toSpanSingleton R Γ(M,U) s)
  have hgen : ∀ i, ∃ n : ℕ, g i ^ n ∈ J := by
    intro i
    let hgi : basicOpen (g i) ≤ U := hU ▸ le_iSup_of_le i le_rfl
    obtain ⟨m,t,ht⟩ := ((isLocalizing_iff_aux M).mp hloc).existence (g i) le_top
      (res (basicOpen (g i)) U hgi s)
    have hzero : res (basicOpen (g i)) U hgi (res U ⊤ le_top t - g i ^ m • s) = 0 := by
      rw [map_sub, map_smul, res_comp]
      exact sub_eq_zero.mpr ht
    obtain ⟨n,hn⟩ := (aux_of_isCompact M U hU' hloc).uniqueness (g i) hgi _ hzero
    refine ⟨n+m, ?_⟩
    change g i ^ (n+m) • s ∈ (res U ⊤ le_top (M := M)).range
    refine ⟨g i ^ n • t, ?_⟩
    rw [map_smul, pow_add, mul_smul]
    exact sub_eq_zero.mp (by simpa only [smul_sub] using hn)
  obtain ⟨n,hn⟩ := power_in_ideal_of_generator_powers g J hgen
  exact ⟨n,fun a ha => hn ha⟩

end MaximalSeshadri.AffineDenominators

end

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial

variable {σ R : Type*} [CommRing R]

abbrev JetIndex (σ : Type*) (n : ℕ) := {d : σ →₀ ℕ // d.degree < n}

instance jetIndexFinite [Finite σ] (n : ℕ) : Finite (JetIndex σ n) :=
  (Finsupp.finite_of_degree_lt n).to_subtype

def polynomialJetCoeffs (n : ℕ) : MvPolynomial σ R →ₗ[R] (JetIndex σ n → R) where
  toFun polynomial index := polynomial.coeff index.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

lemma polynomialJetCoeffs_ker (n : ℕ) :
    (polynomialJetCoeffs (σ := σ) (R := R) n).ker =
      ((idealOfVars σ R) ^ n).restrictScalars R := by
  ext p
  rw [LinearMap.mem_ker, funext_iff]
  change (∀ index : JetIndex σ n, p.coeff index.val = 0) ↔ _
  rw [Submodule.restrictScalars_mem, mem_pow_idealOfVars_iff']
  exact ⟨fun h d hd => h ⟨d, hd⟩, fun h d => h d.val d.property⟩

lemma polynomialJetCoeffs_surjective [Finite σ] (n : ℕ) :
    Function.Surjective (polynomialJetCoeffs (σ := σ) (R := R) n) := by
  classical
  let : Fintype (JetIndex σ n) := Fintype.ofFinite _
  intro a
  refine ⟨∑ d : JetIndex σ n, monomial d.val (a d), ?_⟩
  ext e
  change (∑ index : JetIndex σ n, monomial index.val (a index)).coeff e.val = a e
  simp only [coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single e]
  · simp
  · intro d _ hde
    rw [ite_eq_right (fun equality => hde (Subtype.ext equality))]
  · simp

def polynomialJetEquiv [Finite σ] (n : ℕ) :
    (MvPolynomial σ R ⧸ (idealOfVars σ R) ^ n) ≃ₗ[R] (JetIndex σ n → R) := by
  let e := LinearMap.quotKerEquivOfSurjective
    (polynomialJetCoeffs (σ := σ) (R := R) n) (polynomialJetCoeffs_surjective n)
  exact (Submodule.quotEquivOfEq _ _ (polynomialJetCoeffs_ker n).symm).trans e

end

noncomputable section
open MvPolynomial
variable {σ R : Type*} [CommRing R]

@[simp] lemma polynomialJetEquiv_mk [Finite σ] (n : ℕ)
    (p : MvPolynomial σ R) (d : JetIndex σ n) :
    polynomialJetEquiv (σ := σ) (R := R) n (Ideal.Quotient.mk _ p) d =
      p.coeff d.val := rfl

end

noncomputable section
open MvPolynomial

variable {σ R : Type*} [CommRing R]

abbrev JetAlgebra (σ R : Type*) [CommRing R] (n : ℕ) :=
  MvPolynomial σ R ⧸ (idealOfVars σ R) ^ n

def jetAugment (n : ℕ) (hn : 0 < n) : JetAlgebra σ R n →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (aeval (fun _ : σ => (0 : R))) (by
    intro p hp
    have hc := (mem_pow_idealOfVars_iff' n p).mp hp 0 (by simpa using hn)
    simpa [aeval_def, eval_zero, constantCoeff_eq] using hc)

end

noncomputable section
open MvPolynomial

variable {σ F S B : Type*} [CommRing F] [CommRing S] [Algebra F S]
  [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

end

noncomputable section
open MvPolynomial

variable {σ F R S : Type*} [CommRing F] [CommRing R] [CommRing S]
  [Algebra F R] [Algebra F S]

lemma map_idealOfVars (φ : R →ₐ[F] S) :
    (idealOfVars σ R).map (MvPolynomial.map φ.toRingHom) = idealOfVars σ S := by
  rw [idealOfVars, Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (MvPolynomial.map_X φ.toRingHom i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨X i, ⟨i, rfl⟩, MvPolynomial.map_X φ.toRingHom i⟩

def mapJetAlgebra (φ : R →ₐ[F] S) (n : ℕ) :
    JetAlgebra σ R n →ₐ[F] JetAlgebra σ S n :=
  Ideal.quotientMapₐ _ (MvPolynomial.mapAlgHom φ) (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    change ((idealOfVars σ R).map (MvPolynomial.map φ.toRingHom)) ^ n ≤ _
    rw [map_idealOfVars])

@[simp] lemma mapJetAlgebra_mk (φ : R →ₐ[F] S) (n : ℕ) (p : MvPolynomial σ R) :
    mapJetAlgebra (σ := σ) φ n (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map φ.toRingHom p) := rfl

end
end MaximalSeshadri.AlgebraicJets

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri
open scoped BigOperators Topology
open Filter Set

abbrev Exponent := ℕ × ℕ

noncomputable def monomialDeriv (n a : ℕ) (x : ℂ) : ℂ :=
  (n.descFactorial a : ℂ) * x ^ (n - a)

lemma monomialDeriv_eq (n a : ℕ) :
    monomialDeriv n a = iteratedDeriv a (fun x : ℂ => x ^ n) := by
  ext x
  simp only [monomialDeriv, iteratedDeriv_pow]

lemma deriv_monomialDeriv (n a : ℕ) :
    deriv (monomialDeriv n a) = monomialDeriv n (a + 1) := by
  simp only [monomialDeriv_eq, iteratedDeriv_succ]

lemma differentiable_monomialDeriv (n a : ℕ) :
    Differentiable ℂ (monomialDeriv n a) := by
  unfold monomialDeriv
  fun_prop

noncomputable def seriesPartial (c : Exponent → ℂ) (a b : ℕ) (x z : ℂ) : ℂ :=
  ∑' p : Exponent, c p * monomialDeriv p.1 a x * monomialDeriv p.2 b z

noncomputable def seriesEval (c : Exponent → ℂ) (x z : ℂ) : ℂ :=
  ∑' p : Exponent, c p * x ^ p.1 * z ^ p.2

lemma seriesPartial_zero (c : Exponent → ℂ) : seriesPartial c 0 0 = seriesEval c := by
  ext x z
  simp [seriesPartial, seriesEval, monomialDeriv]

noncomputable def derivativeMajorant (c : Exponent → ℂ) (R : ℝ) (a b : ℕ)
    (p : Exponent) : ℝ :=
  ‖c p‖ * ((p.1.descFactorial a : ℝ) * R ^ (p.1 - a)) *
    ((p.2.descFactorial b : ℝ) * R ^ (p.2 - b))

def DerivativeSummable (c : Exponent → ℂ) (R : ℝ) : Prop :=
  ∀ a b : ℕ, Summable (derivativeMajorant c R a b)

lemma norm_monomialDeriv_le (n a : ℕ) (x : ℂ) (R : ℝ) (hx : ‖x‖ ≤ R) :
    ‖monomialDeriv n a x‖ ≤ (n.descFactorial a : ℝ) * R ^ (n - a) := by
  simp only [monomialDeriv, norm_mul, norm_natCast, norm_pow]
  gcongr

lemma norm_seriesTerm_le (c : Exponent → ℂ) (R : ℝ) (a b : ℕ) (p : Exponent)
    (x z : ℂ) (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    ‖c p * monomialDeriv p.1 a x * monomialDeriv p.2 b z‖ ≤
      derivativeMajorant c R a b p := by
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_monomialDeriv_le _ _ _ _ hx)
    (norm_nonneg _)) (norm_monomialDeriv_le _ _ _ _ hz) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg
      ((norm_nonneg x).trans hx) _)))

lemma deriv_seriesPartial_left (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ ≤ R) :
    deriv (fun w => seriesPartial c a b w z) x = seriesPartial c (a + 1) b x z := by
  have hsum := Complex.hasSum_deriv_of_summable_norm (hs a b)
    (U := Metric.ball (0 : ℂ) R)
    (F := fun p : Exponent => fun w : ℂ => c p * monomialDeriv p.1 a w *
      monomialDeriv p.2 b z)
    (fun p => ((differentiable_monomialDeriv p.1 a).const_mul (c p)).mul_const
      (monomialDeriv p.2 b z) |>.differentiableOn)
    Metric.isOpen_ball
    (fun p w hw => norm_seriesTerm_le c R a b p w z
      (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hw).le) hz)
    (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
  have he (p : Exponent) :
      deriv (fun w : ℂ => c p * monomialDeriv p.1 a w * monomialDeriv p.2 b z) x =
        c p * monomialDeriv p.1 (a + 1) x * monomialDeriv p.2 b z := by
    rw [deriv_mul_const_field, deriv_const_mul_field, deriv_monomialDeriv]
  simpa only [seriesPartial, he] using hsum.tsum_eq.symm

lemma deriv_seriesPartial_right (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ ≤ R) (hz : ‖z‖ < R) :
    deriv (fun w => seriesPartial c a b x w) z = seriesPartial c a (b + 1) x z := by
  have hsum := Complex.hasSum_deriv_of_summable_norm (hs a b)
    (U := Metric.ball (0 : ℂ) R)
    (F := fun p : Exponent => fun w : ℂ => c p * monomialDeriv p.1 a x *
      monomialDeriv p.2 b w)
    (fun p => ((differentiable_monomialDeriv p.2 b).const_mul
      (c p * monomialDeriv p.1 a x)).differentiableOn)
    Metric.isOpen_ball
    (fun p w hw => norm_seriesTerm_le c R a b p x w hx
      (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hw).le))
    (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  have he (p : Exponent) :
      deriv (fun w : ℂ => c p * monomialDeriv p.1 a x * monomialDeriv p.2 b w) z =
        c p * monomialDeriv p.1 a x * monomialDeriv p.2 (b + 1) z := by
    rw [deriv_const_mul_field, deriv_monomialDeriv]
  simpa only [seriesPartial, he] using hsum.tsum_eq.symm

lemma iteratedDeriv_series_left (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a : ℕ) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ < R) :
    iteratedDeriv a (fun w => seriesEval c w z) x = seriesPartial c a 0 x z := by
  induction a generalizing x with
  | zero => simp [← seriesPartial_zero]
  | succ a ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv a (fun w => seriesEval c w z) =ᶠ[𝓝 x]
        (fun w => seriesPartial c a 0 w z) := by
      filter_upwards [((continuous_norm.tendsto x).eventually (gt_mem_nhds hx))] with w hw
      exact ih w hw
    rw [he.deriv_eq]
    exact deriv_seriesPartial_left c R hs a 0 x z hx hz.le

lemma iteratedDeriv_series_right (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ < R) :
    iteratedDeriv b (fun w => seriesPartial c a 0 x w) z = seriesPartial c a b x z := by
  induction b generalizing z with
  | zero => rfl
  | succ b ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv b (fun w => seriesPartial c a 0 x w) =ᶠ[𝓝 z]
        (fun w => seriesPartial c a b x w) := by
      filter_upwards [((continuous_norm.tendsto z).eventually (gt_mem_nhds hz))] with w hw
      exact ih w hw
    rw [he.deriv_eq]
    exact deriv_seriesPartial_right c R hs a b x z hx.le hz

theorem mixedDeriv_seriesEval (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ < R) :
    iteratedDeriv b (fun v => iteratedDeriv a (fun u => seriesEval c u v) x) z =
      seriesPartial c a b x z := by
  have he : (fun v => iteratedDeriv a (fun u => seriesEval c u v) x) =ᶠ[𝓝 z]
      (fun v => seriesPartial c a 0 x v) := by
    filter_upwards [((continuous_norm.tendsto z).eventually (gt_mem_nhds hz))] with v hv
    exact iteratedDeriv_series_left c R hs a x v hx hv
  rw [he.iteratedDeriv_eq b]
  exact iteratedDeriv_series_right c R hs a b x z hx hz

def AbsolutelyConvergentAt (c : Exponent → ℂ) (R : ℝ) : Prop :=
  Summable (fun p : Exponent => ‖c p‖ * R ^ (p.1 + p.2))

def ConvergentSeries (c : Exponent → ℂ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ AbsolutelyConvergentAt c R

lemma descFactorial_radius_le (n a : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    (n.descFactorial a : ℝ) * ρ ^ (n - a) ≤
      (n : ℝ) ^ a * (ρ ^ n / ρ ^ a) := by
  by_cases h : a ≤ n
  · have he : ρ ^ (n - a) = ρ ^ n / ρ ^ a := by
      apply (eq_div_iff (pow_ne_zero _ hρ.ne')).2
      rw [← pow_add, Nat.sub_add_cancel h]
    rw [← he]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.descFactorial_le_pow n a)
      (pow_nonneg hρ.le _)
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero, zero_mul]
    positivity

theorem derivativeSummable_of_absolute (c : Exponent → ℂ) (R ρ : ℝ)
    (hR : 0 < R) (hρ : 0 < ρ) (hsmall : ρ < R)
    (hc : AbsolutelyConvergentAt c R) : DerivativeSummable c ρ := by
  let C : ℝ := ∑' p : Exponent, ‖c p‖ * R ^ (p.1 + p.2)
  have hC : 0 ≤ C := tsum_nonneg (fun p => by positivity)
  have hb (p : Exponent) : ‖c p‖ ≤ C / R ^ (p.1 + p.2) := by
    apply (le_div_iff₀ (pow_pos hR _)).2
    exact hc.le_tsum p (fun p _ => by positivity)
  have ht0 : 0 ≤ ρ / R := div_nonneg hρ.le hR.le
  have ht : ‖ρ / R‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht0]
    exact (div_lt_one hR).2 hsmall
  intro a b
  have hsum := ((summable_pow_mul_geometric_of_norm_lt_one a ht).mul_of_nonneg
    (summable_pow_mul_geometric_of_norm_lt_one b ht)
    (fun n => by positivity) (fun n => by positivity)).mul_left (C / (ρ ^ a * ρ ^ b))
  refine Summable.of_nonneg_of_le (fun p => by unfold derivativeMajorant; positivity)
    (fun p => ?_) hsum
  unfold derivativeMajorant
  calc
    _ ≤ (C / R ^ (p.1 + p.2)) *
        ((p.1 : ℝ) ^ a * (ρ ^ p.1 / ρ ^ a)) *
        ((p.2 : ℝ) ^ b * (ρ ^ p.2 / ρ ^ b)) := by
      apply mul_le_mul _ (descFactorial_radius_le p.2 b ρ hρ) (by positivity) (by positivity)
      exact mul_le_mul (hb p) (descFactorial_radius_le p.1 a ρ hρ)
        (by positivity) (by positivity)
    _ = C / (ρ ^ a * ρ ^ b) *
        ((p.1 : ℝ) ^ a * (ρ / R) ^ p.1 * ((p.2 : ℝ) ^ b * (ρ / R) ^ p.2)) := by
      rw [pow_add, div_pow, div_pow]
      ring

end MaximalSeshadri

end
end
end

end OAI
end


