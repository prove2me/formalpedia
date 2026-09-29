-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_dualNumber_kernel_equiv_addMonoidHom_intLattice_baseChange_of_surjective_of_ker_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/17b458bd-6dc2-51d3-8806-857b979e4fe5

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_LatticeHeckeFamily
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPoints_baseChange_surjective_and_fibre
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPoints_mul_mem_and_comp_mem
import Theorems.Thm_CuspForm_intLattice_free_and_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_dualNumber_kernel_equiv_addMonoidHom_intLattice_baseChange_of_surjective_of_ker_eq_span
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing CuspForm

namespace A2iPrime

universe u

theorem fstHom_toRingHom_eq (S A : Type*) [CommRing S] [CommRing A] [Algebra S A] :
    (TrivSqZeroExt.fstHom S A A).toRingHom = (TrivSqZeroExt.fstHom A A A).toRingHom := rfl

section Lattice

variable {S : Type*} [AddCommGroup S] [Module.Free ℤ S]
variable {R A : Type*} [CommRing R] [CommRing A]

theorem exists_lift (red : R →+* A) (hred : Function.Surjective red) (h : S →+ A) :
    ∃ h' : S →+ R, red.toAddMonoidHom.comp h' = h := by
  classical
  let b := Module.Free.chooseBasis ℤ S
  refine ⟨(b.constr ℤ fun i => (hred (h (b i))).choose).toAddMonoidHom, ?_⟩
  apply AddMonoidHom.toIntLinearMap_injective
  refine b.ext fun i => ?_
  simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_comp, Function.comp_apply,
    LinearMap.toAddMonoidHom_coe, Module.Basis.constr_basis, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
  exact (hred (h (b i))).choose_spec

theorem exists_eq_smul_of_forall_mem (π : R) (h : S →+ R) (hh : ∀ s, h s ∈ Ideal.span {π}) :
    ∃ v : S →+ R, h = π • v := by
  classical
  let b := Module.Free.chooseBasis ℤ S
  have hb : ∀ i, ∃ r, h (b i) = π * r := fun i => by
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hh (b i))
    exact ⟨r, by rw [← hr, mul_comm]⟩
  refine ⟨(b.constr ℤ fun i => (hb i).choose).toAddMonoidHom, ?_⟩
  apply AddMonoidHom.toIntLinearMap_injective
  refine b.ext fun i => ?_
  simp only [AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe, Module.Basis.constr_basis,
    AddMonoidHom.smul_apply, smul_eq_mul]
  exact (hb i).choose_spec

end Lattice

theorem beta_eq (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    (β : DualNumber R →+* DualNumber A)
    (h1 : β.comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber A))
    (h2 : β DualNumber.eps = DualNumber.eps) :
    β = (DualNumber.lift ⟨(Algebra.ofId R (DualNumber A), DualNumber.eps), DualNumber.eps_mul_eps,
      fun _ => Commute.all _ _⟩ : DualNumber R →ₐ[R] DualNumber A).toRingHom := by
  apply DualNumber.ringHom_ext
  · rw [h1]
    ext r
    · simp
    · simp
  · rw [h2]
    change DualNumber.eps = DualNumber.lift (R := R)
      ⟨(Algebra.ofId R (DualNumber A), DualNumber.eps), DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩
        DualNumber.eps
    rw [DualNumber.lift_apply_eps]

end A2iPrime

open A2iPrime in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) c)
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt p) c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase)
    (𝒱 : X.TwoAffineOpenCover)
    (φ : HeckeAlg → SchemeHomOver D.toBase D.toBase)

    (hφL : letI L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
      ∀ (t : HeckeAlg) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
        (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp (L.mul s x y) (φ t) =
        L.mul s (NeronModelInfra.schemeHomOverComp x (φ t)) (NeronModelInfra.schemeHomOverComp y (φ t)))
    (A : Type) [CommRing A] [Algebra ↥(GaloisRep.ratLocalizedAt p) A]
    (hA : Function.Surjective (algebraMap ↥(GaloisRep.ratLocalizedAt p) A))
    (hker : RingHom.ker (algebraMap ↥(GaloisRep.ratLocalizedAt p) A) =
      Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}) :
    letI L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
    letI := (CuspForm.latticeHeckeFamily N).module
    ∀ τ : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber ↥(GaloisRep.ratLocalizedAt p))))) D.toBase //
            Spec.map (CommRingCat.ofHom
                (TrivSqZeroExt.fstHom ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p)).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p))))).1} ≃
          (↥(CuspForm.intLattice N 2) →+ ↥(GaloisRep.ratLocalizedAt p)),
      (∀ x y z : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber ↥(GaloisRep.ratLocalizedAt p))))) D.toBase //
            Spec.map (CommRingCat.ofHom
                (TrivSqZeroExt.fstHom ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p)).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p))))).1},
          z.1 = L.mul _ x.1 y.1 → τ z = τ x + τ y) →
      (∀ (t : HeckeAlg) (x y : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber ↥(GaloisRep.ratLocalizedAt p))))) D.toBase //
            Spec.map (CommRingCat.ofHom
                (TrivSqZeroExt.fstHom ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p)).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p))))).1}),
          y.1.1 = x.1.1 ≫ (φ t).1 → ∀ g : ↥(CuspForm.intLattice N 2), τ y g = τ x (t • g)) →
      ∃ τk : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber A)))) D.toBase //
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) A)))).1} ≃
          (↥(CuspForm.intLattice N 2) →+ A),

        (∀ x y z : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber A)))) D.toBase //
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) A)))).1},
          z.1 = L.mul _ x.1 y.1 → τk z = τk x + τk y) ∧

        (∀ (β : DualNumber ↥(GaloisRep.ratLocalizedAt p) →+* DualNumber A)
          (x : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber ↥(GaloisRep.ratLocalizedAt p))))) D.toBase //
            Spec.map (CommRingCat.ofHom
                (TrivSqZeroExt.fstHom ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p)).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p))))).1})
          (xk : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber A)))) D.toBase //
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) A)))).1}),
          β.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber ↥(GaloisRep.ratLocalizedAt p))) = algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber A) →
          β DualNumber.eps = DualNumber.eps →
          xk.1.1 = Spec.map (CommRingCat.ofHom β) ≫ x.1.1 →
          ∀ g : ↥(CuspForm.intLattice N 2), τk xk g = algebraMap ↥(GaloisRep.ratLocalizedAt p) A (τ x g)) ∧

        (∀ (t : HeckeAlg) (x y : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber A)))) D.toBase //
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) A)))).1}),
          y.1.1 = x.1.1 ≫ (φ t).1 → ∀ g : ↥(CuspForm.intLattice N 2), τk y g = τk x (t • g)) := by
  intro τ hadd hhecke
  classical
  letI := (CuspForm.latticeHeckeFamily N).module

  obtain ⟨hfree, -⟩ := CuspForm.intLattice_free_and_finite N 2

  let R : Type := ↥(GaloisRep.ratLocalizedAt p)
  let L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
  let tR := Scheme.TwoAffineOpenCover.specMap R (DualNumber R)
  let tA := Scheme.TwoAffineOpenCover.specMap R (DualNumber A)
  let KR : Type := {x : SchemeHomOver tR D.toBase //
    dualNumberReduction R R ≫ x.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R R)).1}
  let KA : Type := {y : SchemeHomOver tA D.toBase //
    dualNumberReduction R A ≫ y.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R A)).1}
  let lam : DualNumber R →ₐ[R] DualNumber A :=
    DualNumber.lift ⟨(Algebra.ofId R (DualNumber A), DualNumber.eps), DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩
  let σ : Spec (CommRingCat.of (DualNumber A)) ⟶ Spec (CommRingCat.of (DualNumber R)) :=
    (RelPicard.LFP.stageHom R lam).1
  have hσ : σ ≫ tR = tA := (RelPicard.LFP.stageHom R lam).2

  obtain ⟨hres, hmul, hendo, hsurj, hfib⟩ :=
    AlgebraicGeometry.RelPicard.RepresentsRelSubPic.kerPoints_baseChange_surjective_and_fibre
      c ε D hD hsm hpr 𝒱 A hA p hker
  obtain ⟨hmulR, hcompR⟩ :=
    AlgebraicGeometry.RelPicard.RepresentsRelSubPic.kerPoints_mul_mem_and_comp_mem hD R

  let resV : KR → SchemeHomOver tA D.toBase := fun x => ⟨σ ≫ x.1.1, by rw [Category.assoc, x.1.2]; exact hσ⟩
  let res : KR → KA := fun x => ⟨resV x, hres x.1 x.2⟩
  have res_val : ∀ x : KR, (res x).1.1 = σ ≫ x.1.1 := fun _ => rfl

  have hone : dualNumberReduction R R ≫ (L.one tR).1 = (L.one (Scheme.TwoAffineOpenCover.specMap R R)).1 := by
    have h := L.one_natural tR (Scheme.TwoAffineOpenCover.specMap R R) (dualNumberReduction R R)
      (dualNumberReduction_comp_specMap R R)
    exact congrArg Subtype.val h
  let oneR : KR := ⟨L.one tR, hone⟩
  let mulR : KR → KR → KR := fun x y => ⟨L.mul tR x.1 y.1, hmulR x.1 y.1 x.2 y.2⟩
  let nsmulR : ℕ → KR → KR := fun n z => Nat.rec oneR (fun _ ih => mulR ih z) n
  have nsmulR_val : ∀ (n : ℕ) (z : KR), (nsmulR n z).1 = L.nsmul tR n z.1 := by
    intro n z
    induction n with
    | zero => rfl
    | succ n ih =>
      show L.mul tR (nsmulR n z).1 z.1 = L.mul tR (L.nsmul tR n z.1) z.1
      rw [ih]

  have τ_mul : ∀ x y : KR, τ (mulR x y) = τ x + τ y := fun x y => hadd x y (mulR x y) rfl
  have τ_one : τ oneR = 0 := by
    have h : τ oneR = τ oneR + τ oneR := hadd oneR oneR oneR (L.one_mul tR _).symm
    simpa using h
  have τ_nsmul : ∀ (n : ℕ) (z : KR), τ (nsmulR n z) = n • τ z := by
    intro n z
    induction n with
    | zero => first | exact τ_one | simpa using τ_one | simpa +zetaDelta using τ_one
    | succ n ih =>
      show τ (mulR (nsmulR n z) z) = (n + 1) • τ z
      rw [τ_mul, ih, succ_nsmul]

  let red : R →+ A := (algebraMap R A).toAddMonoidHom
  have hredp : ∀ m : ↥(CuspForm.intLattice N 2) →+ R, red.comp (p • m) = 0 := by
    intro m
    ext g
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.smul_apply, AddMonoidHom.zero_apply]
    show algebraMap R A (p • m g) = 0
    rw [nsmul_eq_mul, map_mul, map_natCast]
    have hp : ((p : ℕ) : A) = 0 := by
      have : ((p : ℕ) : R) ∈ RingHom.ker (algebraMap R A) := by
        rw [hker]; exact Ideal.mem_span_singleton_self _
      simpa using this
    rw [hp, zero_mul]

  have key : ∀ x x' : KR, (res x).1.1 = (res x').1.1 → red.comp (τ x) = red.comp (τ x') := by
    intro x x' h
    rw [res_val, res_val] at h
    obtain ⟨z, hz, hx'⟩ := (hfib x.1 x'.1 x.2 x'.2).mp h
    let zK : KR := ⟨z, hz⟩
    have hx'K : x' = mulR x (nsmulR p zK) := by
      apply Subtype.ext
      show x'.1 = L.mul tR x.1 (nsmulR p zK).1
      rw [nsmulR_val]
      exact hx'
    rw [hx'K, τ_mul, τ_nsmul, AddMonoidHom.comp_add, hredp, add_zero]

  have lift_spec : ∀ y : KA, ∃ x : KR, res x = y := by
    intro y
    obtain ⟨x, hx, hxy⟩ := hsurj y.1 y.2
    exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext hxy)⟩
  let lift : KA → KR := fun y => (lift_spec y).choose
  have res_lift : ∀ y : KA, res (lift y) = y := fun y => (lift_spec y).choose_spec

  let τk : KA → (↥(CuspForm.intLattice N 2) →+ A) := fun y => red.comp (τ (lift y))
  have τk_res : ∀ x : KR, τk (res x) = red.comp (τ x) := by
    intro x
    show red.comp (τ (lift (res x))) = red.comp (τ x)
    apply key
    rw [res_lift]

  have hred_surj : Function.Surjective (algebraMap R A) := hA
  haveI := hfree
  have hliftHom : ∀ h : ↥(CuspForm.intLattice N 2) →+ A, ∃ h' : ↥(CuspForm.intLattice N 2) →+ R,
      red.comp h' = h := fun h => A2iPrime.exists_lift (algebraMap R A) hred_surj h
  let inv : (↥(CuspForm.intLattice N 2) →+ A) → KA := fun h => res (τ.symm (hliftHom h).choose)
  have right_inv : ∀ h, τk (inv h) = h := by
    intro h
    show τk (res (τ.symm (hliftHom h).choose)) = h
    rw [τk_res, Equiv.apply_symm_apply]
    exact (hliftHom h).choose_spec
  have left_inv : ∀ y, inv (τk y) = y := by
    intro y

    obtain ⟨x, rfl⟩ : ∃ x : KR, res x = y := ⟨lift y, res_lift y⟩
    set h' := (hliftHom (τk (res x))).choose with hh'def
    have hh' : red.comp h' = red.comp (τ x) := by rw [(hliftHom (τk (res x))).choose_spec, τk_res]

    have hvals : ∀ g, (h' - τ x) g ∈ Ideal.span {((p : ℕ) : R)} := by
      intro g
      rw [← hker, RingHom.mem_ker]
      have := congrArg (fun φ : ↥(CuspForm.intLattice N 2) →+ A => φ g) hh'
      simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
      show algebraMap R A ((h' - τ x) g) = 0
      rw [AddMonoidHom.sub_apply, map_sub]
      exact sub_eq_zero.mpr this
    obtain ⟨v, hv⟩ := A2iPrime.exists_eq_smul_of_forall_mem ((p : ℕ) : R) (h' - τ x) hvals
    have hv' : h' = τ (mulR x (nsmulR p (τ.symm v))) := by
      rw [τ_mul, τ_nsmul, Equiv.apply_symm_apply]
      have : h' = τ x + (h' - τ x) := by abel
      rw [this, hv]
      congr 1
    have hsymm : τ.symm h' = mulR x (nsmulR p (τ.symm v)) := by
      rw [hv', Equiv.symm_apply_apply]
    show res (τ.symm h') = res x
    apply Subtype.ext; apply Subtype.ext
    rw [res_val, res_val]
    symm
    apply (hfib x.1 (τ.symm h').1 x.2 (τ.symm h').2).mpr
    refine ⟨(τ.symm v).1, (τ.symm v).2, ?_⟩
    rw [hsymm]
    show L.mul tR x.1 (nsmulR p (τ.symm v)).1 = L.mul tR x.1 (L.nsmul tR p (τ.symm v).1)
    rw [nsmulR_val]
  let E : KA ≃ (↥(CuspForm.intLattice N 2) →+ A) := ⟨τk, inv, left_inv, right_inv⟩
  refine ⟨E, ?_, ?_, ?_⟩
  ·
    intro x y z hz
    obtain ⟨lx, rfl⟩ : ∃ lx : KR, res lx = x := ⟨lift x, res_lift x⟩
    obtain ⟨ly, rfl⟩ : ∃ ly : KR, res ly = y := ⟨lift y, res_lift y⟩
    have hzres : z = res (mulR lx ly) := by
      apply Subtype.ext; apply Subtype.ext
      rw [res_val]
      show z.1.1 = σ ≫ (L.mul tR lx.1 ly.1).1
      rw [hmul lx.1 ly.1, hz]
    show τk z = τk (res lx) + τk (res ly)
    rw [hzres, τk_res, τk_res, τk_res, τ_mul, AddMonoidHom.comp_add]
  ·
    intro β x xk hβ1 hβ2 hxk g
    have hβ : β = lam.toRingHom := A2iPrime.beta_eq R A β hβ1 hβ2
    let xK : KR := ⟨x.1, x.2⟩
    have hxkres : xk = res xK := by
      apply Subtype.ext; apply Subtype.ext
      rw [res_val, hxk, hβ]
      rfl
    show τk xk g = algebraMap R A (τ xK g)
    rw [hxkres, τk_res]
    rfl
  ·
    intro t x y hy g
    obtain ⟨lx, rfl⟩ : ∃ lx : KR, res lx = x := ⟨lift x, res_lift x⟩
    let ly : KR := ⟨NeronModelInfra.schemeHomOverComp lx.1 (φ t), hcompR (φ t) (hφL t) lx.1 lx.2⟩
    have hyres : y = res ly := by
      apply Subtype.ext; apply Subtype.ext
      rw [res_val, hy, res_val]
      show (σ ≫ lx.1.1) ≫ (φ t).1 = σ ≫ (lx.1.1 ≫ (φ t).1)
      rw [Category.assoc]
    show τk y g = τk (res lx) (t • g)
    rw [hyres, τk_res, τk_res]
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [hhecke t lx ly rfl g]

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_dualNumber_kernel_equiv_addMonoidHom_intLattice_baseChange_of_surjective_of_ker_eq_span
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_dualNumber_kernel_equiv_addMonoidHom_intLattice_baseChange_of_surjective_of_ker_eq_span (solution)
