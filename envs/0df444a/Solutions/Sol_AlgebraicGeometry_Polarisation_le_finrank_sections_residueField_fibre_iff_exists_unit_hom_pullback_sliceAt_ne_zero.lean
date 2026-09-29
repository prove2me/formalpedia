-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.le_finrank_sections_residueField_fibre_iff_exists_unit_hom_pullback_sliceAt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7383010a-b7a1-5213-a8d8-dd0c515db402

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_iso_pullback_snd_specMap_quotient_comp_fst_fst_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_finite_sections_of_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_le_finrank_sections_residueField_fibre_iff_exists_unit_hom_pullback_sliceAt_ne_zero
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation Opposite"

namespace FibreIdent

def HasSec {X : Scheme.{0}} (M : X.Modules) : Prop := ∃ s : 𝟙_ X.Modules ⟶ M, s ≠ 0

theorem hasSec_of_iso {X : Scheme.{0}} {M M' : X.Modules} (e : M ≅ M') : HasSec M → HasSec M' := by
  rintro ⟨s, hs⟩
  refine ⟨s ≫ e.hom, fun h => hs ?_⟩
  rw [← cancel_mono e.hom, h, zero_comp]

theorem hasSec_iff_of_iso {X : Scheme.{0}} {M M' : X.Modules} (e : M ≅ M') : HasSec M ↔ HasSec M' :=
  ⟨hasSec_of_iso e, hasSec_of_iso e.symm⟩

theorem faithful_pullback_of_isIso {X Y : Scheme.{0}} (e : X ⟶ Y) [IsIso e] : (Scheme.Modules.pullback e).Faithful :=
  Functor.Faithful.of_comp_iso
    (Scheme.Modules.pullbackComp (inv e) e ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id e) ≪≫
      Scheme.Modules.pullbackId Y)

theorem map_ne_zero_of_isIso {X Y : Scheme.{0}} (e : X ⟶ Y) [IsIso e] {M N : Y.Modules} {s : M ⟶ N} (hs : s ≠ 0) :
    (Scheme.Modules.pullback e).map s ≠ 0 := by
  haveI := faithful_pullback_of_isIso e
  intro h
  exact hs ((Functor.map_eq_zero_iff (Scheme.Modules.pullback e)).1 h)

theorem hasSec_pullback_iff {X Y : Scheme.{0}} (e : X ⟶ Y) [IsIso e] (M : Y.Modules) :
    HasSec ((Scheme.Modules.pullback e).obj M) ↔ HasSec M := by
  constructor
  · rintro ⟨s, hs⟩

    let G := Scheme.Modules.pullback (inv e)
    let back : (Scheme.Modules.pullback e ⋙ G) ≅ 𝟭 _ :=
      Scheme.Modules.pullbackComp (inv e) e ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id e) ≪≫
        Scheme.Modules.pullbackId Y
    refine ⟨(Scheme.Modules.pullbackTensorUnitObjIso (inv e)).inv ≫ G.map s ≫ (back.app M).hom, fun h => ?_⟩
    have h2 : G.map s ≫ (back.app M).hom = 0 :=
      (cancel_epi (Scheme.Modules.pullbackTensorUnitObjIso (inv e)).inv).1 (h.trans comp_zero.symm)
    have h1 : G.map s = 0 := (cancel_mono (back.app M).hom).1 (h2.trans zero_comp.symm)
    exact map_ne_zero_of_isIso (inv e) hs h1
  · rintro ⟨s, hs⟩
    refine ⟨(Scheme.Modules.pullbackTensorUnitObjIso e).inv ≫ (Scheme.Modules.pullback e).map s, fun h => ?_⟩
    have h1 : (Scheme.Modules.pullback e).map s = 0 := by
      rw [← cancel_epi (Scheme.Modules.pullbackTensorUnitObjIso e).inv, h, comp_zero]
    exact map_ne_zero_of_isIso e hs h1

def toU {X : Scheme.{0}} (V : X.Opens) (t : Γ(X, V)) : Γ(𝟙_ X.Modules, V) := t
theorem toU_mul {X : Scheme.{0}} (V : X.Opens) (a t : Γ(X, V)) : toU V (a * t) = a • toU V t := rfl

theorem unit_hom_app {X : Scheme.{0}} {M : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (V : X.Opens) (t : Γ(X, V)) :
    s.app V (toU V t) = t • M.presheaf.map (homOfLE (le_top (a := V))).op (s.app ⊤ (toU ⊤ 1)) := by
  have hnat := PresheafOfModules.naturality_apply s.val (homOfLE (le_top (a := V))).op (toU ⊤ 1)
  have h1 : (𝟙_ X.Modules).val.map (homOfLE (le_top (a := V))).op (toU ⊤ 1) = toU V 1 := by
    change X.presheaf.map (homOfLE (le_top (a := V))).op 1 = 1; exact map_one _
  rw [h1] at hnat
  have ht : toU V t = t • toU V 1 := by rw [← toU_mul, mul_one]
  rw [ht, Scheme.Modules.Hom.app_smul]
  congr 1

def secFamily {X : Scheme.{0}} (M : X.Modules) (n : Γ(M, ⊤)) : M.val.sections :=
  ⟨fun V => M.presheaf.map (homOfLE (le_top (a := V.unop))).op n, fun {V W} g => by
    change M.presheaf.map g (M.presheaf.map (homOfLE (le_top (a := V.unop))).op n) =
      M.presheaf.map (homOfLE (le_top (a := W.unop))).op n
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
    exact congrArg (fun φ => M.presheaf.map φ n) (Subsingleton.elim _ _)⟩

theorem hasSec_iff_exists_ne_zero {X : Scheme.{0}} (M : X.Modules) :
    HasSec M ↔ ∃ n : Γ(M, ⊤), n ≠ 0 := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s.app ⊤ (toU ⊤ 1), fun h0 => hs ?_⟩
    apply Scheme.Modules.hom_ext
    intro V
    ext t
    change s.app V (toU V t) = 0
    rw [unit_hom_app, h0, map_zero, smul_zero]
  · rintro ⟨n, hn⟩
    refine ⟨M.unitHomEquiv.symm (secFamily M n), fun h0 => hn ?_⟩
    have h1 := SheafOfModules.unitHomEquiv_apply_coe M (M.unitHomEquiv.symm (secFamily M n)) (op ⊤)
    rw [Equiv.apply_symm_apply, h0] at h1
    change M.presheaf.map (homOfLE (le_top (a := (⊤ : X.Opens)))).op n = _ at h1
    have h2 : M.presheaf.map (homOfLE (le_top (a := (⊤ : X.Opens)))).op n = n := by
      have : (homOfLE (le_top (a := (⊤ : X.Opens)))) = 𝟙 _ := Subsingleton.elim _ _
      rw [this, op_id, M.presheaf.map_id]; rfl
    rw [← h2, h1]
    rfl

theorem one_le_finrank_iff {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] :
    1 ≤ Module.finrank K V ↔ ∃ v : V, v ≠ 0 := by
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero]
  exact Module.finrank_pos_iff_exists_ne_zero

section Chart

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (U : A.Opens) (hU : IsAffineOpen U)

abbrev chartMap : pullback f (hU.fromSpec ≫ f) ⟶ Spec Γ(A, U) := pullback.snd f (hU.fromSpec ≫ f)

abbrev mMap : pullback f (hU.fromSpec ≫ f) ⟶ pullback f f :=
  pullback.lift (pullback.fst f (hU.fromSpec ≫ f)) (pullback.snd f (hU.fromSpec ≫ f) ≫ hU.fromSpec)
    (by rw [Category.assoc]; exact pullback.condition)

variable (R : Type) [CommRing R] [Algebra Γ(A, U) R]

abbrev fib : Scheme.{0} := pullback (chartMap f U hU) (Scheme.TwoAffineOpenCover.specMap Γ(A, U) R)

abbrev fibι : fib f U hU R ⟶ pullback f (hU.fromSpec ≫ f) :=
  pullback.fst (chartMap f U hU) (Scheme.TwoAffineOpenCover.specMap Γ(A, U) R)

abbrev fibπ : fib f U hU R ⟶ Spec (CommRingCat.of R) :=
  pullback.snd (chartMap f U hU) (Scheme.TwoAffineOpenCover.specMap Γ(A, U) R)

theorem exists_iso_fib {R' : Type} [CommRing R'] [Algebra Γ(A, U) R'] (g : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    [IsIso g] (hg : Scheme.TwoAffineOpenCover.specMap Γ(A, U) R' = g ≫ Scheme.TwoAffineOpenCover.specMap Γ(A, U) R) :
    ∃ e : fib f U hU R' ⟶ fib f U hU R, IsIso e ∧ e ≫ fibι f U hU R = fibι f U hU R' := by
  let e : fib f U hU R' ⟶ fib f U hU R :=
    pullback.lift (fibι f U hU R') (fibπ f U hU R' ≫ g) (by rw [Category.assoc, ← hg]; exact pullback.condition)
  let e' : fib f U hU R ⟶ fib f U hU R' :=
    pullback.lift (fibι f U hU R) (fibπ f U hU R ≫ inv g)
      (by rw [Category.assoc, hg, IsIso.inv_hom_id_assoc]; exact pullback.condition)
  refine ⟨e, ⟨⟨e', ?_, ?_⟩⟩, pullback.lift_fst _ _ _⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id, Category.id_comp]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id, Category.id_comp]

end Chart

theorem main
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (Λ : (pullback f f).Modules) (hΛ : Scheme.Modules.IsInvertible Λ)
    (U : A.Opens) (hU : IsAffineOpen U)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (𝔭 : PrimeSpectrum Γ(A, U))
    (h𝔭 : hU.fromSpec.base 𝔭 = x.1.base (IsLocalRing.closedPoint k)) :
    (1 ≤ @Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback (fibι f U hU 𝔭.asIdeal.ResidueField)).obj ((Scheme.Modules.pullback (mMap f U hU)).obj Λ), ⊤)
        _ _ (Scheme.TwoAffineOpenCover.moduleSectionsOfHom (fibπ f U hU 𝔭.asIdeal.ResidueField)
          ((Scheme.Modules.pullback (fibι f U hU 𝔭.asIdeal.ResidueField)).obj ((Scheme.Modules.pullback (mMap f U hU)).obj Λ)) ⊤)) ↔
      HasSec ((Scheme.Modules.pullback (sliceAt f x)).obj Λ) := by
  classical
  haveI : IsProper f := hA.proper
  set κ := 𝔭.asIdeal.ResidueField with hκ

  let N : (fib f U hU κ).Modules :=
    (Scheme.Modules.pullback (fibι f U hU κ)).obj ((Scheme.Modules.pullback (mMap f U hU)).obj Λ)
  have hN : Scheme.Modules.IsInvertible N := (hΛ.pullback _).pullback _
  haveI : IsProper (fibπ f U hU κ) := inferInstance
  have hfin := AlgebraicGeometry.Scheme.Modules.IsInvertible.finite_sections_of_isProper κ (fibπ f U hU κ) N hN

  have step1 : (1 ≤ @Module.finrank κ Γ(N, ⊤) _ _ (Scheme.TwoAffineOpenCover.moduleSectionsOfHom (fibπ f U hU κ) N ⊤)) ↔
      HasSec N := by
    rw [hasSec_iff_exists_ne_zero]
    exact @one_le_finrank_iff κ Γ(N, ⊤) _ _ (Scheme.TwoAffineOpenCover.moduleSectionsOfHom (fibπ f U hU κ) N ⊤) hfin
  refine step1.trans ?_

  letI alg : Algebra k Γ(A, U) := (Spec.preimage (hU.fromSpec ≫ f)).hom.toAlgebra
  have hi : hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Γ(A, U))) := (Spec.map_preimage _).symm
  have hpt : ∀ p : PrimeSpectrum k, p = IsLocalRing.closedPoint k := fun p =>
    PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)
  have hrange : Set.range x.1.base ⊆ Set.range hU.fromSpec.base := by
    rintro _ ⟨p, rfl⟩
    rw [hpt p, ← h𝔭]
    exact ⟨𝔭, rfl⟩
  let x' : Spec (CommRingCat.of k) ⟶ Spec Γ(A, U) := IsOpenImmersion.lift hU.fromSpec x.1 hrange
  have hx' : x' ≫ hU.fromSpec = x.1 := IsOpenImmersion.lift_fac _ _ _
  let χ₀ : Γ(A, U) ⟶ CommRingCat.of k := Spec.preimage x'
  have hχ₀ : Spec.map χ₀ = x' := Spec.map_preimage _
  have hcomp : Spec.preimage (hU.fromSpec ≫ f) ≫ χ₀ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, hχ₀, Spec.map_preimage, ← Category.assoc, hx']
    exact x.2
  let χ : Γ(A, U) →ₐ[k] k :=
    { toRingHom := χ₀.hom
      commutes' := fun r => by
        change (Spec.preimage (hU.fromSpec ≫ f) ≫ χ₀).hom r = r
        rw [hcomp]
        rfl }
  have h𝔭' : 𝔭 = x'.base (IsLocalRing.closedPoint k) := by
    apply hU.fromSpec.isOpenEmbedding.injective
    rw [h𝔭, ← hx']
    rfl
  have hχ : ∀ b : Γ(A, U), b ∈ 𝔭.asIdeal ↔ χ b = 0 := by
    intro b
    rw [h𝔭', ← hχ₀]
    change b ∈ Ideal.comap χ₀.hom (IsLocalRing.closedPoint k).asIdeal ↔ _
    rw [Ideal.mem_comap]
    change χ₀.hom b ∈ IsLocalRing.maximalIdeal k ↔ χ₀.hom b = 0
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]
  have hsurj : Function.Surjective χ₀.hom := fun r => ⟨algebraMap k Γ(A, U) r, χ.commutes r⟩
  haveI hmax : 𝔭.asIdeal.IsMaximal := by
    have : 𝔭.asIdeal = RingHom.ker χ₀.hom := Ideal.ext fun b => by rw [hχ b, RingHom.mem_ker]; rfl
    rw [this]
    exact RingHom.ker_isMaximal_of_surjective χ₀.hom hsurj

  obtain ⟨Φ, hΦ, -, -, -, hmod⟩ :=
    AlgebraicGeometry.Scheme.exists_iso_pullback_snd_specMap_quotient_comp_fst_fst_eq_id f Γ(A, U) hU.fromSpec hi
      𝔭.asIdeal χ hχ
  obtain ⟨eΦ⟩ := hmod Λ

  let q : (Γ(A, U) ⧸ 𝔭.asIdeal) →+* κ := algebraMap _ _
  let qe : (Γ(A, U) ⧸ 𝔭.asIdeal) ≃+* κ := RingEquiv.ofBijective q (Ideal.bijective_algebraMap_quotient_residueField _)
  let g : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of (Γ(A, U) ⧸ 𝔭.asIdeal)) := Spec.map qe.toCommRingCatIso.hom
  haveI : IsIso g := inferInstance
  have hg : Scheme.TwoAffineOpenCover.specMap Γ(A, U) κ = g ≫ Scheme.TwoAffineOpenCover.specMap Γ(A, U) (Γ(A, U) ⧸ 𝔭.asIdeal) := by
    change Spec.map (CommRingCat.ofHom (algebraMap Γ(A, U) κ)) =
      Spec.map (CommRingCat.ofHom q) ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(A, U) (Γ(A, U) ⧸ 𝔭.asIdeal)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq Γ(A, U) (Γ(A, U) ⧸ 𝔭.asIdeal) κ]
  obtain ⟨e, he, heι⟩ := exists_iso_fib f U hU (Γ(A, U) ⧸ 𝔭.asIdeal) g hg
  haveI := he

  have step2 : HasSec N ↔ HasSec ((Scheme.Modules.pullback (fibι f U hU (Γ(A, U) ⧸ 𝔭.asIdeal))).obj
      ((Scheme.Modules.pullback (mMap f U hU)).obj Λ)) := by
    refine (hasSec_iff_of_iso ?_).trans (hasSec_pullback_iff e _)
    exact (Scheme.Modules.pullbackCongr heι.symm).app _ ≪≫ ((Scheme.Modules.pullbackComp e _).app _).symm
  refine step2.trans ?_

  refine (hasSec_pullback_iff Φ _).symm.trans ?_
  refine (hasSec_iff_of_iso eΦ).trans ?_

  have hχx : Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hU.fromSpec = x.1 := by
    change Spec.map χ₀ ≫ hU.fromSpec = x.1
    rw [hχ₀, hx']
  have hslice : sliceAt f x = pullback.fst f (𝟙 _) ≫
      pullback.lift (𝟙 A) (f ≫ Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hU.fromSpec)
        (by rw [Category.id_comp, Category.assoc, Category.assoc, hi, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
              show χ.toRingHom.comp (algebraMap k Γ(A, U)) = RingHom.id k from RingHom.ext fun x => χ.commutes x,
              CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) := by
    apply pullback.hom_ext
    · simp only [sliceAt, pullback.lift_fst, Category.assoc, Category.comp_id]
    · simp only [sliceAt, pullback.lift_snd, Category.assoc]
      rw [hχx, ← Category.assoc, pullback.condition, Category.comp_id]
  rw [hasSec_iff_of_iso ((Scheme.Modules.pullbackCongr hslice).app Λ ≪≫ ((Scheme.Modules.pullbackComp _ _).app Λ).symm)]
  exact (hasSec_pullback_iff _ _).symm

end FibreIdent

open FibreIdent in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (Λ : (pullback f f).Modules) (hΛ : Scheme.Modules.IsInvertible Λ)
    (U : A.Opens) (hU : IsAffineOpen U)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (𝔭 : PrimeSpectrum Γ(A, U))
    (h𝔭 : hU.fromSpec.base 𝔭 = x.1.base (IsLocalRing.closedPoint k)) :
    let m : pullback f (hU.fromSpec ≫ f) ⟶ pullback f f :=
      Limits.pullback.lift (Limits.pullback.fst f (hU.fromSpec ≫ f)) (Limits.pullback.snd f (hU.fromSpec ≫ f) ≫ hU.fromSpec)
        (by rw [Category.assoc]; exact Limits.pullback.condition)
    let ι := Limits.pullback.fst (Limits.pullback.snd f (hU.fromSpec ≫ f))
      (Scheme.TwoAffineOpenCover.specMap Γ(A, U) 𝔭.asIdeal.ResidueField)
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
      (Limits.pullback.snd (Limits.pullback.snd f (hU.fromSpec ≫ f))
        (Scheme.TwoAffineOpenCover.specMap Γ(A, U) 𝔭.asIdeal.ResidueField))
      ((Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback m).obj Λ)) ⊤
    (1 ≤ Module.finrank 𝔭.asIdeal.ResidueField Γ((Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback m).obj Λ), ⊤)) ↔
      ∃ s : 𝟙_ (pullback f (𝟙 (Spec (CommRingCat.of k)))).Modules ⟶ (Scheme.Modules.pullback (sliceAt f x)).obj Λ, s ≠ 0 := by
  intro m ι
  exact main k f L hA Λ hΛ U hU x 𝔭 h𝔭

end
end S_AlgebraicGeometry_Polarisation_le_finrank_sections_residueField_fibre_iff_exists_unit_hom_pullback_sliceAt_ne_zero
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_le_finrank_sections_residueField_fibre_iff_exists_unit_hom_pullback_sliceAt_ne_zero (solution)
