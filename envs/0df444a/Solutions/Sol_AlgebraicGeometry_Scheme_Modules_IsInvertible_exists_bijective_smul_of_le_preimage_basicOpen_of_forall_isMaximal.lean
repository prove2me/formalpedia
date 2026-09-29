-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_bijective_smul_of_le_preimage_basicOpen_of_forall_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/49998a57-31e4-5800-ab1c-31355209f132

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isClosed_setOf_le_finrank_sections_pullback_residueField
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_eq_sum_smul_pullbackSection_of_isReduced_of_finrank_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_bijective_smul_of_le_preimage_basicOpen_of_forall_isMaximal
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace TensorProduct

namespace P2mSeesawAffine

section Transport

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) {M N : V.Modules}

def sectionsEquivOfIso (e : M ≅ N) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π N ⊤
    Γ(M, ⊤) ≃ₗ[R] Γ(N, ⊤) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π N ⊤
  { toFun := fun x => Scheme.Modules.Hom.app e.hom ⊤ x
    invFun := fun y => Scheme.Modules.Hom.app e.inv ⊤ y
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r x => by
      show Scheme.Modules.Hom.app e.hom ⊤ ((algebraMap R Γ(V, ⊤) r) • x)
        = (algebraMap R Γ(V, ⊤) r) • Scheme.Modules.Hom.app e.hom ⊤ x
      exact Scheme.Modules.Hom.app_smul _ _ _
    left_inv := fun x => by
      change (Scheme.Modules.Hom.app e.hom ⊤ ≫ Scheme.Modules.Hom.app e.inv ⊤) x = x
      rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
    right_inv := fun y => by
      change (Scheme.Modules.Hom.app e.inv ⊤ ≫ Scheme.Modules.Hom.app e.hom ⊤) y = y
      rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl }

variable (V) in

def unitSectionsEquiv :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π (SheafOfModules.unit V.ringCatSheaf) ⊤
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
    Γ(SheafOfModules.unit V.ringCatSheaf, ⊤) ≃ₗ[R] Γ(V, ⊤) :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π (SheafOfModules.unit V.ringCatSheaf) ⊤
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
  { toFun := fun x => (show Γ(V, ⊤) from x)
    invFun := fun y => (show Γ(SheafOfModules.unit V.ringCatSheaf, ⊤) from y)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem finrank_eq_one_of_iso_unit {K : Type u} [Field K] {W : Scheme.{u}} (ϖ : W ⟶ Spec (.of K))
    (hO : letI := Scheme.TwoAffineOpenCover.algebraOfHom ϖ ⊤; Function.Bijective (algebraMap K Γ(W, ⊤)))
    (N : W.Modules) (e : N ≅ SheafOfModules.unit W.ringCatSheaf) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom ϖ N ⊤
    Module.finrank K Γ(N, ⊤) = 1 := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom ϖ ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom ϖ N ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom ϖ (SheafOfModules.unit W.ringCatSheaf) ⊤
  let e' : Γ(N, ⊤) ≃ₗ[K] K := (sectionsEquivOfIso ϖ e).trans ((unitSectionsEquiv W ϖ).trans
    (LinearEquiv.ofBijective (Algebra.linearMap K Γ(W, ⊤)) hO).symm)
  rw [e'.finrank_eq, Module.finrank_self]

end Transport

section Frame

variable {W : Scheme.{u}}

lemma app_map {N N' : W.Modules} (φ : N ⟶ N') {U U' : W.Opens} (i : U' ⟶ U) (n : Γ(N, U)) :
    φ.app U' (N.presheaf.map i.op n) = N'.presheaf.map i.op (φ.app U n) := by
  have h := φ.mapPresheaf.naturality i.op
  exact ConcreteCategory.congr_hom h n

abbrev unitOne (U : W.Opens) : Γ((SheafOfModules.unit W.ringCatSheaf : W.Modules), U) :=
  (show Γ(W, U) from 1)

theorem map_unitOne {U U' : W.Opens} (i : U' ⟶ U) :
    (Scheme.Modules.presheaf (SheafOfModules.unit W.ringCatSheaf : W.Modules)).map i.op (unitOne U)
      = unitOne U' := by
  change (W.presheaf.map i.op).hom 1 = 1
  exact map_one _

theorem bijective_smul_map_inv_one (N : W.Modules) (e : N ≅ SheafOfModules.unit W.ringCatSheaf)
    (U : W.Opens) :
    Function.Bijective fun a : Γ(W, U) =>
      a • (N.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (e.inv.app ⊤ (unitOne ⊤)) : Γ(N, U)) := by
  have hfun : (fun a : Γ(W, U) =>
      a • (N.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (e.inv.app ⊤ (unitOne ⊤)) : Γ(N, U)))
      = (fun a : Γ(W, U) => e.inv.app U (show Γ((SheafOfModules.unit W.ringCatSheaf : W.Modules), U) from a)) := by
    funext a
    rw [← app_map, map_unitOne, ← Scheme.Modules.Hom.app_smul]
    congr 1
    change a * 1 = a
    exact mul_one a
  rw [hfun]
  exact ConcreteCategory.bijective_of_isIso (e.inv.app U)

end Frame

section Jacobson

variable {R : Type u} [CommRing R]

theorem closedPoints_primeSpectrum :
    closedPoints (PrimeSpectrum R) = {𝔪 | 𝔪.asIdeal.IsMaximal} := by
  ext 𝔪
  exact PrimeSpectrum.isClosed_singleton_iff_isMaximal 𝔪

variable [IsJacobsonRing R]

theorem eq_univ_of_isOpen_of_forall_isMaximal {U : Set (PrimeSpectrum R)} (hU : IsOpen U)
    (h : ∀ 𝔪 : PrimeSpectrum R, 𝔪.asIdeal.IsMaximal → 𝔪 ∈ U) : U = Set.univ := by
  have hZ : closure (Uᶜ ∩ closedPoints (PrimeSpectrum R)) = Uᶜ :=
    JacobsonSpace.closure_inter_closedPoints hU.isClosed_compl
  have hempty : Uᶜ ∩ closedPoints (PrimeSpectrum R) = ∅ := by
    ext 𝔪
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, closedPoints_primeSpectrum, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro h𝔪 hmax
    exact h𝔪 (h 𝔪 hmax)
  rw [hempty, closure_empty] at hZ
  exact Set.compl_empty_iff.mp hZ.symm

theorem eq_one_of_isClosed_of_forall_isMaximal (h : PrimeSpectrum R → ℕ) (h2 : IsClosed {𝔭 | 2 ≤ h 𝔭})
    (h1 : IsClosed {𝔭 | 1 ≤ h 𝔭}) (hmax : ∀ 𝔪 : PrimeSpectrum R, 𝔪.asIdeal.IsMaximal → h 𝔪 = 1)
    (𝔭 : PrimeSpectrum R) : h 𝔭 = 1 := by
  have hlt : {𝔭 : PrimeSpectrum R | 2 ≤ h 𝔭}ᶜ = Set.univ :=
    eq_univ_of_isOpen_of_forall_isMaximal h2.isOpen_compl fun 𝔪 h𝔪 => by
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hmax 𝔪 h𝔪]; omega
  have hge : {𝔭 : PrimeSpectrum R | 1 ≤ h 𝔭} = Set.univ := by
    have hZ := JacobsonSpace.closure_inter_closedPoints h1
    have hsub : {𝔭 : PrimeSpectrum R | 1 ≤ h 𝔭} ∩ closedPoints (PrimeSpectrum R)
        = closedPoints (PrimeSpectrum R) := by
      refine Set.inter_eq_right.mpr fun 𝔪 h𝔪 => ?_
      rw [closedPoints_primeSpectrum] at h𝔪
      simp only [Set.mem_setOf_eq, hmax 𝔪 h𝔪, le_refl]
    rw [hsub, closure_closedPoints] at hZ
    exact hZ.symm
  have h𝔭2 : 𝔭 ∈ ({𝔭 : PrimeSpectrum R | 2 ≤ h 𝔭}ᶜ) := hlt ▸ Set.mem_univ 𝔭
  have h𝔭1 : 𝔭 ∈ {𝔭 : PrimeSpectrum R | 1 ≤ h 𝔭} := hge ▸ Set.mem_univ 𝔭
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at h𝔭2 h𝔭1
  omega

end Jacobson

section PullbackSections

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)) (L : Y.Modules)
  (K : Type u) [CommRing K] [Algebra R K]

abbrev eta (x : Γ(L, ⊤)) :
    Γ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R K))).obj L, ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst f (specMap R K))).unit.app L).app ⊤ x

theorem eta_add (x y : Γ(L, ⊤)) : eta f L K (x + y) = eta f L K x + eta f L K y := map_add _ x y

theorem eta_sum {ι : Type*} (s : Finset ι) (x : ι → Γ(L, ⊤)) :
    eta f L K (∑ i ∈ s, x i) = ∑ i ∈ s, eta f L K (x i) := map_sum _ x s

theorem eta_smul (s : Γ(Y, ⊤)) (x : Γ(L, ⊤)) :
    eta f L K (s • x) = (Limits.pullback.fst f (specMap R K)).appTop s • eta f L K x :=
  Scheme.Modules.Hom.app_smul _ s x

theorem appTop_snd_algebraMap (b : R) :
    (Limits.pullback.snd f (specMap R K)).appTop ((Scheme.ΓSpecIso (.of K)).inv (algebraMap R K b))
      = (Limits.pullback.fst f (specMap R K)).appTop
          (letI := algebraOfHom f ⊤; algebraMap R Γ(Y, ⊤) b) := by
  letI := algebraOfHom f ⊤
  have h1 : (letI := algebraOfHom f ⊤; algebraMap R Γ(Y, ⊤) b)
      = f.appTop ((Scheme.ΓSpecIso (.of R)).inv b) := by
    have happ : f.appLE ⊤ ⊤ le_top = f.app ⊤ := Scheme.Hom.appLE_eq_app f
    change (f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of R)).inv b) = _
    rw [happ]
  rw [h1]
  change ((Scheme.ΓSpecIso (.of K)).inv ≫ (Limits.pullback.snd f (specMap R K)).appTop)
      (CommRingCat.ofHom (algebraMap R K) b) = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫
        (Limits.pullback.fst f (specMap R K)).appTop) b
  rw [← Scheme.Hom.comp_appTop, Limits.pullback.condition, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end PullbackSections

section Maximal

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

theorem exists_frame_of_isMaximal
    {R : Type u} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) [IsProper f] [Flat f] (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hconst : ∀ 𝔭 : PrimeSpectrum R,
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj L) ⊤
      Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj L, ⊤) = 1)
    (𝔪 : PrimeSpectrum R) (h𝔪 : 𝔪.asIdeal.IsMaximal)
    (e : (Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔪.asIdeal.ResidueField))).obj L ≅
      SheafOfModules.unit (Limits.pullback f (specMap R 𝔪.asIdeal.ResidueField)).ringCatSheaf) :
    ∃ (g : R) (m : Γ(L, ⊤)), g ∉ 𝔪.asIdeal ∧ ∀ V : Y.Opens, V ≤ f ⁻¹ᵁ (PrimeSpectrum.basicOpen g) →
      Function.Bijective fun a : Γ(Y, V) => a • (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op m : Γ(L, V)) := by
  haveI := h𝔪
  let K := 𝔪.asIdeal.ResidueField
  let p₁ := Limits.pullback.fst f (specMap R K)
  let LK : (Limits.pullback f (specMap R K)).Modules := (Scheme.Modules.pullback p₁).obj L
  let σ : Γ(LK, ⊤) := e.inv.app ⊤ (unitOne ⊤)

  obtain ⟨N, m', c, hc⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_eq_sum_smul_pullbackSection_of_isReduced_of_finrank_eq
      f L hL.1 1 hconst K (k := 1) (fun _ => σ)
  have hσ := hc 0

  have hlift : ∀ j, ∃ b : R, algebraMap R K b = c 0 j := fun j =>
    Ideal.algebraMap_residueField_surjective 𝔪.asIdeal (c 0 j)
  choose b hb using hlift
  letI := algebraOfHom f ⊤
  letI := moduleSectionsOfHom f L ⊤
  let m : Γ(L, ⊤) := ∑ j, b j • m' j
  have hm : eta f L K m = σ := by
    rw [hσ, eta_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change eta f L K ((algebraMap R Γ(Y, ⊤) (b j)) • m' j) = _
    rw [eta_smul, ← appTop_snd_algebraMap, hb]

  have hframe : ∀ V' : (Limits.pullback f (specMap R K)).Opens,
      Function.Bijective fun a : Γ(Limits.pullback f (specMap R K), V') =>
        a • (LK.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op (eta f L K m) : Γ(LK, V')) := by
    rw [hm]
    exact bijective_smul_map_inv_one LK e

  obtain ⟨g, hg, hloc⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_basicOpen_forall_exists_frame_of_frame_pullback f L hL
      (ι := Fin 1) (fun _ => m) K 𝔪 (Ideal.ker_algebraMap_residueField 𝔪.asIdeal)
      (fun z => ⟨0, ⊤, trivial, fun V' _ => hframe V'⟩)

  refine ⟨g, m, hg, fun V hV => ?_⟩
  refine AlgebraicGeometry.Scheme.Modules.bijective_smul_of_forall_exists_bijective_smul L m V
    fun x hx => ?_
  obtain ⟨-, U, hxU, hU⟩ := hloc x (hV hx)
  exact ⟨U, hxU, hU⟩

end Maximal

section Main

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

theorem main
    {R : Type u} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] [IsJacobsonRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) [IsProper f] [Flat f]
    (hO : ∀ 𝔭 : PrimeSpectrum R,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField)) ⊤
      Function.Bijective (algebraMap 𝔭.asIdeal.ResidueField
        Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField), ⊤)))
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (htriv : ∀ 𝔪 : PrimeSpectrum R, 𝔪.asIdeal.IsMaximal →
      Nonempty ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔪.asIdeal.ResidueField))).obj L ≅
        SheafOfModules.unit
          (Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R 𝔪.asIdeal.ResidueField)).ringCatSheaf))
    (𝔭 : PrimeSpectrum R) :
    ∃ (g : R) (m : Γ(L, ⊤)), g ∉ 𝔭.asIdeal ∧ ∀ V : Y.Opens, V ≤ f ⁻¹ᵁ (PrimeSpectrum.basicOpen g) →
      Function.Bijective fun a : Γ(Y, V) => a • (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op m : Γ(L, V)) := by

  let h0 : PrimeSpectrum R → ℕ := fun 𝔭 =>
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
      (Limits.pullback.snd f (specMap R 𝔭.asIdeal.ResidueField))
      ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj L) ⊤
    Module.finrank 𝔭.asIdeal.ResidueField
      Γ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj L, ⊤)
  have hSC : ∀ n, IsClosed {𝔭 : PrimeSpectrum R | n ≤ h0 𝔭} := fun n =>
    AlgebraicGeometry.Scheme.Modules.isClosed_setOf_le_finrank_sections_pullback_residueField f L hL.1 n
  have hmax : ∀ 𝔪 : PrimeSpectrum R, 𝔪.asIdeal.IsMaximal → h0 𝔪 = 1 := fun 𝔪 h𝔪 => by
    obtain ⟨e⟩ := htriv 𝔪 h𝔪
    exact finrank_eq_one_of_iso_unit (Limits.pullback.snd f (specMap R 𝔪.asIdeal.ResidueField)) (hO 𝔪) _ e
  have hconst : ∀ 𝔭, h0 𝔭 = 1 := eq_one_of_isClosed_of_forall_isMaximal h0 (hSC 2) (hSC 1) hmax

  have hloc : ∀ 𝔪 : PrimeSpectrum R, 𝔪.asIdeal.IsMaximal → ∃ (g : R) (m : Γ(L, ⊤)), g ∉ 𝔪.asIdeal ∧
      ∀ V : Y.Opens, V ≤ f ⁻¹ᵁ (PrimeSpectrum.basicOpen g) →
        Function.Bijective fun a : Γ(Y, V) => a • (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op m : Γ(L, V)) :=
    fun 𝔪 h𝔪 => by
      obtain ⟨e⟩ := htriv 𝔪 h𝔪
      exact exists_frame_of_isMaximal f L hL hconst 𝔪 h𝔪 e

  let U : Set (PrimeSpectrum R) :=
    ⋃ (𝔪 : PrimeSpectrum R) (h𝔪 : 𝔪.asIdeal.IsMaximal), (PrimeSpectrum.basicOpen (hloc 𝔪 h𝔪).choose : Set _)
  have hU : IsOpen U :=
    isOpen_iUnion fun _ => isOpen_iUnion fun _ => (PrimeSpectrum.basicOpen _).isOpen
  have hUmax : ∀ 𝔪 : PrimeSpectrum R, 𝔪.asIdeal.IsMaximal → 𝔪 ∈ U := fun 𝔪 h𝔪 =>
    Set.mem_iUnion₂.mpr ⟨𝔪, h𝔪, (PrimeSpectrum.mem_basicOpen _ _).mpr (hloc 𝔪 h𝔪).choose_spec.choose_spec.1⟩
  have h𝔭U : 𝔭 ∈ U := (eq_univ_of_isOpen_of_forall_isMaximal hU hUmax).symm ▸ Set.mem_univ 𝔭
  obtain ⟨𝔪, h𝔪, h𝔭g⟩ := Set.mem_iUnion₂.mp h𝔭U
  obtain ⟨m, -, hframe⟩ := (hloc 𝔪 h𝔪).choose_spec
  exact ⟨_, m, (PrimeSpectrum.mem_basicOpen _ _).mp h𝔭g, hframe⟩

end Main

end P2mSeesawAffine

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] [IsJacobsonRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) [IsProper f] [Flat f]
    (hO : ∀ 𝔭 : PrimeSpectrum R,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField)) ⊤
      Function.Bijective (algebraMap 𝔭.asIdeal.ResidueField
        Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField), ⊤)))
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (htriv : ∀ 𝔪 : PrimeSpectrum R, 𝔪.asIdeal.IsMaximal →
      Nonempty ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔪.asIdeal.ResidueField))).obj L ≅
        SheafOfModules.unit
          (Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R 𝔪.asIdeal.ResidueField)).ringCatSheaf))
    (𝔭 : PrimeSpectrum R) :
    ∃ (g : R) (m : Γ(L, ⊤)), g ∉ 𝔭.asIdeal ∧ ∀ V : Y.Opens, V ≤ f ⁻¹ᵁ (PrimeSpectrum.basicOpen g) →
      Function.Bijective fun a : Γ(Y, V) =>
        a • (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op m : Γ(L, V)) :=
  P2mSeesawAffine.main f hO L hL htriv 𝔭

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_bijective_smul_of_le_preimage_basicOpen_of_forall_isMaximal
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_bijective_smul_of_le_preimage_basicOpen_of_forall_isMaximal (solution)
