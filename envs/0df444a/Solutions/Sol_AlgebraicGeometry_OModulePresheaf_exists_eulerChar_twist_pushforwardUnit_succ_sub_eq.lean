-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_eulerChar_twist_pushforwardUnit_succ_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b359c76f-673a-5f54-be2c-47d59b0bfc0e

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ker
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite"
open scoped TensorProduct

namespace P2mTwistStep

open AlgebraicGeometry.OModulePresheaf

section General

variable {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) (K : V.OrderedAffineCover) (L : V.Modules)
  (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))

include hL in
theorem locTriv_tensorPow (n : ℕ) : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj (L.tensorPow n) ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  suffices h : Scheme.Modules.IsInvertible (L.tensorPow n) from h.1
  induction n with
  | zero => exact Scheme.Modules.isInvertible_unit V
  | succ n ih => exact ih.tensor ⟨hL⟩

include hL in
theorem coh_twist (G : OModulePresheaf π) (hc : G.IsCoherent) (hq : G.IsQuasicoherent) (n : ℕ) :
    (G.twist (L.tensorPow n)).IsCoherent ∧ (G.twist (L.tensorPow n)).IsQuasicoherent :=
  ⟨(G.isQuasicoherent_isCoherent_supportedIn_tensor (ofModules π (L.tensorPow n))).2.1 hc
      (isCoherent_ofModules_of_locallyTrivial π _ (locTriv_tensorPow L hL n)),
    (G.isQuasicoherent_isCoherent_supportedIn_tensor (ofModules π (L.tensorPow n))).1 hq
      (isQuasicoherent_ofModules_of_locallyTrivial π _ (locTriv_tensorPow L hL n))⟩

include hL in
theorem cechFinite_twist [IsProper π] (G : OModulePresheaf π) (hc : G.IsCoherent) (hq : G.IsQuasicoherent) (n : ℕ) :
    (G.twist (L.tensorPow n)).CechFinite K :=
  (G.twist (L.tensorPow n)).cechFinite_of_isProper (coh_twist π L hL G hc hq n).1 (coh_twist π L hL G hc hq n).2 K

include hL in
theorem flat_sections (n : ℕ) (U : V.affineOpens) : Module.Flat Γ(V, U.1) ((ofModules π (L.tensorPow n)).obj U.1) := by
  haveI := Scheme.Modules.projective_sections_of_locallyTrivial (L.tensorPow n) (locTriv_tensorPow L hL n) U
  show Module.Flat Γ(V, U.1) Γ(L.tensorPow n, U.1)
  exact Module.Flat.of_projective

include hL in

theorem eulerChar_twist_add [IsProper π] {G₁ G₂ G₃ : OModulePresheaf π} (S : AffSES G₁ G₂ G₃)
    (h₁c : G₁.IsCoherent) (h₁q : G₁.IsQuasicoherent) (h₂c : G₂.IsCoherent) (h₂q : G₂.IsQuasicoherent)
    (h₃c : G₃.IsCoherent) (h₃q : G₃.IsQuasicoherent) (n : ℕ) :
    (G₂.twist (L.tensorPow n)).eulerChar K =
      (G₁.twist (L.tensorPow n)).eulerChar K + (G₃.twist (L.tensorPow n)).eulerChar K := by
  obtain ⟨S', -⟩ := exists_affSES_tensor_of_flat S (ofModules π (L.tensorPow n)) (flat_sections π L hL n)
  exact eulerChar_eq_add_of_affSES S' K (cechFinite_twist π K L hL G₁ h₁c h₁q n)
    (cechFinite_twist π K L hL G₂ h₂c h₂q n) (cechFinite_twist π K L hL G₃ h₃c h₃q n)

theorem eulerChar_eq_of_bijective [IsSeparated π] {F G : OModulePresheaf π} (φ : AffHom F G)
    (hφ : ∀ U : V.affineOpens, Function.Bijective (φ.app U)) : F.eulerChar K = G.eulerChar K := by
  obtain ⟨⟨e0⟩, hS⟩ := AffHom.nonempty_H0_equiv_and_HSucc_equiv_of_bijective φ hφ K
  have h : ∀ i, F.cechFinrank K i = G.cechFinrank K i := by
    intro i
    cases i with
    | zero => exact e0.finrank_eq
    | succ j => obtain ⟨e⟩ := hS j; exact e.finrank_eq
  rw [eulerChar_def, eulerChar_def]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

end General

section Setup

variable {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) (Z₀ : Closeds V)

noncomputable abbrev ZZ : Scheme.{u} := (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme

private noncomputable abbrev _root_.P2mTwistStep.ι : ZZ Z₀ ⟶ V := (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι

p2m_export "P2mTwistStep" "ι"

noncomputable abbrev OZ : OModulePresheaf π := pushforwardUnit π (ι Z₀)

variable (I : (ZZ Z₀).IdealSheafData)

noncomputable abbrev ιI : I.subscheme ⟶ V := I.subschemeι ≫ ι Z₀

noncomputable abbrev OZI : OModulePresheaf π := pushforwardUnit π (ιI Z₀ I)

noncomputable abbrev W (U : V.affineOpens) : (ZZ Z₀).affineOpens := ⟨ι Z₀ ⁻¹ᵁ U.1, U.2.preimage _⟩

theorem W_le {U U' : V.affineOpens} (h : U.1 ≤ U'.1) : (W Z₀ U).1 ≤ (W Z₀ U').1 :=
  (Opens.map (ι Z₀).base).monotone h

theorem res_rfl {X : Scheme.{u}} (O : X.Opens) (x : Γ(X, O)) : X.presheaf.map (homOfLE (le_refl O)).op x = x := by
  rw [Subsingleton.elim (homOfLE (le_refl O)).op (𝟙 (op O)), X.presheaf.map_id]; rfl

theorem appLE_rfl_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)) :
    f.appLE U (f ⁻¹ᵁ U) le_rfl a = f.app U a := by
  show X.presheaf.map (homOfLE (le_refl _)).op (f.app U a) = _
  exact res_rfl _ _

theorem appLE_comp_apply (U : V.Opens) (a : Γ(V, U)) :
    (show Γ(I.subscheme, I.subschemeι ⁻¹ᵁ (ι Z₀ ⁻¹ᵁ U)) from (ιI Z₀ I).appLE U ((ιI Z₀ I) ⁻¹ᵁ U) le_rfl a) =
      I.subschemeι.app (ι Z₀ ⁻¹ᵁ U) ((ι Z₀).appLE U (ι Z₀ ⁻¹ᵁ U) le_rfl a) := by
  rw [appLE_rfl_apply, appLE_rfl_apply]
  rfl

noncomputable def rho : Hom (OZ π Z₀) (OZI π Z₀ I) where
  app U :=
    { toFun := fun x => show Γ(I.subscheme, (ιI Z₀ I) ⁻¹ᵁ U) from I.subschemeι.app (ι Z₀ ⁻¹ᵁ U) x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
        show I.subschemeι.app _ ((Scheme.TwoAffineOpenCover.algebraOfHom (ι Z₀ ≫ π) (ι Z₀ ⁻¹ᵁ U)).algebraMap r *
            (show Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U) from x)) =
          (show Γ(I.subscheme, I.subschemeι ⁻¹ᵁ (ι Z₀ ⁻¹ᵁ U)) from
            (Scheme.TwoAffineOpenCover.algebraOfHom (ιI Z₀ I ≫ π) ((ιI Z₀ I) ⁻¹ᵁ U)).algebraMap r) *
            I.subschemeι.app (ι Z₀ ⁻¹ᵁ U) x
        rw [map_mul]
        congr 1
        rw [← appLE_algebraMap (π := π) (ι Z₀) U r, ← appLE_comp_apply]
        exact appLE_algebraMap (π := π) (ιI Z₀ I) U r }
  app_smul U a x := by
    show I.subschemeι.app _ ((ι Z₀).appLE U (ι Z₀ ⁻¹ᵁ U) le_rfl a * (show Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U) from x)) =
      (show Γ(I.subscheme, I.subschemeι ⁻¹ᵁ (ι Z₀ ⁻¹ᵁ U)) from (ιI Z₀ I).appLE U ((ιI Z₀ I) ⁻¹ᵁ U) le_rfl a) *
        I.subschemeι.app (ι Z₀ ⁻¹ᵁ U) x
    rw [map_mul, appLE_comp_apply]
  naturality {U U'} h := by
    refine LinearMap.ext fun x => ?_
    have := CategoryTheory.ConcreteCategory.congr_hom
      (I.subschemeι.naturality (homOfLE ((Opens.map (ι Z₀).base).monotone h)).op) (show Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U') from x)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at this
    exact this

theorem rho_app (U : V.Opens) (x : Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U)) :
    (rho π Z₀ I).app U (show (OZ π Z₀).obj U from x) =
      (show (OZI π Z₀ I).obj U from I.subschemeι.app (ι Z₀ ⁻¹ᵁ U) x) := rfl

noncomputable abbrev KI : OModulePresheaf π := ker (rho π Z₀ I)

noncomputable def sesI : AffSES (KI π Z₀ I) (OZ π Z₀) (OZI π Z₀ I) where
  inc := (kerImSES (rho π Z₀ I)).inc.toAffHom
  proj := (rho π Z₀ I).toAffHom
  injective _ := Subtype.val_injective
  surjective U := I.subschemeι_app_surjective (W Z₀ U)
  exact U := Submodule.range_subtype _

theorem mem_KI_iff (U : V.affineOpens) (x : Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U.1)) :
    (show (OZ π Z₀).obj U.1 from x) ∈ LinearMap.ker ((rho π Z₀ I).app U.1) ↔ x ∈ I.ideal (W Z₀ U) := by
  rw [LinearMap.mem_ker, ← I.ker_subschemeι_app (W Z₀ U)]
  exact Iff.rfl

@[reducible] noncomputable def algVZ (U : V.affineOpens) : Algebra Γ(V, U.1) Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U.1) :=
  ((ι Z₀).app U.1).hom.toAlgebra

noncomputable def kappa (U : V.affineOpens) :
    letI := algVZ Z₀ U
    (KI π Z₀ I).obj U.1 ≃ₗ[Γ(V, U.1)] ↥(I.ideal (W Z₀ U)) :=
  letI := algVZ Z₀ U
  { toFun := fun x => ⟨(show (OZ π Z₀).obj U.1 from x.1), (mem_KI_iff π Z₀ I U x.1).mp x.2⟩
    invFun := fun y => ⟨(show (OZ π Z₀).obj U.1 from y.1), (mem_KI_iff π Z₀ I U y.1).mpr y.2⟩
    left_inv := fun x => rfl
    right_inv := fun y => rfl
    map_add' := fun x y => rfl
    map_smul' := fun a x => by
      refine Subtype.ext ?_
      show (ι Z₀).appLE U.1 (ι Z₀ ⁻¹ᵁ U.1) le_rfl a * (show Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U.1) from x.1) =
        (ι Z₀).app U.1 a * (show Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U.1) from x.1)
      rw [appLE_rfl_apply] }

theorem kappa_coe (U : V.affineOpens) (x : (KI π Z₀ I).obj U.1) :
    ((kappa π Z₀ I U x : ↥(I.ideal (W Z₀ U))) : Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U.1)) = (show (OZ π Z₀).obj U.1 from x.1) := rfl

theorem kappa_symm_coe (U : V.affineOpens) (y : ↥(I.ideal (W Z₀ U))) :
    (((kappa π Z₀ I U).symm y : (KI π Z₀ I).obj U.1).1 : Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U.1)) = y.1 := rfl

theorem KI_res_coe {U U' : V.affineOpens} (h : U.1 ≤ U'.1) (x : (KI π Z₀ I).obj U'.1) :
    ((((KI π Z₀ I).res h x).1 : (OZ π Z₀).obj U.1) : Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U.1)) =
      (ZZ Z₀).presheaf.map (homOfLE (W_le Z₀ h)).op ((x.1 : (OZ π Z₀).obj U'.1) : Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U'.1)) := by
  show (ZZ Z₀).presheaf.map _ _ = _
  rw [Subsingleton.elim (homOfLE ((Opens.map (ι Z₀).base).monotone h)) (homOfLE (W_le Z₀ h))]
  rfl

theorem OZ_good : (OZ π Z₀).IsCoherent ∧ (OZ π Z₀).IsQuasicoherent ∧
    (OZ π Z₀).SupportedIn ⟨Set.range (ι Z₀).base, (ι Z₀).isClosedEmbedding.isClosed_range⟩ :=
  isCoherent_isQuasicoherent_supportedIn_pushforwardUnit π (ι Z₀)

theorem OZI_good : (OZI π Z₀ I).IsCoherent ∧ (OZI π Z₀ I).IsQuasicoherent ∧
    (OZI π Z₀ I).SupportedIn ⟨Set.range (ιI Z₀ I).base, (ιI Z₀ I).isClosedEmbedding.isClosed_range⟩ :=
  isCoherent_isQuasicoherent_supportedIn_pushforwardUnit π (ιI Z₀ I)

theorem KI_good [IsProper π] : (KI π Z₀ I).IsCoherent ∧ (KI π Z₀ I).IsQuasicoherent := by
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian π
  exact ⟨isCoherent_ker (rho π Z₀ I) (OZ_good π Z₀).1,
    isQuasicoherent_ker (rho π Z₀ I) (OZ_good π Z₀).2.1 (OZI_good π Z₀ I).2.1⟩

def YI : Closeds V := ⟨Set.range (ιI Z₀ I).base, (ιI Z₀ I).isClosedEmbedding.isClosed_range⟩

theorem range_ι : Set.range (ι Z₀).base = (Z₀ : Set V) := by
  have := (Scheme.IdealSheafData.vanishingIdeal Z₀).range_subschemeι
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
  exact this

theorem YI_le : YI Z₀ I ≤ Z₀ := by
  intro v hv
  obtain ⟨z, rfl⟩ := hv
  have : (ι Z₀).base (I.subschemeι.base z) ∈ Set.range (ι Z₀).base := ⟨_, rfl⟩
  rw [range_ι] at this
  exact this

theorem YI_lt (hZint : IsIntegral (ZZ Z₀)) (hI : I ≠ ⊥) : YI Z₀ I < Z₀ := by
  haveI := hZint
  refine lt_of_le_of_ne (YI_le Z₀ I) fun h => hI ?_
  rw [← Scheme.IdealSheafData.support_eq_top_iff]
  rw [eq_top_iff]
  intro z _
  have hz : (ι Z₀).base z ∈ (Z₀ : Set V) := by rw [← range_ι]; exact ⟨z, rfl⟩
  have hz' : (ι Z₀).base z ∈ (YI Z₀ I : Set V) := by rw [h]; exact hz
  obtain ⟨w, hw⟩ := hz'
  have hinj : Function.Injective (ι Z₀).base := (ι Z₀).isClosedEmbedding.injective
  have : I.subschemeι.base w = z := hinj hw
  rw [← this]
  have hmem : I.subschemeι.base w ∈ (I.support : Set (ZZ Z₀)) := by
    rw [← I.range_subschemeι]; exact ⟨w, rfl⟩
  exact hmem

theorem exists_affine_nonempty (hZ₀ : (Z₀ : Set V).Nonempty) : ∃ O : (ZZ Z₀).affineOpens, Nonempty O.1 := by
  obtain ⟨v, hv⟩ := hZ₀
  rw [← range_ι] at hv
  obtain ⟨z, rfl⟩ := hv
  obtain ⟨O, hO, hzO, -⟩ := Opens.isBasis_iff_nbhd.mp (ZZ Z₀).isBasis_affineOpens
    (show z ∈ (⊤ : (ZZ Z₀).Opens) from trivial)
  exact ⟨⟨O, hO⟩, ⟨⟨z, hzO⟩⟩⟩

theorem ne_bot_of_ideal_ne_bot (O : (ZZ Z₀).affineOpens) (h : I.ideal O ≠ ⊥) : I ≠ ⊥ := by
  rintro rfl
  exact h rfl

end Setup

section Theta

variable {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) (Z₀ : Closeds V)
variable (L : V.Modules) (hLi : Scheme.Modules.IsInvertible L)

attribute [local instance] algVZ

noncomputable abbrev M : (ZZ Z₀).Modules := (Scheme.Modules.pullback (ι Z₀)).obj L

noncomputable def eta (U : V.Opens) (s : Γ(L, U)) : Γ(M Z₀ L, ι Z₀ ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (ι Z₀)).unit.app L).app U s

theorem map_eta {U U' : V.Opens} (h : U ≤ U') (s : Γ(L, U')) :
    (M Z₀ L).presheaf.map (homOfLE ((Opens.map (ι Z₀).base).monotone h)).op (eta Z₀ L U' s) =
      eta Z₀ L U (L.presheaf.map (homOfLE h).op s) := by
  rw [Subsingleton.elim (homOfLE ((Opens.map (ι Z₀).base).monotone h)) ((Opens.map (ι Z₀).base).map (homOfLE h))]
  exact (PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction (ι Z₀)).unit.app L).val (homOfLE h).op s).symm

noncomputable def tau (n : ℕ) (U : V.affineOpens) :
    Γ(L.tensorPow n, U.1) ⊗[Γ(V, U.1)] Γ(L, U.1) ≃ₗ[Γ(V, U.1)] Γ(L.tensorPow (n + 1), U.1) :=
  LinearEquiv.ofBijective (TensorProduct.lift (Scheme.Modules.tensorSectionsBilin (L.tensorPow n) L U.1))
    (Scheme.Modules.IsInvertible.bijective_lift_tensorSectionsBilin
      (show Scheme.Modules.IsInvertible (L.tensorPow n) from ⟨locTriv_tensorPow L hLi.1 n⟩) hLi U)

theorem tau_tmul (n : ℕ) (U : V.affineOpens) (y : Γ(L.tensorPow n, U.1)) (s : Γ(L, U.1)) :
    tau L hLi n U (y ⊗ₜ s) = Scheme.Modules.tensorSections y s := by
  show TensorProduct.lift (Scheme.Modules.tensorSectionsBilin (L.tensorPow n) L U.1) (y ⊗ₜ s) = _
  rw [TensorProduct.lift.tmul, Scheme.Modules.tensorSectionsBilin_apply]

theorem map_tau_tmul (n : ℕ) {U U' : V.affineOpens} (h : U.1 ≤ U'.1) (y : Γ(L.tensorPow n, U'.1)) (s : Γ(L, U'.1)) :
    (L.tensorPow (n + 1)).presheaf.map (homOfLE h).op (tau L hLi n U' (y ⊗ₜ s)) =
      tau L hLi n U ((L.tensorPow n).presheaf.map (homOfLE h).op y ⊗ₜ L.presheaf.map (homOfLE h).op s) := by
  rw [tau_tmul, tau_tmul]
  exact Scheme.Modules.map_tensorSections (homOfLE h) y s

variable (I J : (ZZ Z₀).IdealSheafData)
  (e : ∀ O : (ZZ Z₀).affineOpens, ↥(I.ideal O) ⊗[Γ(ZZ Z₀, O.1)] Γ(M Z₀ L, O.1) ≃ₗ[Γ(ZZ Z₀, O.1)] ↥(J.ideal O))
  (β : ∀ U : V.affineOpens,
    Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U.1) ⊗[Γ(V, U.1)] Γ(L, U.1) ≃ₗ[Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U.1)] Γ(M Z₀ L, ι Z₀ ⁻¹ᵁ U.1))

noncomputable def twistIso (n : ℕ) (U : V.affineOpens) :
    ↥(I.ideal (W Z₀ U)) ⊗[Γ(V, U.1)] Γ(L.tensorPow (n + 1), U.1) ≃ₗ[Γ(V, U.1)]
      ↥(J.ideal (W Z₀ U)) ⊗[Γ(V, U.1)] Γ(L.tensorPow n, U.1) :=
  (TensorProduct.congr (LinearEquiv.refl _ _) (tau L hLi n U).symm).trans <|
  (TensorProduct.congr (LinearEquiv.refl _ _) (TensorProduct.comm _ _ _)).trans <|
  (TensorProduct.assoc Γ(V, U.1) _ _ _).symm.trans <|
  TensorProduct.congr
    ((((TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(V, U.1) Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U.1)
        Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U.1) ↥(I.ideal (W Z₀ U)) Γ(L, U.1)).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) (β U))).trans (e (W Z₀ U))).restrictScalars Γ(V, U.1))
    (LinearEquiv.refl _ _)

theorem twistIso_tmul (n : ℕ) (U : V.affineOpens) (a : ↥(I.ideal (W Z₀ U))) (y : Γ(L.tensorPow n, U.1)) (s : Γ(L, U.1)) :
    twistIso Z₀ L hLi I J e β n U (a ⊗ₜ tau L hLi n U (y ⊗ₜ s)) = e (W Z₀ U) (a ⊗ₜ β U (1 ⊗ₜ s)) ⊗ₜ y := by
  simp only [twistIso, LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    LinearEquiv.symm_apply_apply, TensorProduct.comm_tmul, TensorProduct.assoc_symm_tmul,
    LinearEquiv.restrictScalars_apply, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul]

noncomputable def Theta (n : ℕ) (U : V.affineOpens) :
    ((KI π Z₀ I).twist (L.tensorPow (n + 1))).obj U.1 ≃ₗ[Γ(V, U.1)] ((KI π Z₀ J).twist (L.tensorPow n)).obj U.1 :=
  (TensorProduct.congr (kappa π Z₀ I U) (LinearEquiv.refl Γ(V, U.1) Γ(L.tensorPow (n + 1), U.1))).trans <|
  (twistIso Z₀ L hLi I J e β n U).trans
  (TensorProduct.congr (kappa π Z₀ J U) (LinearEquiv.refl Γ(V, U.1) Γ(L.tensorPow n, U.1))).symm

theorem Theta_tmul (n : ℕ) (U : V.affineOpens) (x : (KI π Z₀ I).obj U.1) (y : Γ(L.tensorPow n, U.1)) (s : Γ(L, U.1)) :
    Theta π Z₀ L hLi I J e β n U
        ((x ⊗ₜ[Γ(V, U.1)] tau L hLi n U (y ⊗ₜ s) : (KI π Z₀ I).obj U.1 ⊗[Γ(V, U.1)] Γ(L.tensorPow (n + 1), U.1))) =
      (((kappa π Z₀ J U).symm (e (W Z₀ U) (kappa π Z₀ I U x ⊗ₜ β U (1 ⊗ₜ s)))) ⊗ₜ[Γ(V, U.1)] y :
        (KI π Z₀ J).obj U.1 ⊗[Γ(V, U.1)] Γ(L.tensorPow n, U.1)) := by
  show (TensorProduct.congr (kappa π Z₀ J U) (LinearEquiv.refl Γ(V, U.1) Γ(L.tensorPow n, U.1))).symm
      (twistIso Z₀ L hLi I J e β n U (TensorProduct.congr (kappa π Z₀ I U) (LinearEquiv.refl _ _)
        (x ⊗ₜ[Γ(V, U.1)] tau L hLi n U (y ⊗ₜ s)))) = _
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, twistIso_tmul, TensorProduct.congr_symm_tmul,
    LinearEquiv.refl_symm, LinearEquiv.refl_apply]

noncomputable def ThetaHom (n : ℕ)
    (henat : ∀ (O O' : (ZZ Z₀).affineOpens) (h : (O' : (ZZ Z₀).Opens) ≤ O) (a : ↥(I.ideal O)) (m : Γ(M Z₀ L, O)),
      (ZZ Z₀).presheaf.map (homOfLE h).op (e O (a ⊗ₜ m) : Γ(ZZ Z₀, O)) =
        e O' (⟨(ZZ Z₀).presheaf.map (homOfLE h).op a, I.ideal_le_comap_ideal h a.2⟩ ⊗ₜ
          (M Z₀ L).presheaf.map (homOfLE h).op m))
    (hβ : ∀ (U : V.affineOpens) (s : Γ(L, U.1)), β U (1 ⊗ₜ s) = eta Z₀ L U.1 s) :
    AffHom ((KI π Z₀ I).twist (L.tensorPow (n + 1))) ((KI π Z₀ J).twist (L.tensorPow n)) where
  app U :=
    { toFun := Theta π Z₀ L hLi I J e β n U
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r t => map_smul (Theta π Z₀ L hLi I J e β n U)
        ((Scheme.TwoAffineOpenCover.algebraOfHom π U.1).algebraMap r) t }
  app_smul U a t := map_smul (Theta π Z₀ L hLi I J e β n U) a t
  naturality {U U'} h := by
    refine LinearMap.ext fun t => ?_
    show Theta π Z₀ L hLi I J e β n U (((KI π Z₀ I).twist (L.tensorPow (n + 1))).res h t) =
      ((KI π Z₀ J).twist (L.tensorPow n)).res h (Theta π Z₀ L hLi I J e β n U' t)

    set Φ : (KI π Z₀ I).obj U'.1 ⊗[Γ(V, U'.1)] Γ(L.tensorPow (n + 1), U'.1) → ((KI π Z₀ J).twist (L.tensorPow n)).obj U.1 :=
      fun t => Theta π Z₀ L hLi I J e β n U (((KI π Z₀ I).twist (L.tensorPow (n + 1))).res h t) with hΦ
    set Ψ : (KI π Z₀ I).obj U'.1 ⊗[Γ(V, U'.1)] Γ(L.tensorPow (n + 1), U'.1) → ((KI π Z₀ J).twist (L.tensorPow n)).obj U.1 :=
      fun t => ((KI π Z₀ J).twist (L.tensorPow n)).res h (Theta π Z₀ L hLi I J e β n U' t) with hΨ
    have hΦ0 : Φ 0 = 0 := by
      show Theta π Z₀ L hLi I J e β n U (((KI π Z₀ I).twist (L.tensorPow (n + 1))).res h
        (0 : ((KI π Z₀ I).twist (L.tensorPow (n + 1))).obj U'.1)) = 0
      rw [map_zero, map_zero]
    have hΨ0 : Ψ 0 = 0 := by
      show ((KI π Z₀ J).twist (L.tensorPow n)).res h (Theta π Z₀ L hLi I J e β n U'
        (0 : ((KI π Z₀ I).twist (L.tensorPow (n + 1))).obj U'.1)) = 0
      rw [map_zero, map_zero]
    have hΦa : ∀ a b, Φ (a + b) = Φ a + Φ b := fun a b => by
      simp only [hΦ]
      erw [LinearMap.map_add, LinearEquiv.map_add]
    have hΨa : ∀ a b, Ψ (a + b) = Ψ a + Ψ b := fun a b => by
      simp only [hΨ]
      erw [LinearEquiv.map_add, LinearMap.map_add]
    suffices H : ∀ t' : (KI π Z₀ I).obj U'.1 ⊗[Γ(V, U'.1)] Γ(L.tensorPow (n + 1), U'.1), Φ t' = Ψ t' from H t
    intro t'
    induction t' using TensorProduct.induction_on with
    | zero => rw [hΦ0, hΨ0]
    | add a b ha hb => rw [hΦa, hΨa, ha, hb]
    | tmul x m =>
      obtain ⟨w, rfl⟩ := (tau L hLi n U').surjective m
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, TensorProduct.tmul_zero, hΦ0, hΨ0]
      | add a b ha hb => rw [map_add, TensorProduct.tmul_add, hΦa, hΨa, ha, hb]
      | tmul y s =>
        simp only [hΦ, hΨ]

        rw [Theta_tmul]

        have eL : ((KI π Z₀ I).twist (L.tensorPow (n + 1))).res h
              ((x ⊗ₜ[Γ(V, U'.1)] tau L hLi n U' (y ⊗ₜ s) :
                (KI π Z₀ I).obj U'.1 ⊗[Γ(V, U'.1)] Γ(L.tensorPow (n + 1), U'.1))) =
            (((KI π Z₀ I).res h x) ⊗ₜ[Γ(V, U.1)]
              (L.tensorPow (n + 1)).presheaf.map (homOfLE h).op (tau L hLi n U' (y ⊗ₜ s)) :
                (KI π Z₀ I).obj U.1 ⊗[Γ(V, U.1)] Γ(L.tensorPow (n + 1), U.1)) := rfl
        rw [eL, map_tau_tmul, Theta_tmul]

        have eR : ((KI π Z₀ J).twist (L.tensorPow n)).res h
              ((((kappa π Z₀ J U').symm (e (W Z₀ U') (kappa π Z₀ I U' x ⊗ₜ β U' (1 ⊗ₜ s)))) ⊗ₜ[Γ(V, U'.1)] y :
                (KI π Z₀ J).obj U'.1 ⊗[Γ(V, U'.1)] Γ(L.tensorPow n, U'.1))) =
            (((KI π Z₀ J).res h ((kappa π Z₀ J U').symm (e (W Z₀ U') (kappa π Z₀ I U' x ⊗ₜ β U' (1 ⊗ₜ s))))) ⊗ₜ[Γ(V, U.1)]
              (L.tensorPow n).presheaf.map (homOfLE h).op y :
                (KI π Z₀ J).obj U.1 ⊗[Γ(V, U.1)] Γ(L.tensorPow n, U.1)) := rfl
        rw [eR]
        congr 1
        refine Subtype.ext ?_
        have e1 := KI_res_coe π Z₀ J h ((kappa π Z₀ J U').symm (e (W Z₀ U') (kappa π Z₀ I U' x ⊗ₜ β U' (1 ⊗ₜ s))))
        have e2 := kappa_symm_coe π Z₀ J U (e (W Z₀ U) (kappa π Z₀ I U ((KI π Z₀ I).res h x) ⊗ₜ
          β U (1 ⊗ₜ L.presheaf.map (homOfLE h).op s)))
        refine Eq.symm (e1.trans (Eq.trans ?_ e2.symm))
        rw [kappa_symm_coe, henat (W Z₀ U') (W Z₀ U) (W_le Z₀ h), hβ, hβ, map_eta]
        have ex : (⟨(ZZ Z₀).presheaf.map (homOfLE (W_le Z₀ h)).op ((kappa π Z₀ I U' x : ↥(I.ideal (W Z₀ U'))) :
              Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U'.1)), I.ideal_le_comap_ideal (W_le Z₀ h) (kappa π Z₀ I U' x).2⟩ :
              ↥(I.ideal (W Z₀ U))) = kappa π Z₀ I U ((KI π Z₀ I).res h x) :=
          Subtype.ext (KI_res_coe π Z₀ I h x).symm
        rw [ex]

theorem ThetaHom_bijective (n : ℕ) (henat) (hβ) (U : V.affineOpens) :
    Function.Bijective ((ThetaHom π Z₀ L hLi I J e β n henat hβ).app U) :=
  (Theta π Z₀ L hLi I J e β n U).bijective

end Theta

section Main

variable {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
  (K : V.OrderedAffineCover) (L : V.Modules)
  (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
  (Z₀ : Closeds V) (hZ₀ : (Z₀ : Set V).Nonempty)
  (hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme)

attribute [local instance] algVZ

include hL hZ₀ hint in
theorem main :
    ∃ (Y₁ Y₂ : Closeds V) (G₁ G₂ : OModulePresheaf π),
      Y₁ < Z₀ ∧ Y₂ < Z₀ ∧
      G₁.IsCoherent ∧ G₁.IsQuasicoherent ∧ G₁.SupportedIn Y₁ ∧
      G₂.IsCoherent ∧ G₂.IsQuasicoherent ∧ G₂.SupportedIn Y₂ ∧
      ∀ n : ℕ,
        ((OZ π Z₀).twist (L.tensorPow (n + 1))).eulerChar K - ((OZ π Z₀).twist (L.tensorPow n)).eulerChar K =
        (G₁.twist (L.tensorPow (n + 1))).eulerChar K - (G₂.twist (L.tensorPow n)).eulerChar K := by
  haveI : IsIntegral (ZZ Z₀) := hint
  have hLi : Scheme.Modules.IsInvertible L := ⟨hL⟩
  have hM : Scheme.Modules.IsInvertible (M Z₀ L) := hLi.pullback (ι Z₀)

  obtain ⟨φ, hφ⟩ := Scheme.Modules.IsInvertible.exists_functionField_presentation (M Z₀ L) hM
  obtain ⟨I, J, e, -, hIJ, -, henat⟩ :=
    Scheme.Modules.IsInvertible.exists_idealSheafData_tensor_linearEquiv_of_presentation (M Z₀ L) hM φ hφ

  have hβ' : ∀ U : V.affineOpens,
      ∃ βU : Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U.1) ⊗[Γ(V, U.1)] Γ(L, U.1) ≃ₗ[Γ(ZZ Z₀, ι Z₀ ⁻¹ᵁ U.1)] Γ(M Z₀ L, ι Z₀ ⁻¹ᵁ U.1),
        ∀ s : Γ(L, U.1), βU (1 ⊗ₜ s) = eta Z₀ L U.1 s := fun U =>
    Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback (ι Z₀) hLi U.1 U.2 (W Z₀ U).2
  choose β hβ using hβ'

  obtain ⟨O, hO⟩ := exists_affine_nonempty Z₀ hZ₀
  have hI : I ≠ ⊥ := ne_bot_of_ideal_ne_bot Z₀ I O (hIJ O hO).1
  have hJ : J ≠ ⊥ := ne_bot_of_ideal_ne_bot Z₀ J O (hIJ O hO).2
  refine ⟨YI Z₀ I, YI Z₀ J, OZI π Z₀ I, OZI π Z₀ J, YI_lt Z₀ I hint hI, YI_lt Z₀ J hint hJ,
    (OZI_good π Z₀ I).1, (OZI_good π Z₀ I).2.1, (OZI_good π Z₀ I).2.2,
    (OZI_good π Z₀ J).1, (OZI_good π Z₀ J).2.1, (OZI_good π Z₀ J).2.2, fun n => ?_⟩

  have h1 := eulerChar_twist_add π K L hL (sesI π Z₀ I) (KI_good π Z₀ I).1 (KI_good π Z₀ I).2
    (OZ_good π Z₀).1 (OZ_good π Z₀).2.1 (OZI_good π Z₀ I).1 (OZI_good π Z₀ I).2.1 (n + 1)
  have h2 := eulerChar_twist_add π K L hL (sesI π Z₀ J) (KI_good π Z₀ J).1 (KI_good π Z₀ J).2
    (OZ_good π Z₀).1 (OZ_good π Z₀).2.1 (OZI_good π Z₀ J).1 (OZI_good π Z₀ J).2.1 n
  have h3 := eulerChar_eq_of_bijective π K (ThetaHom π Z₀ L hLi I J e β n henat hβ)
    (ThetaHom_bijective π Z₀ L hLi I J e β n henat hβ)
  omega

end Main

end P2mTwistStep

theorem solution
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
    (K : V.OrderedAffineCover) (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (Z₀ : Closeds V) (hZ₀ : (Z₀ : Set V).Nonempty)
    (hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme) :
    ∃ (Y₁ Y₂ : Closeds V) (G₁ G₂ : OModulePresheaf π),
      Y₁ < Z₀ ∧ Y₂ < Z₀ ∧
      G₁.IsCoherent ∧ G₁.IsQuasicoherent ∧ G₁.SupportedIn Y₁ ∧
      G₂.IsCoherent ∧ G₂.IsQuasicoherent ∧ G₂.SupportedIn Y₂ ∧
      ∀ n : ℕ,
        ((OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι).twist
              (L.tensorPow (n + 1))).eulerChar K -
          ((OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι).twist
              (L.tensorPow n)).eulerChar K =
        (G₁.twist (L.tensorPow (n + 1))).eulerChar K - (G₂.twist (L.tensorPow n)).eulerChar K :=
  P2mTwistStep.main π K L hL Z₀ hZ₀ hint

end S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq (solution)
