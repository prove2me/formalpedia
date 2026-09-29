-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_isInvertible_sectionsOf_equiv_of_projective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/886c4cea-7c5f-56eb-828f-9a28a82f9fe5

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
import Theorems.Thm_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_tilde
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_of_bijective_app_of_le_opensRange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective

set_option autoImplicit false

universe u

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.congr_app tilde.map Scheme.Modules.Hom.app_smul IsOpenImmersion.of_comp Scheme.Modules.pullback tilde.toOpen_map_app Scheme.Hom Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom moduleSpecΓFunctor Spec Spec.map Scheme Scheme.Modules.Hom.id_app pullbackSpecIso Scheme.Modules.Hom.app tilde.isoTop IsOpenImmersion modulesSpecToSheaf tilde.functor StructureSheaf.globalSectionsIso IsAffineOpen Scheme.Modules tilde Scheme.Modules.map_smul tilde.toOpen Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.Modules.IsInvertible Scheme.Modules.IsLocallyFreeOfRank tilde.pullbackSpecIso Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Modules.bijective_unit_app_of_le_opensRange tilde.pullbackSpecIso_hom_app_top_unit_toOpen Scheme.Modules.isLocallyFreeOfRank_tilde Scheme.Modules.IsLocallyFreeOfRank.pullback Scheme.Modules.IsLocallyFreeOfRank.of_forall_exists_opens Scheme.Modules.exists_fibreProduct_sections_bijective Scheme.Modules.nonempty_pullback_iso_of_bijective_app_of_le_opensRange"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.congr_app Modules.Hom.app_smul Modules.pullback Hom.id_app Hom Γ Hom.preimage_inf Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.id_app Modules.Hom.app isoSpec Hom.comp_app Modules Opens Modules.map_smul restrict ΓSpecIso TwoAffineOpenCover Modules.IsInvertible Modules.IsLocallyFreeOfRank Modules.isLocallyFreeOfRank_one_iff_isInvertible Modules.bijective_unit_app_of_le_opensRange Modules.isLocallyFreeOfRank_tilde Modules.IsLocallyFreeOfRank.pullback Modules.IsLocallyFreeOfRank.of_forall_exists_opens Modules.exists_fibreProduct_sections_bijective Modules.nonempty_pullback_iso_of_bijective_app_of_le_opensRange"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "sectionsOf cover pullback isAffineOpen_U0 isAffineOpen_inf U1 U0 sup_eq_top isAffineOpen_U1"
namespace GlueInvertible
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry Opposite TopologicalSpace TensorProduct AlgebraicGeometry.Scheme.Modules"

variable {X : Scheme.{u}} (U0 U1 : X.Opens)

section Generic

variable {Y : Scheme.{u}}

omit U0 U1 in
theorem op_hom_eq {U V : Y.Opens} (i j : op U ⟶ op V) : i = j :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

omit U0 U1 in

theorem map_endo (M : Y.Modules) {U : Y.Opens} (i : op U ⟶ op U) (x : Γ(M, U)) :
    M.presheaf.map i x = x := by
  rw [op_hom_eq i (𝟙 _), CategoryTheory.Functor.map_id]; rfl

omit U0 U1 in

theorem map_map (M : Y.Modules) {U V W : Y.Opens} (i : op U ⟶ op V) (j : op V ⟶ op W) (x : Γ(M, U)) :
    M.presheaf.map j (M.presheaf.map i x) = M.presheaf.map (i ≫ j) x := by
  rw [Functor.map_comp]; rfl

omit U0 U1 in

theorem map_irrel (M : Y.Modules) {U V : Y.Opens} (i j : op U ⟶ op V) (x : Γ(M, U)) :
    M.presheaf.map i x = M.presheaf.map j x := by rw [op_hom_eq i j]

omit U0 U1 in

theorem ring_map_endo {U : Y.Opens} (i : op U ⟶ op U) (x : Y.presheaf.obj (op U)) :
    Y.presheaf.map i x = x := by
  rw [op_hom_eq i (𝟙 _), CategoryTheory.Functor.map_id]; rfl

omit U0 U1 in
theorem ring_map_map {U V W : Y.Opens} (i : op U ⟶ op V) (j : op V ⟶ op W) (x : Y.presheaf.obj (op U)) :
    Y.presheaf.map j (Y.presheaf.map i x) = Y.presheaf.map (i ≫ j) x := by
  rw [Functor.map_comp]; rfl

omit U0 U1 in

theorem app_naturality {M N : Y.Modules} (φ : M ⟶ N) {U V : Y.Opens} (i : op U ⟶ op V) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map i x) = N.presheaf.map i (φ.app U x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i) x

omit U0 U1 in

theorem bijective_app_of_iso {M N : Y.Modules} (e : M ≅ N) (U : Y.Opens) :
    Function.Bijective (e.hom.app U) := by
  rw [← ConcreteCategory.isIso_iff_bijective]
  exact ⟨⟨e.inv.app U, by rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app],
    by rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]⟩⟩

omit U0 U1 in
theorem bijective_app_comp {M N K : Y.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (U : Y.Opens)
    (hφ : Function.Bijective (φ.app U)) (hψ : Function.Bijective (ψ.app U)) :
    Function.Bijective ((φ ≫ ψ).app U) := by
  rw [Scheme.Modules.Hom.comp_app]; exact hψ.comp hφ

omit U0 U1 in

theorem isLocallyFreeOfRank_of_iso {n : ℕ} {M N : Y.Modules} (e : M ≅ N)
    (h : Scheme.Modules.IsLocallyFreeOfRank n M) : Scheme.Modules.IsLocallyFreeOfRank n N := by
  refine ⟨fun y => ?_⟩
  obtain ⟨U, hyU, ⟨eU⟩⟩ := h.1 y
  exact ⟨U, hyU, ⟨((Scheme.Modules.pullback U.ι).mapIso e).symm ≪≫ eU⟩⟩

end Generic

private abbrev _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible.ρ0 : X.presheaf.obj (op U0) ⟶ X.presheaf.obj (op (U0 ⊓ U1)) :=
  X.presheaf.map (homOfLE inf_le_left).op
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible" "ρ0"

private abbrev _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible.ρ1 : X.presheaf.obj (op U1) ⟶ X.presheaf.obj (op (U0 ⊓ U1)) :=
  X.presheaf.map (homOfLE inf_le_right).op
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible" "ρ1"

abbrev g0 : Spec (X.presheaf.obj (op (U0 ⊓ U1))) ⟶ Spec (X.presheaf.obj (op U0)) := Spec.map (ρ0 U0 U1)

abbrev g1 : Spec (X.presheaf.obj (op (U0 ⊓ U1))) ⟶ Spec (X.presheaf.obj (op U1)) := Spec.map (ρ1 U0 U1)

variable (hU0 : IsAffineOpen U0) (hU1 : IsAffineOpen U1) (hU01 : IsAffineOpen (U0 ⊓ U1))

theorem g0_f0 : g0 U0 U1 ≫ hU0.fromSpec = hU01.fromSpec :=
  hU0.map_fromSpec hU01 (homOfLE inf_le_left).op
theorem g1_f1 : g1 U0 U1 ≫ hU1.fromSpec = hU01.fromSpec :=
  hU1.map_fromSpec hU01 (homOfLE inf_le_right).op
include hU01 in
theorem g1_f1_eq_g0_f0 : g1 U0 U1 ≫ hU1.fromSpec = g0 U0 U1 ≫ hU0.fromSpec :=
  (g1_f1 U0 U1 hU1 hU01).trans (g0_f0 U0 U1 hU0 hU01).symm

include hU0 hU01 in
theorem isOpenImmersion_g0 : IsOpenImmersion (g0 U0 U1) := by
  have : IsOpenImmersion (g0 U0 U1 ≫ hU0.fromSpec) := by rw [g0_f0 U0 U1 hU0 hU01]; infer_instance
  exact IsOpenImmersion.of_comp _ hU0.fromSpec

include hU1 hU01 in
theorem isOpenImmersion_g1 : IsOpenImmersion (g1 U0 U1) := by
  have : IsOpenImmersion (g1 U0 U1 ≫ hU1.fromSpec) := by rw [g1_f1 U0 U1 hU1 hU01]; infer_instance
  exact IsOpenImmersion.of_comp _ hU1.fromSpec

omit U0 U1 in

theorem preimage_le_opensRange_of_comp {Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f]
    [IsOpenImmersion g] (h : Z ⟶ X) [IsOpenImmersion h] (hgf : g ≫ f = h) {W : X.Opens}
    (hW : W ≤ h.opensRange) :
    f ⁻¹ᵁ W ≤ g.opensRange := by
  intro y hy
  obtain ⟨z, hz⟩ := hW hy
  refine ⟨z, f.isOpenEmbedding.injective ?_⟩
  rw [← hgf] at hz
  simpa using hz

include hU01 in
theorem preimage_f1_le_opensRange_g1 [IsOpenImmersion (g1 U0 U1)] {W : X.Opens} (hW : W ≤ U0) :
    hU1.fromSpec ⁻¹ᵁ W ≤ (g1 U0 U1).opensRange := by
  have h1 : hU1.fromSpec ⁻¹ᵁ W = hU1.fromSpec ⁻¹ᵁ (W ⊓ U1) := by
    rw [Scheme.Hom.preimage_inf]
    conv_lhs => rw [← inf_top_eq (hU1.fromSpec ⁻¹ᵁ W)]
    rw [← hU1.fromSpec_preimage_self]
  rw [h1]
  refine preimage_le_opensRange_of_comp (g1 U0 U1) hU1.fromSpec hU01.fromSpec (g1_f1 U0 U1 hU1 hU01) ?_
  rw [hU01.opensRange_fromSpec]
  exact inf_le_inf_right _ hW

include hU01 in
theorem preimage_f0_le_opensRange_g0 [IsOpenImmersion (g0 U0 U1)] {W : X.Opens} (hW : W ≤ U1) :
    hU0.fromSpec ⁻¹ᵁ W ≤ (g0 U0 U1).opensRange := by
  have h1 : hU0.fromSpec ⁻¹ᵁ W = hU0.fromSpec ⁻¹ᵁ (U0 ⊓ W) := by
    rw [Scheme.Hom.preimage_inf]
    conv_lhs => rw [← top_inf_eq (hU0.fromSpec ⁻¹ᵁ W)]
    rw [← hU0.fromSpec_preimage_self]
  rw [h1]
  refine preimage_le_opensRange_of_comp (g0 U0 U1) hU0.fromSpec hU01.fromSpec (g0_f0 U0 U1 hU0 hU01) ?_
  rw [hU01.opensRange_fromSpec]
  exact inf_le_inf_left _ hW

variable (P0 : Type u) [AddCommGroup P0] [Module (X.presheaf.obj (op U0)) P0]
variable (P1 : Type u) [AddCommGroup P1] [Module (X.presheaf.obj (op U1)) P1]

private abbrev _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible.M0 : (Spec (X.presheaf.obj (op U0))).Modules := tilde (ModuleCat.of (X.presheaf.obj (op U0)) P0)
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible" "M0"

private abbrev _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible.M1 : (Spec (X.presheaf.obj (op U1))).Modules := tilde (ModuleCat.of (X.presheaf.obj (op U1)) P1)
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible" "M1"

abbrev Q0 : ModuleCat (X.presheaf.obj (op (U0 ⊓ U1))) :=
  (ModuleCat.extendScalars (ρ0 U0 U1).hom).obj (ModuleCat.of (X.presheaf.obj (op U0)) P0)
abbrev Q1 : ModuleCat (X.presheaf.obj (op (U0 ⊓ U1))) :=
  (ModuleCat.extendScalars (ρ1 U0 U1).hom).obj (ModuleCat.of (X.presheaf.obj (op U1)) P1)

abbrev T0 : (Spec (X.presheaf.obj (op (U0 ⊓ U1)))).Modules := tilde (Q0 U0 U1 P0)

abbrev N0 : X.Modules := (pushforward hU0.fromSpec).obj (M0 U0 P0)

abbrev N1 : X.Modules := (pushforward hU1.fromSpec).obj (M1 U1 P1)

abbrev N01 : X.Modules := (pushforward (g0 U0 U1 ≫ hU0.fromSpec)).obj (T0 U0 U1 P0)

abbrev β0 : (Scheme.Modules.pullback (g0 U0 U1)).obj (M0 U0 P0) ≅ T0 U0 U1 P0 :=
  tilde.pullbackSpecIso (ρ0 U0 U1) (ModuleCat.of (X.presheaf.obj (op U0)) P0)

def a0 : M0 U0 P0 ⟶ (pushforward (g0 U0 U1)).obj (T0 U0 U1 P0) :=
  (pullbackPushforwardAdjunction (g0 U0 U1)).unit.app (M0 U0 P0) ≫
    (pushforward (g0 U0 U1)).map (β0 U0 U1 P0).hom

def a : N0 U0 hU0 P0 ⟶ N01 U0 U1 hU0 P0 :=
  (pushforward hU0.fromSpec).map (a0 U0 U1 P0) ≫ (pushforwardComp (g0 U0 U1) hU0.fromSpec).hom.app _

theorem a_app (W : X.Opens) :
    (a U0 U1 hU0 P0).app W =
      ((pullbackPushforwardAdjunction (g0 U0 U1)).unit.app (M0 U0 P0)).app (hU0.fromSpec ⁻¹ᵁ W) ≫
        (β0 U0 U1 P0).hom.app ((g0 U0 U1) ⁻¹ᵁ (hU0.fromSpec ⁻¹ᵁ W)) := by
  simp only [a, a0, Scheme.Modules.Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app]
  rfl

theorem a_app_apply (W : X.Opens) (s : Γ(N0 U0 hU0 P0, W)) :
    (a U0 U1 hU0 P0).app W s =
      ((β0 U0 U1 P0).hom.app ((g0 U0 U1) ⁻¹ᵁ (hU0.fromSpec ⁻¹ᵁ W)))
        ((((pullbackPushforwardAdjunction (g0 U0 U1)).unit.app (M0 U0 P0)).app (hU0.fromSpec ⁻¹ᵁ W))
          s) := by
  rw [a_app]
  rfl

section Sigma

variable (σ : letI := (ρ0 U0 U1).hom.toAlgebra; letI := (ρ1 U0 U1).hom.toAlgebra
   ((X.presheaf.obj (op (U0 ⊓ U1))) ⊗[X.presheaf.obj (op U0)] P0) ≃ₗ[X.presheaf.obj (op (U0 ⊓ U1))]
     ((X.presheaf.obj (op (U0 ⊓ U1))) ⊗[X.presheaf.obj (op U1)] P1))

set_option backward.isDefEq.respectTransparency false in

def σinv : Q1 U0 U1 P1 ⟶ Q0 U0 U1 P0 :=
  letI := (ρ0 U0 U1).hom.toAlgebra; letI := (ρ1 U0 U1).hom.toAlgebra
  ModuleCat.ofHom (X := Q1 U0 U1 P1) (Y := Q0 U0 U1 P0)
    { toFun := fun x => σ.symm x
      map_add' := fun x y => σ.symm.map_add x y
      map_smul' := fun r x => σ.symm.map_smul r x }

theorem σinv_apply (x : Q1 U0 U1 P1) :
    letI := (ρ0 U0 U1).hom.toAlgebra; letI := (ρ1 U0 U1).hom.toAlgebra
    σinv U0 U1 P0 P1 σ x = σ.symm x := rfl

set_option backward.isDefEq.respectTransparency false in
theorem bijective_σinv : Function.Bijective (σinv U0 U1 P0 P1 σ) :=
  letI := (ρ0 U0 U1).hom.toAlgebra; letI := (ρ1 U0 U1).hom.toAlgebra
  σ.symm.bijective

scoped instance : IsIso (σinv U0 U1 P0 P1 σ) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_σinv U0 U1 P0 P1 σ)

def β1 : (Scheme.Modules.pullback (g1 U0 U1)).obj (M1 U1 P1) ⟶ T0 U0 U1 P0 :=
  (tilde.pullbackSpecIso (ρ1 U0 U1) (ModuleCat.of (X.presheaf.obj (op U1)) P1)).hom ≫
    tilde.map (σinv U0 U1 P0 P1 σ)

scoped instance : IsIso (β1 U0 U1 P0 P1 σ) := by
  unfold β1
  haveI : IsIso (tilde.map (σinv U0 U1 P0 P1 σ)) :=
    (inferInstance : IsIso ((tilde.functor _).map (σinv U0 U1 P0 P1 σ)))
  infer_instance

def b0 : M1 U1 P1 ⟶ (pushforward (g1 U0 U1)).obj (T0 U0 U1 P0) :=
  (pullbackPushforwardAdjunction (g1 U0 U1)).unit.app (M1 U1 P1) ≫
    (pushforward (g1 U0 U1)).map (β1 U0 U1 P0 P1 σ)

def b : N1 U1 hU1 P1 ⟶ N01 U0 U1 hU0 P0 :=
  (pushforward hU1.fromSpec).map (b0 U0 U1 P0 P1 σ) ≫
    (pushforwardComp (g1 U0 U1) hU1.fromSpec).hom.app _ ≫
    (pushforwardCongr (g1_f1_eq_g0_f0 U0 U1 hU0 hU1 hU01)).hom.app _

theorem b_app (W : X.Opens) :
    (b U0 U1 hU0 hU1 hU01 P0 P1 σ).app W =
      ((pullbackPushforwardAdjunction (g1 U0 U1)).unit.app (M1 U1 P1)).app (hU1.fromSpec ⁻¹ᵁ W) ≫
        (β1 U0 U1 P0 P1 σ).app ((g1 U0 U1) ⁻¹ᵁ (hU1.fromSpec ⁻¹ᵁ W)) ≫
        (T0 U0 U1 P0).presheaf.map (eqToHom (congrArg (fun f => f ⁻¹ᵁ W)
          (g1_f1_eq_g0_f0 U0 U1 hU0 hU1 hU01).symm)).op := by
  simp only [b, b0, Scheme.Modules.Hom.comp_app, pushforward_map_app, pushforwardCongr_hom_app_app]
  rfl

theorem b_app_apply (W : X.Opens) (s : Γ(N1 U1 hU1 P1, W)) :
    (b U0 U1 hU0 hU1 hU01 P0 P1 σ).app W s =
      (T0 U0 U1 P0).presheaf.map (eqToHom (congrArg (fun f => f ⁻¹ᵁ W)
          (g1_f1_eq_g0_f0 U0 U1 hU0 hU1 hU01).symm)).op
      (((β1 U0 U1 P0 P1 σ).app ((g1 U0 U1) ⁻¹ᵁ (hU1.fromSpec ⁻¹ᵁ W)))
        ((((pullbackPushforwardAdjunction (g1 U0 U1)).unit.app (M1 U1 P1)).app (hU1.fromSpec ⁻¹ᵁ W))
          s)) := by
  rw [b_app]
  rfl

include hU01 in
theorem bijective_a_app {W : X.Opens} (hW : W ≤ U1) :
    Function.Bijective ((a U0 U1 hU0 P0).app W) := by
  haveI := isOpenImmersion_g0 U0 U1 hU0 hU01
  refine bijective_app_comp _ _ W ?_
    (bijective_app_of_iso ((pushforwardComp (g0 U0 U1) hU0.fromSpec).app (T0 U0 U1 P0)) W)
  rw [pushforward_map_app]
  refine bijective_app_comp _ _ _ ?_ ?_
  · exact Scheme.Modules.bijective_unit_app_of_le_opensRange (g0 U0 U1) (M0 U0 P0) _
      (preimage_f0_le_opensRange_g0 U0 U1 hU0 hU01 hW)
  · exact bijective_app_of_iso ((pushforward (g0 U0 U1)).mapIso (β0 U0 U1 P0)) _

theorem bijective_b_app {W : X.Opens} (hW : W ≤ U0) :
    Function.Bijective ((b U0 U1 hU0 hU1 hU01 P0 P1 σ).app W) := by
  haveI := isOpenImmersion_g1 U0 U1 hU1 hU01
  refine bijective_app_comp _ _ W ?_ (bijective_app_comp _ _ W
    (bijective_app_of_iso ((pushforwardComp (g1 U0 U1) hU1.fromSpec).app (T0 U0 U1 P0)) W)
    (bijective_app_of_iso ((pushforwardCongr (g1_f1_eq_g0_f0 U0 U1 hU0 hU1 hU01)).app
      (T0 U0 U1 P0)) W))
  rw [pushforward_map_app]
  refine bijective_app_comp _ _ _ ?_ ?_
  · exact Scheme.Modules.bijective_unit_app_of_le_opensRange (g1 U0 U1) (M1 U1 P1) _
      (preimage_f1_le_opensRange_g1 U0 U1 hU1 hU01 hW)
  · exact bijective_app_of_iso (asIso ((pushforward (g1 U0 U1)).map (β1 U0 U1 P0 P1 σ))) _

end Sigma

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.congr_app tilde.map Scheme.Modules.Hom.app_smul IsOpenImmersion.of_comp Scheme.Modules.pullback tilde.toOpen_map_app Scheme.Hom Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom moduleSpecΓFunctor Spec Spec.map Scheme Scheme.Modules.Hom.id_app pullbackSpecIso Scheme.Modules.Hom.app tilde.isoTop IsOpenImmersion modulesSpecToSheaf tilde.functor StructureSheaf.globalSectionsIso IsAffineOpen Scheme.Modules tilde Scheme.Modules.map_smul tilde.toOpen Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.Modules.IsInvertible Scheme.Modules.IsLocallyFreeOfRank tilde.pullbackSpecIso Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Modules.bijective_unit_app_of_le_opensRange tilde.pullbackSpecIso_hom_app_top_unit_toOpen Scheme.Modules.isLocallyFreeOfRank_tilde Scheme.Modules.IsLocallyFreeOfRank.pullback Scheme.Modules.IsLocallyFreeOfRank.of_forall_exists_opens Scheme.Modules.exists_fibreProduct_sections_bijective Scheme.Modules.nonempty_pullback_iso_of_bijective_app_of_le_opensRange"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.congr_app Modules.Hom.app_smul Modules.pullback Hom.id_app Hom Γ Hom.preimage_inf Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.id_app Modules.Hom.app isoSpec Hom.comp_app Modules Opens Modules.map_smul restrict ΓSpecIso TwoAffineOpenCover Modules.IsInvertible Modules.IsLocallyFreeOfRank Modules.isLocallyFreeOfRank_one_iff_isInvertible Modules.bijective_unit_app_of_le_opensRange Modules.isLocallyFreeOfRank_tilde Modules.IsLocallyFreeOfRank.pullback Modules.IsLocallyFreeOfRank.of_forall_exists_opens Modules.exists_fibreProduct_sections_bijective Modules.nonempty_pullback_iso_of_bijective_app_of_le_opensRange"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "sectionsOf cover pullback isAffineOpen_U0 isAffineOpen_inf U1 U0 sup_eq_top isAffineOpen_U1"
namespace GlueInvertible
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry Opposite TopologicalSpace TensorProduct AlgebraicGeometry.Scheme.Modules"

variable {X : Scheme.{u}} (U0 U1 : X.Opens)
  (hU0 : IsAffineOpen U0) (hU1 : IsAffineOpen U1) (hU01 : IsAffineOpen (U0 ⊓ U1))
variable (P0 : Type u) [AddCommGroup P0] [Module (X.presheaf.obj (op U0)) P0]
variable (P1 : Type u) [AddCommGroup P1] [Module (X.presheaf.obj (op U1)) P1]
variable (σ : letI := (ρ0 U0 U1).hom.toAlgebra; letI := (ρ1 U0 U1).hom.toAlgebra
   ((X.presheaf.obj (op (U0 ⊓ U1))) ⊗[X.presheaf.obj (op U0)] P0) ≃ₗ[X.presheaf.obj (op (U0 ⊓ U1))]
     ((X.presheaf.obj (op (U0 ⊓ U1))) ⊗[X.presheaf.obj (op U1)] P1))

theorem glue_exists : ∃ (L : X.Modules) (π₀ : L ⟶ N0 U0 hU0 P0) (π₁ : L ⟶ N1 U1 hU1 P1),
    π₀ ≫ a U0 U1 hU0 P0 = π₁ ≫ b U0 U1 hU0 hU1 hU01 P0 P1 σ ∧
      (∀ U : X.Opens, Function.Injective fun s : Γ(L, U) => (π₀.app U s, π₁.app U s)) ∧
      (∀ (U : X.Opens) (s₀ : Γ(N0 U0 hU0 P0, U)) (s₁ : Γ(N1 U1 hU1 P1, U)),
        (a U0 U1 hU0 P0).app U s₀ = (b U0 U1 hU0 hU1 hU01 P0 P1 σ).app U s₁ →
        ∃ s : Γ(L, U), π₀.app U s = s₀ ∧ π₁.app U s = s₁) :=
  Scheme.Modules.exists_fibreProduct_sections_bijective _ _

def L : X.Modules := (glue_exists U0 U1 hU0 hU1 hU01 P0 P1 σ).choose

def π0 : L U0 U1 hU0 hU1 hU01 P0 P1 σ ⟶ N0 U0 hU0 P0 := (glue_exists U0 U1 hU0 hU1 hU01 P0 P1 σ).choose_spec.choose

def π1 : L U0 U1 hU0 hU1 hU01 P0 P1 σ ⟶ N1 U1 hU1 P1 := (glue_exists U0 U1 hU0 hU1 hU01 P0 P1 σ).choose_spec.choose_spec.choose

theorem π_comm : π0 U0 U1 hU0 hU1 hU01 P0 P1 σ ≫ a U0 U1 hU0 P0 = π1 U0 U1 hU0 hU1 hU01 P0 P1 σ ≫ b U0 U1 hU0 hU1 hU01 P0 P1 σ :=
  (glue_exists U0 U1 hU0 hU1 hU01 P0 P1 σ).choose_spec.choose_spec.choose_spec.1

theorem π_inj (W : X.Opens) : Function.Injective fun s : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, W) =>
    ((π0 U0 U1 hU0 hU1 hU01 P0 P1 σ).app W s, (π1 U0 U1 hU0 hU1 hU01 P0 P1 σ).app W s) :=
  (glue_exists U0 U1 hU0 hU1 hU01 P0 P1 σ).choose_spec.choose_spec.choose_spec.2.1 W

theorem π_lift (W : X.Opens) (s₀ : Γ(N0 U0 hU0 P0, W)) (s₁ : Γ(N1 U1 hU1 P1, W))
    (h : (a U0 U1 hU0 P0).app W s₀ = (b U0 U1 hU0 hU1 hU01 P0 P1 σ).app W s₁) :
    ∃ s : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, W), (π0 U0 U1 hU0 hU1 hU01 P0 P1 σ).app W s = s₀ ∧ (π1 U0 U1 hU0 hU1 hU01 P0 P1 σ).app W s = s₁ :=
  (glue_exists U0 U1 hU0 hU1 hU01 P0 P1 σ).choose_spec.choose_spec.choose_spec.2.2 W s₀ s₁ h

theorem π_comm_app (W : X.Opens) (s : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, W)) :
    (a U0 U1 hU0 P0).app W ((π0 U0 U1 hU0 hU1 hU01 P0 P1 σ).app W s) = (b U0 U1 hU0 hU1 hU01 P0 P1 σ).app W ((π1 U0 U1 hU0 hU1 hU01 P0 P1 σ).app W s) := by
  have h := congrArg (fun φ => Scheme.Modules.Hom.app φ W s) (π_comm U0 U1 hU0 hU1 hU01 P0 P1 σ)
  simp only [Scheme.Modules.Hom.comp_app] at h
  exact h

theorem bijective_π0_app {W : X.Opens} (hW : W ≤ U0) :
    Function.Bijective ((π0 U0 U1 hU0 hU1 hU01 P0 P1 σ).app W) := by
  obtain ⟨binj, bsurj⟩ := bijective_b_app U0 U1 hU0 hU1 hU01 P0 P1 σ hW
  constructor
  · intro s t hst
    apply π_inj U0 U1 hU0 hU1 hU01 P0 P1 σ W
    refine Prod.ext hst (binj ?_)
    rw [← π_comm_app, ← π_comm_app, hst]
  · intro s₀
    obtain ⟨s₁, hs₁⟩ := bsurj ((a U0 U1 hU0 P0).app W s₀)
    obtain ⟨s, hs, -⟩ := π_lift U0 U1 hU0 hU1 hU01 P0 P1 σ W s₀ s₁ hs₁.symm
    exact ⟨s, hs⟩

theorem bijective_π1_app {W : X.Opens} (hW : W ≤ U1) :
    Function.Bijective ((π1 U0 U1 hU0 hU1 hU01 P0 P1 σ).app W) := by
  obtain ⟨ainj, asurj⟩ := bijective_a_app U0 U1 hU0 hU01 P0 hW
  constructor
  · intro s t hst
    apply π_inj U0 U1 hU0 hU1 hU01 P0 P1 σ W
    refine Prod.ext (ainj ?_) hst
    rw [π_comm_app, π_comm_app, hst]
  · intro s₁
    obtain ⟨s₀, hs₀⟩ := asurj ((b U0 U1 hU0 hU1 hU01 P0 P1 σ).app W s₁)
    obtain ⟨s, -, hs⟩ := π_lift U0 U1 hU0 hU1 hU01 P0 P1 σ W s₀ s₁ hs₀
    exact ⟨s, hs⟩

theorem nonempty_pullback_f0_iso :
    Nonempty ((Scheme.Modules.pullback hU0.fromSpec).obj (L U0 U1 hU0 hU1 hU01 P0 P1 σ) ≅ M0 U0 P0) :=
  Scheme.Modules.nonempty_pullback_iso_of_bijective_app_of_le_opensRange hU0.fromSpec (M0 U0 P0)
    (L U0 U1 hU0 hU1 hU01 P0 P1 σ) (π0 U0 U1 hU0 hU1 hU01 P0 P1 σ) (fun _ hW => bijective_π0_app U0 U1 hU0 hU1 hU01 P0 P1 σ (hW.trans_eq hU0.opensRange_fromSpec))

theorem nonempty_pullback_f1_iso :
    Nonempty ((Scheme.Modules.pullback hU1.fromSpec).obj (L U0 U1 hU0 hU1 hU01 P0 P1 σ) ≅ M1 U1 P1) :=
  Scheme.Modules.nonempty_pullback_iso_of_bijective_app_of_le_opensRange hU1.fromSpec (M1 U1 P1)
    (L U0 U1 hU0 hU1 hU01 P0 P1 σ) (π1 U0 U1 hU0 hU1 hU01 P0 P1 σ) (fun _ hW => bijective_π1_app U0 U1 hU0 hU1 hU01 P0 P1 σ (hW.trans_eq hU1.opensRange_fromSpec))

omit hU0 hU1 hU01 in

theorem isLocallyFreeOfRank_pullback_ι {U : X.Opens} (hU : IsAffineOpen U) (L : X.Modules) {n : ℕ}
    (h : Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pullback hU.fromSpec).obj L)) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pullback U.ι).obj L) := by
  have hι : U.ι = hU.isoSpec.hom ≫ hU.fromSpec := by
    rw [← hU.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
  exact isLocallyFreeOfRank_of_iso
    ((pullbackComp hU.isoSpec.hom hU.fromSpec).app L ≪≫ ((pullbackCongr hι).app L).symm)
    (Scheme.Modules.IsLocallyFreeOfRank.pullback hU.isoSpec.hom h)

variable (hsup : U0 ⊔ U1 = ⊤)
variable [Module.Finite (X.presheaf.obj (op U0)) P0] [Module.Projective (X.presheaf.obj (op U0)) P0]
variable [Module.Finite (X.presheaf.obj (op U1)) P1] [Module.Projective (X.presheaf.obj (op U1)) P1]
variable
  (hrk0 : ∀ (K : Type u) [Field K] [Algebra (X.presheaf.obj (op U0)) K],
    Module.finrank K (K ⊗[X.presheaf.obj (op U0)] P0) = 1)
  (hrk1 : ∀ (K : Type u) [Field K] [Algebra (X.presheaf.obj (op U1)) K],
    Module.finrank K (K ⊗[X.presheaf.obj (op U1)] P1) = 1)

include hsup hrk0 hrk1 in
theorem isInvertible_L : Scheme.Modules.IsInvertible (L U0 U1 hU0 hU1 hU01 P0 P1 σ) := by
  rw [← Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible]
  refine Scheme.Modules.IsLocallyFreeOfRank.of_forall_exists_opens (fun x => ?_)
  have hx : x ∈ U0 ⊔ U1 := by rw [hsup]; trivial
  rcases Opens.mem_sup.mp hx with hx0 | hx1
  · refine ⟨U0, hx0, isLocallyFreeOfRank_pullback_ι hU0 _ ?_⟩
    obtain ⟨e⟩ := nonempty_pullback_f0_iso U0 U1 hU0 hU1 hU01 P0 P1 σ
    exact isLocallyFreeOfRank_of_iso e.symm
      (Scheme.Modules.isLocallyFreeOfRank_tilde (ModuleCat.of (X.presheaf.obj (op U0)) P0) 1 hrk0)
  · refine ⟨U1, hx1, isLocallyFreeOfRank_pullback_ι hU1 _ ?_⟩
    obtain ⟨e⟩ := nonempty_pullback_f1_iso U0 U1 hU0 hU1 hU01 P0 P1 σ
    exact isLocallyFreeOfRank_of_iso e.symm
      (Scheme.Modules.isLocallyFreeOfRank_tilde (ModuleCat.of (X.presheaf.obj (op U1)) P1) 1 hrk1)

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.congr_app tilde.map Scheme.Modules.Hom.app_smul IsOpenImmersion.of_comp Scheme.Modules.pullback tilde.toOpen_map_app Scheme.Hom Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom moduleSpecΓFunctor Spec Spec.map Scheme Scheme.Modules.Hom.id_app pullbackSpecIso Scheme.Modules.Hom.app tilde.isoTop IsOpenImmersion modulesSpecToSheaf tilde.functor StructureSheaf.globalSectionsIso IsAffineOpen Scheme.Modules tilde Scheme.Modules.map_smul tilde.toOpen Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.Modules.IsInvertible Scheme.Modules.IsLocallyFreeOfRank tilde.pullbackSpecIso Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Modules.bijective_unit_app_of_le_opensRange tilde.pullbackSpecIso_hom_app_top_unit_toOpen Scheme.Modules.isLocallyFreeOfRank_tilde Scheme.Modules.IsLocallyFreeOfRank.pullback Scheme.Modules.IsLocallyFreeOfRank.of_forall_exists_opens Scheme.Modules.exists_fibreProduct_sections_bijective Scheme.Modules.nonempty_pullback_iso_of_bijective_app_of_le_opensRange"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.congr_app Modules.Hom.app_smul Modules.pullback Hom.id_app Hom Γ Hom.preimage_inf Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.id_app Modules.Hom.app isoSpec Hom.comp_app Modules Opens Modules.map_smul restrict ΓSpecIso TwoAffineOpenCover Modules.IsInvertible Modules.IsLocallyFreeOfRank Modules.isLocallyFreeOfRank_one_iff_isInvertible Modules.bijective_unit_app_of_le_opensRange Modules.isLocallyFreeOfRank_tilde Modules.IsLocallyFreeOfRank.pullback Modules.IsLocallyFreeOfRank.of_forall_exists_opens Modules.exists_fibreProduct_sections_bijective Modules.nonempty_pullback_iso_of_bijective_app_of_le_opensRange"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "sectionsOf cover pullback isAffineOpen_U0 isAffineOpen_inf U1 U0 sup_eq_top isAffineOpen_U1"
namespace GlueInvertible
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry Opposite TopologicalSpace TensorProduct AlgebraicGeometry.Scheme.Modules"

section SpecGeneric

variable {R : CommRingCat.{u}}

theorem Γsmul_def (M : (Spec R).Modules) (r : R) (m : (moduleSpecΓFunctor (R := R)).obj M) :
    r • m = (((Spec R).presheaf.map (homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤)).op)
      ((StructureSheaf.globalSectionsIso R).hom r)) • (show Γ(M, ⊤) from m) := rfl

omit R in
theorem ring_res_top_top {Y : Scheme.{u}} (s : Y.presheaf.obj (op ⊤)) :
    (Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op) s = s :=
  ring_map_endo _ s

theorem Γsmul_def' (M : (Spec R).Modules) (r : R) (m : (moduleSpecΓFunctor (R := R)).obj M) :
    r • m = ((Scheme.ΓSpecIso R).inv r) • (show Γ(M, ⊤) from m) := by
  rw [Γsmul_def, ring_res_top_top]
  rfl

theorem map_toOpen (M : ModuleCat.{u} R) {U V : (Spec R).Opens} (i : op U ⟶ op V) (m : M) :
    (tilde M).presheaf.map i (tilde.toOpen M U m : Γ(tilde M, U)) = tilde.toOpen M V m := by
  rfl

theorem tilde_map_app_toOpen {M N : ModuleCat.{u} R} (f : M ⟶ N) (U : (Spec R).Opens) (m : M) :
    (tilde.map f).app U (tilde.toOpen M U m : Γ(tilde M, U)) = tilde.toOpen N U (f m) := by
  have h := tilde.toOpen_map_app f U
  exact ConcreteCategory.congr_hom h m

theorem toOpen_top_injective (M : ModuleCat.{u} R) : Function.Injective (tilde.toOpen M ⊤) :=
  (tilde.isoTop M).toLinearEquiv.injective

theorem toOpen_isoTop_inv (M : ModuleCat.{u} R) (y : (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op ⊤)) :
    tilde.toOpen M ⊤ ((tilde.isoTop M).inv y) = y := by
  change ((tilde.isoTop M).inv ≫ (tilde.isoTop M).hom) y = y
  rw [Iso.inv_hom_id]; rfl

end SpecGeneric
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"

section SchemeGeneric

variable {Y Z : Scheme.{u}}

theorem pushforward_map_apply (f : Y ⟶ Z) (M : Y.Modules) {U V : Z.Opens} (i : op U ⟶ op V)
    (x : Γ((pushforward f).obj M, U)) :
    ((pushforward f).obj M).presheaf.map i x = M.presheaf.map ((Opens.map f.base).map i.unop).op x := rfl

theorem bijective_map_of_eq (M : Y.Modules) {U V : Y.Opens} (h : U = V) (i : op U ⟶ op V) :
    Function.Bijective (M.presheaf.map i) := by
  subst h
  have : (M.presheaf.map i : Γ(M, U) → Γ(M, U)) = id := funext fun x => map_endo M i x
  rw [this]; exact Function.bijective_id

theorem pushforward_smul_def (f : Y ⟶ Z) (M : Y.Modules) (U : Z.Opens) (r : Z.presheaf.obj (op U))
    (x : Γ((pushforward f).obj M, U)) :
    r • x = (f.app U r) • (show Γ(M, f ⁻¹ᵁ U) from x) := rfl

theorem fromSpec_app_res_top {U : Y.Opens} (hU : IsAffineOpen U) (h : (⊤ : (Spec (Y.presheaf.obj (op U))).Opens) ≤ hU.fromSpec ⁻¹ᵁ U)
    (b : Y.presheaf.obj (op U)) :
    ((Spec (Y.presheaf.obj (op U))).presheaf.map (homOfLE h).op) (hU.fromSpec.app U b)
      = (Scheme.ΓSpecIso (Y.presheaf.obj (op U))).inv b := by
  have hb := congrArg (fun t => ((Spec (Y.presheaf.obj (op U))).presheaf.map (homOfLE h).op)
    ((CommRingCat.Hom.hom t) b)) hU.fromSpec_app_self
  simp only [CommRingCat.comp_apply] at hb
  refine hb.trans ?_
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  exact ring_map_endo _ _

end SchemeGeneric
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"

variable {X : Scheme.{u}} (U0 U1 : X.Opens)
  (hU0 : IsAffineOpen U0) (hU1 : IsAffineOpen U1) (hU01 : IsAffineOpen (U0 ⊓ U1))
variable (P0 : Type u) [AddCommGroup P0] [Module (X.presheaf.obj (op U0)) P0]
variable (P1 : Type u) [AddCommGroup P1] [Module (X.presheaf.obj (op U1)) P1]
variable (σ : letI := (ρ0 U0 U1).hom.toAlgebra; letI := (ρ1 U0 U1).hom.toAlgebra
   ((X.presheaf.obj (op (U0 ⊓ U1))) ⊗[X.presheaf.obj (op U0)] P0) ≃ₗ[X.presheaf.obj (op (U0 ⊓ U1))]
     ((X.presheaf.obj (op (U0 ⊓ U1))) ⊗[X.presheaf.obj (op U1)] P1))

theorem top_le_f0 : (⊤ : (Spec (X.presheaf.obj (op U0))).Opens) ≤ hU0.fromSpec ⁻¹ᵁ U0 :=
  hU0.fromSpec_preimage_self.ge
theorem top_le_f1 : (⊤ : (Spec (X.presheaf.obj (op U1))).Opens) ≤ hU1.fromSpec ⁻¹ᵁ U1 :=
  hU1.fromSpec_preimage_self.ge

abbrev G0 : ModuleCat (X.presheaf.obj (op U0)) :=
  (moduleSpecΓFunctor (R := X.presheaf.obj (op U0))).obj (M0 U0 P0)
abbrev G1 : ModuleCat (X.presheaf.obj (op U1)) :=
  (moduleSpecΓFunctor (R := X.presheaf.obj (op U1))).obj (M1 U1 P1)

def κ0 : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, U0) →ₗ[X.presheaf.obj (op U0)] G0 U0 P0 where
  toFun s := ((M0 U0 P0).presheaf.map (homOfLE (top_le_f0 U0 hU0)).op
      ((π0 U0 U1 hU0 hU1 hU01 P0 P1 σ).app U0 s : Γ(M0 U0 P0, hU0.fromSpec ⁻¹ᵁ U0)) : Γ(M0 U0 P0, ⊤))
  map_add' s t := by rw [map_add]; exact map_add _ _ _
  map_smul' r s := by
    simp only [RingHom.id_apply]
    rw [Scheme.Modules.Hom.app_smul, pushforward_smul_def, Scheme.Modules.map_smul, fromSpec_app_res_top]
    exact (Γsmul_def' (M0 U0 P0) r _).symm

theorem κ0_apply (s : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, U0)) : (κ0 U0 U1 hU0 hU1 hU01 P0 P1 σ s : Γ(M0 U0 P0, ⊤)) =
    (M0 U0 P0).presheaf.map (homOfLE (top_le_f0 U0 hU0)).op
      ((π0 U0 U1 hU0 hU1 hU01 P0 P1 σ).app U0 s : Γ(M0 U0 P0, hU0.fromSpec ⁻¹ᵁ U0)) := rfl

theorem bijective_κ0 : Function.Bijective (κ0 U0 U1 hU0 hU1 hU01 P0 P1 σ) :=
  (bijective_map_of_eq (M0 U0 P0) hU0.fromSpec_preimage_self _).comp
    (bijective_π0_app U0 U1 hU0 hU1 hU01 P0 P1 σ le_rfl)

def e0 : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, U0) ≃ₗ[X.presheaf.obj (op U0)] (ModuleCat.of (X.presheaf.obj (op U0)) P0) :=
  (LinearEquiv.ofBijective (κ0 U0 U1 hU0 hU1 hU01 P0 P1 σ) (bijective_κ0 U0 U1 hU0 hU1 hU01 P0 P1 σ)).trans
    (tilde.isoTop (ModuleCat.of (X.presheaf.obj (op U0)) P0)).toLinearEquiv.symm

theorem toOpen_e0 (s : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, U0)) :
    (tilde.toOpen (ModuleCat.of (X.presheaf.obj (op U0)) P0) ⊤ (e0 U0 U1 hU0 hU1 hU01 P0 P1 σ s) : Γ(M0 U0 P0, ⊤)) =
      (M0 U0 P0).presheaf.map (homOfLE (top_le_f0 U0 hU0)).op
        ((π0 U0 U1 hU0 hU1 hU01 P0 P1 σ).app U0 s : Γ(M0 U0 P0, hU0.fromSpec ⁻¹ᵁ U0)) := by
  show tilde.toOpen _ ⊤ ((tilde.isoTop _).inv (κ0 U0 U1 hU0 hU1 hU01 P0 P1 σ s)) = _
  rw [toOpen_isoTop_inv]
  rfl

def κ1 : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, U1) →ₗ[X.presheaf.obj (op U1)] G1 U1 P1 where
  toFun s := ((M1 U1 P1).presheaf.map (homOfLE (top_le_f1 U1 hU1)).op
      ((π1 U0 U1 hU0 hU1 hU01 P0 P1 σ).app U1 s : Γ(M1 U1 P1, hU1.fromSpec ⁻¹ᵁ U1)) : Γ(M1 U1 P1, ⊤))
  map_add' s t := by rw [map_add]; exact map_add _ _ _
  map_smul' r s := by
    simp only [RingHom.id_apply]
    rw [Scheme.Modules.Hom.app_smul, pushforward_smul_def, Scheme.Modules.map_smul, fromSpec_app_res_top]
    exact (Γsmul_def' (M1 U1 P1) r _).symm

theorem bijective_κ1 : Function.Bijective (κ1 U0 U1 hU0 hU1 hU01 P0 P1 σ) :=
  (bijective_map_of_eq (M1 U1 P1) hU1.fromSpec_preimage_self _).comp
    (bijective_π1_app U0 U1 hU0 hU1 hU01 P0 P1 σ le_rfl)

def e1 : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, U1) ≃ₗ[X.presheaf.obj (op U1)] (ModuleCat.of (X.presheaf.obj (op U1)) P1) :=
  (LinearEquiv.ofBijective (κ1 U0 U1 hU0 hU1 hU01 P0 P1 σ) (bijective_κ1 U0 U1 hU0 hU1 hU01 P0 P1 σ)).trans
    (tilde.isoTop (ModuleCat.of (X.presheaf.obj (op U1)) P1)).toLinearEquiv.symm

theorem toOpen_e1 (s : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, U1)) :
    (tilde.toOpen (ModuleCat.of (X.presheaf.obj (op U1)) P1) ⊤ (e1 U0 U1 hU0 hU1 hU01 P0 P1 σ s) : Γ(M1 U1 P1, ⊤)) =
      (M1 U1 P1).presheaf.map (homOfLE (top_le_f1 U1 hU1)).op
        ((π1 U0 U1 hU0 hU1 hU01 P0 P1 σ).app U1 s : Γ(M1 U1 P1, hU1.fromSpec ⁻¹ᵁ U1)) := by
  show tilde.toOpen _ ⊤ ((tilde.isoTop _).inv (κ1 U0 U1 hU0 hU1 hU01 P0 P1 σ s)) = _
  rw [toOpen_isoTop_inv]
  rfl

include hU01 in
theorem preimage_g0f0_inf : (g0 U0 U1 ≫ hU0.fromSpec) ⁻¹ᵁ (U0 ⊓ U1) = ⊤ := by
  rw [g0_f0 U0 U1 hU0 hU01, hU01.fromSpec_preimage_self]

include hU01 in
theorem top_le_g0f0 : (⊤ : (Spec (X.presheaf.obj (op (U0 ⊓ U1)))).Opens) ≤ (g0 U0 U1 ≫ hU0.fromSpec) ⁻¹ᵁ (U0 ⊓ U1) :=
  (preimage_g0f0_inf U0 U1 hU0 hU01).ge

abbrev G01 : ModuleCat (X.presheaf.obj (op (U0 ⊓ U1))) :=
  (moduleSpecΓFunctor (R := X.presheaf.obj (op (U0 ⊓ U1)))).obj (T0 U0 U1 P0)

include hU01 in

theorem g0f0_app_res_top (r : X.presheaf.obj (op (U0 ⊓ U1))) :
    ((Spec (X.presheaf.obj (op (U0 ⊓ U1)))).presheaf.map (homOfLE (top_le_g0f0 U0 U1 hU0 hU01)).op)
      ((g0 U0 U1 ≫ hU0.fromSpec).app (U0 ⊓ U1) r)
      = (Scheme.ΓSpecIso (X.presheaf.obj (op (U0 ⊓ U1)))).inv r := by
  rw [Scheme.Hom.congr_app (g0_f0 U0 U1 hU0 hU01) (U0 ⊓ U1)]
  have hb := congrArg (fun t => (CommRingCat.Hom.hom t) r) hU01.fromSpec_app_self
  simp only [CommRingCat.comp_apply] at hb ⊢
  rw [hb]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  exact ring_map_endo _ _

def κ01 : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, U0 ⊓ U1) →ₗ[X.presheaf.obj (op (U0 ⊓ U1))] G01 U0 U1 P0 where
  toFun s := ((T0 U0 U1 P0).presheaf.map (homOfLE (top_le_g0f0 U0 U1 hU0 hU01)).op
      ((a U0 U1 hU0 P0).app (U0 ⊓ U1) ((π0 U0 U1 hU0 hU1 hU01 P0 P1 σ).app (U0 ⊓ U1) s) :
        Γ(T0 U0 U1 P0, (g0 U0 U1 ≫ hU0.fromSpec) ⁻¹ᵁ (U0 ⊓ U1))) : Γ(T0 U0 U1 P0, ⊤))
  map_add' s t := by rw [map_add, map_add]; exact map_add _ _ _
  map_smul' r s := by
    simp only [RingHom.id_apply]
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, pushforward_smul_def,
      Scheme.Modules.map_smul, g0f0_app_res_top U0 U1 hU0 hU01]
    exact (Γsmul_def' (T0 U0 U1 P0) r _).symm

theorem bijective_κ01 : Function.Bijective (κ01 U0 U1 hU0 hU1 hU01 P0 P1 σ) :=
  (bijective_map_of_eq (T0 U0 U1 P0) (preimage_g0f0_inf U0 U1 hU0 hU01) _).comp
    ((bijective_a_app U0 U1 hU0 hU01 P0 inf_le_right).comp (bijective_π0_app U0 U1 hU0 hU1 hU01 P0 P1 σ inf_le_left))

def e01 : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, U0 ⊓ U1) ≃ₗ[X.presheaf.obj (op (U0 ⊓ U1))] (Q0 U0 U1 P0) :=
  (LinearEquiv.ofBijective (κ01 U0 U1 hU0 hU1 hU01 P0 P1 σ) (bijective_κ01 U0 U1 hU0 hU1 hU01 P0 P1 σ)).trans
    (tilde.isoTop (Q0 U0 U1 P0)).toLinearEquiv.symm

theorem toOpen_e01 (s : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, U0 ⊓ U1)) :
    (tilde.toOpen (Q0 U0 U1 P0) ⊤ (e01 U0 U1 hU0 hU1 hU01 P0 P1 σ s) : Γ(T0 U0 U1 P0, ⊤)) =
      (T0 U0 U1 P0).presheaf.map (homOfLE (top_le_g0f0 U0 U1 hU0 hU01)).op
      ((a U0 U1 hU0 P0).app (U0 ⊓ U1) ((π0 U0 U1 hU0 hU1 hU01 P0 P1 σ).app (U0 ⊓ U1) s) :
        Γ(T0 U0 U1 P0, (g0 U0 U1 ≫ hU0.fromSpec) ⁻¹ᵁ (U0 ⊓ U1))) := by
  show tilde.toOpen _ ⊤ ((tilde.isoTop _).inv (κ01 U0 U1 hU0 hU1 hU01 P0 P1 σ s)) = _
  rw [toOpen_isoTop_inv]
  rfl

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.congr_app tilde.map Scheme.Modules.Hom.app_smul IsOpenImmersion.of_comp Scheme.Modules.pullback tilde.toOpen_map_app Scheme.Hom Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom moduleSpecΓFunctor Spec Spec.map Scheme Scheme.Modules.Hom.id_app pullbackSpecIso Scheme.Modules.Hom.app tilde.isoTop IsOpenImmersion modulesSpecToSheaf tilde.functor StructureSheaf.globalSectionsIso IsAffineOpen Scheme.Modules tilde Scheme.Modules.map_smul tilde.toOpen Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.Modules.IsInvertible Scheme.Modules.IsLocallyFreeOfRank tilde.pullbackSpecIso Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Modules.bijective_unit_app_of_le_opensRange tilde.pullbackSpecIso_hom_app_top_unit_toOpen Scheme.Modules.isLocallyFreeOfRank_tilde Scheme.Modules.IsLocallyFreeOfRank.pullback Scheme.Modules.IsLocallyFreeOfRank.of_forall_exists_opens Scheme.Modules.exists_fibreProduct_sections_bijective Scheme.Modules.nonempty_pullback_iso_of_bijective_app_of_le_opensRange"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.congr_app Modules.Hom.app_smul Modules.pullback Hom.id_app Hom Γ Hom.preimage_inf Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.id_app Modules.Hom.app isoSpec Hom.comp_app Modules Opens Modules.map_smul restrict ΓSpecIso TwoAffineOpenCover Modules.IsInvertible Modules.IsLocallyFreeOfRank Modules.isLocallyFreeOfRank_one_iff_isInvertible Modules.bijective_unit_app_of_le_opensRange Modules.isLocallyFreeOfRank_tilde Modules.IsLocallyFreeOfRank.pullback Modules.IsLocallyFreeOfRank.of_forall_exists_opens Modules.exists_fibreProduct_sections_bijective Modules.nonempty_pullback_iso_of_bijective_app_of_le_opensRange"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "sectionsOf cover pullback isAffineOpen_U0 isAffineOpen_inf U1 U0 sup_eq_top isAffineOpen_U1"
namespace GlueInvertible
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry Opposite TopologicalSpace TensorProduct AlgebraicGeometry.Scheme.Modules"

section KeyBC

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat.{u} R)

theorem pullbackSpecIso_hom_app_unit_toOpen (V : (Spec R).Opens) (m : M) :
    ((tilde.pullbackSpecIso φ M).hom.app ((Spec.map φ) ⁻¹ᵁ V))
      ((((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app V)
        (tilde.toOpen M V m : Γ(tilde M, V))) =
    (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ((Spec.map φ) ⁻¹ᵁ V) ((1 : S) ⊗ₜ m) :
      Γ(tilde ((ModuleCat.extendScalars φ.hom).obj M), (Spec.map φ) ⁻¹ᵁ V)) := by
  have e1 : ((tilde M).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (tilde.toOpen M ⊤ m) : Γ(tilde M, V)) =
      tilde.toOpen M V m :=
    map_toOpen M (homOfLE (le_top : V ≤ ⊤)).op m
  have e2 := app_naturality ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M))
    (homOfLE (le_top : V ≤ ⊤)).op (tilde.toOpen M ⊤ m)
  have e3 := app_naturality (tilde.pullbackSpecIso φ M).hom
    ((Opens.map (Spec.map φ).base).map (homOfLE (le_top : V ≤ ⊤))).op
    (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤ (tilde.toOpen M ⊤ m))
  have key := tilde.pullbackSpecIso_hom_app_top_unit_toOpen φ M m
  rw [← e1]
  erw [e2, e3, key]
  exact map_toOpen _ _ _

end KeyBC
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"

variable {X : Scheme.{u}} (U0 U1 : X.Opens)
  (hU0 : IsAffineOpen U0) (hU1 : IsAffineOpen U1) (hU01 : IsAffineOpen (U0 ⊓ U1))
variable (P0 : Type u) [AddCommGroup P0] [Module (X.presheaf.obj (op U0)) P0]
variable (P1 : Type u) [AddCommGroup P1] [Module (X.presheaf.obj (op U1)) P1]
variable (σ : letI := (ρ0 U0 U1).hom.toAlgebra; letI := (ρ1 U0 U1).hom.toAlgebra
   ((X.presheaf.obj (op (U0 ⊓ U1))) ⊗[X.presheaf.obj (op U0)] P0) ≃ₗ[X.presheaf.obj (op (U0 ⊓ U1))]
     ((X.presheaf.obj (op (U0 ⊓ U1))) ⊗[X.presheaf.obj (op U1)] P1))

theorem res_π0_eq_toOpen (m : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, U0)) {V : (Spec (X.presheaf.obj (op U0))).Opens}
    (i : op (hU0.fromSpec ⁻¹ᵁ U0) ⟶ op V) :
    (M0 U0 P0).presheaf.map i ((π0 U0 U1 hU0 hU1 hU01 P0 P1 σ).app U0 m : Γ(M0 U0 P0, hU0.fromSpec ⁻¹ᵁ U0)) =
      tilde.toOpen (ModuleCat.of (X.presheaf.obj (op U0)) P0) V (e0 U0 U1 hU0 hU1 hU01 P0 P1 σ m) := by
  rw [map_irrel (M0 U0 P0) i ((homOfLE (top_le_f0 U0 hU0)).op ≫ (homOfLE (le_top : V ≤ ⊤)).op),
    ← map_map]
  erw [← toOpen_e0 U0 U1 hU0 hU1 hU01 P0 P1 σ m]
  exact map_toOpen _ _ _

theorem res_π1_eq_toOpen (m : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, U1)) {V : (Spec (X.presheaf.obj (op U1))).Opens}
    (i : op (hU1.fromSpec ⁻¹ᵁ U1) ⟶ op V) :
    (M1 U1 P1).presheaf.map i ((π1 U0 U1 hU0 hU1 hU01 P0 P1 σ).app U1 m : Γ(M1 U1 P1, hU1.fromSpec ⁻¹ᵁ U1)) =
      tilde.toOpen (ModuleCat.of (X.presheaf.obj (op U1)) P1) V (e1 U0 U1 hU0 hU1 hU01 P0 P1 σ m) := by
  rw [map_irrel (M1 U1 P1) i ((homOfLE (top_le_f1 U1 hU1)).op ≫ (homOfLE (le_top : V ≤ ⊤)).op),
    ← map_map]
  erw [← toOpen_e1 U0 U1 hU0 hU1 hU01 P0 P1 σ m]
  exact map_toOpen _ _ _

theorem β1_app_unit_toOpen (V : (Spec (X.presheaf.obj (op U1))).Opens) (p : P1) :
    ((β1 U0 U1 P0 P1 σ).app ((g1 U0 U1) ⁻¹ᵁ V))
      ((((pullbackPushforwardAdjunction (g1 U0 U1)).unit.app (M1 U1 P1)).app V)
        (tilde.toOpen (ModuleCat.of (X.presheaf.obj (op U1)) P1) V p : Γ(M1 U1 P1, V))) =
    (tilde.toOpen (Q0 U0 U1 P0) ((g1 U0 U1) ⁻¹ᵁ V)
      (σinv U0 U1 P0 P1 σ ((1 : X.presheaf.obj (op (U0 ⊓ U1))) ⊗ₜ p)) :
        Γ(T0 U0 U1 P0, (g1 U0 U1) ⁻¹ᵁ V)) := by
  unfold β1
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
  erw [pullbackSpecIso_hom_app_unit_toOpen (ρ1 U0 U1) (ModuleCat.of (X.presheaf.obj (op U1)) P1) V p]
  exact tilde_map_app_toOpen _ _ _

theorem sq0 (m : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, U0)) :
    e01 U0 U1 hU0 hU1 hU01 P0 P1 σ ((L U0 U1 hU0 hU1 hU01 P0 P1 σ).presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op m) =
      ((1 : X.presheaf.obj (op (U0 ⊓ U1))) ⊗ₜ[X.presheaf.obj (op U0)]
        (e0 U0 U1 hU0 hU1 hU01 P0 P1 σ m : ModuleCat.of (X.presheaf.obj (op U0)) P0) : Q0 U0 U1 P0) := by
  apply toOpen_top_injective (Q0 U0 U1 P0)
  refine (toOpen_e01 U0 U1 hU0 hU1 hU01 P0 P1 σ _).trans ?_
  have n1 := app_naturality (π0 U0 U1 hU0 hU1 hU01 P0 P1 σ) (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op m
  rw [n1, a_app_apply]
  have hs : ((N0 U0 hU0 P0).presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op
      ((π0 U0 U1 hU0 hU1 hU01 P0 P1 σ).app U0 m) : Γ(M0 U0 P0, hU0.fromSpec ⁻¹ᵁ (U0 ⊓ U1))) =
      tilde.toOpen (ModuleCat.of (X.presheaf.obj (op U0)) P0) (hU0.fromSpec ⁻¹ᵁ (U0 ⊓ U1)) (e0 U0 U1 hU0 hU1 hU01 P0 P1 σ m) :=
    res_π0_eq_toOpen U0 U1 hU0 hU1 hU01 P0 P1 σ m _
  rw [hs]
  have hk := pullbackSpecIso_hom_app_unit_toOpen (ρ0 U0 U1) (ModuleCat.of (X.presheaf.obj (op U0)) P0)
    (hU0.fromSpec ⁻¹ᵁ (U0 ⊓ U1)) (e0 U0 U1 hU0 hU1 hU01 P0 P1 σ m)
  erw [hk]
  exact map_toOpen _ _ _

theorem sq1 (m : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, U1)) :
    e01 U0 U1 hU0 hU1 hU01 P0 P1 σ ((L U0 U1 hU0 hU1 hU01 P0 P1 σ).presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op m) =
      σinv U0 U1 P0 P1 σ ((1 : X.presheaf.obj (op (U0 ⊓ U1))) ⊗ₜ[X.presheaf.obj (op U1)]
        (e1 U0 U1 hU0 hU1 hU01 P0 P1 σ m : ModuleCat.of (X.presheaf.obj (op U1)) P1)) := by
  apply toOpen_top_injective (Q0 U0 U1 P0)
  refine (toOpen_e01 U0 U1 hU0 hU1 hU01 P0 P1 σ _).trans ?_
  have n1 := app_naturality (π1 U0 U1 hU0 hU1 hU01 P0 P1 σ) (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op m
  rw [π_comm_app, n1, b_app_apply]
  have hs : ((N1 U1 hU1 P1).presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op
      ((π1 U0 U1 hU0 hU1 hU01 P0 P1 σ).app U1 m) : Γ(M1 U1 P1, hU1.fromSpec ⁻¹ᵁ (U0 ⊓ U1))) =
      tilde.toOpen (ModuleCat.of (X.presheaf.obj (op U1)) P1) (hU1.fromSpec ⁻¹ᵁ (U0 ⊓ U1)) (e1 U0 U1 hU0 hU1 hU01 P0 P1 σ m) :=
    res_π1_eq_toOpen U0 U1 hU0 hU1 hU01 P0 P1 σ m _
  rw [hs]
  have hk := β1_app_unit_toOpen U0 U1 P0 P1 σ (hU1.fromSpec ⁻¹ᵁ (U0 ⊓ U1)) (e1 U0 U1 hU0 hU1 hU01 P0 P1 σ m)
  erw [hk]
  exact (map_map _ _ _ _).trans (map_toOpen _ _ _)

theorem sq1' (m : Γ(L U0 U1 hU0 hU1 hU01 P0 P1 σ, U1)) :
    letI := (ρ0 U0 U1).hom.toAlgebra; letI := (ρ1 U0 U1).hom.toAlgebra
    σ (e01 U0 U1 hU0 hU1 hU01 P0 P1 σ ((L U0 U1 hU0 hU1 hU01 P0 P1 σ).presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op m)) =
      (1 : X.presheaf.obj (op (U0 ⊓ U1))) ⊗ₜ[X.presheaf.obj (op U1)]
        (e1 U0 U1 hU0 hU1 hU01 P0 P1 σ m : ModuleCat.of (X.presheaf.obj (op U1)) P1) := by
  rw [sq1]
  exact σ.apply_symm_apply _

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.congr_app tilde.map Scheme.Modules.Hom.app_smul IsOpenImmersion.of_comp Scheme.Modules.pullback tilde.toOpen_map_app Scheme.Hom Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom moduleSpecΓFunctor Spec Spec.map Scheme Scheme.Modules.Hom.id_app pullbackSpecIso Scheme.Modules.Hom.app tilde.isoTop IsOpenImmersion modulesSpecToSheaf tilde.functor StructureSheaf.globalSectionsIso IsAffineOpen Scheme.Modules tilde Scheme.Modules.map_smul tilde.toOpen Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.Modules.IsInvertible Scheme.Modules.IsLocallyFreeOfRank tilde.pullbackSpecIso Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Modules.bijective_unit_app_of_le_opensRange tilde.pullbackSpecIso_hom_app_top_unit_toOpen Scheme.Modules.isLocallyFreeOfRank_tilde Scheme.Modules.IsLocallyFreeOfRank.pullback Scheme.Modules.IsLocallyFreeOfRank.of_forall_exists_opens Scheme.Modules.exists_fibreProduct_sections_bijective Scheme.Modules.nonempty_pullback_iso_of_bijective_app_of_le_opensRange"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.congr_app Modules.Hom.app_smul Modules.pullback Hom.id_app Hom Γ Hom.preimage_inf Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.id_app Modules.Hom.app isoSpec Hom.comp_app Modules Opens Modules.map_smul restrict ΓSpecIso TwoAffineOpenCover Modules.IsInvertible Modules.IsLocallyFreeOfRank Modules.isLocallyFreeOfRank_one_iff_isInvertible Modules.bijective_unit_app_of_le_opensRange Modules.isLocallyFreeOfRank_tilde Modules.IsLocallyFreeOfRank.pullback Modules.IsLocallyFreeOfRank.of_forall_exists_opens Modules.exists_fibreProduct_sections_bijective Modules.nonempty_pullback_iso_of_bijective_app_of_le_opensRange"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "sectionsOf cover pullback isAffineOpen_U0 isAffineOpen_inf U1 U0 sup_eq_top isAffineOpen_U1"
namespace GlueInvertible
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry Opposite TopologicalSpace TensorProduct AlgebraicGeometry.Scheme.Modules"

variable {X : Scheme.{u}} (U0 U1 : X.Opens)
  (hU0 : IsAffineOpen U0) (hU1 : IsAffineOpen U1) (hU01 : IsAffineOpen (U0 ⊓ U1))
variable (P0 : Type u) [AddCommGroup P0] [Module (X.presheaf.obj (op U0)) P0]
variable (P1 : Type u) [AddCommGroup P1] [Module (X.presheaf.obj (op U1)) P1]
variable (σ : letI := (ρ0 U0 U1).hom.toAlgebra; letI := (ρ1 U0 U1).hom.toAlgebra
   ((X.presheaf.obj (op (U0 ⊓ U1))) ⊗[X.presheaf.obj (op U0)] P0) ≃ₗ[X.presheaf.obj (op (U0 ⊓ U1))]
     ((X.presheaf.obj (op (U0 ⊓ U1))) ⊗[X.presheaf.obj (op U1)] P1))
variable (hsup : U0 ⊔ U1 = ⊤)
variable [Module.Finite (X.presheaf.obj (op U0)) P0] [Module.Projective (X.presheaf.obj (op U0)) P0]
variable [Module.Finite (X.presheaf.obj (op U1)) P1] [Module.Projective (X.presheaf.obj (op U1)) P1]
variable
  (hrk0 : ∀ (K : Type u) [Field K] [Algebra (X.presheaf.obj (op U0)) K],
    Module.finrank K (K ⊗[X.presheaf.obj (op U0)] P0) = 1)
  (hrk1 : ∀ (K : Type u) [Field K] [Algebra (X.presheaf.obj (op U1)) K],
    Module.finrank K (K ⊗[X.presheaf.obj (op U1)] P1) = 1)

include hU0 hU1 hU01 hsup hrk0 hrk1 in

theorem exists_isInvertible_of_projective :
    letI := (ρ0 U0 U1).hom.toAlgebra; letI := (ρ1 U0 U1).hom.toAlgebra
    ∃ (L : X.Modules), Scheme.Modules.IsInvertible L ∧
      ∃ (e0 : Γ(L, U0) ≃ₗ[X.presheaf.obj (op U0)] P0)
        (e1 : Γ(L, U1) ≃ₗ[X.presheaf.obj (op U1)] P1)
        (e01 : Γ(L, U0 ⊓ U1) ≃ₗ[X.presheaf.obj (op (U0 ⊓ U1))]
          ((X.presheaf.obj (op (U0 ⊓ U1))) ⊗[X.presheaf.obj (op U0)] P0)),
        (∀ m, e01 (L.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op m) =
          (1 : X.presheaf.obj (op (U0 ⊓ U1))) ⊗ₜ[X.presheaf.obj (op U0)] e0 m) ∧
        (∀ m, σ (e01 (L.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op m)) =
          (1 : X.presheaf.obj (op (U0 ⊓ U1))) ⊗ₜ[X.presheaf.obj (op U1)] e1 m) :=
  ⟨L U0 U1 hU0 hU1 hU01 P0 P1 σ, isInvertible_L U0 U1 hU0 hU1 hU01 P0 P1 σ hsup hrk0 hrk1, e0 U0 U1 hU0 hU1 hU01 P0 P1 σ, e1 U0 U1 hU0 hU1 hU01 P0 P1 σ, e01 U0 U1 hU0 hU1 hU01 P0 P1 σ, sq0 U0 U1 hU0 hU1 hU01 P0 P1 σ, sq1' U0 U1 hU0 hU1 hU01 P0 P1 σ⟩

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible"

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.AlgebraicGeometry TensorProduct Opposite in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (P0 : Type u) [AddCommGroup P0] [Module (𝒱.cover c).A0 P0]
    [Module.Projective (𝒱.cover c).A0 P0] [Module.Finite (𝒱.cover c).A0 P0]
    (P1 : Type u) [AddCommGroup P1] [Module (𝒱.cover c).A1 P1]
    [Module.Projective (𝒱.cover c).A1 P1] [Module.Finite (𝒱.cover c).A1 P1]
    (hrk0 : ∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A0 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A0] P0) = 1)
    (hrk1 : ∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A1 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A1] P1) = 1)
    (σ : letI : Algebra (𝒱.cover c).A0 (𝒱.cover c).A01 := (𝒱.cover c).ρ0.toRingHom.toAlgebra
         letI : Algebra (𝒱.cover c).A1 (𝒱.cover c).A01 := (𝒱.cover c).ρ1.toRingHom.toAlgebra
         ((𝒱.cover c).A01 ⊗[(𝒱.cover c).A0] P0) ≃ₗ[(𝒱.cover c).A01]
           ((𝒱.cover c).A01 ⊗[(𝒱.cover c).A1] P1)) :
    letI : Algebra (𝒱.cover c).A0 (𝒱.cover c).A01 := (𝒱.cover c).ρ0.toRingHom.toAlgebra
    letI : Algebra (𝒱.cover c).A1 (𝒱.cover c).A01 := (𝒱.cover c).ρ1.toRingHom.toAlgebra
    ∃ (L : X.Modules), Scheme.Modules.IsInvertible L ∧
      ∃ (e0 : (𝒱.sectionsOf c L).M0 ≃ₗ[(𝒱.cover c).A0] P0)
        (e1 : (𝒱.sectionsOf c L).M1 ≃ₗ[(𝒱.cover c).A1] P1)
        (e01 : (𝒱.sectionsOf c L).M01 ≃ₗ[(𝒱.cover c).A01]
          ((𝒱.cover c).A01 ⊗[(𝒱.cover c).A0] P0)),
        (∀ m, e01 ((𝒱.sectionsOf c L).r0 m) = (1 : (𝒱.cover c).A01) ⊗ₜ[(𝒱.cover c).A0] e0 m) ∧
        (∀ m, σ (e01 ((𝒱.sectionsOf c L).r1 m)) = (1 : (𝒱.cover c).A01) ⊗ₜ[(𝒱.cover c).A1] e1 m) := by
  letI i0 : Module (X.presheaf.obj (op 𝒱.U0)) P0 := ‹Module (𝒱.cover c).A0 P0›
  letI i1 : Module (X.presheaf.obj (op 𝒱.U1)) P1 := ‹Module (𝒱.cover c).A1 P1›
  haveI : Module.Finite (X.presheaf.obj (op 𝒱.U0)) P0 := ‹Module.Finite (𝒱.cover c).A0 P0›
  haveI : Module.Projective (X.presheaf.obj (op 𝒱.U0)) P0 := ‹Module.Projective (𝒱.cover c).A0 P0›
  haveI : Module.Finite (X.presheaf.obj (op 𝒱.U1)) P1 := ‹Module.Finite (𝒱.cover c).A1 P1›
  haveI : Module.Projective (X.presheaf.obj (op 𝒱.U1)) P1 := ‹Module.Projective (𝒱.cover c).A1 P1›
  obtain ⟨L, hL, e0, e1, e01, h0, h1⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueInvertible.exists_isInvertible_of_projective
      𝒱.U0 𝒱.U1 𝒱.isAffineOpen_U0 𝒱.isAffineOpen_U1 𝒱.isAffineOpen_inf P0 P1 σ 𝒱.sup_eq_top hrk0 hrk1
  exact ⟨L, hL, e0, e1, e01, h0, h1⟩

end
end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective (solution)
