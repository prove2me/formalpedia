-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:12.896208+00:00
-- url     : https://prove2.me/theorems/30c49fa6-1921-4fb0-852d-82b40ef877ba
-- title:
--   Pull Gt
-- statement:
--   Definitions and structural lemmas for Pull Gt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullGt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGtSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_of_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.PullGtPf
open Semi Geo.Tor
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
  {I' : Ideal R'} (φ : R →+* R') (hφ : I.map φ ≤ I') (e : ℕ)
include hφ in
lemma pow_le : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
  intro x hx
  rw [Ideal.mem_comap]
  have h1 : φ x ∈ (I ^ (e + 1)).map φ := Ideal.mem_map_of_mem φ hx
  rw [Ideal.map_pow] at h1
  first
  | exact Ideal.pow_right_mono hφ (e + 1) h1
  | exact pow_le_pow_left' hφ (e + 1) h1
def φe : R ⧸ I ^ (e + 1) →+* R' ⧸ I' ^ (e + 1) := Ideal.quotientMap _ φ (pow_le φ hφ e)
def sE : Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
  Spec.map (CommRingCat.ofHom (φe φ hφ e))
lemma sE_thick : sE φ hφ e ≫ thick R I e = thick R' I' e ≫ specOf φ := by
  simp only [sE, thick, specOf, ← Spec.map_comp]
  congr 1
  all_goals first | rfl | (ext x; simp [φe])
variable {φ hφ e}
def hMap (Y : Over (Spec (CommRingCat.of R))) (Y' : Over (Spec (CommRingCat.of R')))
    (b : Y' ⟶ (Over.pullback (specOf φ)).obj Y) :
    (thickObj R' I' e Y').left ⟶ (thickObj R I e Y).left :=
  pullback.lift (pullback.fst Y'.hom (thick R' I' e) ≫ b.left ≫ pullback.fst Y.hom (specOf φ))
    (pullback.snd Y'.hom (thick R' I' e) ≫ sE φ hφ e) (by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc b.left,
        show b.left ≫ pullback.snd Y.hom (specOf φ) = Y'.hom from Over.w b, ← Category.assoc,
        pullback.condition, Category.assoc, Category.assoc, sE_thick])
lemma hMap_fst (Y : Over (Spec (CommRingCat.of R))) (Y' : Over (Spec (CommRingCat.of R')))
    (b : Y' ⟶ (Over.pullback (specOf φ)).obj Y) :
    hMap (hφ := hφ) (e := e) Y Y' b ≫ pullback.fst Y.hom (thick R I e) =
      pullback.fst Y'.hom (thick R' I' e) ≫ b.left ≫ pullback.fst Y.hom (specOf φ) := by
  first
  | exact pullback.lift_fst _ _ _
  | simp [hMap]
lemma hMap_snd (Y : Over (Spec (CommRingCat.of R))) (Y' : Over (Spec (CommRingCat.of R')))
    (b : Y' ⟶ (Over.pullback (specOf φ)).obj Y) :
    hMap (hφ := hφ) (e := e) Y Y' b ≫ pullback.snd Y.hom (thick R I e) =
      pullback.snd Y'.hom (thick R' I' e) ≫ sE φ hφ e := by
  first
  | exact pullback.lift_snd _ _ _
  | simp [hMap]
lemma isGrpPullback_hMap (Y : Over (Spec (CommRingCat.of R))) [GrpObj Y]
    (Y' : Over (Spec (CommRingCat.of R'))) [GrpObj Y']
    (b : Y' ≅ (Over.pullback (specOf φ)).obj Y) [IsMonHom b.hom] :
    IsGrpPullback (thickObj R' I' e Y') (thickObj R I e Y) (sE φ hφ e) (hMap (hφ := hφ) Y Y' b.hom) := by
  have A := isGrpPullback_pullback Y' (thick R' I' e)
  have B := ((isGrpPullback_of_iso b).comp (isGrpPullback_pullback Y (specOf φ))).congr
    (Category.id_comp _) rfl
  have C := A.comp B
  have D := isGrpPullback_pullback Y (thick R I e)
  exact D.cancel (C.congr (sE_thick φ hφ e).symm (by rw [hMap_fst])) (hMap_snd Y Y' b.hom)
section MonHom
variable {S S' : Scheme.{0}} {f : S' ⟶ S}
end MonHom
section Q
variable (hφ e)
variable {D : DegPre R} {D' : DegPre R'} (eB : D'.P.A ≅ (Over.pullback (specOf φ)).obj D.P.A)
  [IsMonHom eB.hom]
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
  (bc : G' ≅ (Over.pullback (specOf φ)).obj G) [IsMonHom bc.hom]
abbrev hGm : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left := hMap (hφ := hφ) (e := e) G G' bc.hom
abbrev hBm : (thickObj R' I' e D'.P.A).left ⟶ (thickObj R I e D.P.A).left :=
  hMap (hφ := hφ) (e := e) D.P.A D'.P.A eB.hom
omit [IsCommMonObj G] [IsCommMonObj G'] in
lemma grpG : IsGrpPullback (thickObj R' I' e G') (thickObj R I e G) (sE φ hφ e) (hGm hφ e bc) :=
  isGrpPullback_hMap (hφ := hφ) (e := e) G G' bc
lemma grpB : IsGrpPullback (thickObj R' I' e D'.P.A) (thickObj R I e D.P.A) (sE φ hφ e) (hBm hφ e eB) :=
  isGrpPullback_hMap (hφ := hφ) (e := e) D.P.A D'.P.A eB
variable {e} (g : GtCoord I D e G)
def qL : (thickObj R' I' e G').left ⟶ (thickObj R' I' e D'.P.A).left :=
  (grpB hφ e eB).1.lift (hGm hφ e bc ≫ g.q.left) (thickObj R' I' e G').hom (by
    rw [Category.assoc, Over.w g.q]; exact hMap_snd (hφ := hφ) G G' bc.hom)
def qP : thickObj R' I' e G' ⟶ thickObj R' I' e D'.P.A :=
  Over.homMk (qL hφ eB bc g) ((grpB hφ e eB).1.lift_snd _ _ _)
end Q
section Torus
variable (hφ e) {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (xe : X' ≃+ X)
def ψB : AddMonoidAlgebra ZU.{0} X →ₐc[ZU.{0}] AddMonoidAlgebra ZU.{0} X' :=
  AddMonoidAlgebra.mapDomainBialgHom ZU.{0} xe.symm.toAddMonoidHom
abbrev ψR : AddMonoidAlgebra ZU.{0} X →+* AddMonoidAlgebra ZU.{0} X' := (ψB xe : _ →+* _)
def specψ : splitTorusAff ZU X' ⟶ splitTorusAff ZU X :=
  ((bialgSpec ZU).map (CommBialgCat.ofHom (ψB xe)).op).hom
instance specψ_hom : IsMonHom (specψ xe) :=
  ((bialgSpec ZU).map (CommBialgCat.ofHom (ψB xe)).op).isMonHom_hom
def hT : (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) X').left ⟶
    (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X).left :=
  pullback.lift (pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (ψR xe))) (pullback.snd _ _ ≫ sE φ hφ e)
    (specULiftZIsTerminal.hom_ext _ _)
lemma ψB_left_inv : (ψR xe).comp (ψR xe.symm) = RingHom.id _ := by
  refine RingHom.ext fun x => ?_
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a c ha hc => rw [map_add, map_add, ha, hc]
  | single a r => simp [ψB, AddMonoidAlgebra.mapDomainBialgHom, AddMonoidAlgebra.mapDomainAlgHom_apply]
lemma ψB_right_inv : (ψR xe.symm).comp (ψR xe) = RingHom.id _ := by
  refine RingHom.ext fun x => ?_
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a c ha hc => rw [map_add, map_add, ha, hc]
  | single a r => simp [ψB, AddMonoidAlgebra.mapDomainBialgHom, AddMonoidAlgebra.mapDomainAlgHom_apply]
lemma specψ_left : (specψ xe).left = Spec.map (CommRingCat.ofHom (ψR xe)) := rfl
instance : IsIso (specψ xe).left := by
  rw [specψ_left]
  have : IsIso (CommRingCat.ofHom (ψR xe)) :=
    ⟨⟨CommRingCat.ofHom (ψR xe.symm), by
      rw [← CommRingCat.ofHom_comp, ψB_right_inv]; rfl, by
      rw [← CommRingCat.ofHom_comp, ψB_left_inv]; rfl⟩⟩
  exact (inferInstance : IsIso (Scheme.Spec.map (CommRingCat.ofHom (ψR xe)).op))
def eψ : splitTorusAff ZU X' ≅ splitTorusAff ZU X :=
  Over.isoMk (asIso (specψ xe).left) (Over.w (specψ xe))
lemma eψ_hom : (eψ xe).hom = specψ xe := by
  first
  | rfl
  | (ext1; rfl)
instance : IsMonHom (eψ xe).hom := by rw [eψ_hom]; infer_instance
end Torus
section Unit
end Unit
section IK
variable (hφ) {D : DegPre R} {D' : DegPre R'} (eB : D'.P.A ≅ (Over.pullback (specOf φ)).obj D.P.A)
  [IsMonHom eB.hom] (xe : D'.X ≃+ D.X)
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
  (bc : G' ≅ (Over.pullback (specOf φ)).obj G) [IsMonHom bc.hom] {e : ℕ} (g : GtCoord I D e G)
def iL : (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X).left ⟶ (thickObj R' I' e G').left :=
  (grpG hφ e bc).1.lift (hT hφ e xe ≫ g.i.left) (splitTorus _ D'.X).hom (by
    rw [Category.assoc, Over.w g.i]; exact pullback.lift_snd _ _ _)
def iP : splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X ⟶ thickObj R' I' e G' :=
  Over.homMk (iL hφ xe bc g) ((grpG hφ e bc).1.lift_snd _ _ _)
end IK
end ReciprocityTheory.ChartRestriction.G.Out.PullGtPf


