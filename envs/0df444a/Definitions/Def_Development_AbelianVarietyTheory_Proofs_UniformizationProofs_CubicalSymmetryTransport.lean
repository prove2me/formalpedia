-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T13:56:55.722126+00:00
-- url     : https://prove2.me/theorems/2114ec57-5824-458c-94bd-25353fa227f2
-- title:
--   Cubical Symmetry Transport
-- statement:
--   Definitions and structural lemmas for Cubical Symmetry Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CubicalSymmetryTransport.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__944b82dcaa95
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace CubTransport
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
section Down
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
end Down
section Cub
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}
def thV (t : LB.Gen (Theta G L.L)) {T : Over S} (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι) (x x' y : T ⟶ G) :
    (T.left.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t (lift x (lift x' y)).left z J
theorem val_thV (t : LB.Gen (Theta G L.L)) {T : Over S} {z : T.left} {J : (T.left ⟶ G.left) → L.L.ι}
    (hJ : Good L.L z J) (x x' y : T ⟶ G) :
    val (LB.pullGen L.L (thφ G (x3 G)) thε t (lift x (lift x' y)).left) (𝟙 T.left) z J = thV t z J x x' y := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [Category.id_comp]; rfl
theorem val_id_thV (t : LB.Gen (Theta G L.L)) {z : (G3 G).left} {J : ((G3 G).left ⟶ G.left) → L.L.ι} :
    val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t (𝟙 (G3 G).left) z J = thV t z J (x3 G 0) (x3 G 1) (x3 G 2) := by
  have e : lift (x3 G 0) (lift (x3 G 1) (x3 G 2)) = 𝟙 (G3 G) := by
    ext <;> simp [x3]
  rw [thV, e]; rfl
def cubicalOfVal (t : LB.Gen (Theta G L.L)) (ht : t.IsGen)
    (h : ∀ (T : Over S) (z : T.left) (J), Good L.L z J → IsCub (thV t z J)) : CubicalStr G L where
  t := t
  isGen := ht
  face i := corr_of_val L.isLB fun y J hJ => by
    refine Eq.trans ?_ (val_one _).symm
    have C := h (G2 G) y J hJ
    fin_cases i
    · exact (val_thV t hJ _ _ _).trans (C.face _ _)
    · exact (val_thV t hJ _ _ _).trans (C.face₂ _ _)
    · exact (val_thV t hJ _ _ _).trans (C.face₃ _ _)
  cubeSymmetric_swap_first := corr_of_val L.isLB fun y J hJ =>
    (val_id_thV t).trans (((h (G3 G) y J hJ).s01 _ _ _).trans (val_thV t hJ _ _ _).symm)
  cubeSymmetric_swap_last := corr_of_val L.isLB fun y J hJ =>
    (val_id_thV t).trans (((h (G3 G) y J hJ).s12 _ _ _).trans (val_thV t hJ _ _ _).symm)
  cocycle := corr_of_val L.isLB fun y J hJ =>
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_thV t hJ _ _ _) (val_thV t hJ _ _ _))).trans
      (((h (G4 G) y J hJ).coc _ _ _ _).trans
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_thV t hJ _ _ _) (val_thV t hJ _ _ _))).symm)
end Cub
end CubTransport
end GlobalTheory


