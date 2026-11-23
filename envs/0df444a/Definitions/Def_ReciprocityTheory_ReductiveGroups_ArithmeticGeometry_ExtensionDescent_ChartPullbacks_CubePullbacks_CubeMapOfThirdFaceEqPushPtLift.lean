-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:03.766265+00:00
-- url     : https://prove2.me/theorems/a815bbeb-2f03-4699-b138-4bef38085e68
-- title:
--   Cube Map Of Third Face Eq Push Pt Lift
-- statement:
--   Definitions and structural lemmas for Cube Map Of Third Face Eq Push Pt Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeMapOfThirdFaceEqPushPtLift.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
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
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf
open Semi
section Geo
variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  [IsCommMonObj G] (m : CubeMap G' G)
lemma pzero_left {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] (T : Over S₀) :
    (pzero H T).left = T.hom ≫ eSec H := by
  first
    | rfl
    | simp [pzero, eSec]
lemma eSec_hom {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] : eSec H ≫ H.hom = 𝟙 _ := by
  first
    | simp [eSec]
    | (unfold eSec; exact Over.w _)
lemma psum_empty {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] [IsCommMonObj H] {T : Over S₀} {n : ℕ}
    (x : Fin n → (T ⟶ H)) : psum H x ∅ = pzero H T := by
  first
    | rfl
    | simp [psum, pzero]
lemma padd_pzero {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] [IsCommMonObj H] {T : Over S₀}
    (a : T ⟶ H) : padd H a (pzero H T) = a := by
  first
    | simp [padd, pzero]
    | simp [padd]
lemma psum_single {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] [IsCommMonObj H] {T : Over S₀}
    (x : Fin 3 → (T ⟶ H)) (i : Fin 3) : psum H x {i} = x i := by
  fin_cases i <;>
    first
      | exact padd_pzero H _
      | simp [psum, List.finRange, padd_pzero]
lemma cubeMap_lies_over_base : m.F3 ≫ (G3 G).hom = (G3 G').hom ≫ m.e := by
  have h := m.psum_comm ∅
  rw [psum_empty, psum_empty, pzero_left, pzero_left, Category.assoc, m.e_comm] at h
  have h2 := congrArg (· ≫ G.hom) h
  simp only [Category.assoc, eSec_hom, Category.comp_id] at h2
  exact h2.symm
lemma cubeMap_on_coordinates (i : Fin 3) : (x3 G' i).left ≫ m.F = m.F3 ≫ (x3 G i).left := by
  have h := m.psum_comm {i}
  rwa [psum_single, psum_single] at h
theorem m_over : G'.hom ≫ m.e = m.F ≫ G.hom := by
  have key : (x3 G' 0).left ≫ G'.hom ≫ m.e = (x3 G' 0).left ≫ m.F ≫ G.hom := by
    rw [← Category.assoc, Over.w (x3 G' 0), ← cubeMap_lies_over_base, ← Category.assoc, cubeMap_on_coordinates, Category.assoc,
      Over.w (x3 G 0)]
  have hs : (lift (𝟙 G') (lift (𝟙 G') (𝟙 G')) : G' ⟶ G3 G') ≫ x3 G' 0 = 𝟙 G' := by
    simp [x3]
  have hl := congrArg (fun f => f.left) hs
  simp only [Over.comp_left, Over.id_left] at hl
  have h := congrArg (fun f => (lift (𝟙 G') (lift (𝟙 G') (𝟙 G')) : G' ⟶ G3 G').left ≫ f) key
  simp only [← Category.assoc, hl, Category.id_comp] at h
  exact h
def tb {T : Over S'} (y : T ⟶ G') : (Over.map m.e).obj T ⟶ G :=
  Over.homMk (y.left ≫ m.F) (by
    show (y.left ≫ m.F) ≫ G.hom = T.hom ≫ m.e
    rw [Category.assoc, ← m_over, ← Category.assoc, Over.w y])
def cubeMapOverAlt : (Over.map m.e).obj (G3 G') ⟶ G3 G := Over.homMk m.F3 (cubeMap_lies_over_base m)
abbrev L3 : (Over.map m.e).obj (G3 G') ⟶ G3 G :=
  lift (tb m (x3 G' 0)) (lift (tb m (x3 G' 1)) (tb m (x3 G' 2)))
abbrev L2 : (Over.map m.e).obj (G2 G') ⟶ G2 G := lift (tb m (x2 G' 0)) (tb m (x2 G' 1))
abbrev L4 : (Over.map m.e).obj (G4 G') ⟶ G4 G :=
  lift (tb m (x4 G' 0)) (lift (tb m (x4 G' 1)) (lift (tb m (x4 G' 2)) (tb m (x4 G' 3))))
def pullbackMapSquare : (G2 G').left ⟶ (G2 G).left := (L2 m).left
def pullbackMapFourth : (G4 G').left ⟶ (G4 G).left := (L4 m).left
end Geo
end ReciprocityTheory.ChartRestriction.G.Out.CubePf


