-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEquivPow
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEquivPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:10.615282+00:00
-- url     : https://prove2.me/theorems/05f29aed-5805-4fb0-b9db-85a4d540a5eb
-- title:
--   Exists Equiv Pow
-- statement:
--   Definitions and structural lemmas for Exists Equiv Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsEquivPow.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory
namespace PowSections
variable {Y : Scheme.{0}}
theorem sec_ext {M : LB Y} {s t : LB.Sec M} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s; cases t
  congr 1
  exact funext h
def refine {M M' : LB Y} (σ : M'.ι → M.ι) (hU : ∀ i, M'.U i ≤ M.U (σ i))
    (hg : ∀ i j y, y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y _ (M'.g i j) = gm (𝟙 Y) y _ (M.g (σ i) (σ j))) (s : LB.Sec M) : LB.Sec M' where
  f i := (Y.presheaf.map (homOfLE (hU i)).op).hom (s.f (σ i))
  compat i j := fn_ext fun y hy => by
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ M.U (σ i) ⊓ M.U (σ j) := ⟨hU i hy.1, hU j hy.2⟩
    have e := congrArg (gs (𝟙 Y) y _) (s.compat (σ i) (σ j))
    rw [gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_unit _ y _ hm] at e
    rw [gs_mul _ y _ hy, gs_res _ y inf_le_left hy, gs_res _ y inf_le_right hy, gs_unit _ y _ hy, gs_res _ y (hU i) hy.1,
      gs_res _ y (hU j) hy.2, hg i j y hy.1 hy.2]
    exact e
theorem gs_refine {M M' : LB Y} (σ : M'.ι → M.ι) (hU : ∀ i, M'.U i ≤ M.U (σ i))
    (hg : ∀ i j y, y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y _ (M'.g i j) = gm (𝟙 Y) y _ (M.g (σ i) (σ j))) (s : LB.Sec M) (i : M'.ι) (y : Y)
    (hy : y ∈ M'.U i) :
    gs (𝟙 Y) y _ ((refine σ hU hg s).f i) = gs (𝟙 Y) y _ (s.f (σ i)) :=
  gs_res (𝟙 Y) y (hU i) hy _
def secEquiv {M M' : LB Y} (σ : M'.ι ≃ M.ι) (hU : ∀ i, M'.U i = M.U (σ i))
    (hg : ∀ i j y, y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y _ (M'.g i j) = gm (𝟙 Y) y _ (M.g (σ i) (σ j))) : LB.Sec M ≃ LB.Sec M' :=
  have hU' : ∀ i, M.U i ≤ M'.U (σ.symm i) := fun i => by rw [hU, σ.apply_symm_apply]
  have hg' : ∀ i j y, y ∈ M.U i → y ∈ M.U j →
      gm (𝟙 Y) y _ (M.g i j) = gm (𝟙 Y) y _ (M'.g (σ.symm i) (σ.symm j)) := fun i j y hi hj => by
    rw [hg _ _ y (hU' i hi) (hU' j hj)]
    obtain ⟨i, rfl⟩ := σ.surjective i
    obtain ⟨j, rfl⟩ := σ.surjective j
    rw [σ.apply_symm_apply, σ.apply_symm_apply]
  { toFun := refine σ (fun i => (hU i).le) hg
    invFun := refine σ.symm hU' hg'
    left_inv := fun s => sec_ext fun i => fn_ext fun y hy => by
      rw [gs_refine _ _ _ _ _ y hy, gs_refine _ _ _ _ _ y (hU' i hy), σ.apply_symm_apply]
    right_inv := fun s => sec_ext fun i => fn_ext fun y hy => by
      rw [gs_refine _ _ _ _ _ y hy, gs_refine _ _ _ _ _ y ((hU i).le hy), σ.symm_apply_apply] }
end PowSections
end GlobalTheory


