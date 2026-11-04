-- Prove2me | Definitions.Def_Submission_ThreeSum_ColorParameters
-- name    : Submission_ThreeSum_ColorParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:43:10.198288+00:00
-- url     : https://prove2.me/theorems/23f1d1b2-15e6-4a9b-9636-9c506c0a7683
-- title:
--   Color Parameters
-- statement:
--   Definitions and structural lemmas for Color Parameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorParameters.lean

import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Mathlib.Data.List.FinRange
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.ColorClassLists.value_fin
attribute [local simp] ThreeSum.LightClassFilter.items_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


set_option autoImplicit false
namespace ThreeSum.ColorParameters
def count (W : ℕ) : ℕ := 81*W^2
def colorMap (a b c d : Fin 3) : (Bool × Bool) → Fin 3
  | (false,false) => a
  | (false,true) => b
  | (true,false) => c
  | (true,true) => d
def data (W t : ℕ) : List ℤ :=
  [t/81/W,t/81%W,t/27%3,t/9%3,t/3%3,t%3]
theorem width_pos {W t : ℕ} (ht : t < count W) : 0 < W := by
  by_contra hn
  have hw : W=0 := by omega
  simp [count,hw] at ht
theorem coordinate_bounds {W t : ℕ} (ht : t < count W) :
    t/81/W < W ∧ t/81%W < W := by
  have hw := width_pos ht
  have hq : t/81 < W*W := (Nat.div_lt_iff_lt_mul (by decide : 0 < 81)).mpr (by
    simpa only [count,pow_two,Nat.mul_comm] using ht)
  exact ⟨(Nat.div_lt_iff_lt_mul hw).mpr hq,Nat.mod_lt _ hw⟩
def parameter {W t : ℕ} (ht : t < count W) : Coloring.Parameter W :=
  ((⟨t/81/W,(coordinate_bounds ht).1⟩,⟨t/81%W,(coordinate_bounds ht).2⟩),
    colorMap ⟨t/27%3,Nat.mod_lt _ (by decide)⟩ ⟨t/9%3,Nat.mod_lt _ (by decide)⟩
      ⟨t/3%3,Nat.mod_lt _ (by decide)⟩ ⟨t%3,Nat.mod_lt _ (by decide)⟩)
def fields {W : ℕ} (p : Coloring.Parameter W) : List ℤ :=
  [p.1.1.val,p.1.2.val,(p.2 (false,false)).val,(p.2 (false,true)).val,
    (p.2 (true,false)).val,(p.2 (true,true)).val]
def index {W : ℕ} (p : Coloring.Parameter W) : ℕ :=
  ((((p.1.1.val*W+p.1.2.val)*3+(p.2 (false,false)).val)*3+
    (p.2 (false,true)).val)*3+(p.2 (true,false)).val)*3+(p.2 (true,true)).val
theorem coordinate_pair_lt {W : ℕ} (p : Coloring.Parameter W) :
    p.1.1.val*W+p.1.2.val < W*W := by
  calc
    _ < p.1.1.val*W+W := Nat.add_lt_add_left p.1.2.isLt _
    _ = (p.1.1.val+1)*W := by ring
    _ ≤ W*W := Nat.mul_le_mul_right _ (by omega)
theorem index_lt {W : ℕ} (p : Coloring.Parameter W) : index p < count W := by
  have hp := coordinate_pair_lt p
  have h0 := (p.2 (false,false)).isLt
  have h1 := (p.2 (false,true)).isLt
  have h2 := (p.2 (true,false)).isLt
  have h3 := (p.2 (true,true)).isLt
  unfold index count
  rw [pow_two]
  omega
def parameters (W : ℕ) : List (Coloring.Parameter W) :=
  List.ofFn fun t : Fin (count W) => parameter t.isLt
end ThreeSum.ColorParameters


