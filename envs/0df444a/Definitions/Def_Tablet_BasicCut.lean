-- Prove2me | Definitions.Def_Tablet_BasicCut
-- name    : Tablet_BasicCut
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:02:54.798165+00:00
-- url     : https://prove2.me/theorems/33b7fdce-aa89-5417-b8ef-3c1d7bd37b9b
-- title:
--   Basic Cut
-- statement:
--   Definitions and structural lemmas for Basic Cut, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCut.lean

import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_IsClosedCurve
set_option autoImplicit false
open Set
noncomputable def BasicCut {E : Type*} [MetricSpace E] (GP : GeodesicPairing E) (γ : Curve E)
    (hclosed : IsClosedCurve γ) (t t' : ℝ) (ht0 : 0 ≤ t) (htlen : t ≤ γ.len) (ht'0 : 0 ≤ t')
    (ht'len : t' ≤ γ.len) : Curve E × Curve E := by
-- BODY
  have curveArc_toFun_len : ∀ (a b : ℝ) (ha0 : 0 ≤ a) (hal : a ≤ γ.len) (hb0 : 0 ≤ b)
      (hbl : b ≤ γ.len),
      (curveArc γ hclosed a b ha0 hal hb0 hbl).toFun (curveArc γ hclosed a b ha0 hal hb0 hbl).len
        = γ.toFun b := by
    intro a b ha0 hal hb0 hbl
    have hRestrict_len : ∀ (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ γ.len),
        (curveRestrict γ p q hp hpq hq).len = q - p := fun _ _ _ _ _ => rfl
    have hRestrict_toFun_len : ∀ (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ γ.len),
        (curveRestrict γ p q hp hpq hq).toFun (curveRestrict γ p q hp hpq hq).len = γ.toFun q := by
      intro p q hp hpq hq
      show γ.toFun (p + min (q - p) (max 0 (q - p))) = γ.toFun q
      rw [max_eq_right (by linarith), min_self]
      congr 1
      ring
    unfold curveArc
    split_ifs with h
    · exact hRestrict_toFun_len a b ha0 h hbl
    · have hbt : b < a := not_le.mp h
      have hlen : (curveWrapRestrict γ a b hclosed ha0 hal hb0 hbt).len = (γ.len - a) + b := by
        show (curveRestrict γ a γ.len ha0 hal (le_refl _)).len
            + (curveRestrict γ 0 b (le_refl 0) hb0 (by linarith)).len = (γ.len - a) + b
        rw [hRestrict_len, hRestrict_len]
        ring_nf
      rw [hlen]
      show (if ((γ.len - a) + b) ≤ (curveRestrict γ a γ.len ha0 hal (le_refl _)).len
          then (curveRestrict γ a γ.len ha0 hal (le_refl _)).toFun ((γ.len - a) + b)
          else (curveRestrict γ 0 b (le_refl 0) hb0 (by linarith)).toFun
            (((γ.len - a) + b) - (curveRestrict γ a γ.len ha0 hal (le_refl _)).len))
          = γ.toFun b
      rw [hRestrict_len]
      rcases eq_or_lt_of_le hb0 with hbeq | hbpos
      · rw [if_pos (by linarith)]
        have harg : a + min (γ.len - a) (max 0 (γ.len - a + b)) = γ.len := by
          rw [max_eq_right (by linarith), min_eq_right (by linarith)]
          linarith
        show γ.toFun (a + min (γ.len - a) (max 0 (γ.len - a + b))) = γ.toFun b
        rw [harg, ← hbeq]
        exact hclosed
      · rw [if_neg (by linarith)]
        have harg : (γ.len - a) + b - (γ.len - a) = b := by ring
        rw [harg]
        have h1 := hRestrict_toFun_len 0 b (le_refl 0) hb0 (by linarith)
        simp only [hRestrict_len, sub_zero] at h1
        exact h1
  exact
    ⟨curveConcat (curveArc γ hclosed t' t ht'0 ht'len ht0 htlen) (GP.G (γ.toFun t) (γ.toFun t'))
        (by rw [curveArc_toFun_len, GP.start_eq]),
     curveConcat (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len) (GP.G (γ.toFun t') (γ.toFun t))
        (by rw [curveArc_toFun_len, GP.start_eq])⟩


