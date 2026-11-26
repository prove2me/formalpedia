-- Prove2me | Definitions.Def_Tablet_curveSampling
-- name    : Tablet_curveSampling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:54:38.594156+00:00
-- url     : https://prove2.me/theorems/980d1af7-8a95-4dcc-815b-08ae3d052c9f
-- title:
--   curve Sampling
-- statement:
--   Definitions and structural lemmas for curve Sampling, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/curveSampling.lean

import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_curveConcat
set_option autoImplicit false
open Set
noncomputable def curveSampling {E : Type*} [MetricSpace E] (GP : GeodesicPairing E) (γ : Curve E)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlen : δ < γ.len) : Curve E := by
-- BODY
  have concat_end : ∀ (a b : Curve E) (h : a.toFun a.len = b.toFun 0),
      (curveConcat a b h).toFun (curveConcat a b h).len = b.toFun b.len := by
    intro a b h
    show (if a.len + b.len ≤ a.len then a.toFun (a.len + b.len)
          else b.toFun (a.len + b.len - a.len)) = b.toFun b.len
    rcases eq_or_lt_of_le b.len_nonneg with hb0 | hbpos
    · have hb0' : b.len = 0 := hb0.symm
      rw [if_pos (by linarith)]
      simpa [hb0'] using h
    · rw [if_neg (by linarith)]
      congr 1
      ring
  let s : ℕ → ℝ := fun j => min ((j : ℝ) * δ) γ.len
  let aux : (n : ℕ) → {c : Curve E // c.toFun c.len = γ.toFun (s (n + 1))} := fun n =>
    Nat.rec
      (motive := fun n => {c : Curve E // c.toFun c.len = γ.toFun (s (n + 1))})
      ⟨GP.G (γ.toFun (s 0)) (γ.toFun (s 1)), GP.end_eq _ _⟩
      (fun n ih =>
        ⟨curveConcat ih.1 (GP.G (γ.toFun (s (n + 1))) (γ.toFun (s (n + 2))))
            (by rw [ih.2]; exact (GP.start_eq _ _).symm),
          by rw [concat_end]; exact GP.end_eq _ _⟩)
      n
  exact (aux (Nat.ceil (γ.len / δ) - 1)).1


