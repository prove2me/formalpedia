-- Prove2me | Definitions.Def_BianchiIX_Statistics_GaussInverse
-- name    : BianchiIX_Statistics_GaussInverse
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T13:02:36.066206+00:00
-- url     : https://prove2.me/theorems/149e6b4e-59ba-4ae2-b958-0abb7942aa15
-- title:
--   Gauss inverse branches and recurrence errors
-- statement:
--   Write $g_a(x)=1/(a+x)$. For a finite word
--   $w=(a_0,\ldots,a_{k-1})$ of natural numbers, let
--   $$G_w=g_{a_0}\circ\cdots\circ g_{a_{k-1}},\qquad G_{\varnothing}(x)=x.$$
--
--   For sequences $a:\mathbb N\to\mathbb N$ and $y:\mathbb N\to\mathbb R$, define
--   $$e_m=\left|y_m-g_{a_m}(y_{m+1})\right|.$$
--   These definitions describe finite inverse compositions and the local error of an approximate Gauss recurrence.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussInverse.lean

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Ideal inverse branches and uniform cylinder contraction, Section 3.2. -/

namespace BianchiIX

noncomputable section

open Filter
open scoped Topology

def gaussInv (a x : ℝ) : ℝ := 1 / (a + x)















def gaussWord : List ℕ → ℝ → ℝ
  | [], x => x
  | a :: w, x => gaussInv a (gaussWord w x)









def inverseError (digits : ℕ → ℕ) (y : ℕ → ℝ) (m : ℕ) : ℝ :=
  |y m - gaussInv (digits m) (y (m + 1))|



















end

end BianchiIX


