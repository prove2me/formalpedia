-- Prove2me | Definitions.Def_AltRegret_Supplement_productBody
-- name    : AltRegret_Supplement_productBody
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:09:24.209643+00:00
-- url     : https://prove2.me/theorems/6ca7181f-7487-4e5c-a3ba-0355b7729038
-- title:
--   Product body for the dimension-dependent lower bound
-- statement:
--   For $d\ge2$, set $r=1/\sqrt d$. The body used in Theorem 10 is
--   $$
--   X=\underbrace{rB_2(1)\times\cdots\times rB_2(1)}_{\lfloor d/2\rfloor\text{ copies}}
--     \times[-r,r]^{d-2\lfloor d/2\rfloor}\subseteq\mathbb R^d.
--   $$
--   It is compact, convex, full-dimensional, and contained in $B_d(1)$. The associated exact lower-bound parameters are $m=\min\{\lfloor d/2\rfloor,\lfloor T/16\rfloor\}$ and $K=\lfloor\log_{16}\lfloor T/m\rfloor\rfloor$.
--
--   This is the specific body on which Theorem 10 establishes the dimension dependence.
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, §4.2, p.15

import Mathlib
import Definitions.Def_AltRegret_Supplement_ContinuousAAHedgeRun

namespace AltRegret.Supplement

/-- Coordinate `i`, extended by zero outside `Fin d`. -/
def coord {d : ℕ} (x : Point d) (i : ℕ) : ℝ :=
  if h : i < d then x ⟨i, h⟩ else 0

/-- The radius `r = 1 / √d` in §4.2. -/
noncomputable def blockRadius (d : ℕ) : ℝ := 1 / Real.sqrt d

/-- The product of `⌊d/2⌋` radius-`1/√d` planar balls and, for odd `d`, one interval. -/
noncomputable def productBody (d : ℕ) : Set (Point d) :=
  {x | (∀ j : Fin (d / 2),
      coord x (2 * j.1) ^ 2 + coord x (2 * j.1 + 1) ^ 2 ≤ blockRadius d ^ 2) ∧
    (d % 2 = 1 → |coord x (d - 1)| ≤ blockRadius d)}

/-- `m = min{⌊d/2⌋, ⌊T/16⌋}` from Theorem 10. -/
def lowerBlockCount (d T : ℕ) : ℕ := min (d / 2) (T / 16)

/-- `K = ⌊log₁₆ ⌊T/m⌋⌋` from Theorem 10. -/
noncomputable def lowerLogCount (d T : ℕ) : ℕ :=
  ⌊Real.logb 16 (T / lowerBlockCount d T : ℕ)⌋₊

end AltRegret.Supplement


