-- Prove2me | Definitions.Def_LCPlanarSteiner_ArmsLE
-- name    : LCPlanarSteiner_ArmsLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:25.200768+00:00
-- url     : https://prove2.me/theorems/fbc2789c-da79-4da4-98bc-42140a6553dd
-- title:
--   Junction arm sum $\mathrm{dist}_{H}(s,v) + \mathrm{dist}_{H}(v,t) \le x$
-- statement:
--   For a set $H$ of arcs, a root $v$, a pair $(s, t)$ and a rational $x$, the **arm sum** bound
--   $$
--   \mathrm{dist}_{H}(s, v) + \mathrm{dist}_{H}(v, t) \le x
--   $$
--   holds when there are a walk from $s$ to $v$ and a walk from $v$ to $t$, both inside $H$, whose lengths sum to at most $x$. The two arms may share arcs; their concatenation is a walk from $s$ to $t$ through $v$.
--
--   This is the junction condition (8) of the paper: one budget for the whole pair, not two independent allowances.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §4, p.9

import Mathlib
import Definitions.Def_LCPlanarSteiner_IsWalk
import Definitions.Def_LCPlanarSteiner_plen

namespace LCPlanarSteiner

/-- **Junction arm sum: `dist_{H′}(s, v) + dist_{H′}(v, t) ≤ x`.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §4, p.9: "We bound
dist_{H′}(s_i, v) + dist_{H′}(v, t_i), not two independent complete-path allowances."

`ArmsLE G H v s t x`: there are a directed walk from `s` to `v` and a directed walk from `v` to `t`,
both using only arcs of `H`, whose lengths sum to at most `x`.

**Formalization Note.** The two arms may share arcs. Since the distances are minima over finitely
many simple paths (lengths are nonnegative), this is exactly `dist_H(s,v) + dist_H(v,t) ≤ x`. -/
def ArmsLE (G : Net) (H : Finset ℕ) (v s t : ℕ) (x : ℚ) : Prop :=
  ∃ p₁ p₂ : List ℕ, IsWalk G s v p₁ ∧ IsWalk G v t p₂ ∧ (∀ e ∈ p₁, e ∈ H) ∧ (∀ e ∈ p₂, e ∈ H) ∧
    plen G p₁ + plen G p₂ ≤ x

end LCPlanarSteiner


