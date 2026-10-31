-- Prove2me | Definitions.Def_MultimodularDocks_Instance
-- name    : MultimodularDocks_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:52.025782+00:00
-- url     : https://prove2.me/theorems/5f028ec0-5c83-44e5-8f08-bd0922420190
-- title:
--   Instance of the dock allocation problem, allocations and dock counts
-- statement:
--   An **instance** on a finite set $S$ of stations consists of
--
--   1. a cost $g_i(d,b)$ for each station $i$, for $d$ empty docks and $b$ bikes;
--   2. lower and upper bounds $l_i\le d_i+b_i\le u_i$ on the number of docks at $i$;
--   3. a bike budget $B$ and a number $D$, with $D+B$ docks in the system.
--
--   An **allocation** $(\vec d,\vec b)$ assigns $d_i$ empty docks and $b_i$ bikes to each station; station $i$ then has $d_i+b_i$ docks.
--
--   **Formalization Note** The paper's station cost $c_i$ is $g_i$ on the band $\{d,b\ge 0,\ l_i\le d+b\le u_i\}$ and $+\infty$ elsewhere (p.11). The real function $g_i$ and the band are kept apart; the band enters through feasibility.
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, §2, pp.9–11 (model primitives, decision variables, constraints)

import Mathlib

namespace MultimodularDocks

/-- **An instance of the dock allocation problem** (Freund, Henderson, Shmoys,
arXiv:1611.09304v5, §2, pp.9–11): for every station `i` a cost `g i : ℤ → ℤ → ℝ` of `d` empty
docks and `b` bikes, lower and upper bounds `l i ≤ d + b ≤ u i` on its number of docks, a bike
budget `B` and a number `D` with `D + B` docks in total.

**Formalization Note** The page's station cost `c_i` equals `g i` on the band
`{d, b ≥ 0, l_i ≤ d + b ≤ u_i}` and `+∞` off it (p.11). Lean keeps the real function `g i` and
the band (`InBand`) apart, so no extended-real arithmetic occurs. -/
structure Instance (S : Type*) where
  /-- station costs `g i d b` -/
  g : S → ℤ → ℤ → ℝ
  /-- lower bound on the number of docks at each station -/
  l : S → ℤ
  /-- upper bound on the number of docks at each station -/
  u : S → ℤ
  /-- bike budget -/
  B : ℤ
  /-- the total number of docks is `D + B` -/
  D : ℤ

/-- **An allocation** `(d⃗, b⃗)` (p.9): `d i` empty docks and `b i` bikes at station `i`. -/
@[ext]
structure Alloc (S : Type*) where
  /-- empty docks -/
  d : S → ℤ
  /-- bikes (full docks) -/
  b : S → ℤ

/-- The number of docks `d_i + b_i` at station `i` (p.9). -/
def dockCount {S : Type*} (a : Alloc S) (i : S) : ℤ :=
  a.d i + a.b i

end MultimodularDocks


