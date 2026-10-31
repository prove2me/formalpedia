-- Prove2me | Definitions.Def_LeGallBrownianMap_dCirc
-- name    : LeGallBrownianMap_dCirc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:11.832894+00:00
-- url     : https://prove2.me/theorems/45bba480-50a6-40a3-b3e0-5cde06df7faa
-- title:
--   The function $D^\circ(s,t)$ on $[0,1]^2$
-- statement:
--   For a continuous label path $Z$ on $[0,1]$ and $0\le s\le t\le1$,
--
--   $$
--   D^\circ(s,t) = D^\circ(t,s) = Z_s + Z_t - 2\max\Big(\min_{r\in[s,t]} Z_r,\ \min_{r\in[t,1]\cup[0,s]} Z_r\Big).
--   $$
--
--   Viewing $[0,1]$ as a circle, the two minima are taken over the two arcs between $s$ and $t$. On the tree $\mathcal T_e$, $D^\circ(a,b)$ is the minimum of $D^\circ(s,t)$ over representatives $s$ of $a$ and $t$ of $b$; the Brownian map distance $D^*$ is built from it by chaining.
--
--   **Formalization Note** The minima are written as infima of images (`sInf`), which are the minima for continuous $Z$.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.4, p.15 (also §1, p.3)

import Mathlib

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.4, p.15:
"For every s, t ∈ [0, 1] such that s ≤ t, we set
D°(s, t) = D°(t, s) = Z_s + Z_t − 2 max( min_{r∈[s,t]} Z_r , min_{r∈[t,1]∪[0,s]} Z_r )."

`dCirc Z s t` is this function `D°(s,t)` of two times `s, t ∈ [0,1]` (not yet the function on
the tree `T_e`, which is the minimum over representatives).

**Formalization Note.** The minima are written `sInf (Z '' …)`; for a continuous `Z` (the
paper's labels) they are attained minima of `Z` over the compact sets `[s,t]` and
`[t,1] ∪ [0,s]`. The case `s > t` is the symmetric formula, as the paper defines
`D°(t,s) = D°(s,t)`. -/
noncomputable def dCirc (Z : unitInterval → ℝ) (s t : unitInterval) : ℝ :=
  if s ≤ t then
    Z s + Z t - 2 * max (sInf (Z '' Set.Icc s t)) (sInf (Z '' (Set.Icc t 1 ∪ Set.Icc 0 s)))
  else
    Z t + Z s - 2 * max (sInf (Z '' Set.Icc t s)) (sInf (Z '' (Set.Icc s 1 ∪ Set.Icc 0 t)))

end LeGallBrownianMap


