-- Prove2me | Definitions.Def_AlmostMMS_xStar
-- name    : AlmostMMS_xStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:14.403199+00:00
-- url     : https://prove2.me/theorems/f84e532d-f2e1-40c4-8d12-3d626058f770
-- title:
--   Definitions 3.4, 3.6, pp.22–23 — the set $\Pi$ and the fractional MMS head profile $x^*$
-- statement:
--   The **MMS profile set** is $\Pi=\{\emptyset,\bot\}+\bigcup_{i\in N}\{\pi_{i,j}:j\in[d]\}$. The **fractional MMS head profile** of agent $i$ puts weight $x^*_i(\bot)=1-d/n$ on the no-profile, and
--   $$
--   x^*_i(\pi)=\frac{|\{j\in[d]:\pi_{i,j}=\pi\}|}{n}\qquad\text{for }\pi\ne\bot.
--   $$
--   **Formalization Note** The page writes $x_i(\bot)$ for $x^*_i(\bot)$.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Definition 3.4, p.22; Definition 3.6, p.23

import Mathlib
import Definitions.Def_AlmostMMS_mmsProfileIn

namespace AlmostMMS

open Finset

open Classical in
/-- **The MMS profile set** `Π = {∅, ⊥} + ⋃_{i ∈ N} {π_{i,j} : j ∈ [d]}` (Definition 3.4, p.22).
Feige, Grinberg, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…). -/
noncomputable def mmsProfileSet {n m d : ℕ} (J : OrderedInstance n m d) (q : ℕ) :
    Finset (Option (Multiset ℝ)) :=
  insert (some 0) (insert none
    ((univ : Finset (Fin n × Fin d)).image fun p => some (mmsProfile J q p.1 p.2)))

open Classical in
/-- **Fractional MMS head profile** `x*` (Definition 3.6, p.23): `x*_i(⊥) = 1 - d/n` and
`x*_i(π) = |{j ∈ [d] : π_{i,j} = π}|/n` for `π ≠ ⊥`. -/
noncomputable def xStar {n m d : ℕ} (J : OrderedInstance n m d) (q : ℕ) (i : Fin n) :
    Option (Multiset ℝ) → ℝ
  | none => 1 - (d : ℝ) / (n : ℝ)
  | some π => ((univ.filter fun j => mmsProfile J q i j = π).card : ℝ) / (n : ℝ)

end AlmostMMS


