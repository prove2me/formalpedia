-- Prove2me | Definitions.Def_MWCSherali_otherPair
-- name    : MWCSherali_otherPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:16.985191+00:00
-- url     : https://prove2.me/theorems/93cf9fe4-cb09-4114-ba33-ec2da5d5d35f
-- title:
--   The two indices of $[4]\setminus\{a,b\}$
-- statement:
--   For $a\neq b$ in $[4]$, the pair $(i,j)$ with $i<j$ and $\{i,j\}=[4]\setminus\{a,b\}$, as used in the tube coordinates (12): $t_{ab}(w,u,v)=we_a+(1-w-u-v)e_b+ue_i+ve_j$.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), (12), p.35

import Mathlib

namespace MWCSherali

/-- **The two indices `i < j` of `[4] ∖ {a, b}`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), (12), p.35
("`t_{ab}(w, u, v) = w e_a + (1 − w − u − v) e_b + u e_i + v e_j`", `{i, j} = [4] ∖ {a, b}`).

For `a ≠ b`, `otherPair a b = (i, j)` lists the complement of `{a, b}` in increasing order.

**Formalization Note.** `L` is `[0, 1, 2, 3]` with `a` and `b` removed, which is already in
increasing order; the default `0` of `getD` is never reached when `a ≠ b`. -/
def otherPair (a b : Fin 4) : Fin 4 × Fin 4 :=
  let L := (List.finRange 4).filter fun l => l ≠ a ∧ l ≠ b
  (L.getD 0 0, L.getD 1 0)

end MWCSherali


