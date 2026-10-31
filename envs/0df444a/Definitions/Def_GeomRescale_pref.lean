-- Prove2me | Definitions.Def_GeomRescale_pref
-- name    : GeomRescale_pref
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:41.297874+00:00
-- url     : https://prove2.me/theorems/7ae2de2b-5e7c-45c0-8a15-fe6b1738e825
-- title:
--   The prefix $\{v_1, \dots, v_i\}$ of an order
-- statement:
--   For an order $v_1, \dots, v_n$ and $0 \le i \le n$, the prefix is the set $\{v_1, \dots, v_i\}$, which is $\emptyset$ for $i = 0$ and $V$ for $i = n$. These are the sets on which the greedy vector (2) evaluates $f$ and over which $\mathrm{MinSet}$ takes its minimum.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.4

import Mathlib

namespace GeomRescale

/-- The prefix `{v₁, …, v_i}` of the order with position map `σ`, with `pref σ 0 = ∅`
(Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.4, the sets in (2) and (4)). -/
def pref {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => (σ v : ℕ) < i)

end GeomRescale


