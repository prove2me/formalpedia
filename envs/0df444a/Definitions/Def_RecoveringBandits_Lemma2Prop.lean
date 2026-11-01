-- Prove2me | Definitions.Def_RecoveringBandits_Lemma2Prop
-- name    : RecoveringBandits_Lemma2Prop
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:54:08.861985+00:00
-- url     : https://prove2.me/theorems/530cdce1-98df-43d3-b08c-d3160f5bdf98
-- title:
--   The property of Lemma 2 for a solution of (3)
-- statement:
--   A point $x\in\mathbb R^N$ has the **property of Lemma 2** when
--
--   1. $x_i\le 1/d^{(1)}_i$ for every arm $i$, and
--   2. for all arms $i$ but at most one, $x_i\in\{0\}\cup\{1/d^{(k)}_i\}_{k\ge1}$.
--
--   Algorithm 2 runs the rounding on an optimal solution of (3) with this property.
--
--   **Formalization Note** "All but one" is stated as "at most one arm violates the membership", which also covers $N=0$.
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, Lemma 2, p.11

import Mathlib
import Definitions.Def_RecoveringBandits_supp

namespace RecoveringBandits

open Classical in
/-- **The property of Lemma 2** (arXiv:2106.14813v2, Lemma 2, p.11): `x_i ≤ 1/d^{(1)}_i` for all
`i ∈ [N]`, and "for at least all `i ∈ [N]` but one, `x_i ∈ {0} ∪ {1/d^{(k)}_i}_{k ≥ 1}`".

**Formalization Note.** "All but at most one" is stated as: at most one index violates the
membership, so the property also makes sense for `N = 0`. -/
def Lemma2Prop {N : ℕ} (R : Fin N → ℕ → ℝ) (x : Fin N → ℝ) : Prop :=
  (∀ i, x i ≤ 1 / (supp (R i) 1 : ℝ)) ∧
    (Finset.univ.filter (fun i =>
      ¬ (x i = 0 ∨ ∃ k : ℕ, 1 ≤ k ∧ x i = 1 / (supp (R i) k : ℝ)))).card ≤ 1

end RecoveringBandits


