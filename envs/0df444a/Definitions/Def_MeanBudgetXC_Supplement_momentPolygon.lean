-- Prove2me | Definitions.Def_MeanBudgetXC_Supplement_momentPolygon
-- name    : MeanBudgetXC_Supplement_momentPolygon
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:08:49.385795+00:00
-- url     : https://prove2.me/theorems/c56594ef-c915-49a6-807a-a61aa5872c5b
-- title:
--   The moment polygon $M_a$
-- statement:
--   For an integer $a$, the **moment polygon** is
--   $$M_a=\operatorname{conv}\{(j,\tbinom j2):\ j\in\{0,\dots,a\}\}\subseteq\mathbb R^2.$$
--   Its first coordinate plays the role of the total singleton mass $\sum_ip_i$ and its second the total pair mass $W(q)=\sum_{i<j}q_{ij}$. It contains exactly the aggregate moment pairs of global laws supported on assignments with at most $a$ ones.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Section 6, p.29

import Mathlib

namespace MeanBudgetXC.Supplement

/-- The **moment polygon** `M_a = conv{(j, (j choose 2)) : j ∈ {0, …, a}} ⊆ ℝ²` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 6, p.29). Its first coordinate is the total singleton mass `∑_i p_i` and its
second the total pair mass `W(q)`; it contains exactly the aggregate moment pairs of global laws
supported on assignments with at most `a` ones. -/
def momentPolygon (a : ℕ) : Set (ℝ × ℝ) :=
  convexHull ℝ (Set.range fun j : Fin (a + 1) => ((j.val : ℝ), ((j.val.choose 2 : ℕ) : ℝ)))

end MeanBudgetXC.Supplement


