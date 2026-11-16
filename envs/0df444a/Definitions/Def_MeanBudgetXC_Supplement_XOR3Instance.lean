-- Prove2me | Definitions.Def_MeanBudgetXC_Supplement_XOR3Instance
-- name    : MeanBudgetXC_Supplement_XOR3Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:09:57.451209+00:00
-- url     : https://prove2.me/theorems/acff6479-d3f7-4ce3-95bc-3faeea01099f
-- title:
--   3XOR instances with distinct-variable clauses
-- statement:
--   A **3XOR instance** on $n$ Boolean variables with $m$ clauses assigns to each clause $e$ an ordered scope $I_e$ of three distinct variables and a right-hand side $b_e\in\mathbb F_2$; the clause asks $\sum_{i\in I_e}z_i=b_e$. Repeated clauses are allowed.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Appendix D, Lemma D.1, p.42; D.2, p.43

import Mathlib

namespace MeanBudgetXC.Supplement

/-- A **3XOR instance** on `n` Boolean variables with `m` clauses (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Appendix D,
Lemma D.1, p.42, and D.2, p.43): clause `e` has an ordered scope `I_e` of three distinct
variables and a right-hand side `b_e ∈ F₂`, and asks `∑_{i ∈ I_e} z_i = b_e`. Repeated clauses
are allowed. -/
structure XOR3Instance (n m : ℕ) where
  /-- The ordered scope `I_e` of clause `e`. -/
  scope : Fin m → Fin 3 → Fin n
  /-- The three variables of a clause are distinct. -/
  scope_injective : ∀ e, Function.Injective (scope e)
  /-- The right-hand side `b_e` of clause `e`. -/
  rhs : Fin m → ZMod 2

end MeanBudgetXC.Supplement


