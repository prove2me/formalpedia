-- Prove2me | Definitions.Def_TreeOrient_RecGreedy_Supplement_TopLevel
-- name    : TreeOrient_RecGreedy_Supplement_TopLevel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:51:59.553932+00:00
-- url     : https://prove2.me/theorems/90925634-38a3-474c-9d3b-eec00886ed6e
-- title:
--   Remark 2.1, Algorithms 1–2 — the top-level calls RG(r∗, ∅, B, ∅, d) of Theorems 2.6 and 2.9
-- statement:
--   These definitions fix the two algorithms whose guarantees Theorems 2.6 and 2.9 state, on the submodular tree orienteering model of the published module `TreeOrient.RecGreedy.Model`: an instance has $n$ vertices, a root $r^*$, nonnegative integer edge costs $c$, a budget $B$ and a natural-valued vertex-set reward $f$.
--
--   Remark 2.1 calls the recursive greedy procedure as $RG(r^*,\emptyset,B,\emptyset,d)$ for a depth $d\ge\log_{3/2}k$, where $k$ bounds the number of vertices of an optimal solution. The least such integer is
--
--   $$d_{2.6}(k)=\bigl\lceil \log_{3/2} k\bigr\rceil .$$
--
--   The algorithm of Theorem 2.6 is Algorithm 1, which enumerates every budget split, called as $RG(r^*,\emptyset,B,\emptyset,d_{2.6}(k))$. The algorithm of Theorem 2.9 is Algorithm 2 ($RG\text{-}QP$), which guesses a value threshold $u\in[0,U]$ and finds the budget split by binary search, with $U=n^a$ the polynomial bound on $f$, called as $RG\text{-}QP(r^*,\emptyset,B,\emptyset,d)$ with $d=2\lceil\log_2 k\rceil\ge\log_{3/2}k$.
--
--   Each algorithm returns either "Infeasible" or an edge set, together with the step count of the published model.
--
--   **Formalization Note** Both calls reuse the published `rg` without change: `rg I 1 .enum` is Algorithm 1 and `rg I 1 (.bsearch U)` is Algorithm 2, including the published repairs (budgets guessed from $0$, infeasibility propagated, the root removed from $Y$). The depth of Theorem 2.9 is the published `dOf k`, the same depth the published Theorem 1.1 uses.
-- source:
--   Ghuge & Nagarajan, arXiv:1812.01768v2, p. 5 (PDF 6), Remark 2.1, Algorithm 1; p. 7 (PDF 8), Algorithm 2

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Model

namespace TreeOrient.RecGreedy.Supplement

/-- Remark 2.1, p. 5 (PDF 6): the least integer depth `d` with `d ≥ log_{3/2} k`. -/
noncomputable def d26 (k : ℕ) : ℕ := ⌈Real.logb (3 / 2) k⌉₊

/-- The algorithm of Theorem 2.6: Algorithm 1 (budget enumeration) called as
`RG(r∗, ∅, B, ∅, d)` with Remark 2.1's depth `d = d26 k`. -/
noncomputable def alg26 {n : ℕ} (I : Inst n) (k : ℕ) : Option (Edges n) × ℕ :=
  rg I 1 .enum (d26 k) I.root ∅ I.B ∅

/-- The algorithm of Theorem 2.9: Algorithm 2 (binary search on the budget, value guesses
`u ∈ [0, U]` with `U = n ^ a`) called as `RG-QP(r∗, ∅, B, ∅, d)` with depth `d = dOf k`. -/
noncomputable def alg29 {n : ℕ} (I : Inst n) (a k : ℕ) : Option (Edges n) × ℕ :=
  rg I 1 (.bsearch (n ^ a)) (dOf k) I.root ∅ I.B ∅

end TreeOrient.RecGreedy.Supplement


