-- Prove2me | Definitions.Def_SparseDisc_DiscLE
-- name    : SparseDisc_DiscLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:35.496451+00:00
-- url     : https://prove2.me/theorems/8a7491d0-9b55-4161-9474-e834de9a9625
-- title:
--   Discrepancy at most $c$ of a family of set functions
-- statement:
--   A colouring of the items $\iota$ in red and blue is given by its red set $S$. The family $F = (f_v)_{v \in V}$ has **discrepancy at most $c$** if some colouring balances every function up to $c$:
--   $$
--   \operatorname{disc}(F) \le c \iff \exists\, S \subseteq \iota \ \ \forall v \in V:\ \ |f_v(S) - f_v(\iota \setminus S)| \le c ,
--   $$
--   where $\operatorname{disc}(F) = \min_{\chi : \iota \to [2]} \max_v |f_v(\chi^{-1}(1)) - f_v(\chi^{-1}(2))|$.
--
--   **Formalization Note** The minimum is over finitely many colourings and is attained, so the predicate is exactly $\operatorname{disc}(F) \le c$, and its negation is $\operatorname{disc}(F) > c$. Both colour classes may be empty.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 1, p.1

import Mathlib

namespace SparseDisc

/-- `DiscLE f c`: the family `f = (f_v)_{v ∈ V}` has **discrepancy at most `c`**, i.e. some
red/blue colouring of the items, with red set `S`, satisfies `|f_v(S) − f_v(ι \ S)| ≤ c` for every
`v` (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission
manuscript (sha256 0f09ec60…25b81), Section 1, p.1:
`disc(F) = min_χ max_i |f_i(χ⁻¹(1)) − f_i(χ⁻¹(2))|`).

**Formalization Note** A colouring `χ : [m] → [2]` is its red class `S = χ⁻¹(1)`; both classes may
be empty. The minimum over the finitely many colourings is attained, so `disc(F) ≤ c` iff
`DiscLE f c`, and `disc(F) > c` iff `¬ DiscLE f c`; no `iInf`/`sup` is formed. -/
def DiscLE {V ι : Type} [Fintype ι] [DecidableEq ι] (f : V → Finset ι → ℝ) (c : ℝ) : Prop :=
  ∃ S : Finset ι, ∀ v, |f v S - f v (Finset.univ \ S)| ≤ c

end SparseDisc


