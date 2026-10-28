-- Prove2me | Definitions.Def_WildeQIT_strongCondTypicalSet
-- name    : WildeQIT_strongCondTypicalSet
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T07:36:29.70121+00:00
-- url     : https://prove2.me/theorems/b146e32f-c146-453f-8f3f-bea8514903b3
-- title:
--   Conditional empirical distribution and the strong conditionally typical set (Definitions 14.9.1–14.9.2)
-- statement:
--   **Definition 14.9.1 (Conditional empirical distribution).** $t_{y^n|x^n}(y|x) = t_{x^ny^n}(x,y)/t_{x^n}(x)$.
--
--   **Definition 14.9.2 (Strong conditional typicality).** For a conditioning sequence $x^n$ and the conditional distribution $p(y|x) = p_{Y|X}(y|x)$ (a classical channel $N$), the $\delta$-strong conditionally typical set consists of the sequences whose joint empirical counts are $\delta$-close to the product of the true conditional distribution with the marginal empirical counts:
--
--   $$
--   T_\delta^{Y^n|x^n} \equiv \Bigl\{ y^n : \forall (x,y),\ |N(x,y|x^n,y^n) - p(y|x)N(x|x^n)| \le n\delta \text{ if } p(y|x)>0,\ \text{else } N(x,y|x^n,y^n)=0 \Bigr\}.
--   $$
--
--   **Formalization Note.** `seqPair x y` is the sequence of pairs $(x_i,y_i)$; `condTypeOf x y` is $t_{y^n|x^n}$ (with $a/0=0$); `strongCondTypicalSet N x δ` is the set, defined for every $x^n$ (Wilde states it for a strongly typical $x^n$).
-- source:
--   Wilde, Quantum Information Theory 2nd ed. (Cambridge 2017; arXiv:1106.1445v8), Definition 14.9.2, §Definition of Strong Conditional Typicality, LaTeX label def-ct:strong-cond-typ (roster-items.csv line 26566); with Definition 14.9.1 (Conditional Empirical Distribution, line 26557).

import Definitions.Def_WildeQIT_type
import Definitions.Def_WildeQIT_Channel

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Definition 14.9.1 (Conditional empirical
distribution) `t_{yⁿ|xⁿ}(y|x) = t_{xⁿyⁿ}(x,y) / t_{xⁿ}(x)`, and Definition 14.9.2 (Strong
conditional typicality): for a conditioning sequence `xⁿ`,
`T_δ^{Yⁿ|xⁿ} ≡ { yⁿ : ∀ (x,y), |N(x,y|xⁿ,yⁿ) − p(y|x) N(x|xⁿ)| ≤ nδ if p(y|x) > 0,
else N(x,y|xⁿ,yⁿ) = 0 }`, with `p(y|x) = p_{Y|X}(y|x)` a classical channel.
-/

namespace WildeQIT

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The pair sequence `(xⁿ, yⁿ)` as one sequence of pairs. -/
def seqPair {n : ℕ} (x : Fin n → α) (y : Fin n → β) : Fin n → α × β := fun i => (x i, y i)

/-- Definition 14.9.1. The conditional empirical distribution
`t_{yⁿ|xⁿ}(y|x) = t_{xⁿyⁿ}(x,y) / t_{xⁿ}(x)`. -/
noncomputable def condTypeOf {n : ℕ} (x : Fin n → α) (y : Fin n → β) : α → β → ℝ :=
  fun a b => typeOf (seqPair x y) (a, b) / typeOf x a

/-- Definition 14.9.2. The `δ`-strong conditionally typical set `T_δ^{Yⁿ|xⁿ}` for the channel
`N = p_{Y|X}` and the conditioning sequence `xⁿ`. -/
noncomputable def strongCondTypicalSet (N : Channel α β) {n : ℕ} (x : Fin n → α) (δ : ℝ) :
    Finset (Fin n → β) :=
  Finset.univ.filter fun y => ∀ a b,
    if 0 < (N a).prob b then
      |(seqCount (seqPair x y) (a, b) : ℝ) - (N a).prob b * seqCount x a| ≤ n * δ
    else seqCount (seqPair x y) (a, b) = 0

theorem mem_strongCondTypicalSet {N : Channel α β} {n : ℕ} {x : Fin n → α} {δ : ℝ} {y : Fin n → β} :
    y ∈ strongCondTypicalSet N x δ ↔ ∀ a b,
      if 0 < (N a).prob b then
        |(seqCount (seqPair x y) (a, b) : ℝ) - (N a).prob b * seqCount x a| ≤ n * δ
      else seqCount (seqPair x y) (a, b) = 0 := by
  simp [strongCondTypicalSet]

end WildeQIT


