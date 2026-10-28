-- Prove2me | Definitions.Def_WildeQIT_weakCondTypicalSet
-- name    : WildeQIT_weakCondTypicalSet
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T07:44:20.430929+00:00
-- url     : https://prove2.me/theorems/b6f97dd0-c24c-4d18-b725-75532bf5733f
-- title:
--   Conditional sample entropy and the conditionally typical set $T_\delta^{Y^n|x^n}$ (Definitions 14.6.1–14.6.2)
-- statement:
--   Let $p_{XY}(x,y) = p_X(x)\,p_{Y|X}(y|x)$ with the conditional distribution $p_{Y|X}$ a classical channel $N$ (`WildeQIT.Channel α β`), and $p_{Y^n|X^n}(y^n|x^n) \equiv \prod_i p_{Y|X}(y_i|x_i)$.
--
--   **Definition 14.6.1 (Conditional sample entropy).** $\overline{H}(y^n|x^n) = -\frac{1}{n}\log p_{Y^n|X^n}(y^n|x^n)$.
--
--   **Definition 14.6.2 (Conditionally typical set).** For $x^n\in\mathcal{X}^n$,
--
--   $$
--   T_\delta^{Y^n|x^n} \equiv \bigl\{ y^n : |\overline{H}(y^n|x^n) - H(Y|X)| \le \delta \bigr\}.
--   $$
--
--   **Formalization Note.** `Channel.joint N p` is the joint distribution $p_X(x)N(y|x)$; `Channel.seqProb N x y` is $\prod_i N(y_i|x_i)$; `condSampleEntropy N x y` is $\overline{H}(y^n|x^n)$; `Channel.condEntropyOut N p` is $H(Y|X)$, the conditional entropy (Definition 10.2.1) of the pair $(Y,X)$ under the joint distribution; `weakCondTypicalSet p N x δ` is the set, which requires $p_{Y^n|X^n}(y^n|x^n) > 0$ explicitly (such sequences have $\overline{H} = +\infty$ in the book; Lean's `Real.logb 2 0 = 0` would otherwise admit them).
-- source:
--   Wilde, Quantum Information Theory 2nd ed. (Cambridge 2017; arXiv:1106.1445v8), Definition 14.6.2, §Weak Conditional Typicality (roster-items.csv line 25555); with Definition 14.6.1 (Conditional Sample Entropy, line 25538).

import Definitions.Def_WildeQIT_typicalSet
import Definitions.Def_WildeQIT_condEntropy
import Definitions.Def_WildeQIT_Channel

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Definitions 14.6.1–14.6.2 (Conditional sample
entropy, conditionally typical set). With `p_{XY}(x,y) = p_X(x) p_{Y|X}(y|x)` and
`p_{Yⁿ|Xⁿ}(yⁿ|xⁿ) ≡ ∏ᵢ p_{Y|X}(yᵢ|xᵢ)`, the conditional sample entropy is
`H̄(yⁿ|xⁿ) = -(1/n) log p_{Yⁿ|Xⁿ}(yⁿ|xⁿ)` and
`T_δ^{Yⁿ|xⁿ} ≡ { yⁿ : |H̄(yⁿ|xⁿ) − H(Y|X)| ≤ δ }`.
The conditional distribution `p_{Y|X}` is a classical channel `N : Channel α β`. Output sequences of
conditional probability zero have `H̄ = +∞` in the book and are never conditionally typical, so the
set requires `p_{Yⁿ|Xⁿ}(yⁿ|xⁿ) > 0` explicitly (Lean's `Real.logb 2 0 = 0` would otherwise admit them).
-/

namespace WildeQIT

variable {α β : Type} [Fintype α] [Fintype β]

/-- The joint distribution `p_{XY}(x,y) = p_X(x) N(y|x)` of an input distribution and a channel. -/
noncomputable def Channel.joint (N : Channel α β) (p : FinDist α) : FinDist (α × β) where
  prob xy := p.prob xy.1 * (N xy.1).prob xy.2
  nonneg xy := mul_nonneg (p.nonneg xy.1) ((N xy.1).nonneg xy.2)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (N _).sum_eq_one, mul_one]
    exact p.sum_eq_one

@[simp] theorem Channel.joint_prob (N : Channel α β) (p : FinDist α) (x : α) (y : β) :
    (N.joint p).prob (x, y) = p.prob x * (N x).prob y := rfl

/-- The conditional probability `p_{Yⁿ|Xⁿ}(yⁿ|xⁿ) = ∏ᵢ N(yᵢ|xᵢ)` of the output sequence given the
input sequence. -/
noncomputable def Channel.seqProb (N : Channel α β) {n : ℕ} (x : Fin n → α) (y : Fin n → β) : ℝ :=
  ∏ i, (N (x i)).prob (y i)

/-- Definition 14.6.1. The conditional sample entropy `H̄(yⁿ|xⁿ) = -(1/n) log₂ ∏ᵢ N(yᵢ|xᵢ)`. -/
noncomputable def condSampleEntropy (N : Channel α β) {n : ℕ} (x : Fin n → α) (y : Fin n → β) : ℝ :=
  -(1 / (n : ℝ)) * Real.logb 2 (N.seqProb x y)

/-- The conditional entropy `H(Y|X)` of the output of `N` given its input, for input distribution
`p`: the conditional entropy of the pair `(Y, X)` under the joint distribution `p_X N`. -/
noncomputable def Channel.condEntropyOut (N : Channel α β) (p : FinDist α) : ℝ :=
  condEntropy (N.joint p).swap

/-- Definition 14.6.2. The `δ`-conditionally typical set `T_δ^{Yⁿ|xⁿ}` of output sequences for the
input sequence `xⁿ`: `{ yⁿ : p_{Yⁿ|Xⁿ}(yⁿ|xⁿ) > 0, |H̄(yⁿ|xⁿ) − H(Y|X)| ≤ δ }`. -/
noncomputable def weakCondTypicalSet (p : FinDist α) (N : Channel α β) {n : ℕ} (x : Fin n → α) (δ : ℝ) :
    Finset (Fin n → β) :=
  Finset.univ.filter fun y => 0 < N.seqProb x y ∧ |condSampleEntropy N x y - N.condEntropyOut p| ≤ δ

theorem mem_weakCondTypicalSet {p : FinDist α} {N : Channel α β} {n : ℕ} {x : Fin n → α} {δ : ℝ}
    {y : Fin n → β} :
    y ∈ weakCondTypicalSet p N x δ ↔
      0 < N.seqProb x y ∧ |condSampleEntropy N x y - N.condEntropyOut p| ≤ δ := by
  simp only [weakCondTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and]

end WildeQIT


