-- Prove2me | Definitions.Def_WildeQIT_strongTypicalSet
-- name    : WildeQIT_strongTypicalSet
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T07:36:27.39932+00:00
-- url     : https://prove2.me/theorems/7e90dcec-c8ec-426d-9f16-79c00b81d2db
-- title:
--   Strongly typical set $T_\delta^{X^n}$ and strong jointly typical set (Definitions 14.7.2, 14.8.1–14.8.2)
-- statement:
--   **Definition 14.7.2 (Strongly typical set).** The $\delta$-strongly typical set is the set of all sequences whose empirical distribution $\frac1n N(x|x^n)$ has maximum deviation $\delta$ from $p_X$ and vanishes on every letter of probability zero:
--
--   $$
--   T_\delta^{X^n} \equiv \Bigl\{ x^n : \forall x\in\mathcal{X},\ \bigl|\tfrac1n N(x|x^n) - p_X(x)\bigr| \le \delta \text{ if } p_X(x)>0,\ \text{else } \tfrac1n N(x|x^n) = 0 \Bigr\}.
--   $$
--
--   **Definitions 14.8.1–14.8.2 (Strong joint typicality).** Two sequences $x^n,y^n$ are $\delta$-strongly jointly typical if their joint empirical distribution $\frac1n N(x,y|x^n,y^n)$ has maximum deviation $\delta$ from $p_{XY}$ and vanishes wherever $p_{XY}(x,y)=0$; $T_\delta^{X^nY^n}$ is the set of all such pairs, i.e. the strongly typical set of the joint distribution on the product alphabet.
--
--   **Formalization Note.** `strongTypicalSet p n δ` for `p : FinDist α`; `strongJointTypicalSet p n δ` is an abbreviation for `strongTypicalSet p n δ` with `p : FinDist (α × β)` and sequences of pairs.
-- source:
--   Wilde, Quantum Information Theory 2nd ed. (Cambridge 2017; arXiv:1106.1445v8), Definition 14.7.2, §Types and Strong Typicality, LaTeX label def-ct:strong-typ (roster-items.csv line 25830); and Definitions 14.8.1–14.8.2 (Strong Jointly Typical Sequence / Set, lines 26324, 26331).

import Definitions.Def_WildeQIT_type

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Definition 14.7.2 (Strongly typical set):
`T_δ^{Xⁿ} ≡ { xⁿ : ∀ x ∈ 𝒳, |N(x|xⁿ)/n − p_X(x)| ≤ δ if p_X(x) > 0, else N(x|xⁿ)/n = 0 }`;
Definitions 14.8.1–14.8.2 (Strong jointly typical sequence / set): the same condition for pairs
of sequences with respect to the joint distribution `p_{XY}`, i.e. the strongly typical set of the
product alphabet.
-/

namespace WildeQIT

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Definition 14.7.2. The `δ`-strongly typical set of length-`n` sequences for the source `p`. -/
noncomputable def strongTypicalSet (p : FinDist α) (n : ℕ) (δ : ℝ) : Finset (Fin n → α) :=
  Finset.univ.filter fun x => ∀ a, if 0 < p.prob a then |typeOf x a - p.prob a| ≤ δ else typeOf x a = 0

theorem mem_strongTypicalSet {p : FinDist α} {n : ℕ} {δ : ℝ} {x : Fin n → α} :
    x ∈ strongTypicalSet p n δ ↔
      ∀ a, if 0 < p.prob a then |typeOf x a - p.prob a| ≤ δ else typeOf x a = 0 := by
  simp [strongTypicalSet]

/-- Definitions 14.8.1–14.8.2. The `δ`-strongly jointly typical set `T_δ^{XⁿYⁿ}` of sequences of
pairs: the strongly typical set of the joint distribution on the product alphabet. -/
noncomputable abbrev strongJointTypicalSet (p : FinDist (α × β)) (n : ℕ) (δ : ℝ) :
    Finset (Fin n → α × β) :=
  strongTypicalSet p n δ

end WildeQIT


