-- Prove2me | Definitions.Def_WildeQIT_jointTypicalSet
-- name    : WildeQIT_jointTypicalSet
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T07:42:30.013468+00:00
-- url     : https://prove2.me/theorems/4c43fe63-62f1-489d-8113-e20cb6cec0c1
-- title:
--   Joint sample entropy and the jointly typical set $T_\delta^{X^nY^n}$ (Definitions 14.5.1–14.5.3)
-- statement:
--   Consider $n$ independent realizations $x^n$ and $y^n$ of random variables $X$ and $Y$ with joint distribution $p_{XY}$ on $\mathcal{X}\times\mathcal{Y}$, i.i.d. across positions: $p_{X^nY^n}(x^n,y^n) = \prod_i p_{XY}(x_i,y_i)$. A pair of sequences is represented as one sequence of pairs (`Fin n → α × β`), with component sequences `seqFst`, `seqSnd`.
--
--   **Definition 14.5.1 (Joint sample entropy).** $\overline{H}(x^n,y^n) \equiv -\frac{1}{n}\log p_{X^nY^n}(x^n,y^n)$.
--
--   **Definition 14.5.2 (Jointly typical sequence).** $x^n, y^n$ are $\delta$-jointly typical if their joint sample entropy is $\delta$-close to $H(X,Y)$ and both $x^n$ and $y^n$ are marginally $\delta$-typical.
--
--   **Definition 14.5.3 (Jointly typical set).**
--
--   $$
--   T_\delta^{X^nY^n} \equiv \bigl\{ (x^n,y^n) : |\overline{H}(x^n,y^n)-H(X,Y)|\le\delta,\ x^n\in T_\delta^{X^n},\ y^n\in T_\delta^{Y^n} \bigr\}.
--   $$
--
--   **Formalization Note.** `jointSampleEntropy p z` abbreviates `sampleEntropy p z` for the joint distribution `p : FinDist (α × β)`; `jointTypicalSet p n δ` filters sequences of pairs by positivity of the joint probability plus the three conditions, the marginal ones using `typicalSet p.fst` and `typicalSet p.snd` (pairs of probability zero have sample entropy $+\infty$ in the book and are excluded explicitly). This replaces the retired `WildeQIT_weakJointTypicalSet`.
-- source:
--   Wilde, Quantum Information Theory 2nd ed. (Cambridge 2017; arXiv:1106.1445v8), Definition 14.5.3, §Weak Joint Typicality, LaTeX label def-ct:weak-joint-typ-set (roster-items.csv line 25366); with Definitions 14.5.1 (Joint Sample Entropy, line 25334) and 14.5.2 (Jointly Typical Sequence, line 25357).

import Definitions.Def_WildeQIT_typicalSet

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Definitions 14.5.1–14.5.3 (Joint sample entropy,
jointly typical sequence, jointly typical set). For `n` independent realizations of the pair
`(X,Y)` with i.i.d. joint distribution `p_{XⁿYⁿ}(xⁿ,yⁿ) = ∏ᵢ p_{XY}(xᵢ,yᵢ)`, the joint sample
entropy is `H̄(xⁿ,yⁿ) = -(1/n) log p_{XⁿYⁿ}(xⁿ,yⁿ)`, and
`T_δ^{XⁿYⁿ} ≡ { (xⁿ,yⁿ) : |H̄(xⁿ,yⁿ) − H(X,Y)| ≤ δ, xⁿ ∈ T_δ^{Xⁿ}, yⁿ ∈ T_δ^{Yⁿ} }`.
A pair of sequences is one sequence of pairs, `Fin n → α × β`. Pairs of probability zero are
never jointly typical (their sample entropy is `+∞` in the book). (Replaces the retired
`WildeQIT_weakJointTypicalSet`.)
-/

namespace WildeQIT

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The sequence of first components `xⁿ` of a sequence of pairs. -/
def seqFst {n : ℕ} (z : Fin n → α × β) : Fin n → α := fun i => (z i).1

/-- The sequence of second components `yⁿ` of a sequence of pairs. -/
def seqSnd {n : ℕ} (z : Fin n → α × β) : Fin n → β := fun i => (z i).2

/-- Definition 14.5.1. The joint sample entropy `H̄(xⁿ,yⁿ) = -(1/n) log₂ ∏ᵢ p_{XY}(xᵢ,yᵢ)`,
i.e. the sample entropy of the pair sequence with respect to the joint distribution. -/
noncomputable abbrev jointSampleEntropy (p : FinDist (α × β)) {n : ℕ} (z : Fin n → α × β) : ℝ :=
  sampleEntropy p z

/-- Definitions 14.5.2–14.5.3. The `δ`-jointly typical set `T_δ^{XⁿYⁿ}`: pairs of sequences of
positive joint probability whose joint sample entropy is `δ`-close to `H(X,Y)` and whose
components are each `δ`-typical. -/
noncomputable def jointTypicalSet (p : FinDist (α × β)) (n : ℕ) (δ : ℝ) : Finset (Fin n → α × β) :=
  Finset.univ.filter fun z =>
    0 < (p.iid n).prob z ∧ |sampleEntropy p z - entropy p| ≤ δ ∧
      seqFst z ∈ typicalSet p.fst n δ ∧ seqSnd z ∈ typicalSet p.snd n δ

theorem mem_jointTypicalSet {p : FinDist (α × β)} {n : ℕ} {δ : ℝ} {z : Fin n → α × β} :
    z ∈ jointTypicalSet p n δ ↔
      0 < (p.iid n).prob z ∧ |sampleEntropy p z - entropy p| ≤ δ ∧
        seqFst z ∈ typicalSet p.fst n δ ∧ seqSnd z ∈ typicalSet p.snd n δ := by
  simp only [jointTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and]

end WildeQIT


