-- Prove2me | Definitions.Def_RetailVariety_Fashion_Majorization
-- name    : RetailVariety_Fashion_Majorization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:05.800815+00:00
-- url     : https://prove2.me/theorems/3f25435f-ec18-4b05-bedb-5c59acda8a1b
-- title:
--   Definitions 1–2: majorization $x\prec y$ and the *more fashionable* order
-- statement:
--   For a vector $x\in\mathbb R^n$ let $x_{[1]}\ge x_{[2]}\ge\cdots\ge x_{[n]}$ be its entries in decreasing order.
--
--   **Definition 1 (majorization).** For $x,y\in\mathbb R^n$, $x$ is **majorized** by $y$, written $x\prec y$, if
--   $$\sum_{i=1}^{n}x_{[i]}=\sum_{i=1}^{n}y_{[i]}\qquad\text{and}\qquad \sum_{i=1}^{k}x_{[i]}\le\sum_{i=1}^{k}y_{[i]}\quad\text{for all }k=1,\dots,n-1.$$
--
--   **Definition 2.** A merchandise category with preference vector $v$ is **more fashionable** than a category $w$ (with the same number of variants) if $(v_1,\dots,v_n)\prec(w_1,\dots,w_n)$.
--
--   Majorization formalizes "evenness": a vector that majorizes another concentrates more of its mass on its largest coordinates. A more fashionable category has preferences spread more evenly across its variants.
--
--   **Formalization Note.** The decreasing rearrangement is $x\circ\sigma_x$ for some permutation $\sigma_x$ of the indices with $x\circ\sigma_x$ antitone. Such a permutation always exists, and the partial sums of $x\circ\sigma_x$ do not depend on which one is chosen, so stating the definition with "there exist sorting permutations" is equivalent to stating it for all of them. Partial sums are over the first $k$ (0-based indices $<k$) entries of the rearranged vectors. Partial sums of the unsorted vectors would be a different relation.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1505, Definition 1 and Definition 2

import Mathlib

namespace RetailVariety.Fashion

/-- Majorization, Definition 1 (van Ryzin & Mahajan 1999, p. 1505). For `x, y ∈ ℝⁿ`, `x ≺ y`
(`x` is majorized by `y`) iff, writing `x_[1] ≥ ⋯ ≥ x_[n]` for the decreasing rearrangement,
`∑_{i=1}^n x_[i] = ∑_{i=1}^n y_[i]` and `∑_{i=1}^k x_[i] ≤ ∑_{i=1}^k y_[i]` for `k = 1, …, n − 1`.

The decreasing rearrangement is `x ∘ σx` for a permutation `σx` with `x ∘ σx` antitone (the
paper's `[i]`); such a permutation always exists and the partial sums of `x ∘ σx` do not depend on
which one is chosen, so the existential form agrees with the universal one. The first `k` entries
(0-based indices `< k`) of the rearranged vector are summed. -/
def Majorized {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  ∃ σx σy : Equiv.Perm (Fin n),
    Antitone (x ∘ σx) ∧ Antitone (y ∘ σy) ∧
    ∑ i, x (σx i) = ∑ i, y (σy i) ∧
    ∀ k : ℕ, 1 ≤ k → k < n →
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), x (σx i) ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), y (σy i)

/-- Definition 2 (p. 1505): a merchandise category `v` is *more fashionable* than `w` if
`(v_1, …, v_n) ≺ (w_1, …, w_n)`. -/
def MoreFashionable {n : ℕ} (v w : Fin n → ℝ) : Prop :=
  Majorized v w

end RetailVariety.Fashion


