-- Prove2me | Definitions.Def_GMFGLearn_Smoothing
-- name    : GMFGLearn_Smoothing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:52:34.680906+00:00
-- url     : https://prove2.me/theorems/5ef4a317-7f8b-4660-870f-878aaf705a94
-- title:
--   argmax-e, the generalized softmax $\mathrm{softmax}_h$ (21), the gap $\delta$, and the families $\mathcal F_{c,c'}$ and $\mathcal B_{c,c'}$
-- statement:
--   For $x\in\mathbb R^n$ (indexed by a finite set of size $n$) and $\|\cdot\|_2$ the Euclidean norm:
--
--   1. **argmax-e.** $\mathrm{argmax\text{-}e}(x)$ is the uniform probability vector on the maximizing coordinates $\{i: x_i=\max_jx_j\}$.
--   2. **Generalized softmax (21).** For $h:\mathbb R\to\mathbb R$, $\mathrm{softmax}_h(x)_i=\exp(h(x_i))\big/\sum_{j=1}^n\exp(h(x_j))$.
--   3. **Gap.** $x_{\max}=\max_ix_i$ and $\delta=x_{\max}-\max_{x_j<x_{\max}}x_j$, with $\delta:=\infty$ when all $x_j$ are equal.
--   4. **$\mathcal F_{c,c'}$.** The maps $f:\mathbb R^n\to\mathbb R^n$ with Condition 1, $\|f(x)-f(y)\|_2\le c\|x-y\|_2$, and Condition 2, $\|f(x)-\mathrm{argmax\text{-}e}(x)\|_2\le2n\exp(-c'\delta)$.
--   5. **$\mathcal B_{c,c'}$.** The operators $\mathrm{softmax}_h$ with $c'(x-y)\le h(x)-h(y)\le c(x-y)$ for all $x\ge y$.
--
--   $\mathcal F_{c,c'}$ is the class of smoothed argmax-e's from which the learning algorithm builds its policies; $\mathcal B_{c,c'}$ shows it is nonempty.
--
--   **Formalization Note** $\mathbb R^n$ is `ι → ℝ` for a finite index type with $n=|\iota|$. The case $\delta=\infty$ of Condition 2 (all entries equal) is stated as the equality $f(x)=\mathrm{argmax\text{-}e}(x)$, the value of $2n\exp(-c'\cdot\infty)=0$ for $c'>0$.
-- source:
--   Guo, Hu, Xu, Zhang, A General Framework for Learning Mean-Field Games, arXiv:2003.06069v3, §4.1, p.10 (argmax-e); §4.2, Conditions 1–2, p.11; (21) and B_{c,c'}, p.12

import Mathlib

namespace GMFGLearn

variable {ι : Type*} [Fintype ι]

/-- **The Euclidean norm `‖v‖₂`** of a vector `v ∈ ℝ^ι`, `√(Σ_i v_i²)`. -/
noncomputable def l2 (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The set of maximizing coordinates `{i | x_i = max_j x_j}`. -/
noncomputable def argmaxSet (x : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => ∀ j, x j ≤ x i)

/-- **argmax-e.** Guo–Hu–Xu–Zhang, *A General Framework for Learning Mean-Field Games*,
arXiv:2003.06069v3, §4.1, p.10: "the argmax-e operator is defined so that actions with equal maximum
Q-values would have equal probabilities to be selected" (e.g. `argmax-e(1,1) = (1/2,1/2)`, p.11).
It is the uniform probability vector on the set of maximizing coordinates. -/
noncomputable def argmaxE (x : ι → ℝ) : ι → ℝ := by
  classical
  exact fun i => if i ∈ argmaxSet x then 1 / ((argmaxSet x).card : ℝ) else 0

/-- **The generalized softmax `softmax_h` (21).** Guo–Hu–Xu–Zhang, arXiv:2003.06069v3, (21), p.12:
`softmax_h(x)_i = exp(h(x_i)) / Σ_{j=1}^n exp(h(x_j))`. -/
noncomputable def softmaxH (h : ℝ → ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => Real.exp (h (x i)) / ∑ j, Real.exp (h (x j))

/-- `x_max = max_i x_i` (Condition 2, p.11). -/
noncomputable def xmax (x : ι → ℝ) : ℝ :=
  ⨆ i, x i

/-- All entries of `x` are equal (the case `δ := ∞` of Condition 2, p.11). -/
def AllEqual (x : ι → ℝ) : Prop :=
  ∀ i j, x i = x j

/-- **The gap `δ = x_max − max_{x_j < x_max} x_j`** (Condition 2, p.11; Lemma 7, p.21).

**Formalization Note** Used only when the entries are not all equal, in which case the set
`{x_j | x_j < x_max}` is finite and nonempty and `sSup` is its maximum. The page's `δ := ∞` for
equal entries is encoded separately (`AllEqual`). -/
noncomputable def gap (x : ι → ℝ) : ℝ :=
  xmax x - sSup {t : ℝ | ∃ j, x j = t ∧ t < xmax x}

/-- **The family `F_{c,c′}` of smoothed argmax-e's.** Guo–Hu–Xu–Zhang, arXiv:2003.06069v3, §4.2,
p.11: all `f : ℝⁿ → ℝⁿ` satisfying Condition 1, `‖f(x) − f(y)‖₂ ≤ c‖x − y‖₂`, and Condition 2,
`‖f(x) − argmax-e(x)‖₂ ≤ 2n exp(−c′δ)`, where `δ = x_max − max_{x_j<x_max} x_j`,
`x_max = max_{i=1,…,n} x_i`, and `δ := ∞` when all `x_j` are equal.

**Formalization Note** `ℝⁿ` is `ι → ℝ` for a finite index type with `n = |ι|`. When all entries are
equal, `δ = ∞` and (for `c′ > 0`) the bound `2n exp(−∞) = 0` is the equality `f(x) = argmax-e(x)`,
which is how that case is stated. -/
def FSet (c c' : ℝ) : Set ((ι → ℝ) → ι → ℝ) :=
  {f | (∀ x y, l2 (f x - f y) ≤ c * l2 (x - y)) ∧
    ∀ x, (AllEqual x → f x = argmaxE x) ∧
      (¬ AllEqual x → l2 (f x - argmaxE x) ≤ 2 * (Fintype.card ι : ℝ) * Real.exp (-(c' * gap x)))}

/-- **The subfamily `B_{c,c′}` of generalized softmax operators.** Guo–Hu–Xu–Zhang,
arXiv:2003.06069v3, §4.2, p.12: the operators `softmax_h` of (21) where `h : ℝ → ℝ` satisfies
`c′(x − y) ≤ h(x) − h(y) ≤ c(x − y)` for any `x ≥ y`. -/
def BSet (c c' : ℝ) : Set ((ι → ℝ) → ι → ℝ) :=
  {g | ∃ h : ℝ → ℝ, (∀ x y : ℝ, y ≤ x → c' * (x - y) ≤ h x - h y ∧ h x - h y ≤ c * (x - y)) ∧
    g = softmaxH h}

end GMFGLearn


