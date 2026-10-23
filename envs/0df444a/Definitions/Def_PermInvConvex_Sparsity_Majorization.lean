-- Prove2me | Definitions.Def_PermInvConvex_Sparsity_Majorization
-- name    : PermInvConvex_Sparsity_Majorization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:09.992988+00:00
-- url     : https://prove2.me/theorems/c1cbe098-0aad-48d4-94d7-fd08ff266e07
-- title:
--   §2–§3, pp. 3, 6 — permutation-invariant norms, symmetric gauges, |x|, x_{Δ+} (12), majorization ≥m and weak majorization ≥wm (Definition 2.1)
-- statement:
--   This file fixes the order-theoretic vocabulary of Kim, Tawarmalani and Richard for vectors $x \in \mathbb R^n$.
--
--   1. A function $f : \mathbb R^n \to \mathbb R$ is a **permutation-invariant norm** if it is a norm ($f(x) = 0 \iff x = 0$, $f(x+y) \le f(x) + f(y)$, $f(cx) = |c|\,f(x)$) and $f(Px) = f(x)$ for every permutation matrix $P$.
--   2. It is a **symmetric gauge function** (a sign- and permutation-invariant norm) if moreover $f(\bar x) = f(x)$ whenever $|\bar x| = |x|$ coordinatewise.
--   3. $|x| = (|x_1|, \dots, |x_n|)$, and $x_{\Delta_+} = (|x|_{[1]}, \dots, |x|_{[n]})$ lists the entries of $|x|$ in nonincreasing order, $|x|_{[i]}$ being the $i$-th largest.
--   4. Write $x_{[i]}$ for the $i$-th largest entry of $x$. Then $x$ **majorizes** $y$, written $x \ge_m y$, if
--   $$\sum_{i=1}^{j} x_{[i]} \ge \sum_{i=1}^{j} y_{[i]} \quad (j = 1, \dots, n-1), \qquad \sum_{i=1}^{n} x_{[i]} = \sum_{i=1}^{n} y_{[i]},$$
--   and $y$ is **weakly submajorized** by $x$, written $x \ge_{wm} y$, if $\sum_{i=1}^{j} x_{[i]} \ge \sum_{i=1}^{j} y_{[i]}$ for every $j = 1, \dots, n$.
--
--   These are the notions in which the Sparsity Theorem and the convex-hull description (13) are phrased.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`; Lean index $i$ is the paper's $i+1$. The norm is a plain function carrying the axioms as a structure, never Lean's built-in norm on `Fin n → ℝ` (which is the sup norm). The partial sum $\sum_{i \le j} x_{[i]}$ is the published `ModernConvex.Spectral.sumLargest j x`, the maximum of $\sum_{i \in s} x_i$ over $j$-element index sets $s$; it is only used for $j \le n$. With this choice $x \ge_m y$ is literally the right-hand side of the published Lemma 2.2 (`majorization_principle`). $x_{\Delta_+}$ is built from Mathlib's `Tuple.sort` of $|x|$, read backwards.
-- source:
--   Kim, Tawarmalani, Richard, Convexification of Permutation-Invariant Sets and an Application to Sparse PCA, arXiv:1910.02573v2, p. 3 (permutation and sign invariance, x[i], Definition 2.1), p. 6 (symmetric gauge function, (12))

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR

namespace PermInvConvex.Sparsity

open ModernConvex.Spectral

/-- A permutation-invariant norm on `ℝⁿ` (Kim–Tawarmalani–Richard, p. 3 and Lemma 3.1, p. 7):
`f` is a norm (definite, subadditive, absolutely homogeneous) and `f (x ∘ σ) = f x` for every
permutation `σ` of the coordinates, i.e. `f(Px) = f(x)` for every permutation matrix `P`. -/
structure IsPermInvNorm {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop where
  eq_zero_iff : ∀ x, f x = 0 ↔ x = 0
  add_le : ∀ x y, f (x + y) ≤ f x + f y
  smul : ∀ (c : ℝ) (x : Fin n → ℝ), f (c • x) = |c| * f x
  perm : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ), f (x ∘ σ) = f x

/-- A sign- and permutation-invariant norm, also called a symmetric gauge function (p. 6):
a permutation-invariant norm with `f x = f y` whenever `|xᵢ| = |yᵢ|` for every `i` (sign
invariance, p. 3). -/
structure IsSymmetricGauge {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop extends IsPermInvNorm f where
  sign : ∀ x y : Fin n → ℝ, (∀ i, |x i| = |y i|) → f x = f y

/-- The coordinatewise absolute value `|x| = (|x₁|, …, |xₙ|)`. -/
def absVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => |x i|

/-- `x_{Δ₊}` of (12), p. 6: the vector `(|x|_{[1]}, …, |x|_{[n]})` of the entries of `|x|` in
nonincreasing order. `Tuple.sort` sorts increasingly; reading it backwards (`Fin.rev`) gives the
nonincreasing order. Index `i : Fin n` is the paper's `i + 1`. -/
noncomputable def decAbs {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => |x (Tuple.sort (absVec x) i.rev)|

/-- Majorization, Definition 2.1, p. 3: `x ≥ₘ y` iff `∑_{i ≤ j} x_{[i]} ≥ ∑_{i ≤ j} y_{[i]}` for
`j = 1, …, n − 1` and `∑ x_{[i]} = ∑ y_{[i]}`. The sum of the `j` largest entries is
`sumLargest j`, and the total sum needs no sorting. `Majorizes x y` reads "x majorizes y". -/
def Majorizes {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  (∀ j : ℕ, 1 ≤ j → j ≤ n - 1 → sumLargest j y ≤ sumLargest j x) ∧ ∑ i, y i = ∑ i, x i

/-- Weak (sub)majorization, Definition 2.1, p. 3: `x ≥_{wm} y` iff
`∑_{i ≤ j} x_{[i]} ≥ ∑_{i ≤ j} y_{[i]}` for every `j = 1, …, n`. `WeakMajorizes x y` reads
"y is weakly submajorized by x". -/
def WeakMajorizes {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ n → sumLargest j y ≤ sumLargest j x

end PermInvConvex.Sparsity


