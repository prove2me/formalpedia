-- Prove2me | Definitions.Def_RegretBandits_Contextual_Multiclass
-- name    : RegretBandits_Contextual_Multiclass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:39:05.193542+00:00
-- url     : https://prove2.me/theorems/38d41631-d787-47fa-9f68-5d353f2b6ea3
-- title:
--   Multiclass hinge loss, Frobenius norm and the multiclass Perceptron
-- statement:
--   Online multiclass classification with $K$ labels and instances $x_t \in \mathbb R^d$ (Section 4.4 of Bubeck and Cesa-Bianchi). A linear classifier is a $K\times d$ real matrix $U$; its **Frobenius norm** is $\|U\| = \big(\sum_{i,j} U_{ij}^2\big)^{1/2}$.
--
--   The **multiclass hinge loss** of $U$ on an example $(x_t, y_t)$, $y_t \in \{1,\dots,K\}$, is
--   $$\ell_t(U) = \Big[\,1 - (Ux_t)_{y_t} + \max_{i \ne y_t} (Ux_t)_i\,\Big]_+ ,\qquad [z]_+ = \max\{0, z\},$$
--   the **cumulative hinge loss** is $L_n(U) = \sum_{t=1}^n \ell_t(U)$ and the **average hinge loss** is $\bar L_n(U) = L_n(U)/n$.
--
--   The **multiclass Perceptron** keeps a $K\times d$ matrix $W_t$, starting from $W_1 = 0$. At round $t$ it predicts $\hat y_t \in \arg\max_i (W_t x_t)_i$, observes $y_t$ and updates $W_{t+1} = W_t + X_t$ with $(X_t)_{i,j} = x_{t,j}\,(\mathbb 1_{y_t = i} - \mathbb 1_{\hat y_t = i})$. The number of its mistakes in the first $n$ rounds is $\sum_{t=1}^n \mathbb 1_{\hat y_t \ne y_t}$. The argmax is taken through an **argmax selector**, any map choosing for each score vector an index of maximal score; every tie-breaking rule is allowed.
--
--   **Formalization Note** Example sequences are indexed from $0$ (`x 0` is the book's $x_1$). The maximum over $i \neq y_t$ is the real supremum over the finite set of such labels; it is the maximum whenever $K \ge 2$ (every theorem using it assumes $K \ge 2$). The squared Euclidean norm $\sum_j x_j^2$ is written out explicitly (`sqNorm`), so that $\|x_t\| = 1$ is the Euclidean condition of the book.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 56-57, Section 4.4 (multiclass Perceptron, hinge loss, Frobenius norm)

import Mathlib

namespace RegretBandits.Contextual

/-- Frobenius norm of a `K × d` real matrix: `‖U‖ = √(∑_{i,j} U_{ij}²)`. -/
noncomputable def frobNorm {K d : ℕ} (U : Matrix (Fin K) (Fin d) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, U i j ^ 2)

/-- Squared Euclidean norm of a vector `x ∈ ℝ^d`: `∑_j x_j²`. -/
def sqNorm {d : ℕ} (x : Fin d → ℝ) : ℝ := ∑ j, x j ^ 2

/-- Multiclass hinge loss of the linear classifier `U` on the example `(x, y)`
(Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, p. 57):
`ℓ(U) = [1 - (Ux)_y + max_{i ≠ y} (Ux)_i]_+`. The maximum is the real supremum over the finite
set of labels `i ≠ y`, which is the maximum whenever `K ≥ 2`. -/
noncomputable def hingeLoss {K d : ℕ} (U : Matrix (Fin K) (Fin d) ℝ) (x : Fin d → ℝ)
    (y : Fin K) : ℝ :=
  max 0 (1 - (Matrix.mulVec U x) y + ⨆ i : {i : Fin K // i ≠ y}, (Matrix.mulVec U x) i)

/-- Cumulative hinge loss `L_n(U) = ∑_{t=1}^n ℓ_t(U)` on the examples `(x_t, y_t)`; the
sequences are indexed from `0`, so this is `∑_{t<n} ℓ(U; x t, y t)`. -/
noncomputable def cumHinge {K d : ℕ} (n : ℕ) (x : ℕ → Fin d → ℝ) (y : ℕ → Fin K)
    (U : Matrix (Fin K) (Fin d) ℝ) : ℝ :=
  ∑ t ∈ Finset.range n, hingeLoss U (x t) (y t)

/-- Average hinge loss `L̄_n(U) = L_n(U) / n`. -/
noncomputable def avgHinge {K d : ℕ} (n : ℕ) (x : ℕ → Fin d → ℝ) (y : ℕ → Fin K)
    (U : Matrix (Fin K) (Fin d) ℝ) : ℝ :=
  cumHinge n x y U / n

/-- `sel` picks an argmax: `sel v` maximizes `v`. Any tie-breaking rule is allowed. -/
def IsArgmaxSelector {K : ℕ} (sel : (Fin K → ℝ) → Fin K) : Prop :=
  ∀ v : Fin K → ℝ, ∀ i, v i ≤ v (sel v)

/-- Weight matrices of the (full-information) multiclass Perceptron (p. 57), with argmax
selector `sel`: `W_0 = 0` and `W_{t+1} = W_t + X_t`, where
`(X_t)_{i,j} = x_{t,j} (1{y_t = i} - 1{ŷ_t = i})` and `ŷ_t = sel (W_t x_t)` (rounds 0-based). -/
noncomputable def perceptronW {K d : ℕ} (sel : (Fin K → ℝ) → Fin K) (x : ℕ → Fin d → ℝ)
    (y : ℕ → Fin K) : ℕ → Matrix (Fin K) (Fin d) ℝ
  | 0 => 0
  | t + 1 =>
      let W := perceptronW sel x y t
      let yhat := sel (Matrix.mulVec W (x t))
      W + Matrix.of (fun i j => x t j * ((if y t = i then 1 else 0) - (if yhat = i then 1 else 0)))

/-- The Perceptron's prediction at round `t`: `ŷ_t = argmax_i (W_t x_t)_i`. -/
noncomputable def perceptronPred {K d : ℕ} (sel : (Fin K → ℝ) → Fin K) (x : ℕ → Fin d → ℝ)
    (y : ℕ → Fin K) (t : ℕ) : Fin K :=
  sel (Matrix.mulVec (perceptronW sel x y t) (x t))

/-- Number of mistakes of the multiclass Perceptron in the first `n` rounds:
`∑_{t<n} 1{ŷ_t ≠ y_t}`. -/
noncomputable def perceptronMistakes {K d : ℕ} (sel : (Fin K → ℝ) → Fin K)
    (x : ℕ → Fin d → ℝ) (y : ℕ → Fin K) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, if perceptronPred sel x y t ≠ y t then 1 else 0

end RegretBandits.Contextual


