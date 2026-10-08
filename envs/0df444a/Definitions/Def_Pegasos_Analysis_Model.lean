-- Prove2me | Definitions.Def_Pegasos_Analysis_Model
-- name    : Pegasos_Analysis_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:17:28.559598+00:00
-- url     : https://prove2.me/theorems/da76b81c-9eae-4a74-9d55-ac1d4e4bee8d
-- title:
--   The SVM objective (1), the mini-batch objective (7), the sub-gradient (8), the projection (6) and the mini-batch Pegasos run (Fig. 2)
-- statement:
--   This module fixes the objects of the analysis of mini-batch Pegasos.
--
--   **Data.** A training set of $m$ examples $(x_i, y_i)$, $i \in [m]$, with $x_i \in \mathbb R^n$ and $y_i \in \mathbb R$ (the theorems assume $y_i \in \{+1,-1\}$), a regularisation parameter $\lambda$, and a mini-batch size $k$. The hinge loss is $\ell(w;(x,y)) = \max\{0,\, 1 - y\langle w, x\rangle\}$ (Eq. (2)).
--
--   1. **The SVM objective** (Eq. (1)):
--   $$f(w) = \frac{\lambda}{2}\|w\|^2 + \frac{1}{m}\sum_{i=1}^m \ell(w;(x_i,y_i)).$$
--   2. **The instantaneous objective** on a mini-batch $A$ of $k$ example indices (Eq. (7)):
--   $$f(w;A) = \frac{\lambda}{2}\|w\|^2 + \frac{1}{k}\sum_{i\in A} \ell(w;(x_i,y_i)).$$
--   3. **The margin-violation average** $v(w;A) = \frac1k\sum_{i\in A} \mathbb 1[y_i\langle w,x_i\rangle<1]\, y_i x_i$ and **the sub-gradient** of Eq. (8),
--   $$\nabla(w;A) = \lambda w - v(w;A).$$
--   4. **The projection step** (6): $w \mapsto \min\{1, (1/\sqrt\lambda)/\|w\|\}\, w$.
--   5. **The mini-batch Pegasos run** (Fig. 2): $w_1 = 0$ and, for $t \ge 1$,
--   $$w_{t+1} = P\bigl(w_t - \eta_t \nabla(w_t; A_t)\bigr),\qquad \eta_t = \frac{1}{\lambda t},$$
--   where $P$ is the projection step (6) if projection is performed and the identity otherwise. This is the update $w_{t+1} = (1-\eta_t\lambda)w_t + \frac{\eta_t}{k}\sum_{i\in A_t^+} y_i x_i$ of Fig. 2, with $A_t^+ = \{i \in A_t : y_i\langle w_t, x_i\rangle < 1\}$.
--
--   These are the objects about which Theorem 1 of the paper is stated: the algorithm's iterates $w_t$, the per-round objectives $f(\cdot;A_t)$, and the full objective $f$ whose minimiser is the comparator.
--
--   **Formalization Note.** Vectors live in `EuclideanSpace ℝ (Fin n)`; examples are indexed by `Fin m`. A mini-batch is a $k$-tuple `B : Fin k → Fin m`, and sums over the batch run over its $k$ entries: an injective tuple is a subset of $[m]$ of size $k$ (Fig. 2), a non-injective one a multi-set, which the paper also covers (p. 9). Iterations are 1-based: `run … 1 = 0`, and step $t \ge 1$ uses $\eta_t = 1/(\lambda t)$ and only the batch `A t`; the value at index 0 is set to 0 and never used. At $w = 0$ the paper's projection formula is undefined; Lean's convention $a/0 = 0$ gives $\min\{1,0\}\cdot 0 = 0$, the intended value. The hinge loss is the published `UnderstandingML.hingeLoss`.
-- source:
--   Shalev-Shwartz, Singer, Srebro & Cotter, Pegasos: primal estimated sub-gradient solver for SVM, Math. Program. 127 (2011), p. 4, Eq. (1)-(2); p. 8, Eq. (6)-(8); p. 9, Fig. 2

import Mathlib
import Definitions.Def_UnderstandingML_SGD
import Definitions.Def_LogRegretOCO_OGD_Model

namespace Pegasos.Analysis

/-- The SVM objective of Eq. (1) (p. 4):
`f(w) = λ/2 ‖w‖² + (1/m) Σ_{i=1}^m ℓ(w; (xᵢ, yᵢ))`, with `ℓ` the hinge loss of Eq. (2),
`ℓ(w; (x, y)) = max{0, 1 − y⟨w, x⟩}` (`UnderstandingML.hingeLoss`). Examples are indexed
by `Fin m`. -/
noncomputable def svmObj {n m : ℕ} (lam : ℝ) (x : Fin m → EuclideanSpace ℝ (Fin n))
    (y : Fin m → ℝ) (w : EuclideanSpace ℝ (Fin n)) : ℝ :=
  lam / 2 * ‖w‖ ^ 2 + (1 / (m : ℝ)) * ∑ i, UnderstandingML.hingeLoss w (x i, y i)

/-- The instantaneous (mini-batch) objective of Eq. (7) (p. 8):
`f(w; A) = λ/2 ‖w‖² + (1/k) Σ_{i ∈ A} ℓ(w; (xᵢ, yᵢ))`. The mini-batch is a `k`-tuple
`B : Fin k → Fin m` of example indices; the sum runs over its `k` entries (an injective tuple
is a subset of `[m]` of size `k`, a non-injective one a multi-set, p. 9). -/
noncomputable def instObj {n m k : ℕ} (lam : ℝ) (x : Fin m → EuclideanSpace ℝ (Fin n))
    (y : Fin m → ℝ) (B : Fin k → Fin m) (w : EuclideanSpace ℝ (Fin n)) : ℝ :=
  lam / 2 * ‖w‖ ^ 2 + (1 / (k : ℝ)) * ∑ j, UnderstandingML.hingeLoss w (x (B j), y (B j))

/-- The averaged margin-violation term
`v(w; A) = (1/k) Σ_{i ∈ A} 1l[yᵢ⟨w, xᵢ⟩ < 1] yᵢ xᵢ` (the `v_t` of p. 11, and the second
term of Eq. (8)). -/
noncomputable def hingeTerm {n m k : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin n))
    (y : Fin m → ℝ) (B : Fin k → Fin m) (w : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (1 / (k : ℝ)) • ∑ j, if y (B j) * inner ℝ w (x (B j)) < 1 then y (B j) • x (B j) else 0

/-- The sub-gradient of Eq. (8) (p. 8): `∇ = λ w − (1/k) Σ_{i ∈ A} 1l[yᵢ⟨w, xᵢ⟩ < 1] yᵢ xᵢ`. -/
noncomputable def subgrad {n m k : ℕ} (lam : ℝ) (x : Fin m → EuclideanSpace ℝ (Fin n))
    (y : Fin m → ℝ) (B : Fin k → Fin m) (w : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  lam • w - hingeTerm x y B w

/-- The optional projection step (6) (p. 8): `w ↦ min{1, (1/√λ)/‖w‖} w`. At `w = 0` the
paper's formula is undefined; Lean's `a / 0 = 0` gives `min 1 0 • 0 = 0`. -/
noncomputable def projBall {n : ℕ} (lam : ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  min 1 ((1 / Real.sqrt lam) / ‖w‖) • w

/-- The mini-batch Pegasos run of Fig. 2 (p. 9), with 1-based iterations: `run … 1 = w₁ = 0`
and, for `t ≥ 1`, `run … (t+1) = P(w_t − η_t ∇_t)` with `η_t = 1/(λt)`, `∇_t` the
sub-gradient (8) at `w_t` on the mini-batch `A t`, and `P` the projection step (6) when
`project = true`, the identity otherwise. Step `t` reads only `A t`, so `w_{t+1}` depends only
on `A 1, …, A t`. The value at index `0` is `0` and is never used. -/
noncomputable def run {n m k : ℕ} (lam : ℝ) (x : Fin m → EuclideanSpace ℝ (Fin n))
    (y : Fin m → ℝ) (A : ℕ → Fin k → Fin m) (project : Bool) :
    ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => 0
  | 1 => 0
  | t + 2 =>
    let w := run lam x y A project (t + 1)
    let z := w - (1 / (lam * ((t + 1 : ℕ) : ℝ))) • subgrad lam x y (A (t + 1)) w
    if project then projBall lam z else z

end Pegasos.Analysis


