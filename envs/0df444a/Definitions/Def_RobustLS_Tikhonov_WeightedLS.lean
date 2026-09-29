-- Prove2me | Definitions.Def_RobustLS_Tikhonov_WeightedLS
-- name    : RobustLS_Tikhonov_WeightedLS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:28:26.543432+00:00
-- url     : https://prove2.me/theorems/5709b16d-a1e0-4ba1-9baa-ff6ece1cdbea
-- title:
--   The augmented weighted least-squares system of Remark 3.1
-- statement:
--   Fix $A \in \mathbb R^{n\times m}$, $b \in \mathbb R^n$ and scalars $\lambda, \tau$. Remark 3.1 of El Ghaoui and Lebret considers the augmented system
--   $$\begin{bmatrix} A \\ I \\ 0 \end{bmatrix} x \;\simeq\; \begin{bmatrix} b \\ 0 \\ 1 \end{bmatrix},$$
--   with $n + m + 1$ rows: the rows of $A$, the rows of the $m\times m$ identity $I$, and one zero row; the right-hand side stacks $b$, the zero vector of $\mathbb R^m$ and the number $1$. The residual is weighted by the diagonal matrix
--   $$\Theta = \mathbf{diag}\big((\lambda-\tau) I_n,\ \tau I_m,\ \tau\big).$$
--   For a diagonal matrix $\Theta = \mathbf{diag}(\theta)$ with positive entries, the weighted norm of the paper's Notation, $\|r\|_\Theta = \|\Theta^{-1/2} r\|$, is
--   $$\|r\|_\Theta = \sqrt{\sum_i \frac{r_i^2}{\theta_i}}.$$
--
--   These objects state the paper's interpretation of the robust least-squares solution as an ordinary weighted least-squares solution whose weights are produced by the SOCP (15).
--
--   **Formalization Note** The row index set is `Fin n ⊕ (Fin m ⊕ Unit)`. `weightedNorm θ r` is the explicit formula above; it agrees with $\|\Theta^{-1/2} r\|$ only when every $\theta_i > 0$, which is the situation of Remark 3.1 ($\lambda > \tau \ge 1$).
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1041 (PDF p. 7), Remark 3.1; weighted norm ‖x‖_S = ‖S^{-1/2}x‖ from the Notation, p. 1035 (PDF p. 1)

import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

/-- The augmented matrix `[A; I; 0] ∈ ℝ^{(n+m+1)×m}` of El Ghaoui & Lebret (1997), Remark 3.1,
p. 1041 (PDF p. 7): the rows of `A` (indexed by `Fin n`), then the rows of the `m × m` identity
(indexed by `Fin m`), then one zero row (indexed by `Unit`). -/
def augMatrix {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin n ⊕ (Fin m ⊕ Unit)) (Fin m) ℝ :=
  Matrix.of fun i j =>
    Sum.elim (fun k => A k j) (Sum.elim (fun k => (1 : Matrix (Fin m) (Fin m) ℝ) k j)
      (fun _ => 0)) i

/-- The augmented right-hand side `[b; 0; 1] ∈ ℝ^{n+m+1}` of Remark 3.1 (El Ghaoui & Lebret 1997,
p. 1041, PDF p. 7). -/
def augRhs {n m : ℕ} (b : Fin n → ℝ) : Fin n ⊕ (Fin m ⊕ Unit) → ℝ :=
  Sum.elim b (Sum.elim (fun _ => 0) (fun _ => 1))

/-- The diagonal of the weighting matrix `Θ = diag((λ − τ)I, τI, τ)` of Remark 3.1
(El Ghaoui & Lebret 1997, p. 1041, PDF p. 7): `λ − τ` on the `n` coordinates of the first block,
`τ` on the `m` coordinates of the second block and on the last coordinate. -/
def thetaDiag (n m : ℕ) (lam tau : ℝ) : Fin n ⊕ (Fin m ⊕ Unit) → ℝ :=
  Sum.elim (fun _ => lam - tau) (Sum.elim (fun _ => tau) (fun _ => tau))

/-- The weighted norm `‖r‖_Θ = ‖Θ^{-1/2} r‖` for a diagonal `Θ = diag(θ) > 0`, as defined in the
Notation of El Ghaoui & Lebret (1997), p. 1035 (PDF p. 1): "For S > 0, and given vector x, we
define ‖x‖_S = ‖S^{-1/2}x‖". For diagonal `Θ` with positive entries `θᵢ` this is
`√(∑ᵢ rᵢ² / θᵢ)`. (Meaningful only when every `θᵢ > 0`, which is the case in Remark 3.1.) -/
noncomputable def weightedNorm {ι : Type*} [Fintype ι] (θ : ι → ℝ) (r : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, r i ^ 2 / θ i)

end RobustLS.Tikhonov


