-- Prove2me | Definitions.Def_BallPolyApprox_VertexBudget_SimplexLayer
-- name    : BallPolyApprox_VertexBudget_SimplexLayer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:54:29.350211+00:00
-- url     : https://prove2.me/theorems/d538e57c-6dad-448c-b345-3b81df7e44f2
-- title:
--   Dirichlet law on the simplex, barycentric interpolation gap $W_T$ (26), Greenwood's statistic $Q_k$, its median $\mu_k$, the sign $\sigma_k$ and $\beta_m$ (29), (31)
-- statement:
--   $\Lambda\sim\mathrm{Dirichlet}_k(1,\dots,1)$ is the uniform law on the standard simplex $\{\lambda\in\mathbb R^k:\lambda_i\ge0,\ \sum_i\lambda_i=1\}$.
--
--   For points $v_1,\dots,v_k\in\mathbb R^n$ and $x$ in their affine hull, the **barycentric coordinates** $\lambda_i(x)$ satisfy $\sum_i\lambda_i(x)=1$ and $\sum_i\lambda_i(x)v_i=x$ (unique when the $v_i$ are affinely independent). With $q(x)=|x|^2$, the interpolant on $T=\operatorname{conv}\{v_1,\dots,v_k\}$ and the **interpolation gap** are
--   $$I_Tq(x)=\sum_{i=1}^k\lambda_i(x)|v_i|^2,\qquad W_T(x)=I_Tq(x)-q(x)\quad(26).$$
--   A uniform point $Y$ of the simplex $T$ (in its affine hull) is $Y=\sum_i\Lambda_iv_i$ with $\Lambda\sim\mathrm{Dirichlet}_k(1,\dots,1)$.
--
--   **Greenwood's statistic**, its median and the median sign are
--   $$Q_k=\sum_{i=1}^k\Lambda_i^2,\qquad \mu_k=\mathrm{med}(Q_k),\qquad \sigma_k=\mathrm{sign}(\mu_k-Q_k)\quad(29),$$
--   and $\beta_m=\frac{m+2}{m}\,\mathbb E|Q_{m+1}-\mu_{m+1}|$ (31).
--
--   **Formalization Note.** $\mathrm{Dirichlet}_k(1,\dots,1)$ is the normalized Lebesgue measure on the corner simplex $\{x\in\mathbb R^{k-1}:x_i\ge0,\sum x_i\le1\}$ pushed forward by $x\mapsto(x,1-\sum_ix_i)$ (the zero measure for $k=0$, never used). `baryCoord` picks the weights by choice (unique for affinely independent points) and is $0$ off the affine hull. The median is the least $x$ with $P(Q_k\le x)\ge1/2$ (the median is unique). `Real.sign 0 = 0`; $\{Q_k=\mu_k\}$ is a null event.
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), §5.2, pp. 14–15 (PDF 16–17), (26), (28), (29), (31)

import Mathlib
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError

set_option autoImplicit false

open MeasureTheory

namespace BallPolyApprox.VertexBudget

noncomputable section

/-!
# The simplex layer: Dirichlet law, barycentric interpolation, Greenwood's statistic

Gorodzha, Hoehner, Kur, *Approximating the Euclidean Ball by Polytopes*, arXiv:2610.34651
(sha256 164dc885…), §5.2, pp. 14–15 (PDF 16–17), (26), (28), (29), (31).

`Dirichlet_k(1, …, 1)` is the uniform law on the standard simplex
`{λ ∈ ℝ^k : λ_i ≥ 0, Σ λ_i = 1}`. Since that simplex is Lebesgue-null in `ℝ^k`, it is realized as
the image of the normalized Lebesgue measure on the corner simplex
`{x ∈ ℝ^{k−1} : x_i ≥ 0, Σ x_i ≤ 1}` under `x ↦ (x, 1 − Σ x_i)`.

For points `v_1, …, v_k` of `ℝ^n` and a point `x` of their affine hull, the barycentric
coordinates `λ_i(x)` are the weights with `Σ λ_i = 1`, `Σ λ_i v_i = x` (unique when the `v_i` are
affinely independent). `I_T q(x) = Σ λ_i(x) |v_i|²` interpolates `q(x) = |x|²` at the vertices and
`W_T = I_T q − q` is the interpolation gap (26). A uniform point of the simplex `conv{v_i}` (in its
affine hull) is `Σ Λ_i v_i` with `Λ ~ Dirichlet_k(1, …, 1)`.

Greenwood's statistic is `Q_k = Σ Λ_i²`, `μ_k = med(Q_k)`, `σ_k = sign(μ_k − Q_k)` (29) with
`sign 0 = 0`, and `β_m = ((m + 2)/m) E|Q_{m+1} − μ_{m+1}|` (31).
-/

/-- The corner simplex `{x ∈ ℝ^n : x_i ≥ 0, Σ x_i ≤ 1}` (coordinates `Fin n → ℝ`). -/
def cornerSimplex (n : ℕ) : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- `Dirichlet_k(1, …, 1)`, the uniform probability law on the standard simplex of `ℝ^k`
(coordinates `Fin k → ℝ`): the normalized Lebesgue measure on the corner simplex of `ℝ^{k−1}`,
pushed forward by `x ↦ (x_1, …, x_{k−1}, 1 − Σ x_i)`. (For `k = 0` it is the zero measure; it is
never used there.) -/
def dirichletOnes : (k : ℕ) → Measure (Fin k → ℝ)
  | 0 => 0
  | n + 1 =>
      Measure.map (fun x : Fin n → ℝ => (Fin.snoc (α := fun _ => ℝ) x (1 - ∑ i, x i)))
        ((volume (cornerSimplex n))⁻¹ • volume.restrict (cornerSimplex n))

instance dirichletOnes.instSFinite (k : ℕ) : SFinite (dirichletOnes k) := by
  cases k <;> dsimp [dirichletOnes] <;> infer_instance

/-- Barycentric coordinates `λ(x) = (λ_1(x), …, λ_k(x))` of `x` with respect to the points
`v_1, …, v_k` of `ℝ^n`: the weights with `Σ λ_i = 1` and `Σ λ_i v_i = x` (unique for affinely
independent `v`); `0` if `x` is not in the affine hull. -/
def baryCoord {n k : ℕ} (v : Fin k → Rd n) (x : Rd n) : Fin k → ℝ := by
  classical
  exact if h : ∃ w : Fin k → ℝ, ∑ i, w i = 1 ∧ ∑ i, w i • v i = x then h.choose else 0

/-- The affine interpolant `I_T q(x) = Σ_i λ_i(x) |v_i|²` of `q(x) = |x|²` on the simplex
`T = conv{v_1, …, v_k}`. -/
def interpQ {n k : ℕ} (v : Fin k → Rd n) (x : Rd n) : ℝ :=
  ∑ i, baryCoord v x i * ‖v i‖ ^ 2

/-- The interpolation gap `W_T(x) = I_T q(x) − q(x)` (26). -/
def interpGap {n k : ℕ} (v : Fin k → Rd n) (x : Rd n) : ℝ :=
  interpQ v x - ‖x‖ ^ 2

/-- The uniform law on the simplex `conv{v_1, …, v_k}` (within its affine hull): the image of
`Λ ~ Dirichlet_k(1, …, 1)` under `Λ ↦ Σ Λ_i v_i`. For affinely independent `v` this is the
normalized `(k−1)`-dimensional volume on the simplex. -/
def simplexUniform {n k : ℕ} (v : Fin k → Rd n) : Measure (Rd n) :=
  (dirichletOnes k).map fun w => ∑ i, w i • v i

/-- Greenwood's statistic `Q_k = Σ_i Λ_i²` (29) as a function of the Dirichlet vector. -/
def greenwood {k : ℕ} (w : Fin k → ℝ) : ℝ := ∑ i, w i ^ 2

/-- The median `μ_k = med(Q_k)` of Greenwood's statistic under `Dirichlet_k(1, …, 1)` (29): the
least `x` with `P(Q_k ≤ x) ≥ 1/2` (the median is unique, the cdf being strictly increasing on
`[1/k, 1]`). -/
def greenwoodMedian (k : ℕ) : ℝ :=
  sInf {x : ℝ | (1 : ℝ) / 2 ≤ (dirichletOnes k).real {w | greenwood w ≤ x}}

/-- The median sign `σ_k = sign(μ_k − Q_k)` (29), with `sign 0 = 0`. -/
def medianSign (k : ℕ) (w : Fin k → ℝ) : ℝ := Real.sign (greenwoodMedian k - greenwood w)

/-- `β_m = ((m + 2)/m) E|Q_{m+1} − μ_{m+1}|` (31), the expectation under
`Λ ~ Dirichlet_{m+1}(1, …, 1)`. -/
def betaM (m : ℕ) : ℝ :=
  ((m : ℝ) + 2) / m * ∫ w, |greenwood w - greenwoodMedian (m + 1)| ∂dirichletOnes (m + 1)

end

end BallPolyApprox.VertexBudget


