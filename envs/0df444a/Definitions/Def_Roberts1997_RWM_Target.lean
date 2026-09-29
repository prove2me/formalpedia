-- Prove2me | Definitions.Def_Roberts1997_RWM_Target
-- name    : Roberts1997_RWM_Target
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:43:35.096539+00:00
-- url     : https://prove2.me/theorems/ca8769c6-6ab1-49d4-a409-fe54a98b0d69
-- title:
--   Product target π_n, Gaussian proposal q_n, acceptance function α, and average acceptance rate a_n(l)
-- statement:
--   Fix $f:\mathbb R\to\mathbb R$, a dimension $n$ and a scale $l$. On $\mathbb R^n$ the paper defines (p. 111, (1.1)):
--
--   1. the **product density** $\pi_n(x)=\prod_{i=1}^n f(x_i)$ and the **target measure** $\pi_n(x)\,dx$, the product of $n$ copies of $f(y)\,dy$;
--   2. the **proposal variance** $\sigma_n^2 = l^2/(n-1)$;
--   3. the **Gaussian proposal** $q_n(x,\cdot)=N(x,\sigma_n^2 I_n)$, with density
--   $$ q_n(x,y)=\frac{1}{(2\pi\sigma_n^2)^{n/2}}\exp\Big\{-\frac{1}{2\sigma_n^2}|y-x|^2\Big\}; $$
--   4. the **acceptance function** $\alpha(x,y) = 1\wedge \pi_n(y)/\pi_n(x)$;
--   5. the **first component** $x_1$ of $x\in\mathbb R^n$;
--   6. the **average acceptance rate** (p. 112)
--   $$ a_n(l)=\int\!\!\int \pi_n(x)\,\alpha(x,y)\,q_n(x,y)\,dx\,dy . $$
--
--   These are the ingredients of the random walk Metropolis algorithm and of Corollary 1.2.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`; the paper's component $i$ is the Lean index $i-1$, so $x_1$ is index $0$ (`first x`, which returns $0$ only in the empty case $n=0$). $\sigma_n^2$ is computed in $\mathbb R$ with $(n:\mathbb R)-1$, never with natural-number subtraction; it is positive for $n\ge 2$, and every statement of the mission concerns $n\ge2$ or large $n$. The proposal is the product of the independent normals $N(x_i,\sigma_n^2)$, which has exactly the displayed density; the variance is passed to `gaussianReal` as `(sigmaSq n l).toNNReal`. In $a_n(l)$ the factor $q_n(x,y)\,dy$ is written as integration against the proposal measure. Since $f>0$ (standing hypothesis) $\pi_n(x)>0$ and $\alpha$ involves no division by zero.
-- source:
--   Roberts, Gelman, Gilks, Weak convergence and optimal scaling of random walk Metropolis algorithms, Ann. Appl. Probab. 7(1), 1997, p. 111, Eq. (1.1), definitions of q_n, σ_n² and α; p. 112, definition of a_n(l)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace Roberts1997.RWM

/-- The product density `π_n(x) = ∏_{i=1}^n f(x_i)` of (1.1), on `ℝ^n = Fin n → ℝ`
(the paper's component `i` is the Lean index `i - 1`). -/
noncomputable def targetDens (f : ℝ → ℝ) (n : ℕ) (x : Fin n → ℝ) : ℝ := ∏ i, f (x i)

/-- The target measure `π_n(x) dx`: the product of `n` copies of `f(y) dy`. -/
noncomputable def target (f : ℝ → ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => volume.withDensity (fun y => ENNReal.ofReal (f y)))

/-- The proposal variance `σ_n² = l²/(n - 1)`, computed in `ℝ`. -/
noncomputable def sigmaSq (n : ℕ) (l : ℝ) : ℝ := l ^ 2 / ((n : ℝ) - 1)

/-- The Gaussian proposal `q_n(x, ·) = N(x, σ_n² I_n)`, as the product of the independent
one-dimensional normals `N(x_i, σ_n²)`; its density is the displayed `q_n(x, y)`.
The variance is `σ_n²` coerced to `ℝ≥0` by `Real.toNNReal` (exact for `n ≥ 2`). -/
noncomputable def proposal (n : ℕ) (l : ℝ) (x : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => gaussianReal (x i) (sigmaSq n l).toNNReal)

/-- The acceptance function `α(x, y) = 1 ∧ π_n(y)/π_n(x)`. -/
noncomputable def accept (f : ℝ → ℝ) (n : ℕ) (x y : Fin n → ℝ) : ℝ :=
  min 1 (targetDens f n y / targetDens f n x)

/-- The first component `x_1` of a vector `x ∈ ℝ^n` (Lean index `0`); `0` when `n = 0`. -/
noncomputable def first {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  if h : 0 < n then x ⟨0, h⟩ else 0

/-- The average acceptance rate
`a_n(l) = ∫∫ π_n(x) α(x, y) q_n(x, y) dx dy`, with `q_n(x, y) dy` written as the proposal
measure. -/
noncomputable def accRateN (f : ℝ → ℝ) (n : ℕ) (l : ℝ) : ℝ :=
  ∫ x, ∫ y, accept f n x y ∂(proposal n l x) ∂(target f n)

end Roberts1997.RWM


