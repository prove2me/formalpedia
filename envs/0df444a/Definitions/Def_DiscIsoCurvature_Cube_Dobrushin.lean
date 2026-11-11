-- Prove2me | Definitions.Def_DiscIsoCurvature_Cube_Dobrushin
-- name    : DiscIsoCurvature_Cube_Dobrushin
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:07:39.953846+00:00
-- url     : https://prove2.me/theorems/6211dbb5-8261-4667-b084-66d6e699a65e
-- title:
--   Conditional marginals, the Dobrushin influence matrix (Eq. (6) and Definition 6.6), and the Gibbs sampler
-- statement:
--   Let $\mathcal X$ be a finite set, $\Omega=\mathcal X^n$ and $\mu$ a distribution on $\Omega$. The **one-site conditional marginal** is
--   $$\mu_i(a\mid x_{-i})=\frac{\mu(x_{i\leftarrow a})}{\sum_{c\in\mathcal X}\mu(x_{i\leftarrow c})},$$
--   the law of coordinate $i$ given the other coordinates of $x$. With $d_{TV}(P,Q)=\tfrac12\sum_a|P(a)-Q(a)|$ (the published definition `PureDPQR_tvDist`):
--
--   - the **Dobrushin influence matrix** of Definition 6.6 is $R_{ij}=\sup_{x,y:\,x_{-j}=y_{-j}}d_{TV}(\mu_i(\cdot\mid x_{-i}),\mu_i(\cdot\mid y_{-i}))$;
--   - on the cube, Eq. (6) is $R_{ij}=\max_x d_{TV}(\mu_i(\cdot\mid x_{-i}),\mu_i(\cdot\mid x^j_{-i}))$ for $i\ne j$ and $R_{ii}=0$;
--   - $\alpha=\min_{i,x}\mu_i(x_i\mid x_{-i})$ is the **one-site conditional marginal lower bound**;
--   - the **Gibbs sampler** is $G=\frac1n\sum_iK_i$ with $K_i(z\mid y)=\mathbf 1[z_{-i}=y_{-i}]\,\mu_i(z_i\mid z_{-i})$, acting by $(Gf)(y)=\sum_zG(z\mid y)f(z)$, and its Dirichlet form is $\langle f,(I-G)f\rangle_\mu=\mathbb E_\mu[f\,(f-Gf)]$.
--
--   $R$ measures how much the conditional law of one coordinate moves when another coordinate changes; Theorem 1.1 assumes $\|R\|_1\le C_0$ and $\|R\|_2\le1-\delta$.
--
--   **Formalization Note.** `condMarginal` divides by the conditional mass, so it is $0$ (Lean's $a/0=0$) when that mass is $0$; every statement assumes full support or $\alpha>0$, which excludes this. The supremum in Definition 6.6 is over a finite nonempty set (it contains $x=y$). On $\{\pm1\}^n$ the two matrices coincide (for $i\ne j$, $y\in\{x,x^j\}$; for $i=j$ the distance is $0$). $\alpha$ is $0$ when $n=0$ (empty minimum), so a hypothesis $\alpha>0$ excludes $n=0$.
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 3 Eq. (6), p. 37 Definition 6.6 / Eq. (63), p. 38 Theorem 6.8

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_PureDPQR_tvDist

namespace DiscIsoCurvature.Cube

/-!
# Conditional marginals, the Dobrushin influence matrix, and the Gibbs sampler

Chen, Chen, Zhang, *Discrete Isoperimetric Inequalities via Curvature*, arXiv:2609.24687
(version of November 3, 2026, sha256 ec30d304…): Eq. (6) (p. 3), Definition 6.6, Eq. (63)
(p. 37), Theorem 6.8 (p. 38).

* `X` is a finite alphabet, `Ω = X^n = Fin n → X`, `μ : Ω → ℝ` a distribution.
* `condMarginal μ i x a = μ_i(a | x_{−i}) = μ(x with xᵢ := a) / ∑_c μ(x with xᵢ := c)`, the
  conditional law of coordinate `i` given the other coordinates of `x` (Lean's `a / 0 = 0` when
  the conditioning event has mass `0`; every use assumes full support or `α > 0`).
* `PureDPQR.tvDist P Q = ½ ∑_a |P(a) − Q(a)|` is the total variation distance (published
  platform definition `PureDPQR_tvDist`).
* `dobrushinMatrix μ` is Definition 6.6: `R_ij = sup_{x, y : x_{−j} = y_{−j}} d_TV(μ_i(·|x_{−i}),
  μ_i(·|y_{−i}))`. `dobrushinCube μ` is Eq. (6) on `{±1}^n`:
  `R_ij = max_x d_TV(μ_i(·|x_{−i}), μ_i(·|x^j_{−i}))` for `i ≠ j`, `R_ii = 0`.
* `gibbsSampler μ` is the matrix `G(y, z) = G(z | y) = (1/n) ∑ᵢ 1[z_{−i} = y_{−i}] μ_i(zᵢ | z_{−i})`;
  `(G f)(y) = ∑_z G(z | y) f(z)` is `(gibbsSampler μ).mulVec f`.
-/

/-- The one-site conditional marginal `μ_i(a | x_{−i})`. -/
noncomputable def condMarginal {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (μ : (Fin n → X) → ℝ) (i : Fin n) (x : Fin n → X) (a : X) : ℝ :=
  μ (Function.update x i a) / ∑ c, μ (Function.update x i c)

/-- The Dobrushin influence matrix of Definition 6.6 (Eq. (63), p. 37), over a finite alphabet:
`R_ij = sup_{x, y with x_{−j} = y_{−j}} d_TV(μ_i(· | x_{−i}), μ_i(· | y_{−i}))`. -/
noncomputable def dobrushinMatrix {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (μ : (Fin n → X) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ⨆ p : {p : (Fin n → X) × (Fin n → X) // ∀ k, k ≠ j → p.1 k = p.2 k},
    PureDPQR.tvDist (condMarginal μ i p.1.1) (condMarginal μ i p.1.2)

/-- The Dobrushin influence matrix of Eq. (6) (p. 3) on `{±1}^n`:
`R_ij = max_x d_TV(μ_i(· | X_{−i} = x_{−i}), μ_i(· | X_{−i} = x^j_{−i}))` for `i ≠ j`, `R_ii = 0`. -/
noncomputable def dobrushinCube {n : ℕ} (μ : BoolCube n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then 0 else
    ⨆ x : BoolCube n, PureDPQR.tvDist (condMarginal μ i x) (condMarginal μ i (flip x j))

/-- The one-site conditional marginal lower bound `α = min_{i, x} μ_i(xᵢ | x_{−i})`
(Theorem 6.8). -/
noncomputable def minCondMarginal {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (μ : (Fin n → X) → ℝ) : ℝ :=
  ⨅ p : Fin n × (Fin n → X), condMarginal μ p.1 p.2 (p.2 p.1)

/-- The Gibbs sampler `G = (1/n) ∑ᵢ Kᵢ`, `Kᵢ(z | y) = 1[z_{−i} = y_{−i}] μ_i(zᵢ | z_{−i})`,
as the matrix with entry `G(z | y)` in row `y`, column `z` (Theorem 6.8, p. 38). -/
noncomputable def gibbsSampler {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (μ : (Fin n → X) → ℝ) : Matrix (Fin n → X) (Fin n → X) ℝ :=
  fun y z => (1 / (n : ℝ)) *
    ∑ i, (if ∀ k, k ≠ i → z k = y k then condMarginal μ i z (z i) else 0)

/-- The Dirichlet form `⟨f, (I − G) f⟩_μ = E_μ[f · (f − G f)]` of the Gibbs sampler. -/
noncomputable def gibbsDirichlet {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (μ : (Fin n → X) → ℝ) (f : (Fin n → X) → ℝ) : ℝ :=
  expect μ (fun y => f y * (f y - (gibbsSampler μ).mulVec f y))

end DiscIsoCurvature.Cube


