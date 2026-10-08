-- Prove2me | Definitions.Def_StochKriging_OptimalMSE_Assumption1
-- name    : StochKriging_OptimalMSE_Assumption1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:48.658169+00:00
-- url     : https://prove2.me/theorems/72e37c6a-60c6-40b7-82ee-250ecf99419d
-- title:
--   §3, Assumption 1, p. 365 — stationary Gaussian random field, i.i.d. normal noise, no CRN, noise independent of the field
-- statement:
--   Let the design settings be $\mathbb R^d$, let $\mathsf M$ and $\varepsilon_j$ be as in the stochastic kriging model, let $\mathbf x_1,\dots,\mathbf x_k$ be design points and let $\mathsf V:\mathbb R^d\to[0,\infty)$ be a noise-variance function. **Assumption 1** of the paper ("The random field $\mathsf M$ is a stationary Gaussian random field, and $\varepsilon_1(\mathbf x_i),\varepsilon_2(\mathbf x_i),\dots$ are i.i.d. $N(0,\mathsf V(\mathbf x_i))$, independent of $\varepsilon_j(\mathbf x_h)$ for all $j$ and $h\ne i$ (i.e., no CRN), and independent of $\mathsf M$"), with the paper's gloss of a stationary Gaussian random field, consists of:
--   1. $\mathsf M$ is a Gaussian random field: every finite vector $(\mathsf M(\mathbf y_1),\dots,\mathsf M(\mathbf y_m))$ is multivariate normal, and $\mathrm E\,\mathsf M(\mathbf y)=0$ for every $\mathbf y$;
--   2. stationarity: $\mathrm{Cov}[\mathsf M(\mathbf y),\mathsf M(\mathbf y')]=\tau^2R(\mathbf y-\mathbf y')$ for some $\tau^2>0$ and some function $R$ with $R(\mathbf 0)=1$;
--   3. at every finite family of distinct points the covariance matrix of $\mathsf M$ is positive definite;
--   4. $\mathsf V(\mathbf x_i)>0$ and $\varepsilon_j(\mathbf x_i)\sim N(0,\mathsf V(\mathbf x_i))$ for every design point $i$ and replication $j$;
--   5. the family $\{\varepsilon_j(\mathbf x_i)\}_{i\le k,\ j\ge1}$ is mutually independent (i.i.d. at each design point, no common random numbers across design points);
--   6. this whole noise family is independent of the whole field $\mathsf M$.
--
--   Assumption 1 is the setting in which the paper's predictor (6) becomes the conditional expectation of the response given the sample means.
--
--   **Formalization Note** Gaussianity of the field is Mathlib's `IsGaussianProcess` (all finite-dimensional laws Gaussian). Items 5 and 6 are one `iIndepFun` over the index type `Fin k × ℕ` and one `IndepFun` between the noise family, as a random element of `Fin k × ℕ → ℝ`, and the field, as a random element of `ℝ^d → ℝ` with the product σ-algebra. Replication $j\ge1$ of the paper is index `j - 1`.
-- source:
--   Ankenman, Nelson, Staum, Stochastic Kriging for Simulation Metamodeling, Proc. 2008 Winter Simulation Conference, p. 365, §3, Assumption 1 and the paragraph following it

import Mathlib
import Definitions.Def_StochKriging_OptimalMSE_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StochKriging.OptimalMSE

/-- Assumption 1 of Ankenman, Nelson and Staum (WSC 2008, §3, p. 365) at the design points
`x₁, …, x_k` (Lean `x 0, …, x (k-1)`), for a field indexed by `ℝᵈ`, with the paper's gloss of
"stationary Gaussian random field" (p. 365):
1. `M` is a Gaussian random field (every finite-dimensional law is Gaussian) with mean `0`;
2. stationarity: `Cov[M(y), M(y')] = τ² R(y − y')` with `τ² > 0` and `R(0) = 1`;
3. at every finite family of distinct points the covariance matrix of `M` is positive definite;
4. for each design point `x_i` the noises `ε₁(x_i), ε₂(x_i), …` are `N(0, V(x_i))` with
   `V(x_i) > 0`;
5. the whole noise family `{ε_j(x_i)}_{i,j}` is mutually independent (i.i.d. at each point,
   no CRN across points);
6. the whole noise family is independent of the whole field `M`. -/
structure Assumption1 {Ω : Type*} [MeasurableSpace Ω] {d k : ℕ} (P : Measure Ω)
    (M : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (ε : ℕ → EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (V : EuclideanSpace ℝ (Fin d) → ℝ≥0) (x : Fin k → EuclideanSpace ℝ (Fin d)) : Prop where
  gaussian : IsGaussianProcess M P
  mean_zero : ∀ y, ∫ ω, M y ω ∂P = 0
  stationary : ∃ τ2 : ℝ, 0 < τ2 ∧ ∃ R : EuclideanSpace ℝ (Fin d) → ℝ, R 0 = 1 ∧
    ∀ y y', cov[M y, M y'; P] = τ2 * R (y - y')
  posDef : ∀ (m : ℕ) (y : Fin m → EuclideanSpace ℝ (Fin d)), Function.Injective y →
    (Matrix.of fun a b => cov[M (y a), M (y b); P]).PosDef
  noise_var_pos : ∀ i : Fin k, 0 < V (x i)
  noise_law : ∀ (i : Fin k) (j : ℕ), HasLaw (ε j (x i)) (gaussianReal 0 (V (x i))) P
  noise_indep : iIndepFun (fun (p : Fin k × ℕ) => ε p.2 (x p.1)) P
  noise_indep_field : IndepFun (fun ω (p : Fin k × ℕ) => ε p.2 (x p.1) ω)
    (fun ω y => M y ω) P

end StochKriging.OptimalMSE


