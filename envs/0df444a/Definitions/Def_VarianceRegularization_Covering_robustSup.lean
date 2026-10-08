-- Prove2me | Definitions.Def_VarianceRegularization_Covering_robustSup
-- name    : VarianceRegularization_Covering_robustSup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:11:40.350738+00:00
-- url     : https://prove2.me/theorems/206b877f-48f6-4059-bde6-0dfa514ef5e2
-- title:
--   Eq. (4), (8) — the robust risk of a function at a sample, and the empirical mean and variance
-- statement:
--   Fix a sample size $n \ge 1$ and a radius $\rho \ge 0$. The **$\chi^2$ ball** around the empirical distribution is the set of weight vectors on the $n$ sample points
--   $$
--   \mathcal P_n = \Big\{ p \in \mathbb R^n : p_i \ge 0,\ \sum_{i=1}^n p_i = 1,\ \tfrac12 \sum_{i=1}^n (n p_i - 1)^2 \le \rho \Big\},
--   $$
--   which is the set $\{P : D_\phi(P\|\widehat P_n) \le \rho/n\}$ of distributions supported on the sample, for the $\phi$-divergence with $\phi(t) = \tfrac12 (t-1)^2$. For a vector $z \in \mathbb R^n$ the **robust mean** is
--   $$
--   \sup_{p \in \mathcal P_n} \sum_{i=1}^n p_i z_i ,
--   $$
--   and the **sample mean** and **sample variance** are $\overline z = \frac1n \sum_i z_i$ and $s_n^2 = \frac1n \sum_i z_i^2 - \overline z^{\,2}$ (normalized by $1/n$).
--
--   For a function $f : \mathcal X \to \mathbb R$ and a sample $x = (x_1, \dots, x_n) \in \mathcal X^n$, applying these to the vector $(f(x_1), \dots, f(x_n))$ gives the **robust risk** $\sup_{P : D_\phi(P\|\widehat P_n) \le \rho/n} \mathbb E_P[f(X)]$, the empirical mean $\mathbb E_{\widehat P_n}[f]$ and the empirical variance $\mathrm{Var}_{\widehat P_n}(f)$.
--
--   These are the objects of the robust procedure (4)/(6) of the paper; every statement of this mission is phrased in terms of them.
--
--   **Formalization Note** The $\chi^2$ ball, the robust mean and the sample mean $\overline z$ are the shared definitions `VarianceRegularization.Expansion.chiSqBall`, `VarianceRegularization.Expansion.robustSup` and `VarianceRegularization.Expansion.empMean` of this series; this item defines the sample variance and the function-level wrappers (robust risk, empirical mean, empirical variance) on top of them. The supremum is a real `sSup`; for $n \ge 1$ and $\rho \ge 0$ the ball contains the uniform weights and is compact, so it is a maximum. When sample values are tied, splitting a tied atom's mass equally over its copies does not increase the divergence (convexity of $\phi$) and keeps the mean, so the supremum over weight vectors equals the paper's supremum over distributions on the sample.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 2, eq. (4); p. 5, eq. (8); p. 6 (definition of s_n^2)

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_chiSqBall
import Definitions.Def_VarianceRegularization_Expansion_robustSup
import Definitions.Def_VarianceRegularization_Expansion_empMean

namespace VarianceRegularization.Covering

/-- The sample variance `s_n² = (1/n) ∑ zᵢ² - z̄²` (normalized by `1/n`, p. 6). -/
noncomputable def sampleVar {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, z i ^ 2 - VarianceRegularization.Expansion.empMean z ^ 2

/-- The robust risk of `f` at the sample `s = (x₁,…,xₙ)`:
`sup { E_P[f(X)] : D_φ(P‖P̂ₙ) ≤ ρ/n }`, `P` ranging over reweightings of the sample. -/
noncomputable def robustRisk {X : Type*} {n : ℕ} (ρ : ℝ) (f : X → ℝ) (s : Fin n → X) : ℝ :=
  VarianceRegularization.Expansion.robustSup n ρ (fun i => f (s i))

/-- The empirical mean `E_{P̂ₙ}[f] = (1/n) ∑ f(xᵢ)`. -/
noncomputable def empMean {X : Type*} {n : ℕ} (f : X → ℝ) (s : Fin n → X) : ℝ :=
  VarianceRegularization.Expansion.empMean (fun i => f (s i))

/-- The empirical variance `Var_{P̂ₙ}(f) = (1/n) ∑ f(xᵢ)² - (E_{P̂ₙ}[f])²`. -/
noncomputable def empVar {X : Type*} {n : ℕ} (f : X → ℝ) (s : Fin n → X) : ℝ :=
  sampleVar (fun i => f (s i))

end VarianceRegularization.Covering


