-- Prove2me | Definitions.Def_BayesEnsemble_GenProbit_Model
-- name    : BayesEnsemble_GenProbit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:30.180512+00:00
-- url     : https://prove2.me/theorems/d6691f1f-68c9-4022-8cb0-d410817f497f
-- title:
--   §3 — Gaussian information states and generalized probit ensemble
-- statement:
--   Let $x=(x_1,\ldots,x_k)$ be jointly normal with mean $\mu$ and covariance matrix $\Sigma=(\sigma_{ij})$, and let $z_0$ have probability law $\nu$. The event model is
--
--   $$
--   P(y=1\mid x)=F_{z_0}\!\left(\alpha_0+\sum_i\alpha_i x_i\right),\qquad F_{z_0}(u)=\nu(({-}\infty,u]).
--   $$
--
--   The module defines the paper's $m_0$, $v_0$, the conditional means $\theta_i,\theta_{-i}$, conditional covariance entries $b_{-i,-i},b_{-i,i},b_{i,i}$, $v_i$, correlations $\rho_{ij}$, and weights $\beta_i$ and $\beta_0$ exactly as in Lemma 1 and Proposition 4. It defines $G_v=F_{z_0+\sqrt v x_0}$ as the cdf of a convolution with a centered normal law, its inverse $G_v^{-1}$, and the formula on the right of (10).
--
--   An expert's report is $p_i=P(y=1\mid x_i)$; the aggregate is $\hat p=P(y=1\mid p_1,\ldots,p_k)$. These are conditional probabilities and are deliberately independent of the claimed closed forms. The standing conditions require a positive semidefinite $\Sigma$, a continuous full-support law $\nu$, and the nonzero denominators in Proposition 4.
--
--   **Formalization Note** Experts are indexed by `Fin k`. The cdf inverse is a real infimum and is used only at probabilities in $(0,1)$. Variances are converted to nonnegative real numbers; positive semidefiniteness ensures no clipping on model inputs. The added nondegeneracy conditions are $\alpha_i\ne0$, $\sigma_{ii}>0$, and $\sum_j\alpha_j\sigma_{ij}\ne0$.
-- source:
--   Lichtendahl, Grushka-Cockayne, Jose & Winkler, Bayesian Ensembles of Binary-Event Forecasts: When Is It Appropriate to Extremize or Anti-Extremize?, arXiv:1705.02391v2, pp. 13–14, §3; p. 27, Lemma 1; p. 14, Proposition 4

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace BayesEnsemble.GenProbit

/-- The information-state law and the coefficients of the generalized linear model in §3. -/
structure Params (k : ℕ) where
  mean : EuclideanSpace ℝ (Fin k)
  S : Matrix (Fin k) (Fin k) ℝ
  alpha0 : ℝ
  alpha : Fin k → ℝ
  nu : Measure ℝ

/-- The assumptions of §3, with the nondegeneracy conditions needed by Proposition 4. -/
structure Standing {k : ℕ} (P : Params k) : Prop where
  posSemidef : P.S.PosSemidef
  diag_pos : ∀ i, 0 < P.S i i
  alpha_ne : ∀ i, P.alpha i ≠ 0
  denom_ne : ∀ i, (∑ j, P.alpha j * P.S i j) ≠ 0
  prob : IsProbabilityMeasure P.nu
  absCont : P.nu ≪ volume
  fullSupport : ∀ a b : ℝ, a < b → 0 < P.nu (Set.Ioo a b)

variable {k : ℕ}

/-- The mean `m₀` of the linear predictor, Lemma 1(i). -/
def m0 (P : Params k) : ℝ := P.alpha0 + ∑ i, P.alpha i * P.mean i

/-- The variance `v₀` of the linear predictor, Lemma 1(i). -/
def v0 (P : Params k) : ℝ := ∑ i, ∑ j, P.alpha i * P.alpha j * P.S i j

/-- The mean `θᵢ` of `αᵢxᵢ`, Lemma 1(iii). -/
def thetaI (P : Params k) (i : Fin k) : ℝ := P.alpha i * P.mean i

/-- The mean `θ₋ᵢ` of the remaining linear predictor, Lemma 1(iii). -/
def thetaMinus (P : Params k) (i : Fin k) : ℝ :=
  P.alpha0 + ∑ j ∈ Finset.univ.erase i, P.alpha j * P.mean j

/-- The variance `b₋ᵢ,₋ᵢ`, Lemma 1(iii). -/
def bMM (P : Params k) (i : Fin k) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, ∑ j' ∈ Finset.univ.erase i,
    P.alpha j * P.alpha j' * P.S j j'

/-- The covariance `b₋ᵢ,ᵢ`, Lemma 1(iii). -/
def bMI (P : Params k) (i : Fin k) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, P.alpha j * P.alpha i * P.S i j

/-- The variance `bᵢ,ᵢ`, Lemma 1(iii). -/
def bII (P : Params k) (i : Fin k) : ℝ := P.alpha i ^ 2 * P.S i i

/-- The conditional mean `mᵢ(t)` of the remaining predictor given `αᵢxᵢ = t`. -/
noncomputable def mi (P : Params k) (i : Fin k) (t : ℝ) : ℝ :=
  thetaMinus P i + bMI P i * (bII P i)⁻¹ * (t - thetaI P i)

/-- The conditional variance `vᵢ`, in the form printed in Proposition 4. -/
noncomputable def vi (P : Params k) (i : Fin k) : ℝ :=
  bMM P i - (∑ j ∈ Finset.univ.erase i, P.alpha j * P.S i j) ^ 2 / P.S i i

/-- The correlation `ρᵢⱼ` of information states. -/
noncomputable def rho (P : Params k) (i j : Fin k) : ℝ :=
  P.S i j / (Real.sqrt (P.S i i) * Real.sqrt (P.S j j))

/-- The coefficient `βᵢ` of expert `i`, Proposition 4. -/
noncomputable def beta (P : Params k) (i : Fin k) : ℝ :=
  P.alpha i * Real.sqrt (P.S i i) /
    ∑ j, P.alpha j * Real.sqrt (P.S j j) * rho P i j

/-- The prior-predictive coefficient `β₀`, Proposition 4. -/
noncomputable def beta0 (P : Params k) : ℝ := 1 - ∑ i, beta P i

/-- The cdf of the sum of independent `z₀` and a normal variable of variance `v`. -/
noncomputable def G (P : Params k) (v : ℝ) (u : ℝ) : ℝ :=
  cdf (P.nu ∗ gaussianReal 0 v.toNNReal) u

/-- Generalized inverse of `G`. It is used only at probabilities strictly between 0 and 1. -/
noncomputable def Ginv (P : Params k) (v p : ℝ) : ℝ :=
  sInf {u : ℝ | p ≤ G P v u}

/-- The right-hand side of the generalized probit ensemble (10). -/
noncomputable def ensemble (P : Params k) (prior : ℝ) (p : Fin k → ℝ) : ℝ :=
  cdf P.nu (beta0 P * Ginv P (v0 P) prior +
    ∑ i, beta P i * Ginv P (vi P i) (p i))

/-- Expert `i`'s report is the conditional probability of the event given `xᵢ`. -/
noncomputable def report {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (x : Ω → EuclideanSpace ℝ (Fin k))
    (Y : Set Ω) (i : Fin k) : Ω → ℝ :=
  μ[Y.indicator (1 : Ω → ℝ) |
    MeasurableSpace.comap (fun ω => x ω i) inferInstance]

/-- The Bayesian aggregate is the conditional probability of the event given all reports. -/
noncomputable def aggregate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (x : Ω → EuclideanSpace ℝ (Fin k))
    (Y : Set Ω) : Ω → ℝ :=
  μ[Y.indicator (1 : Ω → ℝ) |
    MeasurableSpace.comap (fun ω i => report μ x Y i ω) inferInstance]

end BayesEnsemble.GenProbit


