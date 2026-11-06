-- Prove2me | Definitions.Def_SKAnnealing_Sampling_lawMean
-- name    : SKAnnealing_Sampling_lawMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:40.745471+00:00
-- url     : https://prove2.me/theorems/25404eac-d0c1-46d2-8d08-e55fad0645ae
-- title:
--   Expectation, variance, covariance matrix, its operator norm, and total variation for a law on $\{\pm1\}^N$
-- statement:
--   A **law** on the hypercube $\{\pm1\}^N$ is a function $p$ giving each configuration $x$ a weight $p(x)$. For an observable $f:\{\pm1\}^N\to\mathbb R$ we write
--   $$\mathbf E_p[f]=\sum_{x}p(x)f(x),\qquad \mathbf{Var}_p[f]=\mathbf E_p\big[(f-\mathbf E_p f)^2\big],$$
--   and the **covariance matrix** of the spins
--   $$\mathbf{Cov}(p)_{ij}=\mathbf E_p\big[(\sigma_i-\mathbf E_p\sigma_i)(\sigma_j-\mathbf E_p\sigma_j)\big],\qquad i,j\in[N],$$
--   with its Euclidean operator norm $\|\mathbf{Cov}(p)\|_{\mathrm{op}}$. The **total variation distance** between two laws is $d_{\mathrm{TV}}(p,q)=\tfrac12\sum_x|p(x)-q(x)|$.
--
--   These are the statistics of a measure on $\{\pm1\}^N$ used throughout the paper (Lemmas 2.3–2.4, Theorem 1.4, Section 4). They are needed for laws other than the zero-field SK Gibbs measure: tilted and planted measures along the localization path.
--
--   **Formalization Note** A law is a function `Spin N → ℝ`; in every use it is nonnegative and sums to one. The bodies are those of the published `OAI.CriticalSK.mean`, `variance`, `covariance`, `covarianceNorm` with a general $p$ in place of `gibbs W`.
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), §2 (pp. 11–12) and §4 (p. 15)

import Mathlib
import Definitions.Def_CriticalSK

open OAI.CriticalSK

namespace SKAnnealing.Sampling

/-- Expectation `E_p[f] = ∑_x p(x) f(x)` of an observable `f` under a law `p` on `{±1}^N`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), §2 (p. 11) and §4 (p. 15): `⟨·⟩`, `Var`, `Cov` of a measure on `{±1}^N`.

**Formalization Note** A law on the finite cube is a function `p : Spin N → ℝ` (in every use it is a
Gibbs measure or a tilt of one, so it is nonnegative and sums to one). The same body as
`OAI.CriticalSK.mean`, with `p` in place of `gibbs W`, because Lemmas 2.3–2.4 and Section 4 apply these
statistics to laws outside the zero-field Gibbs family. -/
noncomputable def lawMean {N : ℕ} (p : Spin N → ℝ) (f : Spin N → ℝ) : ℝ :=
  ∑ x : Spin N, p x * f x

/-- Variance `Var_p[f] = E_p[(f − E_p f)^2]`. -/
noncomputable def lawVar {N : ℕ} (p : Spin N → ℝ) (f : Spin N → ℝ) : ℝ :=
  lawMean p (fun x => (f x - lawMean p f) ^ 2)

/-- Covariance matrix `Cov(p)_{ij} = E_p[(σ_i − E σ_i)(σ_j − E σ_j)]` of the spins under `p`
(same body as `OAI.CriticalSK.covariance` with `p` in place of `gibbs W`). -/
noncomputable def lawCov {N : ℕ} (p : Spin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => lawMean p (fun x =>
    (spinValue (x i) - lawMean p (fun y => spinValue (y i))) *
    (spinValue (x j) - lawMean p (fun y => spinValue (y j))))

/-- Euclidean operator norm `‖Cov(p)‖_op` (same convention as `OAI.CriticalSK.covarianceNorm`). -/
noncomputable def lawCovNorm {N : ℕ} (p : Spin N → ℝ) : ℝ :=
  ‖(lawCov p).toEuclideanLin.toContinuousLinearMap‖

/-- Total variation distance `d_TV(p, q) = ½ ∑_x |p(x) − q(x)|` between two laws on `{±1}^N`. -/
noncomputable def lawTV {N : ℕ} (p q : Spin N → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x : Spin N, |p x - q x|

end SKAnnealing.Sampling


