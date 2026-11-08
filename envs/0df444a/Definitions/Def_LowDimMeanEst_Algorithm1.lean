-- Prove2me | Definitions.Def_LowDimMeanEst_Algorithm1
-- name    : LowDimMeanEst_Algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:50:20.718221+00:00
-- url     : https://prove2.me/theorems/dfb7e048-c85c-421b-a4bd-cab17b5d1e6e
-- title:
--   Algorithm 1 (trimming-based mean estimator) as a relation between samples and outputs $\hat\mu$
-- statement:
--   **Algorithm 1** receives $n=m+N$ samples $x_1,\dots,x_n\in\mathbb R^d$ and a confidence parameter $\delta$, together with an initial estimator $\kappa(\cdot)$ that maps $m$ points to a point of $\mathbb R^d$:
--
--   1. compute the initial estimate $\kappa=\kappa(x_1,\dots,x_m)$ from the first $m$ samples;
--   2. recentre the remaining $N=n'$ samples, $x'_i=x_{m+i}-\kappa$, and run Algorithm 2 (with correction C1) on $x'_1,\dots,x'_N$ and $\delta$ to obtain weights $w$;
--   3. return
--   $$\hat\mu=\kappa+\frac1N\sum_{i=1}^N(1-w_i)\,x'_i .$$
--
--   The paper takes $m=\sqrt{n\log(1/\delta)}$ and the estimator of Fact 49 at confidence $\delta/2$; Theorem 6 fixes these choices. Here $\hat\mu$ is **an output of Algorithm 1** when some output $w$ of Algorithm 2 produces it.
--
--   **Formalization Note** Samples are a vector indexed by `Fin (m + N)`: the first $m$ coordinates feed $\kappa$, the last $N$ feed Algorithm 2, as in the proof of Theorem 6 (p.14). The initial estimator is a parameter.
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Algorithm 1, p.2; proof of Theorem 6, p.14

import Mathlib
import Definitions.Def_LowDimMeanEst_Algorithm2

open MeasureTheory

namespace LowDimMeanEst

/-!
# Algorithm 1 (trimming-based low-dimensional mean estimator), as a relation

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…), Algorithm 1, p.2:

"Input: n i.i.d. samples {xᵢ} ∈ ℝᵈ from the unknown distribution D, confidence parameter δ.
1. Compute an initial estimate κ using Fact 49 on √(n log 1/δ) many samples with confidence
   parameter δ/2.
2. For the remaining n′ = n − √(n log 1/δ) samples, use Algorithm 2 to compute weights
   {wᵢ}_{i∈[1..n′]} for samples x′ᵢ = xᵢ − κ.
3. Return µ̂ = κ + (1/n′) Σ_i^{n′} (1 − wᵢ)(xᵢ − κ)."

**Formalization Note.**
* The `n = m + N` samples are `x : Fin (m + N) → E d`; the first `m` (`Fin.castAdd`) feed the initial
  estimator `kap : (Fin m → E d) → E d`, and the remaining `N = n′` (`Fin.natAdd`) are recentred by
  `κ` and passed to Algorithm 2, as in the proof of Theorem 6 (p.14). The initial estimator is a
  parameter; in Theorem 6 it is an estimator with the guarantee of Fact 49 at confidence `δ/2`, and
  `m` is any natural number within `1` of `√(n log(1/δ))`.
* Algorithm 2 is the relation `IsTrimOutput` (correction C1), so `IsAlg1Output` holds for every
  output `µ̂` the algorithm can return.
-/

/-- The first `m` samples, used for the initial estimate. -/
def firstPart {d m N : ℕ} (x : Fin (m + N) → E d) : Fin m → E d := fun j => x (Fin.castAdd N j)

/-- The remaining `N` samples recentred by the initial estimate: `x′ᵢ = x_{m+i} − κ`. -/
noncomputable def recentred {d m N : ℕ} (kap : (Fin m → E d) → E d) (x : Fin (m + N) → E d) :
    Fin N → E d :=
  fun i => x (Fin.natAdd m i) - kap (firstPart x)

/-- `µ̂` is an output of Algorithm 1 on the samples `x` with confidence `δ`, when the initial
estimate is computed by `kap`: with `κ = kap(x₁, …, x_m)` and `x′ᵢ = x_{m+i} − κ`, there are weights
`w` output by Algorithm 2 on `x′` with parameter `δ` such that `µ̂ = κ + (1/N) Σᵢ (1 − wᵢ) x′ᵢ`. -/
def IsAlg1Output {d m N : ℕ} (kap : (Fin m → E d) → E d) (δ : ℝ) (x : Fin (m + N) → E d)
    (muHat : E d) : Prop :=
  ∃ w : Fin N → ℝ, IsTrimOutput (recentred kap x) δ w ∧
    muHat = kap (firstPart x) + (1 / (N : ℝ)) • ∑ i, (1 - w i) • recentred kap x i

end LowDimMeanEst


