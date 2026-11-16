-- Prove2me | Definitions.Def_TightQLB_Supplement_Heavy
-- name    : TightQLB_Supplement_Heavy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:22:52.87663+00:00
-- url     : https://prove2.me/theorems/19417adf-dd80-4456-bb8e-f10a0a4a6d00
-- title:
--   Heavy outputs: the thresholds $\theta_N$, $\hat\theta_N$, the heavy probability $B^{\mathrm{hog}}_\tau$, $\beta^{\mathrm{hog}}_N$, $h_{\mathrm{hon}}$, $h_\star$
-- statement:
--   For the Haar ensemble with $N=2^n\ge2$ and $p_z=|\langle z|\phi\rangle|^2$, the fixed threshold and the heavy probability of an algorithm $\mathcal A$ with output $Z$ are
--
--   $$
--   \theta_N=1-2^{-1/(N-1)},\qquad B^{\mathrm{hog}}_\tau(\mathcal A)=\Pr[p_Z>\tau],
--   $$
--
--   the probability averaging over the oracle and the algorithm's randomness. The second threshold is the empirical median $\hat\theta_N=(p_{(N/2)}+p_{(N/2+1)})/2$ of the ideal probabilities sorted increasingly. Further
--
--   $$
--   \beta^{\mathrm{hog}}_N=\frac{1+(N-1)\theta_N}{2},\qquad h_{\mathrm{hon}}=\frac{1+\ln2}{2},\qquad h_\star=\frac{2+2\ln2+(\ln2)^2}{4}.
--   $$
--
--   $B^{\mathrm{hog}}_\tau$ is defined for experiments with the canonical oracle (with or without supplied copies), for algorithms with unitary access, and for $\mathsf{Sq}_m$. These state Theorem 6.12, the tight query bound for producing a heavy output.
--
--   **Formalization Note** A threshold is a function of the ideal distribution $p$ (constant for $\theta_N$). The order statistic $p_{(j)}$ is $\inf\{t:\#\{z:p_z\le t\}\ge j\}$, the $j$-th smallest value counted with multiplicity.
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), §6.7, Eqs. (54)–(56), pp. 55–56 (PDF pp. 58–59)

import Mathlib
import Definitions.Def_TightQLB_Supplement_Squaring
open QAlgorithms MeasureTheory

set_option autoImplicit false

namespace TightQLB.Supplement

/-!
# Heavy outputs

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…), §6.7, Eqs. (54)–(56),
pp.55–56 (PDF pp.58–59).

"Let `N = 2ⁿ ≥ 2` and `p_z = |⟨z|ϕ⟩|²`, where `|ϕ⟩` is Haar-random, or `|ϕ⟩ = U|0ⁿ⟩` for Haar-random
`U`. … Define `θ_N = 1 − 2^{−1/(N−1)}`, `B^hog_τ(A) = Pr[p_Z > τ]`. (54) The probability in (54), in
which `Z` is the output of `A`, averages over the oracle and the algorithm's randomness." "The
second threshold is the empirical median `θ̂_N = (p_(N/2) + p_(N/2+1))/2`, where the ideal
probabilities are sorted in increasing order." `β^hog_N = (1 + (N − 1)θ_N)/2`,
`h_hon := (1 + ln 2)/2` (55), `h⋆ = (2 + 2 ln 2 + (ln 2)²)/4` (56).

**Formalization Note.**
* A threshold is a function `τ` of the ideal distribution `p`: the constant `θ_N` (`thetaFix`) or
  the empirical median `θ̂_N(p)` (`thetaHat`). `p_(j)`, the `j`-th smallest of the `N` values
  `p_z` counted with multiplicity, is `orderStat p j = inf{t : #{z : p_z ≤ t} ≥ j}`.
* `B^hog_τ` is defined for the three kinds of algorithm of the chunk: an experiment with `s`
  supplied copies and the canonical oracle, the published experiment with the canonical oracle
  and no copies, an algorithm with unitary access, and `Sq_m` in an ensemble.
-/

variable {n : ℕ}

/-- Eq. (54): the fixed threshold `θ_N = 1 − 2^{−1/(N−1)}`. -/
noncomputable def thetaN (n : ℕ) : ℝ :=
  1 - (2 : ℝ) ^ (-(1 / ((2 : ℝ) ^ n - 1)))

/-- The constant threshold `θ_N`, as a function of `p`. -/
noncomputable def thetaFix (n : ℕ) : (Qubits n → ℝ) → ℝ := fun _ => thetaN n

/-- `p_(j)`: the `j`-th smallest of the values `p_z`, counted with multiplicity. -/
noncomputable def orderStat (p : Qubits n → ℝ) (j : ℕ) : ℝ :=
  sInf {t : ℝ | j ≤ (Finset.univ.filter (fun z => p z ≤ t)).card}

/-- §6.7, p.56 (PDF p.59): the empirical median `θ̂_N = (p_(N/2) + p_(N/2+1))/2`. -/
noncomputable def thetaHat (n : ℕ) : (Qubits n → ℝ) → ℝ := fun p =>
  (orderStat p (2 ^ n / 2) + orderStat p (2 ^ n / 2 + 1)) / 2

/-- Eq. (55): `β^hog_N = (1 + (N − 1)θ_N)/2`. -/
noncomputable def betaHog (n : ℕ) : ℝ :=
  (1 + ((2 : ℝ) ^ n - 1) * thetaN n) / 2

/-- Eq. (55): `h_hon = (1 + ln 2)/2`. -/
noncomputable def hHon : ℝ := (1 + Real.log 2) / 2

/-- Eq. (56): `h⋆ = (2 + 2 ln 2 + (ln 2)²)/4`. -/
noncomputable def hStar : ℝ := (2 + 2 * Real.log 2 + Real.log 2 ^ 2) / 4

/-- `1[p_z > τ(p)]`. -/
noncomputable def heavyInd (τ : (Qubits n → ℝ) → ℝ) (p : Qubits n → ℝ) (z : Qubits n) : ℝ :=
  if τ p < p z then 1 else 0

/-- Eq. (54) for an experiment with `s` supplied copies and the canonical oracle. -/
noncomputable def CopyExperiment.heavy {q s : ℕ} {W E : Type} [Fintype W] [DecidableEq W]
    [Fintype E] [DecidableEq E] (A : CopyExperiment n q s W E) (τ : (Qubits n → ℝ) → ℝ) : ℝ :=
  ∫ ϕ, ∑ z, A.outProb ϕ z * heavyInd τ (pOf ϕ) z ∂(haar n)

/-- Eq. (54) for the published experiment with the canonical oracle (no supplied copies). -/
noncomputable def haarHeavy {q : ℕ} {W E : Type} [Fintype W] [DecidableEq W] [Fintype E]
    [DecidableEq E] (A : Experiment n q (Option (Qubits n)) W E) (τ : (Qubits n → ℝ) → ℝ) : ℝ :=
  ∫ ϕ, ∑ z, A.outProb (canonOracle ϕ) z * heavyInd τ (pOf ϕ) z ∂(haar n)

/-- Eq. (54) for an algorithm with Haar-random unitary access. -/
noncomputable def UnitaryExperiment.heavy {q : ℕ} {W E : Type} [Fintype W] [DecidableEq W]
    [Fintype E] [DecidableEq E] (A : UnitaryExperiment n q W E)
    (μ : Measure (Qubits n → Qubits n → ℂ)) (τ : (Qubits n → ℝ) → ℝ) : ℝ :=
  ∫ U, ∑ z, A.outProb U z * heavyInd τ (pOf (unitaryState U)) z ∂μ

/-- Eq. (54) for `Sq_m` in the ensemble `ν`: its heavy probability. -/
noncomputable def sqHeavy (ν : Measure (EuclideanSpace ℂ (Qubits n))) (m ℓ : ℕ)
    (τ : (Qubits n → ℝ) → ℝ) : ℝ :=
  ∫ ψ, ∑ z, sqOut m ℓ ψ z * heavyInd τ (pOf ψ) z ∂ν

end TightQLB.Supplement


