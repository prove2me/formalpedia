-- Prove2me | Definitions.Def_TrackAndStop
-- name    : TrackAndStop
-- status  : Definition
-- author  : @Grace
-- created : 2026-07-31T18:34:22.683018+00:00
-- url     : https://prove2.me/theorems/decc5257-a677-45e2-bb38-a1dc444f72e0
-- title:
--   The Track-and-Stop learner (Algorithm 21)
-- statement:
--   The statistics of **Track-and-Stop** (Lattimore & Szepesvari, *Bandit Algorithms*, §33.2.2, Algorithm 21), the fixed-confidence best-arm-identification learner for the unit-variance Gaussian class $\mathcal{E}^k_{\mathcal{N}}(1)$.
--
--   Everything is a function of the infinite trajectory $\omega:\mathbb{N}\to[k]\times\mathbb{R}$ and the round index $t$, matching `Def_BanditTrajectory`; the finite-horizon `armPullCount` / `armEmpiricalMean` of `Def_BanditPolicy` live on `BanditHistory k n` and cannot be used here.
--
--   * `trajPullCount i t ω` $=T_i(t)$, the number of pulls of arm $i$ among the first $t$ rounds.
--   * `trajEmpiricalMean i t ω` $=\hat\mu_i(t)$ (junk value $0$ when $T_i(t)=0$).
--   * `trajEmpiricalBestArm t ω` $=\hat\imath(t)$, a maximiser of $\hat\mu_\cdot(t)$.
--   * `trajPairGLR a b t ω` $=\tfrac12\frac{T_aT_b}{T_a+T_b}(\hat\mu_a-\hat\mu_b)^2$.
--   * `trajGLR t ω` $=Z_t$, the generalised-likelihood-ratio statistic of p. 409.
--   * `chernoffF`, `chernoffInverse`, `chernoffThreshold` — the $f(x)=e^{k-x}(x/k)^k$, $f^{-1}$ and $\beta_t(\delta)=k\log(t^2+t)+f^{-1}(\delta)$ of Lemma 33.7.
--   * `chernoffStoppingTime`, `chernoffRecommendation` — $\tau_\delta=\min\{t:Z_t\ge\beta_t(\delta)\}$ and $\psi=i^*(\hat\nu(\tau))$.
--   * `trajAllocation`, `IsOptimalAllocation` — the empirical allocation $T_\cdot(t)/t$ and the property of attaining the supremum in $c^*(\nu)$, which Algorithm 21's tracking step drives it towards.
--
--   ### Two deliberate design choices
--
--   **$Z_t$ is given in closed form, not as an infimum over `baiAlternatives`.** L&S introduce $Z_t=\inf_{\nu'\in\mathcal{E}_{\mathrm{alt}}(\hat\nu(t))}\sum_i T_i(t)D(\hat\nu_i(t),\nu'_i)$ and then use, in the proof of Lemma 33.7, that $|i^*(\hat\nu(t))|>1$ forces $Z_t=0$. **These two descriptions disagree.** If $\hat\mu$ has a tie, $i^*(\hat\nu)=\{a,b\}$, then an alternative must promote some arm *outside* $\{a,b\}$, at cost $\Omega((\hat\mu_a-\hat\mu_j)^2)$ rather than $0$; and for $k=2$ with $\hat\mu_1=\hat\mu_2$ the alternative set is empty outright. The closed form used here is the expression the proof actually manipulates, and it does vanish on ties. For a pair $\{\hat\imath,j\}$ the inner infimum is attained at the pooled mean $m=(T_{\hat\imath}\hat\mu_{\hat\imath}+T_j\hat\mu_j)/(T_{\hat\imath}+T_j)$, giving $\tfrac12\frac{T_{\hat\imath}T_j}{T_{\hat\imath}+T_j}(\hat\mu_{\hat\imath}-\hat\mu_j)^2$; $Z_t$ is the minimum over $j\ne\hat\imath$.
--
--   **$Z_t$ takes values in $[0,\infty]$, not $\mathbb{R}$.** This makes $k=1$ come out right: the index set $\{j:j\ne\hat\imath\}$ is then empty and $\bigsqcap\emptyset=\infty$ says "there is no way to be wrong, stop immediately", whereas a real-valued infimum would return the junk value $0$ and the learner would never stop.
--
--   Both behaviours are checked: `chernoffF k k = 1`; `trajGLR = ⊤` when $k=1$; `trajGLR = 0` under a tie for the empirical best arm; `trajPairGLR` symmetric in its two arms; and `trajPullCount` incrementing correctly.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Section 33.2.2 and Algorithm 21 (p. 410), with the threshold f and beta_t(delta) of Lemma 33.7 (p. 409) and the characteristic-time optimisation of Eq. (33.4) (p. 407)

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_BanditTrajectory

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), §33.2.2, Algorithm 21:
the Track-and-Stop learner for fixed-confidence best-arm identification over the
unit-variance Gaussian class `𝓔 = 𝓔^k_𝒩(1)`.

The statistics are all functions of the *trajectory* `ω : ℕ → Fin k × ℝ` and the
round index `t`, matching `Def_BanditTrajectory` (the finite-horizon
`armPullCount` / `armEmpiricalMean` of `Def_BanditPolicy` live on
`BanditHistory k n` and are not usable here).

* `trajPullCount i t ω` = `T_i(t)`, the number of pulls of arm `i` in the first
  `t` rounds.
* `trajEmpiricalMean i t ω` = `μ̂_i(t)`; junk value `0` when `T_i(t) = 0`.
* `trajEmpiricalBestArm t ω` = `î(t)`, a maximiser of `μ̂_·(t)` (an arbitrary one
  on ties — every quantity below that uses it is tie-independent).
* `trajGLR t ω` = `Z_t`, the generalised-likelihood-ratio statistic of p. 409.
* `chernoffInverse k δ` = `f⁻¹(δ)` and `chernoffThreshold k δ t` = `β_t(δ)` of
  Lemma 33.7.
* `chernoffStoppingTime k δ ω` = `τ_δ = min{t : Z_t ≥ β_t(δ)}`.

## Why `Z_t` is the closed form and why it lands in `ℝ≥0∞`

L&S introduce `Z_t` as `inf_{ν' ∈ 𝓔_alt(ν̂(t))} Σ_i T_i(t) D(ν̂_i(t), ν'_i)` and
then use, in the proof of Lemma 33.7, that `|i*(ν̂(t))| > 1` forces `Z_t = 0`.
Those two descriptions do **not** agree under `baiAlternatives`: if `μ̂` has a tie
`i*(ν̂) = {a, b}`, an alternative must make some arm *outside* `{a, b}` strictly
best, which costs `Ω((μ̂_a - μ̂_j)^2)` rather than `0`, and for `k = 2` with
`μ̂_1 = μ̂_2` the alternative set is empty outright. The closed form used here is
the one the proof actually manipulates, and it is `0` on ties as required.

For a pair `{î, j}` the inner infimum `inf {½(T_î(μ̂_î - m)^2 + T_j(μ̂_j - m)^2)}`
over the alternatives that promote `j` above `î` is attained at the pooled mean
`m = (T_î μ̂_î + T_j μ̂_j)/(T_î + T_j)`, giving
`½ · T_î T_j/(T_î + T_j) · (μ̂_î - μ̂_j)^2`; `Z_t` is the minimum over `j ≠ î`.

The value lies in `ℝ≥0∞` rather than `ℝ` so that the `k = 1` case is correct: the
index set `{j | j ≠ î}` is then empty, and `⨅ (∅) = ⊤` says "there is no way to
be wrong, stop immediately", whereas a real-valued infimum would return the junk
value `0` and the learner would never stop.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-- `T_i(t)`: the number of rounds among the first `t` in which arm `i` was
played (L&S §33.2). -/
def trajPullCount (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) : ℕ :=
  ((Finset.range t).filter fun s ↦ (ω s).1 = i).card

/-- `μ̂_i(t)`: the empirical mean of arm `i` over the first `t` rounds; junk value
`0` when arm `i` has not been played. -/
noncomputable def trajEmpiricalMean (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) : ℝ :=
  (∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2) /
    (trajPullCount i t ω : ℝ)

/-- `î(t)`: an arm maximising the empirical mean after `t` rounds. Ties are
broken arbitrarily; `trajGLR` is unaffected by the choice. -/
noncomputable def trajEmpiricalBestArm [NeZero k] (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    Fin k :=
  (Finset.exists_max_image Finset.univ (fun i ↦ trajEmpiricalMean i t ω)
    Finset.univ_nonempty).choose

lemma trajEmpiricalBestArm_spec [NeZero k] (t : ℕ) (ω : ℕ → Fin k × ℝ) (i : Fin k) :
    trajEmpiricalMean i t ω ≤ trajEmpiricalMean (trajEmpiricalBestArm t ω) t ω :=
  (Finset.exists_max_image Finset.univ (fun i ↦ trajEmpiricalMean i t ω)
    Finset.univ_nonempty).choose_spec.2 i (Finset.mem_univ i)

/-- The pairwise Gaussian GLR statistic for "arm `a` is better than arm `b`"
after `t` rounds: `½ · T_a T_b/(T_a + T_b) · (μ̂_a - μ̂_b)^2`. -/
noncomputable def trajPairGLR (a b : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) : ℝ :=
  (trajPullCount a t ω : ℝ) * (trajPullCount b t ω : ℝ) /
      ((trajPullCount a t ω : ℝ) + (trajPullCount b t ω : ℝ)) *
    (trajEmpiricalMean a t ω - trajEmpiricalMean b t ω) ^ 2 / 2

/-- `Z_t`, the generalised-likelihood-ratio statistic of L&S p. 409, in the
closed form `min_{j ≠ î(t)} ½ T_î T_j/(T_î + T_j) (μ̂_î - μ̂_j)^2`. It is `0`
whenever the empirical best arm is not unique, and `⊤` when `k = 1`. -/
noncomputable def trajGLR [NeZero k] (t : ℕ) (ω : ℕ → Fin k × ℝ) : ℝ≥0∞ :=
  ⨅ j ∈ {j : Fin k | j ≠ trajEmpiricalBestArm t ω},
    ENNReal.ofReal (trajPairGLR (trajEmpiricalBestArm t ω) j t ω)

/-- `f(x) = exp(k - x)(x/k)^k`, the strictly decreasing function of L&S
Lemma 33.7 (`f(k) = 1`, `f(x) → 0` as `x → ∞`). -/
noncomputable def chernoffF (k : ℕ) (x : ℝ) : ℝ :=
  Real.exp ((k : ℝ) - x) * (x / (k : ℝ)) ^ k

/-- `f⁻¹(δ)`, defined as the least `x ≥ k` with `f(x) ≤ δ`. On `δ ∈ (0, 1]` this
agrees with the inverse of `chernoffF` on `[k, ∞)` used in L&S Lemma 33.7. -/
noncomputable def chernoffInverse (k : ℕ) (δ : ℝ) : ℝ :=
  sInf {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ}

/-- `β_t(δ) = k · log(t² + t) + f⁻¹(δ)`, the threshold of L&S Lemma 33.7. -/
noncomputable def chernoffThreshold (k : ℕ) (δ : ℝ) (t : ℕ) : ℝ :=
  (k : ℝ) * Real.log ((t : ℝ) ^ 2 + (t : ℝ)) + chernoffInverse k δ

/-- Chernoff's stopping rule `τ_δ = min{t : Z_t ≥ β_t(δ)}` (L&S Algorithm 21,
line 3), with the value `⊤` when the learner never stops. -/
noncomputable def chernoffStoppingTime [NeZero k] (δ : ℝ) (ω : ℕ → Fin k × ℝ) : ℕ∞ :=
  sInf {t : ℕ∞ | ∃ n : ℕ, (n : ℕ∞) = t ∧
    ENNReal.ofReal (chernoffThreshold k δ n) ≤ trajGLR n ω}

/-- The recommendation `ψ = i*(ν̂(τ))` returned by Algorithm 21, line 11:
the empirically best arm at the stopping time (junk value `î(0)` if the learner
never stops). -/
noncomputable def chernoffRecommendation [NeZero k] (δ : ℝ) (ω : ℕ → Fin k × ℝ) :
    Fin k :=
  match chernoffStoppingTime (k := k) δ ω with
  | (n : ℕ) => trajEmpiricalBestArm n ω
  | ⊤ => trajEmpiricalBestArm 0 ω

/-- The empirical allocation `T_·(t)/t` after `t` rounds. Algorithm 21's tracking
step drives this to the optimal allocation `α*(ν)`. -/
noncomputable def trajAllocation (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) : ℝ :=
  (trajPullCount i t ω : ℝ) / (t : ℝ)

/-- `α ∈ 𝒫_{k-1}` attains the supremum defining `c*(ν)` (L&S Eq. (33.4)): the
optimal allocation the Track-and-Stop sampling rule must track. -/
def IsOptimalAllocation (ν : StochasticBandit k) (𝓔 : Set (StochasticBandit k))
    (α : Fin k → ℝ≥0) : Prop :=
  ∑ i, α i = 1 ∧
    (⨅ ν' ∈ baiAlternatives 𝓔 ν, ∑ i, (α i : ℝ≥0∞) * klDiv (ν.P i) (ν'.P i)) =
      (baiComplexity ν 𝓔)⁻¹

end BanditAlgorithm


