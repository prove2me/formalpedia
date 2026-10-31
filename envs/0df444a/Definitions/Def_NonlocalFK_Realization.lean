-- Prove2me | Definitions.Def_NonlocalFK_Realization
-- name    : NonlocalFK_Realization
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:35.194033+00:00
-- url     : https://prove2.me/theorems/fce1f7ad-1a18-46c7-b497-fa7363e9cb49
-- title:
--   The process $(v,X)$ with jumps from the boundary, and the payoffs of (1.6), (2.15), (A.16)
-- statement:
--   A **realization** with real start time $t$ and clock start $(u,x)$, that is $v_{t-}=u$, $X_{t-}=x$, consists of a filtered probability space under the usual assumptions, independent $d$-dimensional $\mathcal F$-Brownian motions, stopping times $\theta_0=t\le\theta_1<\theta_2<\cdots$, pre-jump points $\xi_i=(v_{\theta_i-},X_{\theta_i-})\in\partial_pQ$, post-jump points $\zeta_i=(v_{\theta_i},X_{\theta_i})\in Q$, and paths $(v,X)$ such that:
--
--   1. on each cycle $[\theta_i,\theta_{i+1})$ the state stays in $Q$, $v_s=v_{\theta_i}+(s-\theta_i)$, $X$ is continuous and solves $dX_s=b(v_s,X_s)\,ds+\sigma(v_s,X_s)\,dB^{i+1}_s$, and the left limit at $\theta_{i+1}$ is $\xi_{i+1}$;
--   2. if $(u,x)\in Q$ then $\zeta_0=(u,x)$ and $\theta_1>t$; if $(u,x)\in\partial_pQ$ then $\theta_1=t$ and $\xi_1=(u,x)$;
--   3. $\zeta_i$ is $\mathcal F_{\theta_i}$-measurable with conditional law $\tilde\nu_{\xi_i}$ given $\mathcal F_{\theta_i-}$.
--
--   With $Y_{s-}=\prod_{t\le\theta_j<s}\bar\nu(\xi_j)$ the module defines the functional of (1.6),
--
--   $$
--   \int_t^\infty e^{-r(s-t)}Y_{s-}f(v_{s-},X_{s-})\,ds+\sum_{\theta_i\ge t}e^{-r(\theta_i-t)}Y_{\theta_i-}h(v_{\theta_i-},X_{\theta_i-}),
--   $$
--
--   the finite-horizon functional of (2.15) up to $\gamma_N^t=\inf\{s\ge t:NT-s-m_s^t\le0\}$ with $m_s^t=\sum_{t\le\theta_i\le s}(T-v_{\theta_i-}+v_{\theta_i})$, and the truncated functional of (A.16).
--
--   **Formalization Note** The first-hit form of the cycles replaces the infimum defining $\theta_{i+1}$. $\sup_i\theta_i=\infty$ is not assumed; it is Lemma 2.3. Independence of the repeated jumps is carried by the conditional law together with the Brownian motions being $\mathcal F$-Brownian motions. Under $ds$ the state is evaluated at $s$ rather than $s-$, a change on a null set of times. The filtered probability space is part of the data, so statements about the process quantify over realizations.
-- source:
--   Dai, Kou, Yang, A Stochastic Representation for Nonlocal Parabolic PDEs with Applications, SSRN 3541591, eq. (1.6)-(1.7), p.2; §2.2, eq. (2.8)-(2.9), p.8; eq. (2.14)-(2.15), pp.9-10; eq. (A.16), p.27

import Definitions.Def_NonlocalFK_Model
import Definitions.Def_NonlocalFK_IsBrownianFamily

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace NonlocalFK

/-- A realization of the process `(v, X)` of §1.1 and §2.2 (Dai, Kou, Yang, SSRN 3541591, pp.2, 8),
with real start time `t` and clock start `(u, x)`, i.e. `v_{t−} = u`, `X_{t−} = x`.

The data are a filtered probability space under the usual assumptions, independent `d`-dimensional
`𝓕`-Brownian motions `B i` (the paper's `B^{i+1}`), stopping times `θ₀ = t ≤ θ₁ < θ₂ < ⋯`, pre-jump
points `ξ i` (`= (v_{θᵢ−}, X_{θᵢ−})`) and post-jump points `ζ i` (`= (v_{θᵢ}, X_{θᵢ})`).

* On each nonempty cycle `[θᵢ, θ_{i+1})`, `(v, X)` starts at `ζ i`, stays in `Q`, the clock runs at
  unit speed, `X` is continuous and solves (1.7) with `B i`, and the left limit at `θ_{i+1}` is
  `ξ (i+1) ∈ ∂ₚQ`.
* If `(u, x) ∈ Q` then `ζ 0 = (u, x)` and `θ₁ > t`. If `(u, x) ∈ ∂ₚQ` then `θ₁ = t` and
  `ξ 1 = (u, x)`, "by viewing `t` as a passage time" (p.10); the cycle `0` is then empty.
* At `θᵢ`, `i ≥ 1`, `ζ i` is `𝓕_{θᵢ}`-measurable with conditional law `ν̃_{ξ i}` given `𝓕_{θᵢ−}`.

**Formalization Note.** The first-hit form replaces
`θ_{i+1} = inf{s > θᵢ : X_{s−} ∈ ∂𝒪 or v_{s−} = T}`: `(v, X)` is in `Q` before `θ_{i+1}` and its
left limit there is in `∂ₚQ`, and `Q`, `∂ₚQ` are disjoint. `sup θᵢ = ∞` is **not** assumed; `v`, `X`
are unconstrained after `sup θᵢ`. "This same jump mechanism is repeated independently" (p.8) is
carried by the conditional law together with `B i` being an `𝓕`-Brownian motion. Path properties
are almost sure. -/
structure Realization {d : ℕ} (m : Model d) (t u : ℝ) (x : E d)
    (Ω : Type*) [mΩ : MeasurableSpace Ω] where
  P : Measure Ω
  F : Filtration ℝ mΩ
  B : ℕ → Fin d → ℝ → Ω → ℝ
  θ : ℕ → Ω → ℝ
  ξ : ℕ → Ω → ℝ × E d
  ζ : ℕ → Ω → ℝ × E d
  v : ℝ → Ω → ℝ
  X : ℝ → Ω → E d
  brownian : IsBrownianFamily P F (fun q : ℕ × Fin d => B q.1 q.2)
  stopping : ∀ i, IsStoppingTime F (fun ω => (θ i ω : WithTop ℝ))
  theta_zero : ∀ᵐ ω ∂P, θ 0 ω = t
  theta_mono : ∀ᵐ ω ∂P, θ 0 ω ≤ θ 1 ω ∧ ∀ i, 1 ≤ i → θ i ω < θ (i + 1) ω
  adapted : ∀ (i : ℕ) (s : ℝ) (A : Set (ℝ × E d)), MeasurableSet A →
    MeasurableSet[F s] {ω | θ i ω ≤ s ∧ s < θ (i + 1) ω ∧ (v s ω, X s ω) ∈ A}
  start_Q : (u, x) ∈ m.Q → ∀ᵐ ω ∂P, ζ 0 ω = (u, x) ∧ t < θ 1 ω
  start_bdry : (u, x) ∈ m.bdry → ∀ᵐ ω ∂P, θ 1 ω = t ∧ ξ 1 ω = (u, x)
  xi_mem : ∀ᵐ ω ∂P, ∀ i, 1 ≤ i → ξ i ω ∈ m.bdry
  cycle : ∀ᵐ ω ∂P, ∀ i, θ i ω < θ (i + 1) ω →
    (v (θ i ω) ω, X (θ i ω) ω) = ζ i ω ∧
    (∀ s ∈ Ico (θ i ω) (θ (i + 1) ω),
      (v s ω, X s ω) ∈ m.Q ∧ v s ω = v (θ i ω) ω + (s - θ i ω)) ∧
    ContinuousOn (fun s => X s ω) (Ico (θ i ω) (θ (i + 1) ω)) ∧
    Tendsto (fun s => (v s ω, X s ω)) (𝓝[<] θ (i + 1) ω) (𝓝 (ξ (i + 1) ω))
  sde : ∀ i, ∃ J : Fin d → Fin d → ℝ → Ω → ℝ,
    (∀ k j (n : ℕ), EntropyMFG.Enhanced.HasItoIntegral P F (B i j) 0 n
      (fun s ω => (Ioc (θ i ω) (θ (i + 1) ω)).indicator
        (fun s => m.σ (v s ω, X s ω) k j) s) (J k j)) ∧
    ∀ᵐ ω ∂P, ∀ s ∈ Ico (θ i ω) (θ (i + 1) ω), ∀ k,
      X s ω k = X (θ i ω) ω k + (∫ r in θ i ω..s, m.b (v r ω, X r ω) k) + ∑ j, J k j s ω
  measurable_ζ : ∀ i, 1 ≤ i → Measurable[(stopping i).measurableSpace] (ζ i)
  jump_law : ∀ i, 1 ≤ i → ∀ A : Set (ℝ × E d), MeasurableSet A →
    ∀ G : Set Ω, MeasurableSet[strictPast F (θ i)] G →
      P (G ∩ ζ i ⁻¹' A) = ∫⁻ ω in G, m.jumpLaw (ξ i ω) A ∂P

namespace Realization

variable {d : ℕ} {m : Model d} {t u : ℝ} {x : E d} {Ω : Type*} [MeasurableSpace Ω]
  (R : Realization m t u x Ω)

/-- The mass `Y_{s−} = ∏_{t ≤ θⱼ < s} ν̄(v_{θⱼ−}, X_{θⱼ−})`, `j ≥ 1`, with `Y_{t−} = 1`
(SSRN 3541591, (1.6), p.2; (2.9), p.8).

**Formalization Note.** `∏ᶠ` is the finite product over the indices in the condition. Under
Assumption 2.2 only finitely many `θⱼ` lie below `s` almost surely (Lemma 2.3). -/
def massBefore (s : ℝ) (ω : Ω) : ℝ :=
  ∏ᶠ (j : ℕ) (_ : 1 ≤ j ∧ t ≤ R.θ j ω ∧ R.θ j ω < s), m.mass (R.ξ j ω)

/-- The mass `Y_s = ∏_{t ≤ θⱼ ≤ s} ν̄(v_{θⱼ−}, X_{θⱼ−})`, `j ≥ 1`, (2.9), p.8. -/
def massUpTo (s : ℝ) (ω : Ω) : ℝ :=
  ∏ᶠ (j : ℕ) (_ : 1 ≤ j ∧ t ≤ R.θ j ω ∧ R.θ j ω ≤ s), m.mass (R.ξ j ω)

/-- The running payoff `e^{−r(s−t)} Y_{s−} f(v_{s−}, X_{s−})` of (1.6), p.2.

**Formalization Note.** The state is evaluated at `s` rather than at `s−`. The two differ at the
jump times only, a Lebesgue null set of `s`, and this term only enters through `ds` integrals. -/
def rateTerm (s : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-m.r * (s - t)) * R.massBefore s ω * m.f (R.v s ω, R.X s ω)

/-- The lump-sum payoff `e^{−r(θᵢ−t)} Y_{θᵢ−} h(v_{θᵢ−}, X_{θᵢ−})` of (1.6), p.2. -/
def lumpTerm (i : ℕ) (ω : Ω) : ℝ :=
  Real.exp (-m.r * (R.θ i ω - t)) * R.massBefore (R.θ i ω) ω * m.h (R.ξ i ω)

/-- The functional inside the expectation of (1.6), p.2:
`∫_t^∞ e^{−r(s−t)} Y_{s−} f ds + ∑_{i≥1} e^{−r(θᵢ−t)} Y_{θᵢ−} h`.

**Formalization Note.** Every `θᵢ`, `i ≥ 1`, is `≥ t`, so the constraint `θᵢ ≥ t` of the printed sum
is vacuous. -/
def payoff (ω : Ω) : ℝ :=
  (∫ s in Ioi t, R.rateTerm s ω) + ∑' i : ℕ, R.lumpTerm (i + 1) ω

/-- The payoff of (1.6) is well defined: almost surely the time integral exists and the series
converges absolutely, and the payoff is integrable. -/
def PayoffIntegrable : Prop :=
  (∀ᵐ ω ∂(R.P), IntegrableOn (fun s => R.rateTerm s ω) (Ioi t) ∧
    Summable (fun i : ℕ => R.lumpTerm (i + 1) ω)) ∧
  Integrable R.payoff R.P

/-- The clock `m_s^t = ∑_{t ≤ θᵢ ≤ s} (T − v_{θᵢ−} + v_{θᵢ})`, `i ≥ 1`, (SSRN 3541591, p.10). -/
def clockSum (s : ℝ) (ω : Ω) : ℝ :=
  ∑ᶠ (i : ℕ) (_ : 1 ≤ i ∧ t ≤ R.θ i ω ∧ R.θ i ω ≤ s), (m.T - (R.ξ i ω).1 + (R.ζ i ω).1)

/-- `γ_N^t = inf{s ≥ t : NT − s − m_s^t ≤ 0}`, p.10.

**Formalization Note.** The set is bounded below by `t`, and almost surely nonempty, since it
contains `θ_N` when `t ∈ [0, T)`. -/
def gamma (N : ℕ) (ω : Ω) : ℝ := sInf {s | t ≤ s ∧ (N : ℝ) * m.T - s - R.clockSum s ω ≤ 0}

/-- The functional inside the expectation of the finite-horizon problem (2.15), p.10, with
`m = 0`, `y = 1`:
`∫_t^{γ_N^t} e^{−r(s−t)} Y_{s−} f ds + ∑_{t ≤ θᵢ ≤ γ_N^t} e^{−r(θᵢ−t)} Y_{θᵢ−} h`. -/
def finitePayoff (N : ℕ) (ω : Ω) : ℝ :=
  (∫ s in t..R.gamma N ω, R.rateTerm s ω) +
    ∑ᶠ (i : ℕ) (_ : 1 ≤ i ∧ t ≤ R.θ i ω ∧ R.θ i ω ≤ R.gamma N ω), R.lumpTerm i ω

/-- The functional inside the expectation of (A.16), p.27:
`∑_{i=1}^N e^{−r(θᵢ−t)} Y_{θᵢ−} h + ∫_t^{θ_N} e^{−r(s−t)} Y_{s−} f ds
  + e^{−r(θ_N−t)} Y_{θ_N} W(v_{θ_N}, X_{θ_N})`. -/
def truncatedPayoff (W : ℝ × E d → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.Icc 1 N, R.lumpTerm i ω) + (∫ s in t..R.θ N ω, R.rateTerm s ω) +
    Real.exp (-m.r * (R.θ N ω - t)) * R.massUpTo (R.θ N ω) ω * W (R.ζ N ω)

end Realization

end NonlocalFK


