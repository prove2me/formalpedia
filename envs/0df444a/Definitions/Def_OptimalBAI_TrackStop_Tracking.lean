-- Prove2me | Definitions.Def_OptimalBAI_TrackStop_Tracking
-- name    : OptimalBAI_TrackStop_Tracking
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:12:33.552331+00:00
-- url     : https://prove2.me/theorems/bbaa4829-c1e5-4e4e-a3ba-828a80b1f71e
-- title:
--   C-Tracking and D-Tracking sampling rules
-- statement:
--   After $t$ rounds of a $K$-armed bandit, $N_a(t)$ is the number of draws of arm $a$ and $\hat{\boldsymbol\mu}(t)=(\hat\mu_1(t),\dots,\hat\mu_K(t))$ the vector of empirical means. The two sampling rules of the paper aim at the optimal proportions $w^*(\hat{\boldsymbol\mu}(t))$, read through a **target map** $w^*:\mathbb R^K\to\mathbb R^K$.
--
--   1. **C-Tracking.** For $\epsilon\in(0,1/K]$ let $\Sigma^\epsilon_K=\{(w_1,\dots,w_K)\in[\epsilon,1]^K:\ w_1+\dots+w_K=1\}$, and let $w^\epsilon(\boldsymbol\mu)$ be an $L^\infty$ projection of $w^*(\boldsymbol\mu)$ onto $\Sigma^\epsilon_K$ (a point of $\Sigma^\epsilon_K$ at minimal sup-distance). With $\epsilon_s=(K^2+s)^{-1/2}/2$, the next arm is chosen as
--   $$A_{t+1}\in\operatorname*{argmax}_{1\le a\le K}\ \sum_{s=0}^{t}w^{\epsilon_s}_a(\hat{\boldsymbol\mu}(s))-N_a(t).$$
--   2. **D-Tracking.** With $U_t=\{a:\ N_a(t)<\sqrt t-K/2\}$,
--   $$A_{t+1}\in\begin{cases}\operatorname*{argmin}_{a\in U_t}N_a(t)&\text{if }U_t\ne\emptyset\quad\text{(forced exploration)},\\ \operatorname*{argmax}_{1\le a\le K}\ t\,w^*_a(\hat{\boldsymbol\mu}(t))-N_a(t)&\text{otherwise}\quad\text{(direct tracking)}.\end{cases}$$
--
--   A policy is a run of C-Tracking (resp. D-Tracking) when, after every history, its next arm is drawn among the arms the rule allows; any tie-breaking, including randomized, is permitted, and for C-Tracking any choice of the projections. The pathwise versions say that a single trajectory makes, at every round, a choice the rule allows.
--
--   These rules are the sampling half of the Track-and-Stop strategy.
--
--   **Formalization Note** A history of $t$ rounds gives $N_a(t)$ and $\hat\mu_a(t)$ through the platform's pull counts and empirical means; an arm never drawn has empirical mean $0$. The paper's $w^*$ is undefined when $\hat{\boldsymbol\mu}(t)\notin\mathcal S$, so the rules take an arbitrary target map, and the theorems quantify over every target map with values in $\Sigma_K$ that returns optimal proportions on $\mathcal S$. On a trajectory, coordinate $t$ is round $t+1$, so the arm of coordinate $t$ is $A_{t+1}$ and is chosen from the first $t$ coordinates.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 7, §3.1 (C-Tracking, D-Tracking)

import Mathlib
import Definitions.Def_TrackAndStop
import Definitions.Def_OptimalBAI_TrackStop_OptimalProportions

/-!
Garivier, Kaufmann, *Optimal Best Arm Identification with Fixed Confidence*, arXiv:1602.04589v2,
§3.1, p. 7: the C-Tracking and D-Tracking sampling rules.

Conventions. A history `h : BanditHistory K t` holds the first `t` rounds; `armPullCount a h` is
`N_a(t)` and `armEmpiricalMean a h` is `μ̂_a(t)` (junk value `0` for an arm never pulled). The
policy's kernel `π.select t h` is the law of `A_{t+1}`. On a trajectory `ω : ℕ → Fin K × ℝ`,
coordinate `t` is round `t + 1`, so `(ω t).1` is `A_{t+1}`, chosen from the prefix of length `t`.

Both rules evaluate the optimal proportions `w*(μ̂(s))` at the empirical means. The paper leaves
`w*` undefined off `𝒮` (an unpulled arm, tied empirical means, a mean outside `ḃ(Θ)`), so every
predicate below takes an arbitrary *target map* `wt : ℝ^K → ℝ^K`; the theorems quantify over every
`wt` with values in `Σ_K` that agrees with `w*` on `𝒮`. Ties in every `argmax`/`argmin` may be
broken arbitrarily, including at random: a policy follows a rule when its kernel gives the arms the
rule allows full mass.
-/

open BanditAlgorithm

namespace OptimalBAI.TrackStop

variable {K : ℕ}

/-- The vector of empirical means `μ̂(s) = (μ̂_1(s), …, μ̂_K(s))` computed from the first
`min s t` rounds of a history of `t` rounds (for `s ≤ t`, the first `s` rounds). -/
noncomputable def histMeanAt {t : ℕ} (h : BanditHistory K t) (s : ℕ) : Fin K → ℝ :=
  fun a => armEmpiricalMean a (fun i : Fin (min s t) => h (Fin.castLE (Nat.min_le_right s t) i))

/-- The vector of empirical means `μ̂(s)` after the first `s` rounds of a trajectory. -/
noncomputable def trajMeanVec (s : ℕ) (ω : ℕ → Fin K × ℝ) : Fin K → ℝ :=
  fun a => trajEmpiricalMean a s ω

/-- `Σ^ε_K = {(w_1, …, w_K) ∈ [ε, 1]^K : w_1 + ⋯ + w_K = 1}` (p. 7). -/
def simplexEps (K : ℕ) (ε : ℝ) : Set (Fin K → ℝ) :=
  {w | (∀ a, ε ≤ w a ∧ w a ≤ 1) ∧ ∑ a, w a = 1}

/-- `wp ε μ'` is an `L^∞` projection of `wt μ'` onto `Σ^ε_K`, for every `ε ∈ (0, 1/K]` and every
`μ'`: it lies in `Σ^ε_K` and no point of `Σ^ε_K` is closer to `wt μ'` in the sup norm
(the norm of `Fin K → ℝ`). This is the paper's `w^ε(μ)` (p. 7); projections need not be unique,
and any choice is allowed. -/
def IsLinftyProjection (K : ℕ) (wt : (Fin K → ℝ) → (Fin K → ℝ))
    (wp : ℝ → (Fin K → ℝ) → (Fin K → ℝ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (K : ℝ) → ∀ μ' : Fin K → ℝ,
    wp ε μ' ∈ simplexEps K ε ∧ ∀ v ∈ simplexEps K ε, ‖wp ε μ' - wt μ'‖ ≤ ‖v - wt μ'‖

/-- The C-Tracking exploration levels `ε_s = (K² + s)^{-1/2} / 2` (p. 7). -/
noncomputable def cEps (K : ℕ) (s : ℕ) : ℝ :=
  1 / (2 * Real.sqrt ((K : ℝ) ^ 2 + (s : ℝ)))

/-- The C-Tracking target `∑_{s=0}^{t} w^{ε_s}_a(μ̂(s))` after a history of `t` rounds. -/
noncomputable def cTarget (wp : ℝ → (Fin K → ℝ) → (Fin K → ℝ)) {t : ℕ} (h : BanditHistory K t)
    (a : Fin K) : ℝ :=
  ∑ s ∈ Finset.range (t + 1), wp (cEps K s) (histMeanAt h s) a

/-- The arms C-Tracking allows as `A_{t+1}` after a history `h` of `t` rounds (p. 7):
`argmax_{1 ≤ a ≤ K} ∑_{s=0}^{t} w^{ε_s}_a(μ̂(s)) - N_a(t)`. -/
noncomputable def allowedC (wp : ℝ → (Fin K → ℝ) → (Fin K → ℝ)) {t : ℕ} (h : BanditHistory K t) :
    Set (Fin K) :=
  {a | ∀ b, cTarget wp h b - (armPullCount b h : ℝ) ≤ cTarget wp h a - (armPullCount a h : ℝ)}

/-- The forced-exploration set `U_t = {a : N_a(t) < √t - K/2}` (p. 7). -/
noncomputable def forcedSet {t : ℕ} (h : BanditHistory K t) : Set (Fin K) :=
  {a | (armPullCount a h : ℝ) < Real.sqrt (t : ℝ) - (K : ℝ) / 2}

/-- The arms D-Tracking allows as `A_{t+1}` after a history `h` of `t` rounds (p. 7):
`argmin_{a ∈ U_t} N_a(t)` if `U_t ≠ ∅` (forced exploration), and otherwise
`argmax_{1 ≤ a ≤ K} t w*_a(μ̂(t)) - N_a(t)` (direct tracking), with `w*` read through the
target map `wt`. -/
noncomputable def allowedD (wt : (Fin K → ℝ) → (Fin K → ℝ)) {t : ℕ} (h : BanditHistory K t) :
    Set (Fin K) :=
  {a | ((forcedSet h).Nonempty ∧ a ∈ forcedSet h ∧
          ∀ b ∈ forcedSet h, armPullCount a h ≤ armPullCount b h) ∨
       (forcedSet h = ∅ ∧
          ∀ b, (t : ℝ) * wt (histMeanAt h t) b - (armPullCount b h : ℝ) ≤
            (t : ℝ) * wt (histMeanAt h t) a - (armPullCount a h : ℝ))}

/-- The policy `π` is a run of C-Tracking with target map `wt`: for some choice `wp` of `L^∞`
projections onto `Σ^ε_K`, at every round and after every history the next arm is drawn among the
arms `allowedC` permits (any tie-breaking, possibly randomized). -/
def IsCTrackingPolicy (wt : (Fin K → ℝ) → (Fin K → ℝ)) (π : BanditPolicy K) : Prop :=
  ∃ wp : ℝ → (Fin K → ℝ) → (Fin K → ℝ), IsLinftyProjection K wt wp ∧
    ∀ (t : ℕ) (h : BanditHistory K t), π.select t h (allowedC wp h)ᶜ = 0

/-- The policy `π` is a run of D-Tracking with target map `wt`: at every round and after every
history the next arm is drawn among the arms `allowedD` permits (any tie-breaking). -/
def IsDTrackingPolicy (wt : (Fin K → ℝ) → (Fin K → ℝ)) (π : BanditPolicy K) : Prop :=
  ∀ (t : ℕ) (h : BanditHistory K t), π.select t h (allowedD wt h)ᶜ = 0

/-- The trajectory `ω` follows C-Tracking with target map `wt`: for some choice `wp` of `L^∞`
projections, every arm `A_{t+1} = (ω t).1` is one C-Tracking allows after the first `t` rounds. -/
def FollowsCTracking (wt : (Fin K → ℝ) → (Fin K → ℝ)) (ω : ℕ → Fin K × ℝ) : Prop :=
  ∃ wp : ℝ → (Fin K → ℝ) → (Fin K → ℝ), IsLinftyProjection K wt wp ∧
    ∀ t : ℕ, (ω t).1 ∈ allowedC wp (banditTrajPrefix K t ω)

/-- The trajectory `ω` follows D-Tracking with target map `wt`: every arm `A_{t+1} = (ω t).1` is
one D-Tracking allows after the first `t` rounds. -/
def FollowsDTracking (wt : (Fin K → ℝ) → (Fin K → ℝ)) (ω : ℕ → Fin K × ℝ) : Prop :=
  ∀ t : ℕ, (ω t).1 ∈ allowedD wt (banditTrajPrefix K t ω)

end OptimalBAI.TrackStop


