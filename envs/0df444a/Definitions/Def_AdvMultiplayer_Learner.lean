-- Prove2me | Definitions.Def_AdvMultiplayer_Learner
-- name    : AdvMultiplayer_Learner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:55:45.202141+00:00
-- url     : https://prove2.me/theorems/1f2231d2-b31b-4e15-b190-0bbe3e149bf3
-- title:
--   The logical learner: Algorithm 1 with the interface (I1)-(I4)
-- statement:
--   The logical learner is a family of processes on a probability space with a filtration $(\mathcal F_t)$ of pre-round histories: the slow set $U_t$, fast arm $j_t$, recorded arm $I_t$, proposal bit $B_t$, integer scores and queues, and the episode schedule. Its behaviour is the recursions (10), (11), the stopped continuation after the first queue-overflow round $\tau_*$, and the interface: (I1) episode starts are stopping times, and the initial slow set of an episode starting before overflow has conditional law $p_{\bar w}$; (I2) on enabled rounds $t\le\tau_*$ the recorded arm has the conditional law (9); (I3) the fast arm has conditional law $q^\gamma_{w_t}(\cdot\mid U_t)$; (I4) the proposal bit is $\mathrm{Bernoulli}(h)$ independent of the history through the update, and a refresh draws from $\rho_t$ with fresh randomness.
--
--   The module also defines $\tau_*$ and the auxiliary regret $R_{\mathrm{aux}}(S)$. Section 3 holds on every such space, with rounded rewards and every dyadic rate $\eta$ with $\eta D$ integral and $0<\eta\le(1024mKL_{\mathrm{stab}})^{-1}$.
--
--   **Formalization Note.** The conditional laws are conditional expectations of indicators. Three families of $\sigma$-algebras mark the histories before the slow-set draw, through the update, and through the proposal bit.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Section 3, Algorithm 1 and Interface, pp.13-16

import Mathlib
import Definitions.Def_AdvMultiplayer_Size
import Definitions.Def_AdvMultiplayer_Strategy
import Definitions.Def_AdvMultiplayer_SetLaw
import Definitions.Def_AdvMultiplayer_Queue

open MeasureTheory

namespace AdvMultiplayer

/-- **The standing rate conditions of Section 3** (p.13): `η` is dyadic, `ηD` is integral, and
`0 < η ≤ (1024 m K L_stab)⁻¹`. Section 3 holds for every such rate, not only the tuned one. -/
def RateOK (p : Size) (η : ℝ) : Prop :=
  (∃ e : ℕ, η = ((1 : ℝ) / 2) ^ e) ∧ (∃ n : ℕ, η * (p.D : ℝ) = n) ∧ 0 < η ∧
    η ≤ ((1024 : ℝ) * p.m * p.K * p.Lstab)⁻¹

/-- Rewards rounded down to multiples of `1/D` (p.6): `r_t(a) ∈ [0,1]` and `D r_t(a) ∈ ℕ`. -/
def IsRounded (p : Size) (r : Rewards p) : Prop :=
  IsRewards p r ∧ ∀ t ∈ Finset.Icc 1 p.T, ∀ a, ∃ n : ℕ, r t a = (n : ℝ) / (p.D : ℝ)

/-- **The processes of Algorithm 1** (p.16). Gan, arXiv:2610.05688, Section 3: on a sample space `Ω`,
for each calendar round the slow set `U_t`, fast arm `j_t`, recorded arm `I_t` (`none` is `⊥`),
proposal bit `B_t`, integer scores `z_t` and integer backlogs `B_t(i)`, and the episode starts of the
schedule. Their joint behaviour is `Learner.IsRealization`. -/
structure Learner (p : Size) (Ω : Type*) where
  /-- `isStart t ω`: an episode starts at `t`. -/
  isStart : ℕ → Ω → Prop
  /-- The slow set `U_t`. -/
  slow : ℕ → Ω → Finset (Fin p.K)
  /-- The fast arm `j_t`. -/
  fast : ℕ → Ω → Fin p.K
  /-- The recorded arm `I_t`. -/
  recd : ℕ → Ω → Option (Fin p.K)
  /-- The proposal bit `B_t`. -/
  bit : ℕ → Ω → Bool
  /-- The integer scores `z_{t,i}`. -/
  z : ℕ → Ω → Fin p.K → ℕ
  /-- The integer backlogs `B_t(i)`. -/
  Bq : ℕ → Ω → Fin p.K → ℕ

namespace Learner

variable {p : Size} {Ω : Type*} (L : Learner p Ω) (η : ℝ)

/-- The weights `w_{t,i} = (1+1/D)^{z_{t,i}}` (p.14). -/
noncomputable def w (t : ℕ) (ω : Ω) : Fin p.K → ℝ := fun i => weightOf p (L.z t ω i)

/-- The grid endpoint `τ̄` of an episode starting at `s` (p.13). -/
noncomputable def epEnd (s : ℕ) : ℕ := p.gridEnd (Size.gridOf η) s

/-- `t` is enabled: it lies in an episode `[s, τ̄)` of the schedule (p.13). -/
def enabled (t : ℕ) (ω : Ω) : Prop :=
  ∃ s ∈ Finset.Icc 1 t, L.isStart s ω ∧ t < epEnd (p := p) η s

/-- The start of the last episode begun at or before `t` (`0` if none). -/
noncomputable def startOf (t : ℕ) (ω : Ω) : ℕ := sSup {s | s ≤ t ∧ L.isStart s ω}

/-- The anchor `w̄` of the episode containing `t`. -/
noncomputable def anchor (t : ℕ) (ω : Ω) : Fin p.K → ℝ := L.w (L.startOf t ω) ω

/-- The recording probabilities `ξ_i` in force at round `t`, frozen at the episode start (7). -/
noncomputable def xi (t : ℕ) (ω : Ω) (i : Fin p.K) : ℝ := xiRate p η (L.anchor t ω) i

/-- The normalized backlog `b_t(i) = B_t(i)/(ηD)` (p.15). -/
noncomputable def b (t : ℕ) (ω : Ω) (i : Fin p.K) : ℝ := (L.Bq t ω i : ℝ) / (η * (p.D : ℝ))

/-- `s` is an overflow round: `max_i b_{s+1}(i) > B_cap` (p.15). -/
def overflow (s : ℕ) (ω : Ω) : Prop := ∃ i, Size.BcapOf η < L.b η (s + 1) ω i

/-- The first queue-overflow round `τ_* = inf{t ∈ [T] : max_i b_{t+1}(i) > B_cap}` (p.15), with
`inf ∅ = +∞`. -/
noncomputable def tauStar (ω : Ω) : ℕ∞ :=
  sInf ((fun s : ℕ => (s : ℕ∞)) '' {s | s ∈ Finset.Icc 1 p.T ∧ L.overflow η s ω})

/-- `t` is retained: `t ≤ τ_*`, that is, no earlier overflow (p.17). -/
def retained (t : ℕ) (ω : Ω) : Prop := (t : ℕ∞) ≤ L.tauStar η ω

/-- The integer arrival `Δ_t(i)` of the logical learner (10), (11): zero on disabled rounds, when
nothing is recorded on `i`, and after overflow. -/
noncomputable def arrival (r : Rewards p) (t : ℕ) (ω : Ω) (i : Fin p.K) : ℕ := by
  classical exact
    if L.enabled η t ω ∧ L.retained η t ω ∧ L.recd t ω = some i then
      arrivalOf p η (L.xi η t ω i) (r t i) else 0

/-- The service `Γ_t(i)` (11): zero on disabled rounds and after overflow. -/
noncomputable def service (r : Rewards p) (t : ℕ) (ω : Ω) (i : Fin p.K) : ℕ := by
  classical exact
    if L.enabled η t ω ∧ L.retained η t ω then
      serviceOf (p.capOf η) (L.Bq t ω i) (L.arrival η r t ω i) else 0

/-- The raw estimate `r̃_t(i) = Δ_t(i)/(ηD)`. -/
noncomputable def est (r : Rewards p) (t : ℕ) (ω : Ω) (i : Fin p.K) : ℝ :=
  (L.arrival η r t ω i : ℝ) / (η * (p.D : ℝ))

/-- The auxiliary per-round reward `r_t(U_t) + r_t(j_t)`. -/
noncomputable def auxReward (r : Rewards p) (t : ℕ) (ω : Ω) : ℝ :=
  setReward p r t (L.slow t ω) + r t (L.fast t ω)

/-- The fixed continuation sets after overflow (p.15): `U = {1,…,m-1}`. -/
def contSlow (p : Size) : Finset (Fin p.K) :=
  Finset.univ.filter fun a => a.val + 1 < p.m

/-- The history `σ(H_s, r̃_s, …, r̃_{t-1})` of p.18 for an episode started at `s`. -/
noncomputable abbrev Ehist (Hpre : ℕ → MeasurableSpace Ω) (r : Rewards p)
    (s t : ℕ) : MeasurableSpace Ω :=
  Hpre s ⊔ ⨆ v ∈ Finset.Ico s t, MeasurableSpace.comap (fun ω => L.est η r v ω) ⊤

/-- The auxiliary regret `R_aux(S) = E Σ_{t∈𝒜}(r_t(S) - r_t(U_t) - r_t(j_t))` (p.18), with `𝒜` all
enabled rounds, including those after overflow. -/
noncomputable def Raux {m0 : MeasurableSpace Ω} (μ : Measure Ω) (r : Rewards p)
    (S : Finset (Fin p.K)) : ℝ := by
  classical exact
    ∫ ω, ∑ t ∈ (Finset.Icc 1 p.T).filter (fun t => L.enabled η t ω),
      (setReward p r t S - L.auxReward r t ω) ∂μ

/-- The indicator of an event, as a real function. -/
noncomputable def ind (A : Set Ω) : Ω → ℝ := A.indicator fun _ => 1

/-- **Algorithm 1 with the interface (I1)–(I4)** (pp.15–16). The recursions (10), (11), (13), the
stopped continuation after `τ_*` (p.15), and (I1)–(I4), on a probability space with filtration
`ℱ` of pre-round histories.

**Formalization Note.** `Hpre t` is the history before the slow-set draw at the start of round `t`,
`Hupd t` the history through round `t`'s update, and `Hprop t` the same plus the proposal bit. The
laws in (I1)–(I4) are stated as conditional expectations of indicators. (I4)'s refresh is stated for
`t + 1 < τ̄`; at the last round of an episode the draw of Algorithm 1 line 15 is never used. -/
structure IsRealization {m0 : MeasurableSpace Ω} (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (r : Rewards p) (Hpre Hupd Hprop : ℕ → MeasurableSpace Ω) : Prop where
  Hpre_le : ∀ t, Hpre t ≤ ℱ t
  le_Hupd : ∀ t, ℱ t ≤ Hupd t
  Hupd_le : ∀ t, Hupd t ≤ Hprop t
  Hprop_le : ∀ t, Hprop t ≤ Hpre (t + 1)
  Hprop_le_m0 : ∀ t, Hprop t ≤ m0
  /-- Line 1: scores and backlogs start at zero. -/
  z_one : ∀ ω i, L.z 1 ω i = 0
  B_one : ∀ ω i, L.Bq 1 ω i = 0
  /-- (11), the score and backlog recursions. -/
  B_succ : ∀ t ω i, 1 ≤ t → L.Bq (t + 1) ω i = L.Bq t ω i + L.arrival η r t ω i - L.service η r t ω i
  z_succ : ∀ t ω i, 1 ≤ t → L.z (t + 1) ω i = L.z t ω i + L.service η r t ω i
  /-- Measurability: scores, backlogs, starts and slow sets are known at the start of the round. -/
  isStart_meas : ∀ t, MeasurableSet[Hpre t] {ω | L.isStart t ω}
  z_meas : ∀ t i n, MeasurableSet[Hpre t] {ω | L.z t ω i = n}
  B_meas : ∀ t i n, MeasurableSet[Hpre t] {ω | L.Bq t ω i = n}
  slow_meas : ∀ t U, MeasurableSet[ℱ t] {ω | L.slow t ω = U}
  fast_meas : ∀ t a, MeasurableSet[Hupd t] {ω | L.fast t ω = a}
  recd_meas : ∀ t a, MeasurableSet[Hupd t] {ω | L.recd t ω = a}
  bit_meas : ∀ t, MeasurableSet[Hprop t] {ω | L.bit t ω = true}
  /-- Episodes are disjoint: a new episode starts only at or after the previous endpoint. -/
  disjoint : ∀ s s' ω, L.isStart s ω → L.isStart s' ω → s < s' → epEnd (p := p) η s ≤ s'
  /-- Disabled rounds have no proposal. -/
  bit_disabled : ∀ t ω, ¬ L.enabled η t ω → L.bit t ω = false
  /-- Within an episode the slow set is retained unless a proposal fires. -/
  retain : ∀ t ω, L.enabled η t ω → L.enabled η (t + 1) ω → L.startOf (t + 1) ω = L.startOf t ω →
    L.bit t ω = false → L.slow (t + 1) ω = L.slow t ω
  /-- The continuation after overflow (lines 17–18). -/
  cont_slow : ∀ t ω, ¬ L.retained η t ω → L.slow t ω = contSlow p
  cont_fast : ∀ t ω, ¬ L.retained η t ω → (L.fast t ω).val + 1 = p.m
  cont_bit : ∀ t ω, ¬ L.retained η t ω → L.bit t ω = false
  /-- (I1): the initial slow set of an episode starting before overflow has conditional law
  `p_{w̄}` given the history before the draw. -/
  I1 : ∀ t U, U ∈ Finset.powersetCard (p.m - 1) Finset.univ → ∀ᵐ ω ∂μ,
    L.isStart t ω → L.retained η t ω →
      (μ[ind {ω | L.slow t ω = U} | Hpre t]) ω = pw p (L.w t ω) (L.w t ω) U
  /-- (I2): the recorded arm has the conditional law (9). -/
  I2 : ∀ t i, ∀ᵐ ω ∂μ, L.enabled η t ω → L.retained η t ω →
    (μ[ind {ω | L.recd t ω = some i} | ℱ t]) ω = L.xi η t ω i
  I2_none : ∀ t, ∀ᵐ ω ∂μ, L.enabled η t ω → L.retained η t ω →
    (μ[ind {ω | L.recd t ω = none} | ℱ t]) ω = 1 - ∑ i, L.xi η t ω i
  /-- (I3): the fast arm has conditional law `q^γ_{w_t}(·|U_t)`. -/
  I3 : ∀ t a, ∀ᵐ ω ∂μ, L.enabled η t ω → L.retained η t ω →
    (μ[ind {ω | L.fast t ω = a} | ℱ t]) ω = qGamma p η (L.anchor t ω) (L.w t ω) (L.slow t ω) a
  /-- (I4): the proposal bit is `Bernoulli(h)`, independent of the history through the update. -/
  I4 : ∀ t, ∀ᵐ ω ∂μ, L.enabled η t ω → L.retained η t ω →
    (μ[ind {ω | L.bit t ω = true} | Hupd t]) ω = p.propOf η
  /-- (I4): a refresh draws from `ρ_t` with fresh randomness. -/
  I4_refresh : ∀ t U, U ∈ Finset.powersetCard (p.m - 1) Finset.univ → ∀ᵐ ω ∂μ,
    L.enabled η t ω → L.retained η t ω → L.bit t ω = true → t + 1 < epEnd (p := p) η (L.startOf t ω) →
      (μ[ind {ω | L.slow (t + 1) ω = U} | Hprop t]) ω =
        rhoLaw p η (L.anchor t ω) (L.w t ω) (L.w (t + 1) ω) U

end Learner

end AdvMultiplayer


