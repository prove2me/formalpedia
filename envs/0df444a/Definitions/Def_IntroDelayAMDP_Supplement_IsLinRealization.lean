-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_IsLinRealization
-- name    : IntroDelayAMDP_Supplement_IsLinRealization
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:54:07.177287+00:00
-- url     : https://prove2.me/theorems/25ac76f1-ed28-405b-a83c-cb2f5dfcc43d
-- title:
--   A probability space carrying the run of Algorithm 3 or 5
-- statement:
--   Let $(\Omega,\mu)$ be a probability space with random variables $(s_{t,h},a_{t,h})$, the trajectory of episode $t$, and $U_{\kappa,k,h}\in\mathbb R$, the acceptance coin of the attempt of the estimate $(k,h)$ with episode $\kappa$, used when $\kappa$ is processed at the end of episode $t(\kappa)$. Let $\pi_t$ be the policy the algorithm plays in episode $t$ on the sample path. The space **carries the run** if, for every episode $t<K$:
--
--   1. $s_{t,0}=s_0$;
--   2. given the trajectories of the earlier episodes, the coins of the episodes processed before episode $t$, and $s_{t,0},a_{t,0},\dots,s_{t,h}$, the action $a_{t,h}$ has law $\pi_t(\cdot\mid s_{t,h})$;
--   3. given the same and $a_{t,h}$, the next state $s_{t,h+1}$ has law $P(\cdot\mid s_{t,h},a_{t,h})$;
--   4. for every episode $\kappa$ processed by the end of the game, its coins $(U_{\kappa,k,h})_{k<K,h<H}$ are i.i.d. uniform on $[0,1]$ and independent of all trajectories of the episodes up to $t(\kappa)$ and of the coins of the episodes processed before $\kappa$.
--
--   This is the protocol of Section 2.1 (states drawn from $P$, actions from the current policy, internal randomness independent of the past), in the processing order of App. C.1.
--
--
--   **Formalization Note** Laws given the past are conditional expectations of indicators. Stating a theorem for every probability space carrying the run makes it a statement about the law of the run. Such a space exists, for instance by the Ionescu-Tulcea theorem on any measurable state space.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Section 2.1, p.12; Lemma C.1, p.58; Algorithms 3 and 5

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace

namespace IntroDelayAMDP.Supplement

open MeasureTheory ProbabilityTheory

open Classical in

/-- **A probability space carrying the interaction of Algorithm 3 or 5 with a (possibly uncountable)
AMDP** (Section 2.1, printed p.12, PDF p.14; Lemma C.1, printed p.58; Algorithms 3 and 5, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)). Printed p.12: "In
episode `k ∈ [K]`, the agent starts from the initial state `s_{k,0} = s₀`. At every step `h` … she observes the
current state `s_{k,h} ∈ S_h`, chooses an action `a_{k,h}`, … and then transitions to a new state `s_{k,h+1}`
that is independently sampled from `P(· | s_{k,h}, a_{k,h})`"; the policy `π_k` "is `F_{k−1}`-measurable up to
any amount of internal randomness".

On a probability space `(Ω, μ)`, `traj t h ω = (s_{t,h}, a_{t,h})` is the trajectory of the 0-based episode `t`
and `coin κ k h ω` the acceptance coin of the attempt of the estimate `(k, h)` with episode `κ`, used when `κ`
is processed, at the end of episode `tp κ`; `πs ω t` is the policy the algorithm plays in episode `t` on the
sample path `ω`. `IsLinRealization μ L P K tp traj coin πs` says: all are random variables; for every
`t < K`:
1. `s_{t,0} = s₀`;
2. given the trajectories of the episodes before `t`, the coins of the episodes processed before episode `t`
   (`tp κ < t`), and `s_{t,0}, a_{t,0}, …, s_{t,h}`, the action `a_{t,h}` has law `π_t(· | s_{t,h})`;
3. given the same and `a_{t,h}`, the next state `s_{t,h+1}` has law `P(· | s_{t,h}, a_{t,h})` (`h + 1 < H`);
4. for every episode `κ < K` processed in time (`tp κ < K`), its coins `(coin κ k h)_{k<K, h<H}` are i.i.d. uniform
   on `[0, 1]` and independent of all trajectories of the episodes `≤ tp κ` and of the coins of the episodes
   processed before `κ` (`tp κ′ < tp κ`, or `tp κ′ = tp κ` and `κ′ < κ`: same-time episodes go in increasing
   order).

**Formalization Note.** This is the protocol's law, stated for every probability space carrying it, so a
theorem quantified over all such `(Ω, μ, traj, coin)` is a statement about the law of the run. Laws given the
past are conditional expectations of indicators. A realization exists (e.g. by the Ionescu-Tulcea theorem,
`ProbabilityTheory.Kernel.traj`, on any measurable state space, the algorithm being a measurable function of
the past); for a finite state space the uniform tape of the base mission is one. -/
def IsLinRealization {Ω X A : Type} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace A]
    {H : ℕ} (μ : Measure Ω) (L : LayeredSpace X H) (P : A → Kernel X X) (K : ℕ) (tp : ℕ → ℕ)
    (traj : ℕ → ℕ → Ω → X × A) (coin : ℕ → ℕ → ℕ → Ω → ℝ) (πs : Ω → ℕ → X → A → ℝ) : Prop :=
  let trajσ : ℕ → ℕ → MeasurableSpace Ω := fun t h => MeasurableSpace.comap (traj t h) inferInstance
  let coinσ : ℕ → MeasurableSpace Ω := fun κ =>
    ⨆ (k : ℕ) (_ : k < K) (h : ℕ) (_ : h < H), MeasurableSpace.comap (coin κ k h) inferInstance
  let hist : ℕ → MeasurableSpace Ω := fun t =>
    (⨆ (j : ℕ) (_ : j < t) (h : ℕ) (_ : h < H), trajσ j h) ⊔
      ⨆ (κ : ℕ) (_ : κ < K ∧ tp κ < t), coinσ κ
  IsProbabilityMeasure μ ∧ (∀ t h, Measurable (traj t h)) ∧ (∀ κ k h, Measurable (coin κ k h)) ∧
  (∀ t < K, ∀ ω, (traj t 0 ω).1 = L.s0) ∧
  (∀ t < K, ∀ h < H, ∀ a : A,
    condExp (hist t ⊔ (⨆ (h' : ℕ) (_ : h' < h), trajσ t h') ⊔
          MeasurableSpace.comap (fun ω => (traj t h ω).1) inferInstance) μ
        (fun ω => if (traj t h ω).2 = a then (1 : ℝ) else 0)
      =ᵐ[μ] fun ω => πs ω t (traj t h ω).1 a) ∧
  (∀ t < K, ∀ h, h + 1 < H → ∀ B : Set X, MeasurableSet B →
    condExp (hist t ⊔ ⨆ (h' : ℕ) (_ : h' ≤ h), trajσ t h') μ
        (fun ω => if (traj t (h + 1) ω).1 ∈ B then (1 : ℝ) else 0)
      =ᵐ[μ] fun ω => (P (traj t h ω).2 (traj t h ω).1 B).toReal) ∧
  (∀ κ < K, tp κ < K →
    Indep (coinσ κ)
      ((⨆ (j : ℕ) (_ : j ≤ tp κ) (h : ℕ) (_ : h < H), trajσ j h) ⊔
        ⨆ (κ' : ℕ) (_ : κ' < K ∧ (tp κ' < tp κ ∨ (tp κ' = tp κ ∧ κ' < κ))), coinσ κ') μ ∧
    μ.map (fun ω (kh : Fin K × Fin H) => coin κ kh.1 kh.2 ω) =
      Measure.pi (fun _ => (volume : Measure ℝ).restrict (Set.Icc 0 1)))

end IntroDelayAMDP.Supplement


