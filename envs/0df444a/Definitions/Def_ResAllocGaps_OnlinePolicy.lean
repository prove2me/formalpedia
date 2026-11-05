-- Prove2me | Definitions.Def_ResAllocGaps_OnlinePolicy
-- name    : ResAllocGaps_OnlinePolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:29:35.594105+00:00
-- url     : https://prove2.me/theorems/0739caf0-4530-4725-83c0-f6157f62e4eb
-- title:
--   Multisecretary model: randomized online policies $\Pi(B,T)$, hindsight value, regret
-- statement:
--   **Sample.** At times $t=1,\dots,T$ a candidate with ability $\theta_t$ arrives, $\theta_1,\dots,\theta_T$ i.i.d. with law $\mu$, together with independent seeds $U_1,\dots,U_T\sim\mathrm{Unif}[0,1]$ independent of the abilities. Let $\mathcal F_t=\sigma(\theta_1,U_1,\dots,\theta_t,U_t)$.
--
--   **Feasible online policies.** A feasible online policy $\pi\in\Pi(B,T)$ is a sequence of $\{\mathcal F_t\}$-measurable actions $a^\pi_t\in\{\text{reject},\text{accept}\}$ that accepts at most $B$ candidates almost surely (multisecretary: $c(\theta,\text{accept})=1$, $r(\theta,\text{accept})=\theta$, rejecting costs and earns nothing). The seeds make randomized policies admissible.
--
--   **Values and regret.** The policy earns $R^\pi_T=\sum_t\theta_t\,\mathbb 1\{a^\pi_t=\text{accept}\}$. The hindsight value is
--   $$V^{hs}_1(B,T;\theta)=\max\Big\{\sum_{t\in S}\theta_t:\ S\subseteq[T],\ |S|\le B\Big\},$$
--   and the regret of $\pi$ is
--   $$\mathrm{Regret}(B,T;\pi)=\mathbb E\big[V^{hs}_1(B,T;\theta)\big]-\mathbb E\big[R^\pi_T\big].$$
--   The pathwise loss is $\Lambda(B,T;\pi)=V^{hs}_1(B,T;\theta)-R^\pi_T$.
--
--   These are the objects in which the universal lower bound of the mission is stated.
--
--   **Formalization Note** Time $t$ is the index $t-1$ of `Fin T`; a sample is a map `Fin T → ℝ × ℝ` (ability, seed) with law `Measure.pi` of $\mu\otimes\mathrm{Unif}[0,1]$. The decision at index $t$ is a measurable `Bool`-valued function of the observed prefix (non-anticipation is in the type; by Doob–Dynkin these are the $\mathcal F_t$-measurable actions). Feasibility holds almost surely, so the type depends on $\mu$. The regret is a difference of two Bochner integrals; for a law on $[0,1]$ both integrands are measurable and bounded by $T$ almost surely.
-- source:
--   O. Besbes, Y. Kanoria and A. Kumar, Dynamic Resource Allocation: Algorithmic Design Principles and Spectrum of Achievable Performances, arXiv:2205.09078v2 (6 Oct 2023), https://arxiv.org/abs/2205.09078v2, §2, pp.8–10 (model, online policies, V^π, hindsight, Regret, multisecretary); Appendix EC.1, (EC.13), p.ec4 (Λ)

import Mathlib

open MeasureTheory

namespace ResAllocGaps

/-- A sample path of the multisecretary problem with horizon `T` (Besbes, Kanoria & Kumar,
arXiv:2205.09078v2, §2, p.8): `ω t = (θ_{t+1}, U_{t+1})`, the candidate ability `θ` and the
independent randomization seed `U` at time `t + 1` of the paper. -/
abbrev Sample (T : ℕ) := Fin T → ℝ × ℝ

/-- The law `Unif[0, 1]` of a randomization seed `U_t` (p.8). -/
noncomputable def seedLaw : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The law of a sample path: `(θ_t, U_t)` i.i.d. over `t ∈ [T]` with `θ_t ∼ μ` independent of
`U_t ∼ Unif[0, 1]` (p.8: requests drawn independently from `F`; `U₁, …, U_T` independent, uniform
on `[0, 1]` and independent of the requests). -/
noncomputable def sampleLaw (μ : Measure ℝ) (T : ℕ) : Measure (Sample T) :=
  Measure.pi (fun _ : Fin T => μ.prod seedLaw)

/-- The candidate abilities `θ₁, …, θ_T` of a sample path. -/
def abilities {T : ℕ} (ω : Sample T) : Fin T → ℝ := fun t => (ω t).1

/-- The observed prefix `(θ₁, U₁, …, θ_{t+1}, U_{t+1})` of a sample path at index `t`, i.e. the
data generating the paper's `𝓕_{t+1} = σ(θ₁, U₁, …, θ_{t+1}, U_{t+1})` (p.8). -/
def obsPrefix {T : ℕ} (ω : Sample T) (t : Fin T) : Fin (t.val + 1) → ℝ × ℝ :=
  fun s => ω ⟨s.val, Nat.lt_of_lt_of_le s.isLt t.isLt⟩

/-- A **feasible online policy** `π ∈ Π(B, T)` of the multisecretary problem (Besbes, Kanoria &
Kumar, arXiv:2205.09078v2, §2, p.8, with the multisecretary specialization of p.10:
`A = {reject, accept}`, `r(θ, accept) = θ`, `c(θ, accept) = 1`, `r(θ, reject) = c(θ, reject) = 0`).
"A feasible online policy π is a sequence of `{𝓕_t}`-measurable random variables
`{a^π_1, …, a^π_T}` such that `Σ_t c(θ_t, a^π_t) ≤ B` almost surely."

**Formalization Note.** Time `t ∈ [T]` of the paper is the index `t − 1 : Fin T`. The action at
index `t` is a measurable function `accept t` of the observed prefix
`(θ₁, U₁, …, θ_{t+1}, U_{t+1})`, `true` meaning *accept*; by the Doob–Dynkin lemma these are
exactly the `𝓕_t`-measurable `{reject, accept}`-valued random variables, so non-anticipation is in
the type. The seeds make the policy randomized. The past actions need not be recorded: they are
functions of the prefix. Feasibility is "at most `B` acceptances" almost surely under the sample
law `sampleLaw μ T`, as on p.8, so the type depends on the ability law `μ`. -/
structure OnlinePolicy (μ : Measure ℝ) (T B : ℕ) where
  /-- The decision at index `t` (paper's time `t + 1`) as a function of the observed prefix. -/
  accept : (t : Fin T) → (Fin (t.val + 1) → ℝ × ℝ) → Bool
  /-- Each decision is a measurable function of the observed prefix. -/
  measurable_accept : ∀ t, Measurable (accept t)
  /-- At most `B` candidates are accepted, almost surely. -/
  budget_ae : ∀ᵐ ω ∂(sampleLaw μ T),
    (Finset.univ.filter (fun t => accept t (obsPrefix ω t) = true)).card ≤ B

namespace OnlinePolicy

variable {μ : Measure ℝ} {T B : ℕ}

/-- The action `a^π_{t+1}` of the policy on the sample path `ω` (`true` = accept). -/
def decision (π : OnlinePolicy μ T B) (ω : Sample T) (t : Fin T) : Bool :=
  π.accept t (obsPrefix ω t)

/-- The total reward `R^π_T = Σ_t r(θ_t, a^π_t) = Σ_t θ_t 1{a^π_t = accept}` (p.8). -/
noncomputable def reward (π : OnlinePolicy μ T B) (ω : Sample T) : ℝ :=
  ∑ t, if π.decision ω t then (ω t).1 else 0

end OnlinePolicy

/-- The **hindsight value** `V^hs_1(B, T; θ_{≥1}) = max_a {Σ_t r(θ_t, a_t) : a ∈ {reject,
accept}^T, Σ_t c(θ_t, a_t) ≤ B}` of the multisecretary problem (p.9, with p.10).

**Formalization Note.** An action vector `a ∈ {reject, accept}^T` is the finite set `S ⊆ [T]` of
accepted times, so the maximum is a finite `Finset.sup'` over `{S | |S| ≤ B}` (nonempty: it
contains `∅`) of `Σ_{t ∈ S} θ_t`. -/
noncomputable def hsValue (T B : ℕ) (θ : Fin T → ℝ) : ℝ :=
  ((Finset.univ : Finset (Finset (Fin T))).filter (fun S => S.card ≤ B)).sup'
    ⟨∅, by simp⟩ (fun S => ∑ t ∈ S, θ t)

/-- The (expected) **regret** `Regret(B, T; π) ≜ V^hs_1(B, T) − V^π_1(B, T)` of a feasible online
policy (p.9), where `V^hs_1(B, T) = E[V^hs_1(B, T; θ_{≥1})]` and `V^π_1(B, T) = E[R^π_T]`.

**Formalization Note.** A difference of two Bochner integrals over `sampleLaw μ T`. For a law
supported on `[0, 1]` both integrands are measurable and bounded by `T` almost surely, hence
integrable, so neither integral is a junk `0`. -/
noncomputable def regret {μ : Measure ℝ} {T B : ℕ} (π : OnlinePolicy μ T B) : ℝ :=
  (∫ ω, hsValue T B (abilities ω) ∂(sampleLaw μ T)) - ∫ ω, π.reward ω ∂(sampleLaw μ T)

/-- The pathwise loss `Λ(B, T; π) = Σ_t θ_t a^hs_t − Σ_t θ_t a^π_t` (Proof of Theorem 1, (EC.13),
p.ec4, written there for the DP policy), the hindsight value minus the policy's reward. -/
noncomputable def OnlinePolicy.loss {μ : Measure ℝ} {T B : ℕ} (π : OnlinePolicy μ T B)
    (ω : Sample T) : ℝ :=
  hsValue T B (abilities ω) - π.reward ω

end ResAllocGaps


