-- Prove2me | Definitions.Def_StatefulPricing_OLSCAlg
-- name    : StatefulPricing_OLSCAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:24:35.188975+00:00
-- url     : https://prove2.me/theorems/af7bd9f3-9453-47ce-836e-73026c788d7a
-- title:
--   Online learning with switching cost: algorithms, switches and regret
-- statement:
--   In **online learning with switching cost** (OLSC) there is a finite set $\Gamma$ of experts and $T$ rounds. At the end of round $t$ an expert reward function $F_t:\Gamma\to[0,1]$ is revealed. An algorithm picks experts $\gamma_1,\dots,\gamma_T$ online and pays a switching cost $\Delta$ every time it changes expert. Its regret is
--   $$
--   \max_{\gamma\in\Gamma}\sum_{t=1}^T F_t(\gamma)-\mathbb E\Big[\sum_{t=1}^T F_t(\gamma_t)-\Delta\sum_{t=2}^T\mathbf 1_{\gamma_t\neq\gamma_{t-1}}\Big].
--   $$
--   The module defines a randomized OLSC algorithm (coins $\omega$, round $t$, reward sequence $\mapsto$ expert), its online property (the round-$t$ pick depends only on $F_1,\dots,F_{t-1}$), the number of switches, and this regret.
--
--   OLSC is the problem to which C&S reduces online decision making on a Dd-MDP: C&S runs an OLSC algorithm over the policies with switching cost equal to the chasability parameter.
--
--   **Formalization Note** The switch count is random, so it sits inside the expectation. The reward sequence is fixed before the coins (oblivious adversary); the maximum is a real supremum over the finite expert type.
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, §3.3, p.10

import Mathlib

set_option autoImplicit false

namespace StatefulPricing

open MeasureTheory

/-- **Online learning with switching cost (OLSC)** (arXiv:2005.01869v2, §3.3, p.10): "we have a
finite set Γ of experts (often called actions or arms) and T ∈ Z>0 rounds. The expert reward
function Ft : Γ ↦ [0, 1) is revealed as feedback at the end of round t = 1, . . . , T. The goal
of an algorithm for this problem is to pick a sequence γ1, . . . , γT of experts in an online
fashion".

A randomized OLSC algorithm with coin space `Ω` and experts `ι`: `A ω t F` is the expert picked at
round `t` against the reward sequence `F` (`F t j` is the reward of expert `j` in round `t`) when
the coins are `ω`. It is online when `A ω t F` depends only on `F 1, …, F (t−1)`
(`OLSCAlg.IsOnline`). -/
def OLSCAlg (Ω ι : Type*) := Ω → ℕ → (ℕ → ι → ℝ) → ι

namespace OLSCAlg

variable {Ω ι : Type*}

/-- The algorithm is online: its pick at round `t` depends on the reward sequence only through
the rewards `F s` of the rounds `1 ≤ s < t`. -/
def IsOnline (A : OLSCAlg Ω ι) : Prop :=
  ∀ ω t (F F' : ℕ → ι → ℝ), (∀ s, 1 ≤ s → s < t → F s = F' s) → A ω t F = A ω t F'

/-- The number of switches `Σ_{t=2}^T 1_{γt ≠ γt−1}` (arXiv:2005.01869v2, p.10). -/
noncomputable def switches (A : OLSCAlg Ω ι) (ω : Ω) (F : ℕ → ι → ℝ) (T : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 2 T).filter (fun t => A ω t F ≠ A ω (t - 1) F)).card

/-- The OLSC regret with switching cost `Δ` (arXiv:2005.01869v2, p.10):
`max_{γ∈Γ} Σ_{t∈[T]} Ft(γ) − ( Σ_{t∈[T]} E[Ft(γt)] − ∆ · Σ_{t=2}^T 1_{γt≠γt−1} )`.

**Formalization Note.** The switch count is random, so it is inside the expectation:
`max_j Σ_t F t j − E[Σ_t F t (γ_t) − Δ · #switches]`. The reward sequence `F` is fixed before the
coins (an oblivious adversary). The maximum is the real `⨆` over the finite expert type `ι`. -/
noncomputable def regret [MeasurableSpace Ω] (A : OLSCAlg Ω ι) (P : Measure Ω) (Δ : ℝ) (T : ℕ)
    (F : ℕ → ι → ℝ) : ℝ :=
  (⨆ j, ∑ t ∈ Finset.Icc 1 T, F t j)
    - ∫ ω, ((∑ t ∈ Finset.Icc 1 T, F t (A ω t F)) - Δ * (A.switches ω F T : ℝ)) ∂P

end OLSCAlg

end StatefulPricing


