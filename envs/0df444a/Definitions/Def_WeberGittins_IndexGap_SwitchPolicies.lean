-- Prove2me | Definitions.Def_WeberGittins_IndexGap_SwitchPolicies
-- name    : WeberGittins_IndexGap_SwitchPolicies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:10.066073+00:00
-- url     : https://prove2.me/theorems/188e7b19-e1e1-4715-8385-f48c96a5dcd3
-- title:
--   Proof of Theorem 3, p. 1029 — the policies $\pi^*(t)$ (switch to Gittins at $t$) and $\pi(t)$ (run $j(t)$, then Gittins)
-- statement:
--   In the proof of Theorem 3, Weber fixes an arbitrary policy $\pi$ and a time $t \ge 0$ and defines two policies that are identical to $\pi$ for times less than $t$. Write $\gamma_i(y)$ for the fair charge of arm $i$ in state $y$, and say that a policy is a *Gittins index policy* in a round if it plays, almost surely, an arm $a$ with $\gamma_a(x_a) = \max_i \gamma_i(x_i)$ at the current states (ties broken arbitrarily).
--
--   1. **$\pi^*(t)$** ("switch to Gittins at $t$"). A policy $\sigma$ is a $\pi^*(t)$ if its selection rule coincides with that of $\pi$ in every round $n < t$, and in every round $n \ge t$, after every history, it is a Gittins index policy. For $t = 0$ this says exactly that $\sigma$ is a Gittins index policy.
--
--   2. **$\pi(t)$** ("run $j(t)$, then Gittins"). A policy $\sigma$ is a $\pi(t)$ if its selection rule coincides with that of $\pi$ in every round $n \le t$ (so it plays the arm $j(t)$ at time $t$, with $\pi$'s own law), and in every round $n > t$: let $j = j(t)$ be the arm played in round $t$ and $c = \gamma_j(x_j(t))$ its fair charge at that time. If $j$ has been played in every round $t, t+1, \dots, n-1$ and
--   $$\gamma_j(x_j(m)) \ge c \quad \text{for every } m \text{ with } t < m \le n,$$
--   then $\sigma$ plays $j$ in round $n$; otherwise $\sigma$ is a Gittins index policy in round $n$. In Weber's words, $\pi(t)$ "continues playing $j(t)$ until its fair charge drops below $\gamma_{j(t)}(x_{j(t)})$ and is identical to the Gittins index policy thereafter".
--
--   These are the two policies compared in equation (8); summing (8) over $t$ yields Theorem 3.
--
--   **Formalization Note** Both are predicates on a policy rather than single constructed policies: $\pi$ may be randomized and Gittins tie-breaking is arbitrary, so the paper's $\pi^*(t)$ and $\pi(t)$ are families, and every statement about them is made for every member. "Drops below" is read strictly: $\pi(t)$ continues while the fair charge of $j(t)$ is at least its value at time $t$. Once the run of $j(t)$ is interrupted or its fair charge has dropped, the continuation condition fails in every later round, so the policy is a Gittins index policy from then on. "Identical to $\pi$" means the same selection kernel in that round, after every history.
-- source:
--   Weber, On the Gittins index for multiarmed bandits, Ann. Appl. Probab. 2 (1992), p. 1029, proof of Theorem 3, first sentence

import Definitions.Def_WeberGittins_Suboptimality_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace WeberGittins.IndexGap

/-- Weber, proof of Theorem 3, p. 1029: "π*(t)". The policy `σ` is identical to `π` at every round
`n < t` (same selection kernel), and from round `t` on it is a Gittins index policy: at every round
`n ≥ t` and after every history `h` of `n` rounds it almost surely plays an arm whose current
fair charge `gittinsIndex P r β` is greatest (ties broken arbitrarily). For `t = 0` this is exactly
`IsGittinsIndexPolicy P r β σ`. -/
def IsSwitchToGittinsAt {S : Type*} [MeasurableSpace S] {k : ℕ} (P : Kernel S S)
    [IsMarkovKernel P] (r : S → ℝ) (β : ℝ) (π : MarkovBanditPolicy k S) (t : ℕ)
    (σ : MarkovBanditPolicy k S) : Prop :=
  (∀ n, n < t → σ.select n = π.select n) ∧
  ∀ n, t ≤ n → ∀ h : MarkovBanditHistory k S n,
    σ.select n h {a | ∀ i, gittinsIndex P r β (h.2 i) ≤ gittinsIndex P r β (h.2 a)} = 1

/-- The continuation condition of "π(t)" at round `n > t` after the history `h` of `n` rounds:
with `j = (h.1 t).2` the arm played at round `t` and `c = γ_j(x_j(t))` its fair charge at round `t`,
the arm `j` was played at every round `m` with `t ≤ m < n`, and its fair charge has stayed at least
`c` at every round `m` with `t < m < n` and at the current round `n`. -/
def RunContinues {S : Type*} [MeasurableSpace S] {k : ℕ} (P : Kernel S S)
    [IsMarkovKernel P] (r : S → ℝ) (β : ℝ) (t n : ℕ) (hn : t < n)
    (h : MarkovBanditHistory k S n) : Prop :=
  (∀ m : Fin n, t ≤ (m : ℕ) → (h.1 m).2 = (h.1 ⟨t, hn⟩).2) ∧
  (∀ m : Fin n, t < (m : ℕ) →
    gittinsIndex P r β ((h.1 ⟨t, hn⟩).1 (h.1 ⟨t, hn⟩).2) ≤
      gittinsIndex P r β ((h.1 m).1 (h.1 ⟨t, hn⟩).2)) ∧
  gittinsIndex P r β ((h.1 ⟨t, hn⟩).1 (h.1 ⟨t, hn⟩).2) ≤
    gittinsIndex P r β (h.2 (h.1 ⟨t, hn⟩).2)

/-- Weber, proof of Theorem 3, p. 1029: "π(t)". The policy `σ` is identical to `π` at every round
`n ≤ t` (so it plays `j(t)` at round `t` with `π`'s own law). At a round `n > t`, after a history
`h`: if `RunContinues` holds (the arm `j(t)` has been played without interruption since round `t`
and its fair charge has not dropped strictly below its value `γ_{j(t)}(x_{j(t)}(t))` at round `t`),
then `σ` plays `j(t)` almost surely; otherwise `σ` almost surely plays an arm of greatest current
fair charge (the Gittins index policy, ties broken arbitrarily). -/
def IsRunThenGittinsAt {S : Type*} [MeasurableSpace S] {k : ℕ} (P : Kernel S S)
    [IsMarkovKernel P] (r : S → ℝ) (β : ℝ) (π : MarkovBanditPolicy k S) (t : ℕ)
    (σ : MarkovBanditPolicy k S) : Prop :=
  (∀ n, n ≤ t → σ.select n = π.select n) ∧
  ∀ n (hn : t < n) (h : MarkovBanditHistory k S n),
    (RunContinues P r β t n hn h → σ.select n h {(h.1 ⟨t, hn⟩).2} = 1) ∧
    (¬ RunContinues P r β t n hn h →
      σ.select n h {a | ∀ i, gittinsIndex P r β (h.2 i) ≤ gittinsIndex P r β (h.2 a)} = 1)

end WeberGittins.IndexGap


