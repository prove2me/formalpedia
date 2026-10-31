-- Prove2me | Definitions.Def_FairExplore_Policies
-- name    : FairExplore_Policies
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:16:58.142719+00:00
-- url     : https://prove2.me/theorems/5aa26148-5c40-499c-9369-ddf16635c167
-- title:
--   The KL-UCB and PF-UCB policies
-- statement:
--   Two policies for the grouped $K$-armed bandit, defined at time $t$ from the history before $t$, with ties in every arg max broken by a tie-breaking rule `sel`.
--
--   1. **KL-UCB** (p.9, p.33): pull the available arm with the highest $\mathrm{UCB}_t(a)$, $a\in\mathcal A^{g_t}$.
--   2. **PF-UCB** (§4.1, p.14). Let $\hat q_t$ be the minimum-norm optimal solution of $P(\hat\theta_t)$ (program (13) at the empirical means), $A^{\mathrm{UCB}}_t(g)\in\arg\max_{a\in\mathcal A^g}\mathrm{UCB}_t(a)$, $\mathcal A^{\mathrm{UCB}}_t=\{A^{\mathrm{UCB}}_t(g):g\in G\}$ and $A^{\mathrm{greedy}}_t(g)\in\arg\max_{a\in\mathcal A^g}\hat\theta_t(a)$. At time $t$:
--      - if some arm $a\in\mathcal A^{g_t}\cap\mathcal A^{\mathrm{UCB}}_t$ has $N^{g_t}_t(a)\le\hat q^{g_t}_t(a)N_t(a)$, pull one of these arms uniformly at random;
--      - otherwise pull the greedy arm $A^{\mathrm{greedy}}_t(g_t)$.
--
--   PF-UCB is the paper's proportionally fair policy; KL-UCB is the regret-optimal policy that defines the disagreement point.
--
--   **Formalization Note** The uniform choice uses the policy's draw $U_t$: the $\lfloor U_t m\rfloor$-th of the $m$ eligible arms in the order of the arm type (the last one if $U_t=1$, a null event). The tie-breaking rule is a parameter: every theorem holds for every rule that picks an element of each nonempty set. Unpulled arms have $\hat\theta_t=0$ and $\mathrm{UCB}_t=+\infty$.
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, KL-UCB p.9 and p.33; PF-UCB §4.1, p.14; greedy arm p.15

import Mathlib
import Definitions.Def_FairExplore_Program

namespace FairExplore

variable {γ α : Type*}

/-- A deterministic tie-breaking rule: it picks an element of every nonempty finite set of arms.
Used for every "∈ arg max" of the paper (KL-UCB's choice p.9, `A^UCB_t(g)` and the greedy arm
p.14). -/
def IsSelector (sel : Finset α → α) : Prop :=
  ∀ s : Finset α, s.Nonempty → sel s ∈ s

/-- `arg max_{a ∈ s} f(a)` as a finite set. -/
def argmaxSet {β : Type*} [LinearOrder β] (s : Finset α) (f : α → β) : Finset α :=
  s.filter fun a => ∀ b ∈ s, f b ≤ f a

variable [Fintype γ] [DecidableEq γ] [DecidableEq α]

/-- `A^UCB_t(g) ∈ arg max_{a ∈ A^g} UCB_t(a)`, the arm with the highest UCB for group `g`
(p.14), computed from the history of the first `t` steps, ties broken by `sel`. -/
noncomputable def History.ucbArm {t : ℕ} (h : History γ α t) (sel : Finset α → α)
    (A : γ → Finset α) (g : γ) : α :=
  sel (argmaxSet (A g) h.ucb)

/-- `A^UCB_t = {A^UCB_t(g) : g ∈ G}`, the arms with the highest UCB for some group (p.14). -/
noncomputable def History.ucbSet {t : ℕ} (h : History γ α t) (sel : Finset α → α)
    (A : γ → Finset α) : Finset α :=
  Finset.univ.image fun g => h.ucbArm sel A g

/-- `A^greedy_t(g) ∈ arg max_{a ∈ A^g} θ̂_t(a)`, the greedy arm of group `g` (p.14–15), ties broken
by `sel`. -/
noncomputable def History.greedy {t : ℕ} (h : History γ α t) (sel : Finset α → α)
    (A : γ → Finset α) (g : γ) : α :=
  sel (argmaxSet (A g) h.mean)

/-- The KL-UCB policy (Garivier–Cappé 2011; p.9 and p.33): pull the available arm with the
highest UCB (16), "out of all arms available", ties broken by `sel`. -/
noncomputable def klucb (A : γ → Finset α) (sel : Finset α → α) : Policy γ α :=
  fun t gs as ys g _ => (History.mk gs as ys : History γ α t).ucbArm sel A g

/-- The PF-UCB policy (§4.1, p.14). At step `t` (paper time `t + 1`) with arriving group `g`, let
`θ̂` be the empirical means and `q̂ = q̂(θ̂)` the minimum-norm optimal solution of `P(θ̂)`.
1. If some available arm `a ∈ A^g ∩ A^UCB_t` has `N^g_t(a) ≤ q̂^g(a) N_t(a)`, pull one of these
   arms uniformly at random.
2. Otherwise pull the greedy arm `A^greedy_t(g)`.

**Formalization Note** The uniform choice in step 1 uses the policy's draw `U_t ∈ [0,1]`: the
`⌊U_t m⌋`-th of the `m` eligible arms in the order of `α` (the last one if `U_t = 1`, an event of
probability `0`). Ties in every arg max are broken by `sel`; θ̂ of an unpulled arm is `0`. -/
noncomputable def pfucb [Fintype α] [LinearOrder α] (A : γ → Finset α) (sel : Finset α → α) :
    Policy γ α :=
  fun t gs as ys g u =>
    let h : History γ α t := ⟨gs, as, ys⟩
    let q := qhat A h.mean
    let E := (A g).filter fun a =>
      a ∈ h.ucbSet sel A ∧ (h.gcount g a : ℝ) ≤ q g a * (h.count a : ℝ)
    if E.Nonempty then
      (E.sort (· ≤ ·)).getD (min ⌊(u : ℝ) * (E.card : ℝ)⌋₊ (E.card - 1)) (h.greedy sel A g)
    else h.greedy sel A g

end FairExplore


