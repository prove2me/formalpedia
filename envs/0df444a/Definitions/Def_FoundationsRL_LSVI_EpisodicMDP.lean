-- Prove2me | Definitions.Def_FoundationsRL_LSVI_EpisodicMDP
-- name    : FoundationsRL_LSVI_EpisodicMDP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:22:41.324978+00:00
-- url     : https://prove2.me/theorems/a84872e6-1c28-4dfc-a22f-f62756dc2f84
-- title:
--   Episodic MDP on a countable state space, Bellman operator $\mathcal T^M_h$, value functions $Q^{M,\pi}_h$, $Q^{M,\star}_h$ and $f^M(\pi_M)$
-- statement:
--   A **finite-horizon episodic MDP** $M=(\mathcal S,\mathcal A,\{P^M_h\}_{h=1}^H,\{R^M_h\}_{h=1}^H,d_1)$ has a countable state space $\mathcal S$, an action space $\mathcal A$ (any set, possibly infinite), transition laws $P^M_h(\cdot\mid s,a)\in\Delta(\mathcal S)$, reward distributions $R^M_h(s,a)\in\Delta(\mathbb R)$ and an initial distribution $d_1\in\Delta(\mathcal S)$.
--
--   The module defines, for a horizon $H$ and steps $h=1,\dots,H$:
--
--   1. the **Bellman operator**
--   $$
--   [\mathcal T^M_h Q](s,a)=\mathbb E[r_h\mid s,a]+\sum_{s'}P^M_h(s'\mid s,a)\max_{a'}Q(s',a');
--   $$
--   2. the optimal value functions $Q^{M,\star}_h=\mathcal T^M_h Q^{M,\star}_{h+1}$, $Q^{M,\star}_{H+1}\equiv0$, $V^{M,\star}_h(s)=\max_a Q^{M,\star}_h(s,a)$, and the optimal value $f^M(\pi_M)=\mathbb E_{s_1\sim d_1}[V^{M,\star}_1(s_1)]$;
--   3. for a randomized non-stationary policy $\pi=(\pi_1,\dots,\pi_H)$, $\pi_h:\mathcal S\to\Delta(\mathcal A)$, the value functions $Q^{M,\pi}_h(s,a)=\mathbb E[r_h\mid s,a]+\sum_{s'}P^M_h(s'\mid s,a)\,\mathbb E_{a'\sim\pi_{h+1}(s')}Q^{M,\pi}_{h+1}(s',a')$;
--   4. for a deterministic policy, the same recursion and its value $f^M(\pi)=\mathbb E_{s_1\sim d_1}[Q^{M,\pi}_1(s_1,\pi_1(s_1))]$.
--
--   These are the objects of §5.1 that §7 reuses with large or infinite state and action spaces.
--
--   **Formalization Note** Steps are 1-based and every recursion is $0$ beyond $H$. $\max_{a'}$ is the supremum $\sup_{a'}$, equal to the maximum when it is attained; where the book's expression is undefined (an unbounded $Q(s',\cdot)$, a divergent series) Lean's value is $0$, and every theorem of the mission states the conditions under which it is defined. $Q^{M,\star}$ is defined by the Bellman optimality recursion, which Proposition 25 (p. 83) shows equals the maximal expected reward-to-go.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §5.1, pp. 81–82, (5.1)–(5.2); Proposition 25, p. 83; restated in §7, p. 129; (7.4), p. 132

import Mathlib

open MeasureTheory

namespace FoundationsRL.LSVI

/-- A finite-horizon episodic MDP `M = (S, A, {P^M_h}, {R^M_h}, d₁)` on a countable state space
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §5.1, p. 81, restated in §7, p. 129).

* `P h s a` is the transition law `P^M_h(· | s, a) ∈ Δ(S)` of step `h`;
* `R h s a` is the reward distribution `R^M_h(s, a) ∈ Δ(ℝ)` of step `h`;
* `d1` is the initial state distribution `d₁ ∈ Δ(S)`.

**Formalization Note.** Steps are 1-based (`h = 1, …, H`); the horizon `H` is an argument of every
object built on the MDP, and the fields at indices outside `[H]` are never used. The state space is
countable because §7.2 writes the transition operator as a sum `Σ_{s'}` (p. 132), so transitions are
probability mass functions; the action space is an arbitrary type, possibly infinite (p. 132). -/
structure EpisodicMDP (S A : Type*) where
  /-- The transition law `P^M_h(· | s, a)` of step `h`. -/
  P : ℕ → S → A → PMF S
  /-- The reward distribution `R^M_h(s, a)` of step `h`. -/
  R : ℕ → S → A → Measure ℝ
  /-- Every reward distribution is a probability measure. -/
  isProb_R : ∀ h s a, IsProbabilityMeasure (R h s a)
  /-- The initial state distribution `d₁`. -/
  d1 : PMF S

namespace EpisodicMDP

variable {S A : Type*}

/-- The mean reward `E[r_h | s, a] = ∫ r dR^M_h(s, a)`. -/
noncomputable def meanReward (M : EpisodicMDP S A) (h : ℕ) (s : S) (a : A) : ℝ :=
  ∫ x, x ∂(M.R h s a)

/-- The one-step backup of a value function `V : S → ℝ` at step `h`:
`E[r_h | s, a] + Σ_{s'} P^M_h(s' | s, a) V(s')`. -/
noncomputable def backup (M : EpisodicMDP S A) (h : ℕ) (V : S → ℝ) (s : S) (a : A) : ℝ :=
  M.meanReward h s a + ∑' s', (M.P h s a s').toReal * V s'

/-- The Bellman operator `T^M_h` (Foster & Rakhlin, arXiv:2312.16730v1, (7.4), p. 132):
`[T^M_h Q](s, a) = E[r_h | s, a] + Σ_{s'} P^M_h(s' | s, a) max_{a'} Q(s', a')`.

**Formalization Note.** `max_{a'}` is the supremum `⨆ a'`, which is the maximum when it is attained
and is the real supremum when `Q(s', ·)` is bounded above; for a `Q(s', ·)` unbounded above the
book's expression is undefined and Lean's `⨆` returns `0`. A series `Σ_{s'}` that is not summable
has Lean value `0`; the book's expression is then undefined. -/
noncomputable def bellman (M : EpisodicMDP S A) (h : ℕ) (Q : S → A → ℝ) : S → A → ℝ :=
  M.backup h (fun s' => ⨆ a', Q s' a')

/-- The optimal state-action value function `Q^{M,⋆}_h`, computed by the Bellman optimality
recursion `Q^{M,⋆}_h = T^M_h Q^{M,⋆}_{h+1}`, `Q^{M,⋆}_{H+1} ≡ 0` (Foster & Rakhlin,
arXiv:2312.16730v1, Proposition 25, p. 83). It is `0` for `h > H`.

**Formalization Note.** The book defines `Q^{M,⋆}_h` as a maximum over `Π_rns` of expected
reward-to-go (p. 83) and proves it satisfies this recursion (Proposition 25). The recursion is
taken as the definition here; `max_a` is `⨆ a`. -/
noncomputable def Qstar (M : EpisodicMDP S A) (H : ℕ) (h : ℕ) : S → A → ℝ :=
  if h ≤ H then M.bellman h (M.Qstar H (h + 1)) else fun _ _ => 0
termination_by H + 1 - h

/-- The optimal value function `V^{M,⋆}_h(s) = max_a Q^{M,⋆}_h(s, a)` (p. 83). -/
noncomputable def Vstar (M : EpisodicMDP S A) (H : ℕ) (h : ℕ) (s : S) : ℝ :=
  ⨆ a, M.Qstar H h s a

/-- The optimal value `f^M(π_M) = E_{s₁ ∼ d₁}[V^{M,⋆}_1(s₁)]` (Foster & Rakhlin,
arXiv:2312.16730v1, (5.1)–(5.2), p. 81, with Proposition 25, p. 83). -/
noncomputable def optValue (M : EpisodicMDP S A) (H : ℕ) : ℝ :=
  ∑' s, (M.d1 s).toReal * M.Vstar H 1 s

/-- A randomized non-stationary (Markov) policy `π = (π₁, …, π_H)`, `π_h : S → Δ(A)`
(`Π_rns`, Foster & Rakhlin, arXiv:2312.16730v1, p. 81). -/
abbrev MarkovPolicy (S A : Type*) [MeasurableSpace A] : Type _ := ℕ → S → ProbabilityMeasure A

/-- The state-action value function `Q^{M,π}_h` of a policy `π ∈ Π_rns`, by the policy
recursion `Q^{M,π}_h(s, a) = E[r_h | s, a] + Σ_{s'} P^M_h(s' | s, a) V^{M,π}_{h+1}(s')` with
`V^{M,π}_{h+1}(s') = E_{a' ∼ π_{h+1}(s')} Q^{M,π}_{h+1}(s', a')` and `Q^{M,π}_{H+1} ≡ 0`
(Foster & Rakhlin, arXiv:2312.16730v1, p. 82). It is `0` for `h > H`.

**Formalization Note.** The book defines `Q^{M,π}_h` as a conditional expected reward-to-go; this
is its standard recursive form. -/
noncomputable def Qpi [MeasurableSpace A] (M : EpisodicMDP S A) (H : ℕ) (π : MarkovPolicy S A)
    (h : ℕ) : S → A → ℝ :=
  if h ≤ H then
    M.backup h (fun s' => ∫ a', M.Qpi H π (h + 1) s' a' ∂((π (h + 1) s' : ProbabilityMeasure A) :
      Measure A))
  else fun _ _ => 0
termination_by H + 1 - h

/-- A deterministic non-stationary policy, `π_h : S → A`. -/
abbrev DetPolicy (S A : Type*) : Type _ := ℕ → S → A

/-- The state-action value function `Q^{M,π}_h` of a deterministic policy `π`:
`Q^{M,π}_h(s, a) = E[r_h | s, a] + Σ_{s'} P^M_h(s' | s, a) Q^{M,π}_{h+1}(s', π_{h+1}(s'))`,
`Q^{M,π}_{H+1} ≡ 0` (p. 82). It is `0` for `h > H`. -/
noncomputable def Qdet (M : EpisodicMDP S A) (H : ℕ) (π : DetPolicy S A) (h : ℕ) : S → A → ℝ :=
  if h ≤ H then M.backup h (fun s' => M.Qdet H π (h + 1) s' (π (h + 1) s')) else fun _ _ => 0
termination_by H + 1 - h

/-- The value `f^M(π) = E_{s₁ ∼ d₁}[Q^{M,π}_1(s₁, π₁(s₁))]` of a deterministic policy
(Foster & Rakhlin, arXiv:2312.16730v1, (5.1), p. 81, and p. 82). -/
noncomputable def valueDet (M : EpisodicMDP S A) (H : ℕ) (π : DetPolicy S A) : ℝ :=
  ∑' s, (M.d1 s).toReal * M.Qdet H π 1 s (π 1 s)

end EpisodicMDP

end FoundationsRL.LSVI


