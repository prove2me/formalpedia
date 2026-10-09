-- Prove2me | Definitions.Def_OnlineCombOpt_BanditLB_Setting
-- name    : OnlineCombOpt_BanditLB_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:54:29.279649+00:00
-- url     : https://prove2.me/theorems/2454463e-073a-428f-9f12-4a443cf66f90
-- title:
--   §1, pp. 2–3 — binary action sets, bandit strategies and pseudo-regret
-- statement:
--   An online combinatorial game has a nonempty finite action set $\mathcal A\subseteq\{0,1\}^d$. Every action has exactly $m$ selected coordinates. In each of $n$ rounds, a behavioural strategy chooses a probability distribution on $\mathcal A$ from the past chosen actions and their observed scalar losses. A loss vector $z_t\in[0,1]^d$ is drawn; the player observes only $a_t^\mathsf T z_t$.
--
--   For a finite-support probability law on loss sequences, define the paper's pseudo-regret by
--
--   $$
--   R_n=\mathbb E\sum_{t=1}^n a_t^\mathsf Tz_t-\min_{a\in\mathcal A}\mathbb E\sum_{t=1}^n a^\mathsf Tz_t.
--   $$
--
--   This protocol lets the player randomize and respond to any real-valued observed loss. It supplies the goal theorem's common model.
--
--   **Formalization Note** Coordinates and rounds are indexed from zero. The loss law is finite and oblivious, and expectations are finite sums. Nonemptiness makes the minimum meaningful. Histories omit earlier distributions because a behavioural strategy determines them from earlier observations. A player with internal randomization is described by the conditional law of $a_t$ given the observed past, so behavioural strategies cover every randomized player of the paper (Kuhn's theorem for games of perfect recall).
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, pp. 2–3, §1 and Figure 1

import Mathlib
import Definitions.Def_OnlineCombOpt_Exp2LB_Setting

namespace OnlineCombOpt.BanditLB

/-- A behavioural bandit strategy: a distribution after each real-valued observation history. -/
abbrev BanditStrategy (d : ℕ) :=
  (t : ℕ) → (Fin t → (Fin d → ℝ) × ℝ) → (Fin d → ℝ) → ℝ

def IsStrategyOn {d : ℕ} (A : Finset (Fin d → ℝ)) (σ : BanditStrategy d) : Prop :=
  (∀ t h a, a ∈ A → 0 ≤ σ t h a) ∧
  (∀ t h, ∑ a ∈ A, σ t h a = 1)

/-- Probability of an action path against one fixed loss sequence. -/
def pathProb {n d : ℕ} (σ : BanditStrategy d)
    (z : Fin n → Fin d → ℝ) (path : Fin n → Fin d → ℝ) : ℝ :=
  ∏ t : Fin n,
    σ t.val (fun s : Fin t.val =>
      let u : Fin n := ⟨s.val, Nat.lt_trans s.isLt t.isLt⟩
      (path u, dotProduct (path u) (z u))) (path t)

/-- Finite, oblivious probability law supported on bounded coordinatewise losses. -/
def IsObliviousAdversary {n d : ℕ}
    (Z : Finset (Fin n → Fin d → ℝ))
    (μ : (Fin n → Fin d → ℝ) → ℝ) : Prop :=
  (∀ z ∈ Z, 0 ≤ μ z) ∧
  (∑ z ∈ Z, μ z = 1) ∧
  (∀ z ∈ Z, ∀ t i, z t i ∈ Set.Icc (0 : ℝ) 1)

/-- Expected cumulative player loss minus the best fixed action's expected loss. -/
noncomputable def banditRegret {n d : ℕ}
    (A : Finset (Fin d → ℝ)) (σ : BanditStrategy d)
    (Z : Finset (Fin n → Fin d → ℝ))
    (μ : (Fin n → Fin d → ℝ) → ℝ) : ℝ :=
  if hA : A.Nonempty then
    (∑ z ∈ Z, μ z *
      ∑ path ∈ Fintype.piFinset (fun _ : Fin n => A),
        pathProb σ z path * ∑ t : Fin n, dotProduct (path t) (z t)) -
      A.inf' hA (fun a => ∑ z ∈ Z, μ z *
        ∑ t : Fin n, dotProduct a (z t))
  else 0

end OnlineCombOpt.BanditLB


