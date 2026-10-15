-- Prove2me | Definitions.Def_OAI_Probability_Localization_RewardBounds
-- name    : OAI_Probability_Localization_RewardBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T19:37:02.611532+00:00
-- url     : https://prove2.me/theorems/7131f352-eda7-43ef-b727-4575ae49b94d
-- title:
--   One-step reward of the localization run
-- statement:
--   Fix $n$, a measure $P$ on $\mathbb{R}^n$ and a starting dyadic cell $Q$ of the cube $\big[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n}\big)^n$; $\ell(c)$ denotes the level of a cell $c$ and $B_c$ its box. For a measure $\mu$ and a cell $c$, a cell $R$ is heavy for $(\mu,c)$ if it is a dyadic descendant of $c$ with $\ell(R)>\ell(c)$ and $\mu(B_R)>2^{-n(\ell(R)-\ell(c))/2}$. It is first heavy if no other heavy cell contains it, and the residual $\mathrm{Res}_\mu(c)$ is the part of $B_c$ covered by no first heavy cell. A letter is a cell or the symbol $\bot$, and a log is a finite word of letters. A state $s=(c_s,E_s,\mathrm{stop}_s)$ consists of a current cell, a current event $E_s\subseteq\mathbb{R}^n$ and a flag (active or stopped), and $\mu_s=P(\cdot\mid E_s)$ is the conditioned measure. Reading a letter $a$ is written $s\mapsto s\cdot a$. It leaves a stopped state unchanged. An active state moves to the cell $a$, or stays at $c_s$ if $a=\bot$, and its event is intersected with the branch of $a$, which is $B_a$ if $a$ is first heavy for $(\mu_s,c_s)$, $\varnothing$ for any other cell, and $\mathrm{Res}_{\mu_s}(c_s)$ if $a=\bot$. The new state is stopped exactly when $a=\bot$ and $\mu_s(\mathrm{Res}_{\mu_s}(c_s))\ge\tfrac12$. The initial state is $s_0=(Q,B_Q,\text{active})$, and $\mathrm{state}(h)$ is the state reached from $s_0$ by reading the log $h$. Finally, $\mathrm{run}_N(z)$ is the log produced by the point $z$ in $N$ steps: starting from the empty log, each step appends the attempt letter of $z$ for the current state (a first heavy cell for $(\mu_s,c_s)$ whose box contains $z$, or $\bot$ if there is none), unless the current state is already stopped.
--
--   Let $r$ be a reward function, assigning a real number $r(s,a)$ to every state $s$ and every letter $a$. For $N\in\mathbb{N}$ and $z\in\mathbb{R}^n$ let $s=\mathrm{state}(\mathrm{run}_N(z))$ be the state reached by $z$ after $N$ steps, and let $a_s(z)$ be the attempt letter of $z$ at that state, namely a first heavy cell for $(\mu_s,c_s)$ whose box contains $z$, or $\bot$ if there is none. The file defines the one-step reward
--
--   $$
--   \mathrm{step}_r(N,z)=r\big(s,\ a_s(z)\big),\qquad s=\mathrm{state}(\mathrm{run}_N(z)),
--   $$
--
--   which is the reward collected by the $(N+1)$-st attempt of $z$.
--
--   For rewards that vanish on stopped states, such as the complement and continuing rewards, the accumulated reward of the run satisfies $\mathrm{rew}_r(\mathrm{run}_{N+1}(z))=\mathrm{rew}_r(\mathrm{run}_N(z))+\mathrm{step}_r(N,z)$. Bounds on the expected one-step reward therefore add up to bounds on the expected total reward. On each fiber $\{z:\mathrm{run}_N(z)=h\}$ the state $s$ is fixed, which is what makes the one-step reward explicitly integrable fiber by fiber.
--
--   **Formalization Note** The Lean name is `rewardStep P Q r N z`. It is evaluated even when the state $s$ is stopped, although in that case the run itself does not grow.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/RewardBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/RewardBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GaussianFiniteEntropy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

noncomputable def rewardStep {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    (r : State n → Letter n → ℝ) (N : ℕ) (z : Coordinate n) : ℝ :=
  let s := state P Q (run P Q N z)
  r s (attemptLetter (ProbabilityTheory.cond P s.event) s.cell z)

end FiniteEntropy

end RepeatedLocalization

end OAI


