-- Prove2me | Definitions.Def_OAI_Probability_Localization_Rewards
-- name    : OAI_Probability_Localization_Rewards
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T19:36:01.793624+00:00
-- url     : https://prove2.me/theorems/03d58bd9-7516-4046-a3c6-820dd9e13147
-- title:
--   Rewards, truncated depth and truncated attempt counts along the localization run
-- statement:
--   Fix $n$, a measure $P$ on $\mathbb{R}^n$ and a starting dyadic cell $Q$ of the cube $\big[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n}\big)^n$; $\ell(c)$ denotes the level of a cell $c$ and $B_c$ its box. For a measure $\mu$ and a cell $c$, a cell $R$ is heavy for $(\mu,c)$ if it is a dyadic descendant of $c$ with $\ell(R)>\ell(c)$ and $\mu(B_R)>2^{-n(\ell(R)-\ell(c))/2}$. It is first heavy if no other heavy cell contains it, and the residual $\mathrm{Res}_\mu(c)$ is the part of $B_c$ covered by no first heavy cell. A letter is a cell or the symbol $\bot$, and a log is a finite word of letters. A state $s=(c_s,E_s,\mathrm{stop}_s)$ consists of a current cell, a current event $E_s\subseteq\mathbb{R}^n$ and a flag (active or stopped), and $\mu_s=P(\cdot\mid E_s)$ is the conditioned measure. Reading a letter $a$ is written $s\mapsto s\cdot a$. It leaves a stopped state unchanged. An active state moves to the cell $a$, or stays at $c_s$ if $a=\bot$, and its event is intersected with the branch of $a$, which is $B_a$ if $a$ is first heavy for $(\mu_s,c_s)$, $\varnothing$ for any other cell, and $\mathrm{Res}_{\mu_s}(c_s)$ if $a=\bot$. The new state is stopped exactly when $a=\bot$ and $\mu_s(\mathrm{Res}_{\mu_s}(c_s))\ge\tfrac12$. The initial state is $s_0=(Q,B_Q,\text{active})$, and $\mathrm{state}(h)$ is the state reached from $s_0$ by reading the log $h$. Finally, $\mathrm{run}_N(z)$ is the log produced by the point $z$ in $N$ steps: starting from the empty log, each step appends the attempt letter of $z$ for the current state (a first heavy cell for $(\mu_s,c_s)$ whose box contains $z$, or $\bot$ if there is none), unless the current state is already stopped.
--
--   The file defines the following bookkeeping quantities for this procedure.
--
--   1. **Complement mass.** The conditional mass of the residual region of a state,
--      $$q(s)=\mu_s\big(\mathrm{Res}_{\mu_s}(c_s)\big),$$
--      read as a real number.
--
--   2. **Complement reward.** $r^{\mathrm{c}}(s,a)=-\log q(s)$ if $s$ is active and $a=\bot$, and $r^{\mathrm{c}}(s,a)=0$ otherwise.
--
--   3. **Continuing reward.** $r^{\mathrm{f}}(s,a)=1$ if $s$ is active, $a=\bot$ and $q(s)<\tfrac12$, and $r^{\mathrm{f}}(s,a)=0$ otherwise. It flags a none-attempt after which the procedure does not stop.
--
--   4. **Accumulated reward.** For a reward $r$ (a real function of a state and a letter), a state $s$ and a log $h=a_1a_2\cdots a_m$,
--      $$\mathrm{acc}_r(s,h)=\sum_{j=1}^{m}r(t_{j-1},a_j),\qquad t_0=s,\quad t_j=t_{j-1}\cdot a_j .$$
--
--   5. **Reward of a log.** $\mathrm{rew}_r(h)=\mathrm{acc}_r(s_0,h)$, the reward accumulated from the initial state.
--
--   6. **Totals along the run.** $J_N(z)=\mathrm{rew}_{r^{\mathrm{c}}}(\mathrm{run}_N(z))$ and $F_N(z)=\mathrm{rew}_{r^{\mathrm{f}}}(\mathrm{run}_N(z))$.
--
--   7. **Truncated depth.** $d_N(z)=\ell(c)-\ell(Q)$, where $c$ is the current cell of $\mathrm{state}(\mathrm{run}_N(z))$.
--
--   8. **Truncated attempts.** $A_N(z)$, the length of the log $\mathrm{run}_N(z)$.
--
--   9. **Activity indicator.** $\iota_N(z)=0$ if $\mathrm{state}(\mathrm{run}_N(z))$ is stopped and $\iota_N(z)=1$ otherwise.
--
--   These quantities drive the entropy budget of the procedure. For a probability measure $P$ with $P(B_Q)=1$, the probability of the current event along a log is at least the product of the heavy-cell thresholds and of the complement masses met so far, so $J_N$ records the surprisal spent on none-attempts; averaged over $z$, each such attempt costs at most $1/e$ because $q(-\log q)\le 1/e$. Every active attempt either descends at least one level, or is a none-attempt counted by $F_N$, or is the final stopping attempt, which gives $A_N(z)\le d_N(z)+F_N(z)+1$ for every $z\in B_Q$. For a point that terminates, $d_N$ and $A_N$ are eventually constant in $N$, equal to its terminal depth and its number of attempts.
--
--   **Formalization Note** The Lean names are `complementMass`, `complementReward`, `continuingReward`, `accumulate`, `rewardLog`, `complementTotal`, `continuingTotal`, `truncatedDepth`, `truncatedAttempts` and `activeIndicator`. The complement mass is the `toReal` of an extended real, Lean's convention $\log 0=0$ gives $r^{\mathrm{c}}=0$ when $q(s)=0$, and $d_N$ uses truncated natural-number subtraction. Conditioning is `ProbabilityTheory.cond`, which is the zero measure when $P(E_s)$ is $0$ or infinite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/Rewards.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/Rewards.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GaussianFiniteEntropy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

noncomputable def complementMass {n : ℕ} (P : Measure (Coordinate n)) (s : State n) : ℝ :=
  ((ProbabilityTheory.cond P s.event) (residual (ProbabilityTheory.cond P s.event) s.cell)).toReal

noncomputable def complementReward {n : ℕ} (P : Measure (Coordinate n)) (s : State n) (a : Letter n) : ℝ :=
  if s.stopped then 0 else if a = none then -Real.log (complementMass P s) else 0

noncomputable def continuingReward {n : ℕ} (P : Measure (Coordinate n)) (s : State n) (a : Letter n) : ℝ :=
  if s.stopped then 0 else if a = none ∧ complementMass P s < 1/2 then 1 else 0

noncomputable def accumulate {n : ℕ} (P : Measure (Coordinate n)) (r : State n → Letter n → ℝ) :
    State n → Log n → ℝ
  | _,[] => 0
  | s,a::h => r s a + accumulate P r (update P s a) h

noncomputable def rewardLog {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    (r : State n → Letter n → ℝ) (h : Log n) : ℝ := accumulate P r ⟨Q,cellSet Q,false⟩ h

noncomputable def complementTotal {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) : ℝ :=
  rewardLog P Q (complementReward P) (run P Q N z)

noncomputable def continuingTotal {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) : ℝ :=
  rewardLog P Q (continuingReward P) (run P Q N z)

noncomputable def truncatedDepth {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) : ℕ :=
  (state P Q (run P Q N z)).cell.1-Q.1

noncomputable def truncatedAttempts {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) : ℕ :=
  (run P Q N z).length

noncomputable def activeIndicator {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) : ℝ :=
  if (state P Q (run P Q N z)).stopped then 0 else 1

end FiniteEntropy

end RepeatedLocalization

end OAI


