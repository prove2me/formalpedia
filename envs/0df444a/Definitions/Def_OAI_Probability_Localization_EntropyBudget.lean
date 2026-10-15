-- Prove2me | Definitions.Def_OAI_Probability_Localization_EntropyBudget
-- name    : OAI_Probability_Localization_EntropyBudget
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T19:38:50.689555+00:00
-- url     : https://prove2.me/theorems/4d85a941-5894-4547-9711-1d6ffe283e91
-- title:
--   Entropy slope, history divergence and history cost of a localization log
-- statement:
--   Fix $n$, a measure $P$ on $\mathbb{R}^n$ and a starting dyadic cell $Q$ of the cube $\big[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n}\big)^n$; $\ell(c)$ denotes the level of a cell $c$ and $B_c$ its box. For a measure $\mu$ and a cell $c$, a cell $R$ is heavy for $(\mu,c)$ if it is a dyadic descendant of $c$ with $\ell(R)>\ell(c)$ and $\mu(B_R)>2^{-n(\ell(R)-\ell(c))/2}$. It is first heavy if no other heavy cell contains it, and the residual $\mathrm{Res}_\mu(c)$ is the part of $B_c$ covered by no first heavy cell. A letter is a cell or the symbol $\bot$, and a log is a finite word of letters. A state $s=(c_s,E_s,\mathrm{stop}_s)$ consists of a current cell, a current event $E_s\subseteq\mathbb{R}^n$ and a flag (active or stopped), and $\mu_s=P(\cdot\mid E_s)$ is the conditioned measure. Reading a letter $a$ is written $s\mapsto s\cdot a$. It leaves a stopped state unchanged. An active state moves to the cell $a$, or stays at $c_s$ if $a=\bot$, and its event is intersected with the branch of $a$, which is $B_a$ if $a$ is first heavy for $(\mu_s,c_s)$, $\varnothing$ for any other cell, and $\mathrm{Res}_{\mu_s}(c_s)$ if $a=\bot$. The new state is stopped exactly when $a=\bot$ and $\mu_s(\mathrm{Res}_{\mu_s}(c_s))\ge\tfrac12$. The initial state is $s_0=(Q,B_Q,\text{active})$, and $\mathrm{state}(h)$ is the state reached from $s_0$ by reading the log $h$. Finally, $\mathrm{run}_N(z)$ is the log produced by the point $z$ in $N$ steps: starting from the empty log, each step appends the attempt letter of $z$ for the current state (a first heavy cell for $(\mu_s,c_s)$ whose box contains $z$, or $\bot$ if there is none), unless the current state is already stopped.
--
--   For a log $h$ write $\mathrm{state}(h)=(c_h,E_h,\cdot)$, and let $U_c$ be the uniform distribution on the box $B_c$ of a cell $c$, i.e. Lebesgue measure conditioned on $B_c$. The file defines:
--
--   1. **Entropy slope.**
--      $$\beta_n=\frac{n\log 2}{2}.$$
--
--   2. **History divergence.** The Kullback–Leibler divergence, with values in $[0,\infty]$, of the conditioned measure from the uniform law on the current cell,
--      $$\mathrm{KL}(h)=D\big(P(\cdot\mid E_h)\,\big\|\,U_{c_h}\big).$$
--
--   3. **History cost.**
--      $$\mathrm{cost}(h)=\mathrm{KL}(h)+\beta_n\,\big(\ell(c_h)-\ell(Q)\big),$$
--      where $\mathrm{KL}(h)$ is read as a real number.
--
--   Descending one level of the dyadic tree in $\mathbb{R}^n$ divides the volume by $2^n$, so the uniform law on a cell gives a descendant at relative depth $\Delta$ mass $2^{-n\Delta}$, a surprisal of $n\Delta\log2$. A heavy cell at relative depth $\Delta$, on the other hand, keeps more than a $2^{-n\Delta/2}$ fraction of the conditional mass, a surprisal of less than $\beta_n\Delta$. The cost functional records this trade-off at the rate $\beta_n$ per level: the budget inequality for the procedure bounds the expected cost of the run after $N$ steps by $D(P\|U_Q)$ plus the expected accumulated complement reward.
--
--   **Formalization Note** The Lean names are `entropySlope`, `historyKL` and `historyCost`; the divergence is `InformationTheory.klDiv` and conditioning is `ProbabilityTheory.cond`. In the cost the divergence enters through `ENNReal.toReal`, so an infinite divergence would contribute $0$, and the depth uses truncated natural-number subtraction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/EntropyBudget.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/EntropyBudget.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GaussianFiniteEntropy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards
import Definitions.Def_OAI_Probability_Localization_RewardBounds

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

noncomputable def entropySlope (n : ℕ) : ℝ := (n:ℝ)*Real.log 2/2

noncomputable def historyKL {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) : ℝ≥0∞ :=
  InformationTheory.klDiv (ProbabilityTheory.cond P (state P Q h).event) (uniformCell (state P Q h).cell)

noncomputable def historyCost {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) : ℝ :=
  (historyKL P Q h).toReal + entropySlope n * ((state P Q h).cell.1-Q.1 : ℕ)

end FiniteEntropy

end RepeatedLocalization

end OAI


