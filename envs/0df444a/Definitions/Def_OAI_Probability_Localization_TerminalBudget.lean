-- Prove2me | Definitions.Def_OAI_Probability_Localization_TerminalBudget
-- name    : OAI_Probability_Localization_TerminalBudget
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T19:40:01.854864+00:00
-- url     : https://prove2.me/theorems/a30523b7-c7b6-4e5c-b29f-ab4486a8ed06
-- title:
--   Terminal relative entropy of the localization procedure
-- statement:
--   Fix $n$, a measure $P$ on $\mathbb{R}^n$ and a starting dyadic cell $Q$ of the cube $\big[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n}\big)^n$; $\ell(c)$ denotes the level of a cell $c$ and $B_c$ its box. For a measure $\mu$ and a cell $c$, a cell $R$ is heavy for $(\mu,c)$ if it is a dyadic descendant of $c$ with $\ell(R)>\ell(c)$ and $\mu(B_R)>2^{-n(\ell(R)-\ell(c))/2}$. It is first heavy if no other heavy cell contains it, and the residual $\mathrm{Res}_\mu(c)$ is the part of $B_c$ covered by no first heavy cell. A letter is a cell or the symbol $\bot$, and a log is a finite word of letters. A state $s=(c_s,E_s,\mathrm{stop}_s)$ consists of a current cell, a current event $E_s\subseteq\mathbb{R}^n$ and a flag (active or stopped), and $\mu_s=P(\cdot\mid E_s)$ is the conditioned measure. Reading a letter $a$ is written $s\mapsto s\cdot a$. It leaves a stopped state unchanged. An active state moves to the cell $a$, or stays at $c_s$ if $a=\bot$, and its event is intersected with the branch of $a$, which is $B_a$ if $a$ is first heavy for $(\mu_s,c_s)$, $\varnothing$ for any other cell, and $\mathrm{Res}_{\mu_s}(c_s)$ if $a=\bot$. The new state is stopped exactly when $a=\bot$ and $\mu_s(\mathrm{Res}_{\mu_s}(c_s))\ge\tfrac12$. The initial state is $s_0=(Q,B_Q,\text{active})$, and $\mathrm{state}(h)$ is the state reached from $s_0$ by reading the log $h$. Finally, $\mathrm{run}_N(z)$ is the log produced by the point $z$ in $N$ steps: starting from the empty log, each step appends the attempt letter of $z$ for the current state (a first heavy cell for $(\mu_s,c_s)$ whose box contains $z$, or $\bot$ if there is none), unless the current state is already stopped.
--
--   A point $z$ terminates if $\mathrm{state}(\mathrm{run}_N(z))$ is stopped for some $N$. Its number of attempts $\mathrm{att}(z)$ is the least such $N$, and its terminal log is $T(z)=\mathrm{run}_{\mathrm{att}(z)}(z)$. For a log $h$ let $c(h)$ be the current cell of $\mathrm{state}(h)$, let
--
--   $$
--   \pi_h=P\big(\cdot\mid\{w:\ T(w)=h\}\big)
--   $$
--
--   be the terminal law of $h$, and let $U_c$ be the uniform distribution on the box $B_c$. The file defines the terminal divergence of a point,
--
--   $$
--   \mathrm{KL}^{\mathrm{term}}(z)=D\big(\pi_{T(z)}\,\big\|\,U_{c(T(z))}\big)\in[0,\infty],
--   $$
--
--   the Kullback–Leibler divergence of the terminal law of $z$'s log from the uniform law on its terminal cell.
--
--   This is the quantity controlled by the finite-entropy regularization theorem, which, for $n\ge32$ and a probability measure $P\ll U_Q$ with $D(P\|U_Q)<\infty$, bounds $\int\mathrm{KL}^{\mathrm{term}}\,dP$ plus $\tfrac{n\log2}{4}$ times the expected depth by $D(P\|U_Q)+2/e$. Since $\mathrm{KL}^{\mathrm{term}}(z)$ depends on $z$ only through $T(z)$, it is measurable as soon as the terminal log is.
--
--   **Formalization Note** The Lean name is `terminalKL P Q z`, built from `terminalLaw`, `terminalCell` and `terminalLog` of the base definitions. For a point that does not terminate, $\mathrm{att}(z)=0$ and $T(z)$ is the empty log by convention.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/TerminalBudget.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/TerminalBudget.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_Localization_EntropyBudget

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

noncomputable def terminalKL {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (z : Coordinate n) : ℝ≥0∞ :=
  InformationTheory.klDiv (terminalLaw P Q (terminalLog P Q z))
    (uniformCell (terminalCell P Q (terminalLog P Q z)))

end FiniteEntropy

end RepeatedLocalization

end OAI


