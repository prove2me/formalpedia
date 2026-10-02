-- Prove2me | Definitions.Def_MDPFinance_LPDuality_Value
-- name    : MDPFinance_LPDuality_Value
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:50:35.945906+00:00
-- url     : https://prove2.me/theorems/a2733d09-7223-4c16-90ab-3155925bf0cd
-- title:
--   The positive-model integrability bound ε, and J∞/δ/J (restated from chunk 07a)
-- statement:
--   Restates chunk `07a`'s value-function apparatus ($J_n^\pi$, $J_n$, $J_\infty^\pi$, $J_\infty$,
--   $\delta$, $J$), and adds $\varepsilon(x) := \sup_\pi J_\infty^{r^-,\pi}(x)$, the analogous
--   integrability bound for **positive** Markov Decision Models (§7.4): where §7.1's theory bounds
--   the *positive* part of the reward (models where reward can run away to $+\infty$ only slowly),
--   §7.4 is the mirror-image theory for models where the reward's *negative* part must be controlled
--   — a genuinely symmetric but logically independent development, since now $J_\infty(x) = \infty$
--   is an admissible possibility, and value iteration converges from *below* rather than above.
--
--   **Moderation note.** All suprema over policies range over $F^\infty$ (`IsPolicyOf`); the draft's suprema over all maps $\mathbb N\to E\to A$ inflate $J_n$, $\delta$, $\varepsilon$, $J_\infty$ through the arbitrary values of $r$ off $D$. The standing Integrability Assumptions of §7.1 ($\delta<\infty$) and §7.4 ($\varepsilon<\infty$) are `IntegrabilityAssumptionA` and `IntegrabilityAssumptionAneg`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 209, §7.4's Convergence Assumption (C⁻) (restated for this chunk)

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model

open MeasureTheory ProbabilityTheory Filter

namespace MDPFinance.LPDuality

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- `J_n^{rew,π}(x) := T_{f_0}\cdots T_{f_{n-1}} 0 (x)`, the `n`-stage reward-to-go of the
Markov policy `π = (f_0,f_1,\dots) \in F^\infty` under a one-stage reward `rew` (`rew := M.r` for
`J_n^\pi`, `rew := fun p => max (M.r p) 0` for the analogous quantity `δ` is built from), computed
by peeling `f_0` off and recursing on the tail `π \circ (\cdot+1)` (Bäuerle–Rieder, p. 197, PDF
209, unnumbered display preceding Lemma 7.1.4). -/
noncomputable def Jnpi (M : MarkovDecisionModel E A) (rew : E × A → ℝ) (π : ℕ → E → A) :
    (n : ℕ) → E → EReal
  | 0, _ => 0
  | (n + 1), x =>
      (rew (x, π 0 x) : EReal) + (M.β : EReal) *
        erealIntegral (M.Q (x, π 0 x)) (Jnpi M rew (fun k => π (k + 1)) n)

/-- `π ∈ F^∞`: a policy for the infinite-horizon model, a sequence of decision rules
(measurable, `f_k(x) ∈ D(x)`). All suprema over policies below range over `F^∞`. -/
def IsPolicyOf (M : MarkovDecisionModel E A) (π : ℕ → E → A) : Prop :=
  ∀ k, IsDecisionRuleOf M (π k)

/-- `J_n(x) := \sup_{\pi ∈ F^∞} J_n^{rew,\pi}(x)`, the `n`-stage value function. -/
noncomputable def Jn (M : MarkovDecisionModel E A) (rew : E × A → ℝ) (n : ℕ) (x : E) : EReal :=
  ⨆ π ∈ {π : ℕ → E → A | IsPolicyOf M π}, Jnpi M rew π n x

/-- `J_\infty^{rew,\pi}(x) := \limsup_n J_n^{rew,\pi}(x)`, standing in for the book's literal
infinite-horizon expectation `𝔼^\pi_x[\sum_k \beta^k rew(X_k,f_k(X_k))]` — under the book's own
Convergence Assumption (C), Theorem B.1.1 (an appendix result, not re-proved here) shows this
sequence genuinely converges and the limit equals that expectation; `limsup` is the total,
junk-safe stand-in used throughout this series for a quantity only conditionally well-defined
(matching `erealIntegral`'s own total convention), agreeing with the intended object whenever (C)
holds. -/
noncomputable def Jinfpi (M : MarkovDecisionModel E A) (rew : E × A → ℝ) (π : ℕ → E → A)
    (x : E) : EReal :=
  atTop.limsup fun n => Jnpi M rew π n x

/-- `δ(x) := \sup_\pi J_\infty^{r^+,\pi}(x)`, the Integrability Assumption (A)'s bound (Bäuerle–
Rieder, p. 195, PDF 206). -/
noncomputable def delta (M : MarkovDecisionModel E A) (x : E) : EReal :=
  ⨆ π ∈ {π : ℕ → E → A | IsPolicyOf M π}, Jinfpi M (fun p => max (M.r p) 0) π x

/-- The Integrability Assumption (A) of Section 7.1 (Bäuerle–Rieder, p. 195, PDF 206): `δ < ∞`. -/
def IntegrabilityAssumptionA (M : MarkovDecisionModel E A) : Prop :=
  ∀ x, delta M x < ⊤

/-- `ε(x) := \sup_\pi J_\infty^{r^-,\pi}(x)`, the positive-model Integrability Assumption (A)'s
bound (Bäuerle–Rieder, §7.4, p. 209, PDF 220, the mirror image of `delta` using the *negative*
part of the reward, since §7.4 treats models where the reward's negative part is what must be
controlled). -/
noncomputable def epsilon (M : MarkovDecisionModel E A) (x : E) : EReal :=
  ⨆ π ∈ {π : ℕ → E → A | IsPolicyOf M π}, Jinfpi M (fun p => max (-M.r p) 0) π x

/-- The Integrability Assumption (A) of Section 7.4 (Bäuerle–Rieder, p. 208, PDF 219), assumed
throughout that section: `ε < ∞`. -/
def IntegrabilityAssumptionAneg (M : MarkovDecisionModel E A) : Prop :=
  ∀ x, epsilon M x < ⊤

/-- `J_\infty(x) := \sup_\pi J_\infty^\pi(x)` (Bäuerle–Rieder, Eq. (7.1), p. 194, PDF 205), the
performance criterion of the infinite-horizon problem. -/
noncomputable def Jinf (M : MarkovDecisionModel E A) (x : E) : EReal :=
  ⨆ π ∈ {π : ℕ → E → A | IsPolicyOf M π}, Jinfpi M M.r π x

/-- `J(x) := \lim_n J_n(x)` (Bäuerle–Rieder, p. 197, PDF 208, the limit value function), via
`limsup` for the same total-convention reason as `Jinfpi`. -/
noncomputable def Jlim (M : MarkovDecisionModel E A) (x : E) : EReal :=
  atTop.limsup fun n => Jn M M.r n x

/-- `IB := \{v \in IM(E) \mid v(x) \le \delta(x) \text{ for all } x\}` (Bäuerle–Rieder, p. 195,
PDF 206, the Integrability Assumption (A)'s set; `J_\infty^\pi \in IB$ for every $\pi$"). -/
def IB (M : MarkovDecisionModel E A) : Set (E → EReal) :=
  {v | v ∈ IM E ∧ ∀ x, v x ≤ delta M x}

/-- `\pi = (f,\sigma)`: the policy with decision rule `f` at stage `0` and tail `\sigma \in
F^\infty` thereafter (Bäuerle–Rieder, Theorem 7.1.6's own notation), used to state the reward
iteration `J_\infty^\pi = T_f J_\infty^\sigma`. -/
def consPolicy (f : E → A) (σ : ℕ → E → A) : ℕ → E → A
  | 0 => f
  | (n + 1) => σ n

end MDPFinance.LPDuality


