-- Prove2me | Definitions.Def_MDPFinance_Bellman_Operators
-- name    : MDPFinance_Bellman_Operators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:08:46.041302+00:00
-- url     : https://prove2.me/theorems/f92e441f-68bd-46dc-b658-010cf1e9bd4c
-- title:
--   The operators $L_n$, $T_n^f$, $T_n$, and a maximizer of $v$
-- statement:
--   Write $\mathrm{IM}(E)$ for the set of measurable functions $v : E \to [-\infty, \infty)$
--   (extended-real-valued but never $+\infty$, since a supremum over unboundedly bad rewards can
--   diverge to $-\infty$ but the model's integrability assumption rules out $+\infty$). For
--   $v \in \mathrm{IM}(E)$, define at each stage $n$:
--
--   $$
--   (L_n v)(x,a) := r_n(x,a) + \int v(x')\, Q_n(dx' \mid x,a), \qquad (x,a) \in D_n,
--   $$
--
--   $$
--   (T_n^f v)(x) := (L_n v)(x, f(x)), \qquad (T_n v)(x) := \sup_{a \in D_n(x)} (L_n v)(x,a),
--   \qquad x \in E,
--   $$
--
--   for a decision rule $f \in F_n$. $L_n$ is the one-step reward-plus-continuation operator;
--   $T_n^f$ evaluates it along a fixed decision rule; $T_n$, the **maximal reward operator**,
--   optimizes over the admissible action. A decision rule $f \in F_n$ is a **maximizer of $v$ at
--   time $n$** if $T_n^f v = T_n v$, i.e. $f(x)$ attains the supremum defining $(T_n v)(x)$ for
--   every state $x$.
--
--   These operators are the mission's central machinery: the Bellman equation is the statement
--   $V_n = T_n V_{n+1}$, and an optimal policy is built from a sequence of maximizers of the value
--   function.
--
--   **Formalization Note.** The integral $\int v\, d\mu$ of an $\mathrm{IM}(E)$-valued function
--   against a measure is implemented by splitting $v$ into its nonnegative and nonpositive parts,
--   integrating each with the (total, $[0,\infty]$-valued) Lebesgue integral, and recombining with
--   `EReal`'s own total addition — under which an a priori undefined $\infty - \infty$ collapses to
--   $-\infty$ rather than being left partial, matching the book's own caveat that $L_n v$ is defined
--   "whenever the integral exists".
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, pp. 20-21, Definition 2.3.1 and Definition 2.3.6

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Bellman

/-- The integral `∫ v dμ ∈ [-∞,∞)` of an extended-real-valued function `v` that never equals
`⊤`, against a measure `μ`, following the standard convention for extended-real integration:
split `v` into its (finite, since `v ≠ ⊤`) nonnegative part and its (possibly infinite)
nonpositive part, integrate each with `∫⁻`, and combine with `EReal`'s total addition (which
uses the convention `⊤ + (-⊤) = ⊥`, i.e. an a priori ill-defined `∞ - ∞` collapses to `-∞`
rather than being left undefined — matching Def. 2.3.1's own caveat "whenever the integral
exists"). -/
noncomputable def erealIntegral {E : Type*} [MeasurableSpace E] (μ : Measure E) (v : E → EReal) :
    EReal :=
  (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal))

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- The operator `L_n` (Bäuerle–Rieder, Definition 2.3.1a, p. 20, PDF 34):
`(L_n v)(x,a) := r_n(x,a) + ∫ v(x') Q_n(dx'|x,a)`. -/
noncomputable def L (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (xa : E × A) :
    EReal :=
  (M.r n xa : EReal) + erealIntegral (M.Q n xa) v

/-- The operator `T_n^f` (Bäuerle–Rieder, Definition 2.3.1b, p. 20, PDF 34):
`(T_n^f v)(x) := (L_n v)(x, f(x))`. -/
noncomputable def Tf (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (f : E → A) (x : E) :
    EReal :=
  L M n v (x, f x)

/-- The maximal reward operator `T_n` (Bäuerle–Rieder, Definition 2.3.1c, p. 20, PDF 34):
`(T_n v)(x) := sup_{a ∈ D_n(x)} (L_n v)(x,a)`. -/
noncomputable def T (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (x : E) : EReal :=
  ⨆ a ∈ M.Dx n x, L M n v (x, a)

/-- `f` is a maximizer of `v` at time `n` (Bäuerle–Rieder, Definition 2.3.6, p. 21, PDF 36):
a decision rule at time `n` with `T_n^f v = T_n v`, i.e. `f(x)` attains the supremum defining
`T_n v(x)` for every `x`. -/
def IsMaximizer (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (f : E → A) : Prop :=
  IsDecisionRule M n f ∧ Tf M n v f = T M n v

end MDPFinance.Bellman


