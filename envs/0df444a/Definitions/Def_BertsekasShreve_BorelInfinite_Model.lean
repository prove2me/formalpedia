-- Prove2me | Definitions.Def_BertsekasShreve_BorelInfinite_Model
-- name    : BertsekasShreve_BorelInfinite_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:39:39.531881+00:00
-- url     : https://prove2.me/theorems/244b3bf9-2662-4abc-a69e-c1ad8c239395
-- title:
--   The infinite horizon stochastic optimal control model (SM), the operator T and the cases (P), (N), (D) (Defs 8.1, 8.5, 9.1)
-- statement:
--   An **infinite horizon stochastic optimal control model** (SM) is an eight-tuple $(S, C, U, W, p, f, \alpha, g)$ where
--
--   1. $S$ (state space), $C$ (control space) and $W$ (disturbance space) are nonempty Borel spaces;
--   2. $U$ (control constraint) maps each $x \in S$ to a nonempty set $U(x) \subseteq C$, and the set
--   $$\Gamma = \{(x, u) \mid x \in S,\ u \in U(x)\}$$
--   is analytic in $SC$;
--   3. $p(dw \mid x, u)$ (disturbance kernel) is a Borel-measurable stochastic kernel on $W$ given $SC$;
--   4. $f : SCW \to S$ (system function) is Borel-measurable;
--   5. $\alpha > 0$ is the discount factor;
--   6. $g : \Gamma \to R^*$ (one-stage cost) is lower semianalytic.
--
--   The system moves by $x_{k+1} = f(x_k, u_k, w_k)$ with $w_k \sim p(dw \mid x_k, u_k)$, so the state transition kernel is
--   $$t(B \mid x, u) = p(\{w \mid f(x, u, w) \in B\} \mid x, u).$$
--   For $J : S \to R^*$, the operator $T$ of Definition 8.5 is
--   $$T(J)(x) = \inf_{u \in U(x)} \Big\{ g(x, u) + \alpha \int_S J(x')\, t(dx' \mid x, u) \Big\}.$$
--   Chapter 9 treats three cases:
--
--   - **(P)** $0 \le g(x, u)$ for every $(x, u) \in \Gamma$;
--   - **(N)** $g(x, u) \le 0$ for every $(x, u) \in \Gamma$;
--   - **(D)** $0 < \alpha < 1$, and for some $b \in \mathbb R$, $-b \le g(x, u) \le b$ for every $(x, u) \in \Gamma$.
--
--   This is the model of every result of the chapter.
--
--   **Formalization Note** $S$, $C$, $W$ are type parameters; the hypotheses that they are nonempty Borel spaces carrying their Borel $\sigma$-algebras are stated in every theorem. The cost $g$ is stored as a function on all of $S \times C$, and only its values on $\Gamma$ enter the model (lower semianalyticity and (P), (N), (D) are required on $\Gamma$ only; every measure that integrates $g$ is concentrated on $\Gamma$, and $T$ takes the infimum over $U(x)$). The sum in $T$ uses the book's convention $\infty - \infty = \infty$, and the integral is the extended integral $\int J^+ - \int J^-$ of Eq. (43) of Chapter 7 (the referenced definition `DupacovaWets.Consistency.expect`, which is $+\infty$ when $\int J^+ = \infty$). These integrals are Lebesgue integrals with respect to the Borel measure $t(\cdot \mid x, u)$; for a universally measurable $J$ they coincide with the integrals with respect to its completion, which is how the book integrates universally measurable functions.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, pp. 188–189, Definition 8.1 and Eqs. (1), (3) of Chapter 8; p. 195, Definition 8.5; pp. 213–214, Definition 9.1 and (P), (N), (D)

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_BorelInfinite_ExtArith
import Definitions.Def_DupacovaWets_Consistency_expect

namespace BertsekasShreve.BorelInfinite

open MeasureTheory ProbabilityTheory

/-- **Definitions 8.1 and 9.1** (pp. 188–189, 213). An *infinite horizon stochastic optimal
control model* (SM) is an eight-tuple `(S, C, U, W, p, f, α, g)`:
* `S` (state space), `C` (control space), `W` (disturbance space): nonempty Borel spaces — these
  are type parameters, and the Borel-space hypotheses are stated in each theorem;
* `U` (control constraint): a map from `S` to the nonempty subsets of `C` whose graph
  `Γ = {(x, u) | x ∈ S, u ∈ U(x)}` (Eq. (1) of Chapter 8) is analytic in `SC`;
* `p(dw | x, u)` (disturbance kernel): a Borel-measurable stochastic kernel on `W` given `SC`;
* `f` (system function): a Borel-measurable function from `SCW` to `S`;
* `α` (discount factor): a positive real number;
* `g` (one-stage cost): a lower semianalytic function from `Γ` to `R*`. It is stored as a function
  on all of `SC`; only its values on `Γ` enter the model. -/
structure Model (S C W : Type*) [TopologicalSpace S] [MeasurableSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [MeasurableSpace W] where
  /-- the control constraint `U(x) ⊆ C` -/
  U : S → Set C
  U_nonempty : ∀ x, (U x).Nonempty
  /-- `Γ = {(x, u) | u ∈ U(x)}` is analytic in `SC` -/
  graph_analytic : AnalyticSet {z : S × C | z.2 ∈ U z.1}
  /-- the disturbance kernel `p(dw | x, u)` -/
  p : Kernel (S × C) W
  p_markov : IsMarkovKernel p
  /-- the system function `x_{k+1} = f(x_k, u_k, w_k)` -/
  f : S × C × W → S
  f_measurable : Measurable f
  /-- the discount factor -/
  α : ℝ
  α_pos : 0 < α
  /-- the one-stage cost -/
  g : S → C → EReal
  g_lowerSemianalytic :
    BertsekasShreve.AnalyticSelection.IsLowerSemianalytic {z : S × C | z.2 ∈ U z.1} (fun z => g z.1.1 z.1.2)

namespace Model

variable {S C W : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [TopologicalSpace C] [MeasurableSpace C] [MeasurableSpace W]

/-- The set `Γ = {(x, u) | x ∈ S, u ∈ U(x)}` (Eq. (1) of Chapter 8). -/
def Γ (M : Model S C W) : Set (S × C) := {z | z.2 ∈ M.U z.1}

/-- Eq. (3) of Chapter 8 (p. 189): the state transition stochastic kernel
`t(B | x, u) = p({w | f(x, u, w) ∈ B} | x, u)`, i.e. the image of `p(· | x, u)` under
`w ↦ f(x, u, w)`. -/
noncomputable def t (M : Model S C W) (z : S × C) : Measure S :=
  (M.p z).map (fun w => M.f (z.1, z.2, w))

/-- `H(x, u, J) = g(x, u) + α ∫_S J(x') t(dx' | x, u)` (p. 195), with the book's extended-real
arithmetic (`∞ − ∞ = ∞`) and the book's extended integral `∫ J dt = ∫ J⁺ dt − ∫ J⁻ dt`
(Eq. (43) of Chapter 7), which is the published `DupacovaWets.Consistency.expect`. -/
noncomputable def H (M : Model S C W) (x : S) (u : C) (J : S → EReal) : EReal :=
  BertsekasShreve.FiniteHorizon.badd (M.g x u) ((M.α : EReal) * DupacovaWets.Consistency.expect (M.t (x, u)) J)

/-- **Definition 8.5** (p. 195). For `J : S → R*`, the operator
`T(J)(x) = inf_{u ∈ U(x)} {g(x, u) + α ∫_S J(x') t(dx' | x, u)}`. -/
noncomputable def T (M : Model S C W) (J : S → EReal) : S → EReal :=
  fun x => ⨅ u ∈ M.U x, M.H x u J

/-- (P) of Section 9.1 (p. 214): `0 ≤ g(x, u)` for every `(x, u) ∈ Γ`. -/
def CaseP (M : Model S C W) : Prop := ∀ x, ∀ u ∈ M.U x, 0 ≤ M.g x u

/-- (N) of Section 9.1 (p. 214): `g(x, u) ≤ 0` for every `(x, u) ∈ Γ`. -/
def CaseN (M : Model S C W) : Prop := ∀ x, ∀ u ∈ M.U x, M.g x u ≤ 0

/-- (D) of Section 9.1 (p. 214): `0 < α < 1`, and for some `b ∈ R`, `−b ≤ g(x, u) ≤ b` for every
`(x, u) ∈ Γ`. (`0 < α` is part of the model.) -/
def CaseD (M : Model S C W) : Prop :=
  M.α < 1 ∧ ∃ b : ℝ, ∀ x, ∀ u ∈ M.U x, -(b : EReal) ≤ M.g x u ∧ M.g x u ≤ (b : EReal)

end Model

end BertsekasShreve.BorelInfinite


