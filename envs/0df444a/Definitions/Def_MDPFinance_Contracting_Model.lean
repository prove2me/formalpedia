-- Prove2me | Definitions.Def_MDPFinance_Contracting_Model
-- name    : MDPFinance_Contracting_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:40:35.600402+00:00
-- url     : https://prove2.me/theorems/f9b5735c-562c-4915-b7ab-cf3437745a71
-- title:
--   Infinite-horizon stationary Markov Decision Model and its operators (Def. 7.1.1)
-- statement:
--   A stationary Markov Decision Model with infinite horizon consists of the same data $(E,A,D,Q,r,
--   \beta)$ as the finite-horizon models of this book's series (chunk `02a`'s Definition 2.1.1), but
--   with no terminal reward ($g \equiv 0$) and no time index: the same decision rule may be applied
--   at every stage, and the discount $\beta$ is baked directly into the one-stage operator
--   $$
--   Lv(x,a) := r(x,a) + \beta\int v(x')\,Q(dx'|x,a),
--   $$
--   rather than appearing separately as it did in the finite-horizon Bellman recursion. The
--   associated operators $T_fv(x) := Lv(x,f(x))$ and $Tv(x) := \sup_{a\in D(x)} Lv(x,a)$ are the
--   stationary counterparts of chunk `02a`'s time-indexed $T_f^n$, $T_n$, and `T°v(x) := \sup_{a\in
--   D(x)} \beta\int v(x')Q(dx'|x,a)$ is the pure time-shift operator with no reward term, used
--   throughout this chapter to control the tail of the infinite sum.
--
--   **Formalization Note.** Restated (not imported) from chunks `02a`/`02b`'s finite-horizon
--   operators, adapted to drop the time index and bake in $\beta$, per this chunk's own
--   file-ownership boundary.
--
--   **Moderation note.** The structure carries Definition 2.1.1's requirements on the data: $D$ measurable and containing the graph of a measurable map (so $D(x)\neq\emptyset$ and decision rules exist), $Q$ a stochastic (Markov) kernel.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 194, Definition 7.1.1

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Contracting

/-- Definition 7.1.1 (Bäuerle–Rieder, p. 194, PDF 205): a stationary Markov Decision Model with
infinite horizon, data `(E,A,D,Q,r,β)` as in Definition 2.1.1 (`D` measurable containing the graph
of a measurable map, `Q` a stochastic kernel, `r` measurable), no terminal reward (`g ≡ 0`). The
operators below drop the time index `n` and bake the discount `β` directly into `L`, unlike the
finite-horizon series' own time-indexed operators. -/
structure MarkovDecisionModel (E A : Type*) [MeasurableSpace E] [MeasurableSpace A] where
  D : Set (E × A)
  hD_meas : MeasurableSet D
  /-- `D` contains the graph of a measurable map (Definition 2.1.1), so `D(x) ≠ ∅`. -/
  hD_graph : ∃ f : E → A, Measurable f ∧ ∀ x, (x, f x) ∈ D
  Q : Kernel (E × A) E
  isMarkovQ : IsMarkovKernel Q
  r : E × A → ℝ
  hr_meas : Measurable r
  β : ℝ
  hβ0 : 0 < β
  hβ1 : β ≤ 1

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- `D(x) := {a ∈ A | (x,a) ∈ D}`. -/
def MarkovDecisionModel.Dx (M : MarkovDecisionModel E A) (x : E) : Set A :=
  {a | (x, a) ∈ M.D}

/-- `IM(E)`: measurable `E → [-∞,∞)`-valued functions (Bäuerle–Rieder p. 19, PDF 34), restated. -/
def IM (E : Type*) [MeasurableSpace E] : Set (E → EReal) :=
  {v | Measurable v ∧ ∀ x, v x ≠ ⊤}

/-- The extended-real integral, restated from `MDPFinance.Bellman.erealIntegral` (chunk `02a`). -/
noncomputable def erealIntegral (μ : Measure E) (v : E → EReal) : EReal :=
  (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal))

/-- `f` is a decision rule for `D`: measurable, `f(x) ∈ D(x)`. -/
def IsDecisionRuleOf (M : MarkovDecisionModel E A) (f : E → A) : Prop :=
  Measurable f ∧ ∀ x, (x, f x) ∈ M.D

/-- `Lv(x,a) := r(x,a) + β ∫ v(x') Q(dx'|x,a)` (Bäuerle–Rieder, p. 197, PDF 209, stationary,
discount baked in). -/
noncomputable def L (M : MarkovDecisionModel E A) (v : E → EReal) (xa : E × A) : EReal :=
  (M.r xa : EReal) + (M.β : EReal) * erealIntegral (M.Q xa) v

/-- `T_f v(x) := Lv(x,f(x))`. -/
noncomputable def Tf (M : MarkovDecisionModel E A) (f : E → A) (v : E → EReal) (x : E) : EReal :=
  L M v (x, f x)

/-- `Tv(x) := sup_{a ∈ D(x)} Lv(x,a)`. -/
noncomputable def T (M : MarkovDecisionModel E A) (v : E → EReal) (x : E) : EReal :=
  ⨆ a ∈ M.Dx x, L M v (x, a)

/-- `T°v(x) := sup_{a ∈ D(x)} β ∫ v(x') Q(dx'|x,a)` (Bäuerle–Rieder, Definition 7.1.2, p. 195,
PDF 206): the pure time-shift operator, no reward term, distinct from `T`. -/
noncomputable def Tcirc (M : MarkovDecisionModel E A) (v : E → EReal) (x : E) : EReal :=
  ⨆ a ∈ M.Dx x, (M.β : EReal) * erealIntegral (M.Q (x, a)) v

/-- `f` is a maximizer of `v` (Def. 2.3.6, restated): a decision rule realizing `T`'s supremum at
every state. -/
def IsMaximizerOf (M : MarkovDecisionModel E A) (v : E → EReal) (f : E → A) : Prop :=
  IsDecisionRuleOf M f ∧ (fun x => L M v (x, f x)) = T M v

end MDPFinance.Contracting


