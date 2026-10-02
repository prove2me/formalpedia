-- Prove2me | Definitions.Def_MDPFinance_LPDuality_Model
-- name    : MDPFinance_LPDuality_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:49:03.392159+00:00
-- url     : https://prove2.me/theorems/c2e6fc64-acdd-4761-ac67-020c1e824df6
-- title:
--   Infinite-horizon Markov Decision Model and operators (restated from chunk 07a)
-- statement:
--   This restates chunk `07a`'s core infinite-horizon vocabulary in this chunk's own namespace, per
--   this series' file-ownership convention: the model data $(D,Q,r,\beta)$, the operators $L$, $T_f$,
--   $T$, $T_\circ$, and the notion of a decision rule/maximizer. §7.4-7.5 of the book build directly
--   on this apparatus, applying it now to *positive* models (§7.4, where the reward's negative part
--   is what must be controlled) and to the computational methods of §7.5 (policy improvement, linear
--   programming, discretization).
--
--   **Moderation note.** As in chunk `07a`: $D$ measurable containing the graph of a measurable map, $Q$ a stochastic kernel (Definition 2.1.1).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 194, Definition 7.1.1 (restated for this chunk)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.LPDuality

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

end MDPFinance.LPDuality


