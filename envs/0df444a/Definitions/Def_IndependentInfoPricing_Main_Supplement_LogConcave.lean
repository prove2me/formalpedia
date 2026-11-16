-- Prove2me | Definitions.Def_IndependentInfoPricing_Main_Supplement_LogConcave
-- name    : IndependentInfoPricing_Main_Supplement_LogConcave
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:48:27.113202+00:00
-- url     : https://prove2.me/theorems/adcde0b5-f27a-4958-a879-191a56a51cff
-- title:
--   Log-concave densities and the conditional magnitudes of §4.3
-- statement:
--   A law on $\mathbb R$ or $\mathbb R^Q$ has a **log-concave density** when some measurable density version $f\ge0$ satisfies
--   $$f(x)^a f(y)^b\le f(ax+by)\qquad(a,b\ge0,\ a+b=1)$$
--   everywhere (the published `LogConcaveOn` on the whole space, which permits zeros). A §4.3 marginal additionally has its density continuously differentiable on the interior of its support.
--
--   For a law $F$ of $v\in\mathbb R^Q$ and an event $C$ with $F(C)>0$, the **conditional law** is $F(\cdot\mid C)=F(C)^{-1}F(\cdot\cap C)$. With $\Sigma(v)=\sum_i v_i$, the **conditional magnitudes** are
--   $$V_i^+=\mathcal L\bigl(v_i\mid \Sigma(v)<0,\ v_i>0\bigr),\qquad V_i^-=\mathcal L\bigl(-v_i\mid \Sigma(v)>0,\ v_i<0\bigr).$$
--
--   These objects are used by Lemma 4.9, Lemma 4.10 and Theorem 4.7.
--
--   **Formalization Note** The conditional laws are meaningful only when the conditioning event has positive probability; every statement assumes that.
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), §4.3, printed p.30–32 (PDF p.32–34); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Laws
import Definitions.Def_LogConcaveOn

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- A law on a real vector space `E` (here `ℝ` or `ℝ^Q`) with a log-concave Lebesgue density:
some measurable density version `f ≥ 0` is log-concave on all of `E` in the zero-permitting
power form (published `ConvexOptimization.LogConcaveOn`). -/
def LogConcaveDensity {E : Type} [AddCommMonoid E] [SMul ℝ E] [MeasureSpace E]
    (D : Measure E) : Prop :=
  ∃ f : E → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
    D = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
    ConvexOptimization.LogConcaveOn Set.univ f

/-- §4.3 marginal: a law on `ℝ` with a density version that is log-concave on `ℝ` and
continuously differentiable on the interior of the support. -/
def SmoothLogConcave (D : Measure ℝ) : Prop :=
  ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
    D = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
    ContDiffOn ℝ 1 f (interior (lawSupport D)) ∧
    ConvexOptimization.LogConcaveOn Set.univ f

/-- Conditional law of `F` given the event `C` (meaningful when `0 < F C`). -/
def conditionOn {α : Type} [MeasurableSpace α] (F : Measure α) (C : Set α) : Measure α :=
  (F C)⁻¹ • F.restrict C

/-- `V_i⁺ = L(v_i | Σ(v) < 0, v_i > 0)`. -/
def plusMagnitudeLaw {Q : ℕ} (F : Measure (Values (Fin Q))) (i : Fin Q) : Measure ℝ :=
  Measure.map (fun v : Values (Fin Q) => v i) (conditionOn F {v | ∑ j, v j < 0 ∧ 0 < v i})

/-- `V_i⁻ = L(−v_i | Σ(v) > 0, v_i < 0)`. -/
def minusMagnitudeLaw {Q : ℕ} (F : Measure (Values (Fin Q))) (i : Fin Q) : Measure ℝ :=
  Measure.map (fun v : Values (Fin Q) => -v i) (conditionOn F {v | 0 < ∑ j, v j ∧ v i < 0})

end IndependentInfoPricing.Main.Supplement


