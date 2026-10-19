-- Prove2me | Definitions.Def_OAIQWCO000
-- name    : OAIQWCO000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T02:50:36.233216+00:00
-- url     : https://prove2.me/theorems/fbf35c70-f9e4-4bec-a6a5-8a55457681d9
-- title:
--   OpenAI classical O(n) split: definitions bundle 1 (weighted means and the continuous FKG property)
-- statement:
--   The first definitions bundle of the split of OpenAI's proof of exponential decay of spin correlations in two-dimensional classical $O(n)$ models, $n \ge 3$ (`OAI.ClassicalON.main`). It holds the four definitions of the continuous FKG property, from `lean/OAI/Probability/ClassicalON` (OpenAI, *Exponential decay in two-dimensional classical O(n) models*, OpenAI Math Release, September 23, 2026, result family 215, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a:
--
--   - `weightedMean μ w f` $= \int w f\,d\mu \big/ \int w\,d\mu$;
--   - `ContinuousAssociated μ w`: for all continuous, nonnegative, monotone $f, g$, $\mathrm{weightedMean}\ \mu\ w\ f \cdot \mathrm{weightedMean}\ \mu\ w\ g \le \mathrm{weightedMean}\ \mu\ w\ (fg)$;
--   - `LogSupermodular w`: $w(x)\,w(y) \le w(x \sqcap y)\,w(x \sqcup y)$ for all $x, y$ in a lattice;
--   - `ContinuousFKG μ`: `ContinuousAssociated μ w` for every continuous, strictly positive, log-supermodular $w$.
--
--   It is the only bundle the statement `OAI.ClassicalON.continuousFKG_pi` imports. It imports no other bundle.
--
--   Modules: `AssociationCore`, `ProductFKG` (each `.lean` in `lean/OAI/Probability/ClassicalON`).
-- source:
--   OpenAI, Exponential decay in two-dimensional classical O(n) models, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 215; Apache License 2.0); definitions carved from lean/OAI/Probability/ClassicalON at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQW_ClassicalON.AssociationCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ClassicalON

def weightedMean {X : Type uX} [MeasurableSpace X] (μ : Measure X) (w f : X → ℝ) : ℝ :=
  (∫ x,w x*f x ∂μ)/(∫ x,w x ∂μ)

def ContinuousAssociated {X : Type uX} [MeasurableSpace X] [TopologicalSpace X]
    [Preorder X] (μ : Measure X) (w : X → ℝ) : Prop :=
  ∀ f g : X → ℝ, Continuous f → Continuous g → (∀ x,0≤f x) → (∀ x,0≤g x) →
    Monotone f → Monotone g →
    weightedMean μ w f * weightedMean μ w g ≤ weightedMean μ w (fun x => f x*g x)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ProductFKG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section
open MeasureTheory
namespace ClassicalON

def LogSupermodular {X : Type uX} [Lattice X] (w : X → ℝ) : Prop :=
  ∀ x y,w x*w y≤w (x⊓y)*w (x⊔y)

def ContinuousFKG {X : Type uX} [Lattice X] [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) : Prop :=
  ∀ w : X → ℝ,Continuous w → (∀ x,0<w x) → LogSupermodular w → ContinuousAssociated μ w

end ClassicalON

end

end OAI
end


