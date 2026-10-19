-- Prove2me | Definitions.Def_OAIQWCO001
-- name    : OAIQWCO001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T02:52:10.254156+00:00
-- url     : https://prove2.me/theorems/6e0ff45f-96ba-46f4-bba9-c2c43fec03be
-- title:
--   OpenAI classical O(n) split: definitions bundle 2 (the Ising model on a finite graph)
-- statement:
--   The second definitions bundle of the split of OpenAI's proof of exponential decay of spin correlations in two-dimensional classical $O(n)$ models, $n \ge 3$ (`OAI.ClassicalON.main`). It holds the seven definitions of OpenAI's Ising model, from `lean/OAI/Probability/ClassicalON` (OpenAI, *Exponential decay in two-dimensional classical O(n) models*, OpenAI Math Release, September 23, 2026, result family 215, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a:
--
--   - `exponentialMean μ H f` $=$ `weightedMean μ (fun x => exp (H x)) f`;
--   - `signValue t` $= 1$ if $t$ is true and $-1$ otherwise; `signLaw` $= \tfrac12\cdot$ counting measure on `Bool`; `isingReference` $=$ the product of `signLaw` over the vertices;
--   - for edge endpoints `left right : E → V`: `isingEnergy left right e s` $= \mathrm{signValue}(s(\mathrm{left}\,e))\cdot\mathrm{signValue}(s(\mathrm{right}\,e))$, `isingHamiltonian left right b s` $= \sum_e b(e)\,\mathrm{isingEnergy}\ e\ s$, and `isingMean left right b f` $=$ `exponentialMean isingReference (isingHamiltonian left right b) f`.
--
--   It is the only bundle the statements `OAI.ClassicalON.ising_edge_covariance_nonneg` and `OAI.ClassicalON.ising_edge_mean_nonneg` import. It imports the bundle `OAIQWCO000` (for `weightedMean`).
--
--   Modules: `GibbsDerivative`, `IsingReference`, `IsingGinibre` (each `.lean` in `lean/OAI/Probability/ClassicalON`).
-- source:
--   OpenAI, Exponential decay in two-dimensional classical O(n) models, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 215; Apache License 2.0); definitions carved from lean/OAI/Probability/ClassicalON at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWCO000

section
-- module Solutions.OAIQW_ClassicalON.GibbsDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section
open MeasureTheory
namespace ClassicalON

section
variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def exponentialMean (H f : X → ℝ) : ℝ := weightedMean μ (fun x => Real.exp (H x)) f

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.IsingReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ClassicalON

def signValue (t : Bool) : ℝ := if t then 1 else -1

def signLaw : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

variable {V : Type uV} [Fintype V]

def isingReference : Measure (V → Bool) := Measure.pi (fun _ => signLaw)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.IsingGinibre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def isingEnergy (left right : E → V) (e : E) (s : V → Bool) : ℝ :=
  signValue (s (left e))*signValue (s (right e))

def isingHamiltonian (left right : E → V) (b : E → ℝ) (s : V → Bool) : ℝ :=
  ∑ e,b e*isingEnergy left right e s

def isingMean (left right : E → V) (b : E → ℝ) (f : (V → Bool) → ℝ) : ℝ :=
  exponentialMean isingReference (isingHamiltonian left right b) f

end ClassicalON

end

end OAI
end


