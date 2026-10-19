-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
-- name    : OAI_Probability_CriticalZ3_Conditioning
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:06:29.914703+00:00
-- url     : https://prove2.me/theorems/8e08442f-efad-4691-b56f-3b303d8673ce
-- title:
--   Revealed bits and conditional product laws
-- statement:
--   Notation for conditioning a product Bernoulli law on revealed values of finitely many bits $J$.
--
--   1. **Replacement.** $\mathrm{replace}_J(\xi,\omega)$ takes the values of $\xi$ on $J$ and of $\omega$ elsewhere. The pattern of $\xi$ on $J$ is the cylinder $\{\omega:\ \omega_e=\xi_e\ (e\in J)\}$, and the all-$b$ cylinder fixes every bit of $J$ to $b$.
--   2. **Fixed parameters.** Conditioning on the revealed values is described by the parameters
--   $$
--   p'_e=\begin{cases}1&e\in J,\ \xi_e=1,\\0&e\in J,\ \xi_e=0,\\ p_e&e\notin J,\end{cases}
--   $$
--   under which the unrevealed bits keep their original law.
--   3. **Bit probabilities.** The probability of value $b$ for a bit of parameter $p$ is $p$ if $b=1$ and $1-p$ otherwise, and each bit generates its own $\sigma$-algebra.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Conditioning.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Conditioning.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CriticalZ3 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials

-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uF

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

/-! The exact revealed-history law used by the adaptive queue.  In particular,
classifications depending only on revealed values do not change fresh bits. -/
namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

noncomputable def replace (J : Finset E) (ξ ω : E → Bool) : E → Bool :=
  fun e => if e ∈ J then ξ e else ω e

noncomputable def fixedParameter (p : E → Set.Icc (0 : ℝ) 1)
    (J : Finset E) (ξ : E → Bool) : E → Set.Icc (0 : ℝ) 1 :=
  fun e => if e ∈ J then if ξ e = true then 1 else 0 else p e

def pattern (J : Finset E) (ξ : E → Bool) : Set (E → Bool) :=
  {ω | ∀ e ∈ J, ω e = ξ e}

 abbrev bitSigma (e : E) : MeasurableSpace (E → Bool) :=
  MeasurableSpace.comap (fun ω => ω e) inferInstance

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E I : Type}

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

noncomputable def bitProbability (p : Set.Icc (0 : ℝ) 1) (b : Bool) : ℝ :=
  if b then p else 1-(p : ℝ)

def allValue (J : Finset E) (b : Bool) : Set (E → Bool) := {ω | ∀ e ∈ J, ω e = b}

variable [Countable E]

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

end InfiniteConditioning

end OAI


