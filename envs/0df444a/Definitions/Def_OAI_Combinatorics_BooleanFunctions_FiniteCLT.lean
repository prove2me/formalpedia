-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
-- name    : OAI_Combinatorics_BooleanFunctions_FiniteCLT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:23:21.74781+00:00
-- url     : https://prove2.me/theorems/6abde9aa-486e-4f28-8a73-856c28a0fcd0
-- title:
--   Normalized sums on finite product spaces and the uniform probability measure
-- statement:
--   The file introduces the normalized sums to which the central limit theorem is applied, and the uniform measure on a finite set.
--
--   1. **Normalized sum.** For a set $\Lambda$ (carrying a measurable structure that plays no role in the formula), a function $T:\Lambda\to\mathbb{R}$, $n\in\mathbb{N}$ and $x=(x_1,\dots,x_n)\in\Lambda^n$,
--   $$Z^T_n(x)=\frac{1}{\sqrt n}\sum_{i=1}^n T(x_i).$$
--   2. **Uniform measure.** For a finite nonempty measurable space $\Lambda$, the measure $\mathrm{Unif}_\Lambda$ assigning mass $1/|\Lambda|$ to each point, i.e. the measure of the uniform probability mass function on $\Lambda$.
--   3. **Probability instance.** It is recorded that $\mathrm{Unif}_\Lambda$ is a probability measure.
--
--   Under $\mathrm{Unif}_{\Lambda^n}$ the coordinates $x_1,\dots,x_n$ are independent and uniform, so $Z^T_n$ is the normalized sum of $n$ independent copies of $T(X)$ with $X$ uniform on $\Lambda$. If $\mathbb{E}\,T=0$ and $\mathbb{E}\,T^2=1$, the central limit theorem says that $Z^T_n$ converges in distribution to the standard Gaussian; this is how Gaussian behaviour enters statements about finite Boolean cubes, with every normalized sum living on an actual finite product space.
--
--   **Formalization Note** `FiniteCLT.normalizedSum T n` is a function on `Fin n → α`, the inverse of `Real.sqrt n` times the sum; for `n = 0` its value is $0$. `UniformFinite.uniformMeasure α` is `(PMF.uniformOfFintype α).toMeasure`, and `uniformMeasure_probability` is the corresponding `IsProbabilityMeasure` instance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/FiniteCLT.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/FiniteCLT.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SquareRootDegree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection

namespace OAI

open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace SquareRootDegree
namespace FiniteCLT
attribute [local instance] Classical.propDecidable

variable {α : Type*} [MeasurableSpace α]

/-- The normalized sum uses an actual finite product space at every index. -/
def normalizedSum (T : α → ℝ) (n : ℕ) (x : Fin n → α) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ i, T (x i)

end FiniteCLT
end SquareRootDegree

namespace SquareRootDegree
namespace UniformFinite
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
variable {α ι : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

def uniformMeasure (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] : Measure α :=
  (PMF.uniformOfFintype α).toMeasure

instance uniformMeasure_probability : IsProbabilityMeasure (uniformMeasure α) := by
  unfold uniformMeasure; infer_instance

end UniformFinite
end SquareRootDegree

end

end OAI


