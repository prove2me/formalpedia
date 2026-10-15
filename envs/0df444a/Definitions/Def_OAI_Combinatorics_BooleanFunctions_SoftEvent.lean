-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_SoftEvent
-- name    : OAI_Combinatorics_BooleanFunctions_SoftEvent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:31:47.221721+00:00
-- url     : https://prove2.me/theorems/8906927f-732d-4ed2-a957-f5ff0ee2601e
-- title:
--   Soft events and the deficit of a constant predictor for a sum of independent values
-- statement:
--   Let $\Lambda$ be a finite nonempty set with the uniform average $\mathbb{E}$, $I$ a finite index set, and $T:\Lambda\to\mathbb{R}$. Points of $\Lambda\times\Lambda^I$ are written $(x_0,(x_j)_{j\in I})$ and averaged uniformly, so that $x_0$ and the $x_j$ are independent uniform elements of $\Lambda$.
--
--   1. **Raw moments.** For weights $w_i:\Lambda\to\mathbb{R}$ and $k\in\{0,1,2\}$, $l_{k,i}=\mathbb{E}_a\big[w_i(a)\,T(a)^k\big]$.
--   2. **Removing one weight.** $w^{(i)}$ is the family with $w^{(i)}_i\equiv1$ and $w^{(i)}_j=w_j$ for $j\neq i$.
--   3. **Soft weight.** For selector weights $s_i$ and leaf weights $w_j$ on $\Lambda$,
--   $$a_{s,w}(x_0,x)=\sum_{i\in I}s_i(x_0)\prod_{j\neq i}w_j(x_j)-\prod_{j\in I}w_j(x_j).$$
--   4. **Deficit.** For $b\in\mathbb{R}$ and a weight $a$ on $\Lambda\times\Lambda^I$,
--   $$\operatorname{def}(T,b,a)=\mathbb{E}_{(x_0,x)}\Big[a(x_0,x)\Big(1-\Big(T(x_0)+\sum_{j\in I}T(x_j)-b\Big)^2\Big)\Big].$$
--
--   If $\sum_is_i\equiv1$, the soft weight equals $\sum_is_i(x_0)\big(1-w_i(x_i)\big)\prod_{j\neq i}w_j(x_j)$, the probability of the soft event in which the selector, reading $x_0$, picks a leaf $i$, leaf $i$ fails its test, and every other leaf passes. For a $0/1$ weight $a=\mathbf 1_A$, the deficit measures, on the event $A$, how far the squared error of the constant prediction $b$ for the total sum falls below $1$; a positive deficit is exactly what one amplification step converts into extra variance.
--
--   **Formalization Note** The Lean names are `SoftEvent.rawMoments`, `without`, `softWeight` and `deficit`; averages are the project's uniform `average` over `α × (ι → α)` and moment orders are `Fin 3`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/SoftEvent.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/SoftEvent.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SquareRootDegree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_MomentTransfer

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace SoftEvent
attribute [local instance] Classical.propDecidable
-- [generator] trimmed: open FiniteMoments MomentTransfer
open MomentTransfer
variable {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]

def rawMoments (T : α → ℝ) (w : ι → α → ℝ) (k : Fin 3) (i : ι) : ℝ :=
  average (fun a => w i a*(T a)^(k:ℕ))

def without (w : ι → α → ℝ) (i j : ι) (a : α) : ℝ := if j = i then 1 else w j a

def softWeight (s w : ι → α → ℝ) (x : α × (ι → α)) : ℝ :=
  (∑ i, s i x.1 * ∏ j ∈ Finset.univ.erase i, w j (x.2 j)) - ∏ j, w j (x.2 j)

def deficit (T : α → ℝ) (b : ℝ) (a : α × (ι → α) → ℝ) : ℝ :=
  average (fun x => a x*(1-(T x.1+∑ j, T (x.2 j)-b)^2))

end SoftEvent
end SquareRootDegree

end

end OAI


