-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_Switching
-- name    : OAI_Combinatorics_BooleanFunctions_Switching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:33:54.344305+00:00
-- url     : https://prove2.me/theorems/1c078bfc-b716-4033-a28e-2b0692cbf742
-- title:
--   Switching observations: reveal a spare coordinate when an event occurs
-- statement:
--   Let $\Lambda$ (inputs) and $B$ (labels) be sets and $I$ a finite index set.
--
--   1. **Event space and full space.** $E(\Lambda,I)=\Lambda\times\Lambda^I$, with points $(x_0,(x_i)_{i\in I})$, and $\mathrm{Full}(\Lambda,I)=E(\Lambda,I)\times\Lambda$, with points $(z,x_\ast)$, where $x_\ast$ is a spare coordinate.
--   2. **Old and total sums.** For $T:\Lambda\to\mathbb{R}$, the old sum $\mathrm{old}_T(x_0,x)=T(x_0)+\sum_iT(x_i)$ on $E$, and the total sum $\mathrm{old}_T(z)+T(x_\ast)$ on $\mathrm{Full}$.
--   3. **Old labels.** For $F:\Lambda\to B$, $\mathrm{lab}_F(x_0,x)=\big(F(x_0),(F(x_i))_{i\in I}\big)\in E(B,I)$.
--   4. **Switched observation.** For an event $A$ on label tuples in $E(B,I)$,
--   $$\mathrm{obs}_{F,A}(z,x_\ast)=\begin{cases}\mathrm{inr}\,F(x_\ast)&\text{if }\mathrm{lab}_F(z)\in A,\\ \mathrm{inl}\,\mathrm{lab}_F(z)&\text{otherwise,}\end{cases}$$
--   with values in the disjoint union $E(B,I)\sqcup B$: when the old labels fall in $A$ only the label of the spare coordinate is revealed, and otherwise all old labels are revealed.
--   5. **Predictor.** For $t:B\to\mathbb{R}$ and $b\in\mathbb{R}$, the function on $E(B,I)\sqcup B$ equal to $t(y_0)+\sum_it(y_i)$ at $\mathrm{inl}(y_0,y)$ and to $b+t(y)$ at $\mathrm{inr}\,y$.
--   6. **Slots.** $\mathrm{Slots}(I)=I\sqcup\{\mathrm{sel},\ast\}$ (two extra slots), and the bijection $\Lambda^{\mathrm{Slots}(I)}\to\mathrm{Full}(\Lambda,I)$ sending $f$ to $\big((f(\mathrm{sel}),(f(i))_{i\in I}),f(\ast)\big)$.
--
--   When $T=t\circ F$, the predictor applied to the switched observation estimates the total sum: off $A$ it misses only the spare term $T(x_\ast)$, and on $A$ it misses only the deviation of the old sum from $b$. This is the mechanism by which an observation trades information about old coordinates (already predictable on $A$) for information about a fresh coordinate, increasing the variance of its score.
--
--   **Formalization Note** The Lean names are `EventSpace` and `FullSpace` (abbreviations for the products), `oldSum`, `totalSum`, `oldLabels`, `observation` with values in `EventSpace β ι ⊕ β`, `predictor` (via `Sum.elim`), `Slots ι := Option (Option ι)`, where `some none` is the slot written sel above, `some (some i)` is slot `i` and `none` is the spare slot, and `fullEquiv`. The event `A` is a predicate on `EventSpace β ι`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Switching.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Switching.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SoftEvent

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Switching
attribute [local instance] Classical.propDecidable
variable {α β ι : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype ι] [DecidableEq ι]

abbrev EventSpace (α ι : Type*) := α × (ι → α)
abbrev FullSpace (α ι : Type*) := EventSpace α ι × α

def oldSum (T : α → ℝ) (x : EventSpace α ι) : ℝ := T x.1 + ∑ i, T (x.2 i)
def totalSum (T : α → ℝ) (x : FullSpace α ι) : ℝ := oldSum T x.1 + T x.2
def oldLabels (F : α → β) (x : EventSpace α ι) : EventSpace β ι :=
  (F x.1,fun i => F (x.2 i))
def observation (F : α → β) (A : EventSpace β ι → Prop) (x : FullSpace α ι) :
    EventSpace β ι ⊕ β :=
  if A (oldLabels F x.1) then Sum.inr (F x.2) else Sum.inl (oldLabels F x.1)
def predictor (t : β → ℝ) (b : ℝ) : EventSpace β ι ⊕ β → ℝ :=
  Sum.elim (oldSum t) (fun y => b+t y)

end Switching
end SquareRootDegree

namespace SquareRootDegree
namespace Switching
attribute [local instance] Classical.propDecidable
variable {α β ι : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype ι]

abbrev Slots (ι : Type*) := Option (Option ι)

def fullEquiv (α ι : Type*) : (Slots ι → α) ≃ FullSpace α ι where
  toFun f := ((f (some none), fun i => f (some (some i))),f none)
  invFun x j := match j with
    | none => x.2
    | some none => x.1.1
    | some (some i) => x.1.2 i
  left_inv f := by funext j; cases j with | none => rfl | some j => cases j <;> rfl
  right_inv _ := rfl

end Switching
end SquareRootDegree

namespace SquareRootDegree
namespace Switching
attribute [local instance] Classical.propDecidable
variable {α β ι : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype ι] [DecidableEq ι]

end Switching
end SquareRootDegree

end

end OAI


