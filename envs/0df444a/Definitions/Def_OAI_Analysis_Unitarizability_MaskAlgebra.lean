-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_MaskAlgebra
-- name    : OAI_Analysis_Unitarizability_MaskAlgebra
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:07:05.680606+00:00
-- url     : https://prove2.me/theorems/85f938c1-156c-48f9-80f9-bbd06ac823e9
-- title:
--   Constant and Boolean-oriented masked operators
-- statement:
--   Notation follows the masked operators: $G$ is a group, $I$ and $K$ are finite sets, $\mathcal H=\ell^2(G;\mathbb{C}^K)$, $v_i\in\mathbb{C}^K$ and $s_i\in G$ for $i\in I$, and $M_{v,s,c}$ is the masked operator $(M_{v,s,c}\xi)(x)=\sum_ic(x,i)\langle v_i,\xi(xs_i)\rangle v_i$ for a coefficient array with $|c(x,i)|\le 1$. For a bit $b$, $[b]$ is $1$ if $b$ is true and $0$ otherwise.
--
--   1. **Constant masked operator.** $A_{v,s}=M_{v,s,1}$:
--   $$(A_{v,s}\,\xi)(x)=\sum_{i\in I}\langle v_i,\xi(xs_i)\rangle\,v_i .$$
--   2. **Boolean masks are admissible.** For every Boolean mask $a:G\times I\to\{\mathrm{true},\mathrm{false}\}$, $|[a(x,i)]|\le 1$ for all $x,i$.
--   3. **Oriented masked operator.** $T_{v,s,a}=M_{v,s,[a]}$:
--   $$(T_{v,s,a}\,\xi)(x)=\sum_{i\in I:\ a(x,i)=\mathrm{true}}\langle v_i,\xi(xs_i)\rangle\,v_i .$$
--
--   The constant operator commutes with left translations, and its block in position $(1,g)$ is the collision kernel $\sum_{i:\,s_i=g}v_iv_i^*$; for unit vectors its kernel energy is at least $|I|$. The oriented operator keeps exactly the edges that the mask assigns to their row endpoints, while $A_{v,s}-T_{v,s,a}$ keeps those assigned to column endpoints. The coboundary of $T$ under the left translation representation $\lambda$, $T-\lambda(g)T\lambda(g)^{-1}$, is again a masked operator, with mask $[a(x,i)]-[a(g^{-1}x,i)]$ supported on the difference sets of $a$, so a sparse mask and a frame bound make it bounded uniformly in $g$. At stage $j$ of the construction, $A_j$ and $T_j$ are these two operators for the words of length $j+1$.
--
--   **Formalization Note** `Masked.constant v s` and `Masked.oriented v s a` are `Masked.operator` with coefficient arrays `fun _ _ => 1` and `fun x i => boolComplex (a x i)`; `bool_mask_norm` supplies the required bound $|c(x,i)|\le 1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/MaskAlgebra.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/MaskAlgebra.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Dixmier mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Countable.Small
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Dixmier
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting
import Definitions.Def_OAI_Analysis_Unitarizability_Regular
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters
import Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters
import Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames
import Definitions.Def_OAI_Analysis_Unitarizability_Frames
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum
import Definitions.Def_OAI_Analysis_Unitarizability_Masked

namespace OAI

/-! Sparse masks yield operator conjugation identities, and the
constant mask has a rank-one collision kernel. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
open scoped ComplexConjugate
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
local instance instDecidableEq_oAI_3 : DecidableEq G := Classical.decEq G
def constant (v : I → Fibre K) (s : I → G) : Space G K →L[ℂ] Space G K :=
  operator v s (fun _ _ => 1) (fun _ _ => by simp)

omit [Group G] [Fintype I] in
theorem bool_mask_norm (a : G → I → Bool) (x : G) (i : I) : ‖boolComplex (a x i)‖ ≤ 1 := by
  cases a x i <;> simp [boolComplex]

def oriented (v : I → Fibre K) (s : I → G) (a : G → I → Bool) : Space G K →L[ℂ] Space G K :=
  operator v s (fun x i => boolComplex (a x i)) (bool_mask_norm a)

end Masked
end Dixmier

end

end OAI


