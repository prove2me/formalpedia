-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum
-- name    : OAI_Analysis_Unitarizability_HilbertSum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:03:45.306882+00:00
-- url     : https://prove2.me/theorems/ef3bd5e9-7cd9-4428-abd8-174f0654e0c3
-- title:
--   Hilbert direct sums of bounded operators, isometric representations and cocycles
-- statement:
--   Let $I$ be an index set and $(E_i)_{i\in I}$ a family of complex inner product spaces. Their Hilbert direct sum is
--   $$\bigoplus_{i\in I}E_i=\Bigl\{x=(x_i)_{i\in I}:\ x_i\in E_i,\ \sum_{i\in I}\|x_i\|^2<\infty\Bigr\},\qquad \|x\|^2=\sum_i\|x_i\|^2 .$$
--
--   1. **Coordinate maps.** The inclusion $\iota_i:E_i\to\bigoplus E$ (the family equal to $v$ in coordinate $i$ and $0$ elsewhere) and the evaluation $P_i:\bigoplus E\to E_i$, $x\mapsto x_i$.
--   2. **Bounded direct sum of operators.** Given $\kappa\ge 0$ and bounded operators $T_i$ on $E_i$ with $\|T_i\|\le\kappa$ for all $i$, the operator $\bigoplus_iT_i$ on $\bigoplus E$ given by $\bigl((\bigoplus_iT_i)x\bigr)_i=T_ix_i$.
--   3. **Isometric representations are contractions.** For a group $G$ and a homomorphism $U$ from $G$ into the bounded operators on $E_i$ with $\|U(g)v\|=\|v\|$ for all $g,v$, one has $\|U(g)\|\le 1$ for all $g$ (a lemma used for the next definition).
--   4. **Direct sum representation.** For homomorphisms $U_i:G\to B(E_i)$ that are isometric, $\|U_i(g)v\|=\|v\|$, the homomorphism $U=\bigoplus_iU_i:G\to B(\bigoplus E)$ with $(U(g)x)_i=U_i(g)x_i$.
--   5. **Direct sum cocycle.** For maps $D_i:G\to B(E_i)$ with $\|D_i(g)\|\le\kappa$ for all $i$ and $g$ (where $\kappa\ge 0$), the map $g\mapsto D(g)=\bigoplus_iD_i(g)$.
--   6. **Diagonal compression.** For $B\in B(\bigoplus E)$ and $i\in I$, the operator $B_{ii}=P_iB\,\iota_i$ on $E_i$.
--
--   Only uniformly bounded data are summed: the stage cocycles $D_i=\delta_{U_i}T_i$ are bounded uniformly in $i$, while the implementing operators $T_i$ need not be and are never assembled into an operator on the sum. The compression goes the other way: if $D=\bigoplus_iD_i$ were the coboundary of a bounded operator $B$ for $U$, then each $D_i$ would be the coboundary of $B_{ii}$ for $U_i$, with $\|B_{ii}\|\le\|B\|$, and this is what the direct-sum obstruction contradicts.
--
--   **Formalization Note** The sum is `lp E 2` (`HilbertSum.Space E`) and `boundedSum` is `lp.mapCLM`; the bound hypotheses are explicit arguments of `boundedSum`, `representation` and `cocycle`. The evaluation lemmas give the coordinate formulas, and `unitary_bound` is item 3.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/HilbertSum.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/HilbertSum.lean by skeleton subtraction
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

namespace OAI

/-! Uniformly bounded Hilbert direct sums. The component implementers
are never summed and need not be uniformly bounded. -/
noncomputable section
namespace Dixmier
namespace HilbertSum
variable {G I : Type*} [Group G] {E : I → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
local instance instDecidableEq_oAI : DecidableEq I := Classical.decEq I
abbrev Space (E : I → Type*) [∀ i, NormedAddCommGroup (E i)] := lp E 2

def inclusion (i : I) : E i →L[ℂ] Space E := lp.singleContinuousLinearMap ℂ E 2 i

def evaluation (i : I) : Space E →L[ℂ] E i := lp.evalCLM ℂ E 2 i

@[simp] theorem inclusion_apply (i : I) (x : E i) : inclusion i x = lp.single 2 i x := rfl
@[simp] theorem evaluation_apply (i : I) (x : Space E) : evaluation i x = x i := rfl

def boundedSum (T : ∀ i, E i →L[ℂ] E i) {κ : ℝ} (hκ : 0 ≤ κ) (hT : ∀ i, ‖T i‖ ≤ κ) :
    Space E →L[ℂ] Space E := lp.mapCLM 2 T hκ hT

@[simp] theorem boundedSum_apply (T : ∀ i, E i →L[ℂ] E i) {κ : ℝ}
    (hκ : 0 ≤ κ) (hT : ∀ i, ‖T i‖ ≤ κ) (x : Space E) (i : I) :
    boundedSum T hκ hT x i = T i (x i) := rfl

theorem unitary_bound {index : I} (U : G →* (E index →L[ℂ] E index))
    (hU : ∀ g x, ‖U g x‖ = ‖x‖) (g : G) :
    ‖U g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp [hU]

def representation (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) : G →* (Space E →L[ℂ] Space E) where
  toFun g := boundedSum (fun i => U i g) zero_le_one (fun i => unitary_bound (U i) (hU i) g)
  map_one' := by ext x i; change U i 1 (x i) = x i; simp
  map_mul' g h := by
    ext x i
    change U i (g*h) (x i) = U i g (U i h (x i))
    rw [map_mul]; rfl

@[simp] theorem representation_apply (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (g : G) (x : Space E) (i : I) :
    representation U hU g x i = U i g (x i) := rfl

def cocycle (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (g : G) : Space E →L[ℂ] Space E :=
  boundedSum (fun i => D i g) hκ (fun i => hb i g)

omit [Group G] in
@[simp] theorem cocycle_apply (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (g : G) (x : Space E) (i : I) :
    cocycle D hκ hb g x i = D i g (x i) := rfl

def compression (B : Space E →L[ℂ] Space E) (i : I) : E i →L[ℂ] E i :=
  (evaluation i).comp (B.comp (inclusion i))

end HilbertSum
end Dixmier

end

end OAI


