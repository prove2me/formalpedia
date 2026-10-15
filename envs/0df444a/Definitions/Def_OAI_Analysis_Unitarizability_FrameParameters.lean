-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters
-- name    : OAI_Analysis_Unitarizability_FrameParameters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:58:41.424767+00:00
-- url     : https://prove2.me/theorems/50e4959d-09e3-4e17-b4c6-84872f626389
-- title:
--   Frame dimension $\lceil 2r\log(2n)\rceil$ and subfamily size $\min(2r,n)$
-- statement:
--   For natural numbers $n$ (the number of vectors of a frame) and $r$ (a capacity), with $\log$ the natural logarithm and $\lceil t\rceil_+$ the natural-number ceiling:
--
--   1. **Frame dimension.**
--   $$k(n,r)=\bigl\lceil 2r\log(2n)\bigr\rceil_+ .$$
--   2. **Subfamily size.**
--   $$p(n,r)=\min(2r,\,n).$$
--
--   These are the parameters of the frame lemma: for $n\ge 2$ and $r\ge 1$ there are $n$ unit vectors in $\mathbb{C}^{k(n,r)}$ such that every subfamily of at most $p(n,r)$ of them has synthesis norm at most $10$. The module checks the elementary arithmetic behind the probabilistic proof: for $n\ge 2$ and $r\ge 1$ one has $1\le k$, $p\le k$ and $p\log n\le k$, which makes the union bound $2n^{p}\,9^{k+p}\,e^{-25k/2}$ strictly smaller than $1$. The subfamily size $\min(2r,n)$ matches the bound on the difference sets of a mask with capacity $r$, and at stage $\ell$ of the construction $k(d^\ell,r_\ell)$ is the fibre dimension $k_\ell$.
--
--   **Formalization Note** `FrameParameters.dimension n r` is `⌈2 * r * Real.log (2 * n)⌉₊` and `FrameParameters.subfamilySize n r` is `min (2*r) n`; for $n=0$ Lean's convention $\log 0=0$ gives dimension $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/FrameParameters.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/FrameParameters.lean by skeleton subtraction
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

namespace OAI

/-! Ceiling dimensions and finite union-bound arithmetic for frames. -/
noncomputable section
namespace Dixmier
namespace FrameParameters

def dimension (n r : ℕ) : ℕ := ⌈2 * (r : ℝ) * Real.log (2 * (n : ℝ))⌉₊
def subfamilySize (n r : ℕ) : ℕ := min (2*r) n

end FrameParameters
end Dixmier

end

end OAI


