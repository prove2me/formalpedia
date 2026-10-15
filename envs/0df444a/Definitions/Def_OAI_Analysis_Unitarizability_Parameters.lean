-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_Parameters
-- name    : OAI_Analysis_Unitarizability_Parameters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:57:53.967233+00:00
-- url     : https://prove2.me/theorems/f0b096ed-febb-4e7a-92a8-3e7b4e6595b2
-- title:
--   Endpoint capacity $\lceil d^\ell\rho^\ell\rceil$ and fibre dimension $\lceil 2r_\ell\log(2d^\ell)\rceil$
-- statement:
--   Let $d\in\mathbb{N}$, $\rho\in\mathbb{R}$ and $\ell\in\mathbb{N}$ (a word length). Write $\lceil t\rceil_+$ for the natural-number ceiling of a real number $t$, the least natural number $\ge t$ (so $\lceil t\rceil_+=0$ for $t\le 0$), and $\log$ for the natural logarithm.
--
--   1. **Endpoint capacity.**
--   $$r_\ell=r(d,\rho,\ell)=\bigl\lceil d^{\ell}\rho^{\ell}\bigr\rceil_+ .$$
--   2. **Fibre dimension.**
--   $$k_\ell=k(d,\rho,\ell)=\bigl\lceil 2\,r_\ell\,\log(2d^{\ell})\bigr\rceil_+ .$$
--
--   In the construction, $d=|S|\ge 2$ is the size of a finite set $S\ni 1$ whose normalized right regular average has norm at most $\rho$, with $0<\rho<1$ (such $S$ exists for a non-amenable group). The labels at stage $\ell$ are the $d^\ell$ words of length $\ell$; $r_\ell$ is the capacity of a sparse mask for those words, and $k_\ell$ is the dimension of the space $\mathbb{C}^{k_\ell}$ carrying $d^\ell$ unit frame vectors with bounds on subfamilies of size $\min(2r_\ell,d^\ell)$. The module shows that both numbers are positive when $d\ge 2$ and $\rho>0$, and that $k_\ell/d^\ell\to 0$ when $d\ge 2$ and $0\le\rho<1$, so a kernel energy of at least $d^\ell$ at stage $\ell$ is unbounded relative to the fibre dimension.
--
--   **Formalization Note** `endpointCapacity d ρ ℓ` and `fiberDimension d ρ ℓ` use `Nat.ceil` and `Real.log`; Lean's convention $\log 0=0$ only matters in the degenerate case $d=0$, $\ell\ge 1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Parameters.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Parameters.lean by skeleton subtraction
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

namespace OAI

/-! Ceiling parameters and dimension-ratio asymptotics. -/
noncomputable section
namespace Dixmier
open Filter Topology

def endpointCapacity (d : ℕ) (ρ : ℝ) (ℓ : ℕ) : ℕ := ⌈(d : ℝ)^ℓ * ρ^ℓ⌉₊
def fiberDimension (d : ℕ) (ρ : ℝ) (ℓ : ℕ) : ℕ :=
  ⌈2 * (endpointCapacity d ρ ℓ : ℝ) * Real.log (2 * (d : ℝ)^ℓ)⌉₊

end Dixmier

end

end OAI


