-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost
-- name    : OAI_Combinatorics_EuclideanRamsey_NormalCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:47:25.065338+00:00
-- url     : https://prove2.me/theorems/f6b59e5e-69fa-43a7-b4d9-cdbeabe8cefc
-- title:
--   Orbit relation, conjugation-invariant costs on a subgroup, and multiplicative orbit averages
-- statement:
--   Let $G$ and $H$ be groups and let $H$ act on a set $X$.
--
--   1. **Same orbit.** Points $x,y\in X$ lie in the same orbit if $hx=y$ for some $h\in H$.
--   2. **Normal cost on a subgroup.** For a subgroup $L\le G$, a *normal cost* on $L$ is a function $\gamma:G\to\mathbb{R}$ such that $\gamma(g)\ge 0$ for all $g\in G$, $\gamma(1)=0$, and
--   $$\gamma(g^{-1})=\gamma(g),\qquad\gamma(kgk^{-1})=\gamma(g),\qquad\gamma(gh)\le\gamma(g)+\gamma(h)\qquad(g,h\in L,\ k\in G).$$
--   Thus, on $L$, $\gamma$ is a length function that is invariant under conjugation by arbitrary elements of $G$.
--   3. **Enumeration of a finite group.** For finite $H$, a fixed list $(h_1,\dots,h_{|H|})$ containing every element of $H$ exactly once.
--   4. **Orbit average.** For finite $H$ and a function $w:X\to G$, the *orbit average* is the ordered product along this enumeration,
--   $$\bar w(x)=\prod_{t=1}^{|H|}w(h_tx)=w(h_1x)\,w(h_2x)\cdots w(h_{|H|}x)\qquad(x\in X).$$
--
--   In a nonabelian group the arithmetic mean over an orbit is replaced by this product. If $N$ is a normal subgroup, $w(hx)\in N$ for all $h\in H$, and $x,y$ lie in the same orbit, then the same factors occur in $\bar w(x)$ and $\bar w(y)$ in permuted orders, so $\bar w(x)\bar w(y)^{-1}$ lies in the commutator subgroup $[N,N]$. Repeated averaging thus pushes orbit-wise differences down the derived series, while a normal cost controls the length of the products that arise.
--
--   **Formalization Note** `SameOrbit x y` is `∃ h : H, h • x = y`. `NormalCost L` is a structure with fields `cost`, `nonneg`, `one`, `inv`, `conj`, `mul`; only `inv`, `conj` and `mul` are restricted to elements of `L`. `groupList H` is `Finset.univ.toList`, an arbitrary but fixed order, and `orbitAverage w x` is the `List.prod` of the mapped list, so it depends on that order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/NormalCost.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/NormalCost.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamsey mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness

namespace OAI

universe uGroup uAction uPoint uAlpha

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set

namespace EuclideanRamsey
open scoped BigOperators commutatorElement
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X]

def SameOrbit (x y : X) : Prop := ∃ h : H,h • x=y
structure NormalCost (L : Subgroup G) where
  cost : G → ℝ
  nonneg : ∀ g,0≤cost g
  one : cost 1=0
  inv : ∀ g∈L,cost g⁻¹=cost g
  conj : ∀ g∈L,∀ k,cost (k*g*k⁻¹)=cost g
  mul : ∀ g∈L,∀ h∈L,cost (g*h)≤cost g+cost h
namespace NormalCost
variable {L : Subgroup G} [L.Normal] (c : NormalCost L)
end NormalCost

noncomputable def groupList (H : Type uAction) [Fintype H] : List H := (Finset.univ : Finset H).toList
noncomputable def orbitAverage [Fintype H] (w : X → G) (x : X) : G :=
  ((groupList H).map (fun h => w (h•x))).prod

end EuclideanRamsey

end

end OAI


