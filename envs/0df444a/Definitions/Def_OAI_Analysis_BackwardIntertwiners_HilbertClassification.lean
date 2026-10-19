-- Prove2me | Definitions.Def_OAI_Analysis_BackwardIntertwiners_HilbertClassification
-- name    : OAI_Analysis_BackwardIntertwiners_HilbertClassification
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:12:19.604514+00:00
-- url     : https://prove2.me/theorems/eb5eb280-f8e4-4c35-b3bf-f494634ebc40
-- title:
--   Existence of a nonzero quasinilpotent operator with transitive commutant
-- statement:
--   Let $H$ be a complex Hilbert space and let $B(H)$ be the algebra of bounded complex-linear operators on $H$. For $T\in B(H)$, the *commutant* of $T$ is $\{T\}'=\{A\in B(H):AT=TA\}$. The commutant is called *transitive* if it has no nontrivial closed invariant subspace: whenever $K\subseteq H$ is a closed complex-linear subspace with $AK\subseteq K$ for every $A\in\{T\}'$, then $K=\{0\}$ or $K=H$. Equivalently, $T$ has no closed hyperinvariant subspace other than $\{0\}$ and $H$.
--
--   The proposition $\mathrm{MainClaim}(H)$ asserts that there exists $T\in B(H)$ such that
--   $$T\neq0,\qquad\lim_{n\to\infty}\|T^n\|^{1/n}=0,\qquad\text{and}\qquad\{T\}'\ \text{is transitive}.$$
--   The middle condition says that $T$ is quasinilpotent, i.e. its spectral radius is $0$.
--
--   This is the core of the project's main statement, which in addition asserts that the commutant $\{T\}'$ is a proper subalgebra of $B(H)$ and is closed in the strong operator topology. The property is invariant under unitary equivalence: if $U:H\to K$ is a surjective linear isometry onto another Hilbert space $K$ and $T$ witnesses $\mathrm{MainClaim}(H)$, then $UTU^{-1}$ witnesses $\mathrm{MainClaim}(K)$. Since all infinite-dimensional separable complex Hilbert spaces are isometrically isomorphic, it suffices to verify the claim on one convenient model space.
--
--   **Formalization Note** `MainClaim` takes $H$ as an implicit argument with `InnerProductSpace ℂ H` and `CompleteSpace H`; no separability or infinite-dimensionality is assumed in the definition. The limit is taken along $n\in\mathbb{N}$ of the real power $\|T^n\|^{1/n}$ (at $n=0$ the exponent $1/0$ equals $0$ by Lean's convention, which does not affect the limit). Transitivity is `TransitiveCommutant T`, which quantifies over closed submodules $K$ and over all operators $A$ with `A * T = T * A`. The file also opens a section for separable $H$ that contains no further definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/HilbertClassification.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/HilbertClassification.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BackwardIntertwiners mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_HaarBase
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberMaps
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_BackwardWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_GlobalOperators
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ErgodicTransitivity
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_OrdinaryStructure
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_DiagonalSymbols
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_PolarDiagonals

namespace OAI

namespace Hyperinvariant233
open Filter
open scoped Topology
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def MainClaim : Prop :=
  ∃ T : H →L[ℂ] H, T ≠ 0 ∧
    Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) ∧
    TransitiveCommutant T

end Hyperinvariant233

namespace Hyperinvariant233
open Submodule TopologicalSpace
universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SeparableSpace H]

end Hyperinvariant233

end OAI


