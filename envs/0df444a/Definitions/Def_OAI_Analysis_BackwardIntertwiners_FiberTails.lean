-- Prove2me | Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
-- name    : OAI_Analysis_BackwardIntertwiners_FiberTails
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:54:36.810914+00:00
-- url     : https://prove2.me/theorems/0b8745fd-543d-4c1c-8e86-307405373223
-- title:
--   The fiber Hilbert space $\ell^2(\mathbb{Z})$ of square-summable two-sided sequences
-- statement:
--   This file fixes the fiber Hilbert space of the construction,
--   $$\mathcal{F}=\ell^2(\mathbb{Z})=\Bigl\{v:\mathbb{Z}\to\mathbb{C}\ :\ \sum_{j\in\mathbb{Z}}|v_j|^2<\infty\Bigr\},\qquad \|v\|=\Bigl(\sum_{j\in\mathbb{Z}}|v_j|^2\Bigr)^{1/2},$$
--   the complex Hilbert space of square-summable two-sided sequences, with inner product $\langle v,z\rangle=\sum_{j}\overline{v_j}\,z_j$ and standard orthonormal basis $(e_j)_{j\in\mathbb{Z}}$, where $e_j$ has entry $1$ at position $j$ and $0$ elsewhere.
--
--   All operators of the model act fiberwise on $\mathcal{F}$: over each point of the base space the forward operator is a weighted shift $e_j\mapsto\beta(j)\,e_{j+1}$ with positive coefficients, and the global Hilbert space consists of square-integrable $\mathcal{F}$-valued functions on the base. In this module $\mathcal{F}$ is used to classify closed subspaces invariant under such a shift: if $w:\mathbb{Z}\to\mathbb{R}$ is a quadratic weight and $T$ is the operator $(Tv)_j=\frac{w(j)}{w(j-1)}\,v_{j-1}$, then every closed $T$-invariant subspace of $\mathcal{F}$ is $\{0\}$, all of $\mathcal{F}$, or a coordinate tail $\{v\in\mathcal{F}\ :\ v_j=0\text{ for all }j<h\}$ for some $h\in\mathbb{Z}$. (Here $w$ is quadratic if it is positive and non-increasing, $n\mapsto\log w(-n)$ and $n\mapsto-\log w(n)$ have non-decreasing increments on $\mathbb{N}$, $\sum_{j\ne0}w(j)^{1/j}<\infty$, and $\log w(n)/n^2\to-a$ and $\log w(-n)/n^2\to a$ for some $a>\log 3$.)
--
--   **Formalization Note** `Fiber` is an abbreviation for Mathlib's `lp (fun _ : ℤ => ℂ) 2`, so it inherits the Hilbert-space structure of $\ell^2$; its elements coerce to functions from the integers to the complex numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/FiberTails.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/FiberTails.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BackwardIntertwiners mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

abbrev Fiber := lp (fun _ : ℤ => ℂ) 2

end
end BackwardIntertwiners

end OAI


