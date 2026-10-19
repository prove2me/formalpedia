-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_ExtremalEmbedding
-- name    : OAI_Analysis_DirectCrouzeix_ExtremalEmbedding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:54:31.711187+00:00
-- url     : https://prove2.me/theorems/4d22b807-0c3f-48c8-b695-8d90cc47d3f4
-- title:
--   Normalized holomorphic embeddings of a planar set into the unit disk
-- statement:
--   Let $U\subseteq\mathbb{C}$, $a\in\mathbb{C}$ and $f:\mathbb{C}\to\mathbb{C}$, and let $\mathbb{D}=\{w\in\mathbb{C}:|w|<1\}$ be the open unit disk. The module defines the property that $f$ is a normalized embedding of $U$ into $\mathbb{D}$ based at $a$, meaning that all of the following hold:
--
--   1. $f$ is complex differentiable on $U$ (at every point of $U$, relative to $U$);
--   2. $f$ maps $U$ into $\mathbb{D}$;
--   3. $f$ is injective on $U$;
--   4. $f'(z)\ne0$ for every $z\in U$;
--   5. $f(a)=0$.
--
--   In symbols, the conditions 2, 4 and 5 read
--
--   $$
--   f(U)\subseteq\mathbb{D},\qquad f'(z)\ne0\ \ (z\in U),\qquad f(a)=0 .
--   $$
--
--   The membership $a\in U$ is not part of the definition. When $U$ is open, condition 1 is holomorphy on $U$.
--
--   This is the class of functions in the extremal-problem proof of the Riemann mapping theorem: for $U$ open, simply connected and different from $\mathbb{C}$, and $a\in U$, normalized embeddings exist, one of them maximizes $|f'(a)|$ among all normalized embeddings, and a maximizer maps $U$ onto $\mathbb{D}$. In this development the resulting Riemann maps are used to parametrize bounded simply connected domains with analytic boundary by injective analytic maps defined on a disk of radius larger than $1$.
--
--   **Formalization Note** `NormalizedEmbedding U a f` is a structure in `Prop` with fields `holomorphic : DifferentiableOn ℂ f U`, `disk : MapsTo f U (ball 0 1)`, `injective : InjOn f U`, `derivative : ∀ z ∈ U, deriv f z ≠ 0` and `normalized : f a = 0`; here `deriv f z` is the derivative of $f$ at $z$ in $\mathbb{C}$, which is $0$ by convention if $f$ is not differentiable at $z$. As stated in the source header, the declaration is adapted from Mathlib's file `Mathlib.Analysis.Complex.RiemannMapping`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/ExtremalEmbedding.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/ExtremalEmbedding.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_NormalFamilies

/-
Portions of this file have been adapted from an external source.
The source copyright header and license information are preserved below.
-/

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

The following conformal embedding declarations are adapted from Mathlib.Analysis.Complex.RiemannMapping.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Complex/RiemannMapping.lean

This code has been modified.
-/

structure NormalizedEmbedding (U : Set ℂ) (a : ℂ) (f : ℂ → ℂ) : Prop where
  holomorphic : DifferentiableOn ℂ f U
  disk : MapsTo f U (ball 0 1)
  injective : InjOn f U
  derivative : ∀ z ∈ U, deriv f z ≠ 0
  normalized : f a = 0

end Conformal

end DirectCrouzeix

end

end

end

end OAI


