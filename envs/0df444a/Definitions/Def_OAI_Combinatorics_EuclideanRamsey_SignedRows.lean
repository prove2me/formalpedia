-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows
-- name    : OAI_Combinatorics_EuclideanRamsey_SignedRows
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:29:15.159976+00:00
-- url     : https://prove2.me/theorems/64126f5c-6899-4efb-9049-249fb7b06a8d
-- title:
--   Positive and negative parts of a finitely supported integer-valued function
-- statement:
--   This file splits a finitely supported integer-valued function into its positive and negative parts.
--
--   Let $X$ be any set and $z:X\to\mathbb{Z}$ a finitely supported function. Its positive and negative parts are the finitely supported functions $z^+,z^-:X\to\mathbb{N}$ given by
--   $$z^+(x)=\max\bigl(z(x),0\bigr),\qquad z^-(x)=\max\bigl(-z(x),0\bigr),$$
--   so that $z=z^+-z^-$ and at each point at most one of $z^+(x)$ and $z^-(x)$ is nonzero.
--
--   These parts turn a signed integer combination into two multisets with nonnegative multiplicities: an element $x$ is listed $z^+(x)$ times on the positive side and $z^-(x)$ times on the negative side. This is used to convert a rational signed combination of vectors, after clearing denominators, into the columns of two real matrices $U,V$ with $UU^{\mathsf T}-VV^{\mathsf T}=I$.
--
--   **Formalization Note** `positiveCount z` and `negativeCount z` are `Finsupp.mapRange` of `Int.toNat` and of `fun n => (-n).toNat`, applied to `z : α →₀ ℤ`. An empty section of the file contains no definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/SignedRows.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/SignedRows.lean by skeleton subtraction
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

namespace OAI

universe uAlpha uBeta

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

open scoped BigOperators
namespace EuclideanRamsey

def positiveCount {α : Type uAlpha} (z : α →₀ ℤ) : α →₀ ℕ := z.mapRange Int.toNat (by simp)
def negativeCount {α : Type uAlpha} (z : α →₀ ℤ) : α →₀ ℕ := z.mapRange (fun n => (-n).toNat) (by simp)

end EuclideanRamsey

namespace EuclideanRamsey
open Matrix

end EuclideanRamsey

end

end OAI


