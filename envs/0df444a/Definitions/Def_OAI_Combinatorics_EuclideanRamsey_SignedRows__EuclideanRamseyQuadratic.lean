-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyQuadratic
-- name    : OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyQuadratic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:37:33.194492+00:00
-- url     : https://prove2.me/theorems/936dc932-6baa-4a0a-9bb8-63215bd04dee
-- title:
--   Positive and negative parts of a finitely supported integer-valued function
-- statement:
--   This file splits a finitely supported integer-valued function into its positive and negative parts, both with values in the natural numbers.
--
--   Let $X$ be any set and $z:X\to\mathbb{Z}$ a finitely supported function. Its positive part and negative part are the finitely supported functions $z^+,z^-:X\to\mathbb{N}$ given by
--   $$z^+(x)=\max\bigl(z(x),0\bigr),\qquad z^-(x)=\max\bigl(-z(x),0\bigr),$$
--   so that $z=z^+-z^-$ and at each point at most one of $z^+(x)$ and $z^-(x)$ is nonzero.
--
--   These parts turn a signed integer combination into two multisets with nonnegative multiplicities: an element $x$ is listed $z^+(x)$ times on the positive side and $z^-(x)$ times on the negative side. In the construction of congruent copies this is applied after clearing the denominators of a rational signed weight, converting it into the columns of two real matrices $U$ and $V$ with $UU^{\mathsf T}-VV^{\mathsf T}=I_d$.
--
--   **Formalization Note** `positiveCount z` and `negativeCount z` are `Finsupp.mapRange` of `Int.toNat` and of `fun n => (-n).toNat`, applied to `z : α →₀ ℤ`; `Int.toNat` sends negative integers to $0$. The decomposition $z=z^+-z^-$ and the matrix construction are proved separately, and an empty section of the file contains no definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/SignedRows.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/SignedRows.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyQuadratic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyQuadratic

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


