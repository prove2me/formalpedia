-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
-- name    : OAI_Combinatorics_GotsmanLinial_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:05:03.891493+00:00
-- url     : https://prove2.me/theorems/878db56b-a830-46da-8e0a-6dab574344e9
-- title:
--   Number of ordered sensitive edges of a function on the Boolean cube
-- statement:
--   The Boolean cube is encoded as the set of maps $\{1,\dots,n\} \to \{\mathrm{false}, \mathrm{true}\}$ and read as the sign cube $\{-1,1\}^n$, with $\mathrm{true}$ representing $1$ and $\mathrm{false}$ representing $-1$. For a vertex $x$ and a coordinate $i$, write $x^{\oplus i}$ for the vertex obtained by flipping the $i$-th coordinate. A vertex $x$ is *sensitive in direction $i$* for a function $f$ if $f(x) \neq f(x^{\oplus i})$.
--
--   This module defines the sensitive-edge count of a real function $f : \{-1,1\}^n \to \mathbb{R}$:
--   $$
--   s(f) = \sum_{i=1}^{n} \#\{x \in \{-1,1\}^n : f(x) \neq f(x^{\oplus i})\}.
--   $$
--   It counts pairs $(i, x)$ of a direction and an initial vertex at which $f$ changes, equivalently ordered cube edges $(x, x^{\oplus i})$ along which $f$ is not constant; every undirected sensitive edge is therefore counted twice, once from each endpoint.
--
--   The count is the numerator of the average sensitivity used in the Gotsman–Linial statement: with uniform counting probability on the $2^n$ vertices, $\mathrm{AS}(f) = s(f)/2^n$. The surrounding statement also fixes the conventions $\operatorname{sgn}(0) = 1$ for the threshold sign and the exact constant $8$ in the bound $\mathrm{AS}(\operatorname{sgn}\circ p) \le 8d\sqrt{n}$.
--
--   **Formalization Note** The definition is `sensitiveEdgeCount f`, a natural number, defined as the sum over `i : Fin n` of the cardinalities of `sensitiveVertices f i`; the cube type `Cube n`, the flip map, `sensitiveVertices` and `averageSensitivity` come from the base statement file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GotsmanLinial mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial

namespace OAI

/-!
# Polynomial thresholds and average sensitivity

The Boolean cube encodes the sign cube `{−1,1}^n`:
`false` represents `−1` and `true` represents `1`. The public statement
quantifies directly over real multilinear polynomials and uses uniform counting
probability, the convention `sign(0) = 1`, and the exact constant `8`.

`GotsmanLinialStatement` is a proposition definition, not a proof of the bound.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

/-- Number of ordered sensitive edges, indexed by their initial vertex and direction. -/
noncomputable def sensitiveEdgeCount {n : ℕ} (f : Cube n → ℝ) : ℕ :=
  ∑ i : Fin n, (sensitiveVertices f i).card

end LeanBlast.GotsmanLinial

end OAI


