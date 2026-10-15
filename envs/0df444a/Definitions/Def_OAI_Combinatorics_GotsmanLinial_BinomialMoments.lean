-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
-- name    : OAI_Combinatorics_GotsmanLinial_BinomialMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:05:42.359629+00:00
-- url     : https://prove2.me/theorems/99d3f0d4-4a1a-4aad-961f-436c89821289
-- title:
--   Symmetric binomial weights $\binom{n}{k}2^{-n}$
-- statement:
--   For a natural number $n$ and an index $k \in \{0, 1, \dots, n\}$, the symmetric binomial weight is the real number
--   $$
--   \beta_n(k) = \frac{\binom{n}{k}}{2^{n}} .
--   $$
--   These are the point masses of the binomial distribution with parameters $n$ and $1/2$, i.e. the fraction of vertices of the cube $\{-1,1\}^n$ having exactly $k$ coordinates equal to $1$; here they are treated purely as a finite real function, without any probability measure.
--
--   In the Gotsman–Linial argument the binomial coefficients $\binom nk$ are the multiplicities (ranks) of the layers of the orthogonal grading of $\mathbb{C}^{\{-1,1\}^n}$; normalising by $2^n$ gives these weights, whose exact finite moments (in particular the variance $n/4$ about the centre $n/2$) feed the finite coupling estimate.
--
--   **Formalization Note** The definition is `binomialWeight n k` with `k : Fin (n + 1)`, given by `(n.choose k.val : ℝ) / 2 ^ n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/BinomialMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/BinomialMoments.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement

namespace OAI

/-!
Exact finite moments of the symmetric binomial weights. These identities provide
the grading multiplicities and the variance used in the finite coupling estimate.
No probabilistic assumptions or measures enter the statements.
-/

namespace LeanBlast.GotsmanLinial

open scoped BigOperators

/-- The symmetric binomial probability weights, presented as a finite real function. -/
noncomputable def binomialWeight (n : ℕ) (k : Fin (n + 1)) : ℝ :=
  (n.choose k.val : ℝ) / (2 : ℝ) ^ n

end LeanBlast.GotsmanLinial

end OAI


