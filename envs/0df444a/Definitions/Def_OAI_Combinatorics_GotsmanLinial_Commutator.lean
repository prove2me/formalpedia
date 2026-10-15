-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator
-- name    : OAI_Combinatorics_GotsmanLinial_Commutator
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:41:37.281695+00:00
-- url     : https://prove2.me/theorems/d77289a6-ac81-4675-9735-42bd38022efc
-- title:
--   Spectral multipliers, the grading phase $\sum_k i^k P_k$, and block tridiagonality
-- statement:
--   Let $\iota$ and $K$ be finite index sets and let $(P_k)_{k\in K}$ be a family of complex matrices in $\mathbb{C}^{\iota\times\iota}$ (typically an orthogonal projection family: Hermitian idempotents with $P_rP_s=0$ for $r\neq s$ and $\sum_kP_k=I$).
--
--   1. **Spectral multiplier.** For complex coefficients $a:K\to\mathbb{C}$, the spectral multiplier is $M_a=\sum_{k\in K}a(k)\,P_k$. For an orthogonal projection family it acts as multiplication by $a(k)$ on the range of $P_k$.
--
--   2. **Grading phase.** For a family $(P_k)_{k=0}^{n}$ indexed by $\{0,1,\dots,n\}$, the grading phase is the spectral multiplier with coefficients $i^k$, where $i$ is the imaginary unit:
--   $$
--   U=\sum_{k=0}^{n} i^{k}\,P_k .
--   $$
--   For an orthogonal projection family $U$ is unitary, with eigenvalue $i^k$ on the range of $P_k$.
--
--   3. **Block tridiagonality.** A matrix $Z\in\mathbb{C}^{\iota\times\iota}$ is block tridiagonal with respect to $(P_k)_{k=0}^{n}$ if all blocks at grading distance at least two vanish:
--   $$
--   P_s\,Z\,P_r=0\qquad\text{for all } r,s\in\{0,\dots,n\}\text{ with } |r-s|\ge 2 .
--   $$
--
--   For a block tridiagonal $Z$ and the degree grading $N=\sum_k k\,P_k$ of an orthogonal projection family, the commutator is a difference of two unitary conjugates, $2i\,(NZ-ZN)=UZU^{*}-U^{*}ZU$, which bounds the Hilbert–Schmidt norm of $NZ-ZN$ by that of $Z$. In the Gotsman–Linial argument the coordinate multipliers of the Boolean cube are block tridiagonal in the weighted degree grading.
--
--   **Formalization Note** The objects are `spectralMultiplier`, `gradingPhase` (coefficients `Complex.I ^ k`) and the predicate `BlockTridiagonal`, whose condition is written as `r + 1 < s` or `s + 1 < r` for indices in `Fin (n + 1)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/Commutator.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/Commutator.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling

namespace OAI

/-!
# Entry bounds for a tridiagonal grading commutator

All norms here are norms of individual complex entries.  No default
norm on a matrix is used.  A complete orthogonal family defines a phase
unitary with eigenvalues `I^k`.  For a tridiagonal operator the commutator is
the difference of two unitary conjugates divided by `2 I`.
-/

noncomputable section

open scoped BigOperators Matrix

namespace LeanBlast.GotsmanLinial

section SpectralMultiplier

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- A complex spectral multiplier for a finite family of projections. -/
def spectralMultiplier (P : κ → Matrix ι ι ℂ) (a : κ → ℂ) : Matrix ι ι ℂ :=
  ∑ k, a k • P k

variable (P : κ → Matrix ι ι ℂ)
variable (hmul : ∀ r s, P r * P s = if r = s then P r else 0)
include hmul

end SpectralMultiplier

section GradingCommutator

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Fin (n + 1) → Matrix ι ι ℂ}

/-- The spectral phase `I^k` of the degree grading. -/
def gradingPhase (P : Fin (n + 1) → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  spectralMultiplier P fun k => Complex.I ^ k.val

/-- Tridiagonality means that blocks at grading distance greater than one vanish. -/
def BlockTridiagonal (P : Fin (n + 1) → Matrix ι ι ℂ) (Z : Matrix ι ι ℂ) : Prop :=
  ∀ r s : Fin (n + 1), (r.val + 1 < s.val ∨ s.val + 1 < r.val) →
    P s * Z * P r = 0

end GradingCommutator

end LeanBlast.GotsmanLinial

end

end OAI


