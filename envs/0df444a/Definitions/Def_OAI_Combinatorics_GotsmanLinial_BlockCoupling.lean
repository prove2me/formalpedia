-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling
-- name    : OAI_Combinatorics_GotsmanLinial_BlockCoupling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:41:06.413051+00:00
-- url     : https://prove2.me/theorems/9f1ab354-08c3-4089-9e91-91a656960add
-- title:
--   Normalized pair weights from a two-index mass array
-- statement:
--   Let $\alpha$ and $\beta$ be index sets, let $B:\alpha\times\beta\to\mathbb{R}$ be an array of masses, and let $Z$ be a real number. The normalized pair weight is the function on pairs
--
--   $$
--   \mu_{B,Z}(a,b)=\frac{B(a,b)}{Z},\qquad (a,b)\in\alpha\times\beta .
--   $$
--
--   When $B$ is nonnegative and $Z>0$ is its total mass $\sum_{a,b}B(a,b)$, $\mu_{B,Z}$ is a probability distribution on $\alpha\times\beta$, that is, a coupling of its two marginals; its row and column sums are the row and column sums of $B$ divided by $Z$.
--
--   In the Gotsman–Linial argument one takes $\alpha=\beta=\{0,1,\dots,n\}$, lets $B(r,s)$ be the squared Hilbert–Schmidt norm of the block $P_sHP_r$ of a unitary matrix $H$ with respect to a degree grading $(P_k)$ whose layers have dimensions $\binom nk$, and normalizes by $Z=2^n$. Both marginals are then the symmetric binomial distribution $k\mapsto\binom nk/2^n$, and the vanishing of low-degree blocks restricts the support of the coupling, which is what the finite coupling estimate exploits.
--
--   **Formalization Note** The definition is `normalizedPairWeight B Z t`, with $B$ given in curried form and $t$ a pair; no hypothesis on $B$ or $Z$ is built in. If $Z=0$, Lean's convention $x/0=0$ makes the weight identically $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/BlockCoupling.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/BlockCoupling.lean by skeleton subtraction
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

namespace OAI

/-!
# The finite block coupling

Normalize a nonnegative matrix of block masses, identify its two binomial
marginals, and reflect its first index.  The low-degree block vanishing gives
the one-sided displacement bound required by the finite coupling lemma.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

/-- Normalize finite two-index masses by their total mass. -/
noncomputable def normalizedPairWeight {α β : Type*}
    (B : α → β → ℝ) (Z : ℝ) (t : α × β) : ℝ :=
  B t.1 t.2 / Z

end LeanBlast.GotsmanLinial

end OAI


