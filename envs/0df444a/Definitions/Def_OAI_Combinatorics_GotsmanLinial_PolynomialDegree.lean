-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_PolynomialDegree
-- name    : OAI_Combinatorics_GotsmanLinial_PolynomialDegree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:45:00.735978+00:00
-- url     : https://prove2.me/theorems/7ca604a8-5e75-4ae9-b9ea-0b2f55e74e47
-- title:
--   Functions on the Boolean cube with Walsh support in degrees at least $k$
-- statement:
--   Let $Q_n=\{-1,1\}^n$ be the Boolean cube and $\chi_S(x)=\prod_{i\in S}x_i$ the Walsh characters, $S\subseteq[n]$. For $k\in\mathbb{N}$, the space of functions whose Walsh support starts in degree $k$ is
--
--   $$
--   V_{\ge k}=\operatorname{span}_{\mathbb{C}}\{\chi_S : S\subseteq[n],\ |S|\ge k\}\subseteq\mathbb{C}^{Q_n}.
--   $$
--
--   It consists of the complex functions on the cube whose Fourier expansion has no terms of degree below $k$; $V_{\ge0}$ is the whole space and $V_{\ge k}=\{0\}$ for $k>n$.
--
--   This is the counterpart of the low-degree space $V_{\le r}=\operatorname{span}\{\chi_S:|S|\le r\}$: if $a\in V_{\le r}$, $b\in V_{\ge s}$ and $r<s$, then $\sum_x a(x)b(x)=0$, and multiplying a function of degree at most $d$ by the full parity $\chi_{[n]}$ lands in $V_{\ge n-d}$. Together with the fact that the values on the cube of a real multilinear polynomial of total degree at most $d$ form a function in $V_{\le d}$, these facts give the vanishing of low-degree blocks for polynomial threshold functions.
--
--   **Formalization Note** The definition is `fourierSpaceFrom n k`, a complex submodule of the functions on `Cube n`, spanned by the characters `walshChar S` for which `S.card` is at least `k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/PolynomialDegree.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/PolynomialDegree.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Walsh

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Polynomial degree and the Walsh filtration

The polynomial lemmas concern real multilinear
`MvPolynomial`s. Restriction to the cube is justified by an explicit monomial
expansion rather than assumed as an alternate polynomial representation.
-/

open scoped BigOperators symmDiff

namespace LeanBlast.GotsmanLinial

noncomputable section

variable {n d : ℕ}

/-- Functions whose Walsh support starts in degree `k`. -/
def fourierSpaceFrom (n k : ℕ) : Submodule ℂ (Cube n → ℂ) :=
  Submodule.span ℂ (walshChar '' {S : Finset (Fin n) | k ≤ S.card})

end

end LeanBlast.GotsmanLinial

end OAI


