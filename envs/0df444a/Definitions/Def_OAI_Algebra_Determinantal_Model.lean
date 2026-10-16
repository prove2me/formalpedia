-- Prove2me | Definitions.Def_OAI_Algebra_Determinantal_Model
-- name    : OAI_Algebra_Determinantal_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:19:42.424019+00:00
-- url     : https://prove2.me/theorems/41454038-f579-4368-b2d7-d482b9ecfa29
-- title:
--   The exponent cube of multi-indices with all entries at most $n$
-- statement:
--   Let $\sigma$ be a finite set of variables and $n\in\mathbb{N}$. The *exponent cube* is the finite set of multi-indices
--   $$\mathcal{C}_n(\sigma)=\{\delta\in\mathbb{N}^{\sigma} : \delta_s\le n\ \text{for every}\ s\in\sigma\},$$
--   that is, the set of exponent vectors lying below the constant vector $(n,\dots,n)$ in the coordinatewise order. The accompanying lemma characterizes membership: $\delta\in\mathcal{C}_n(\sigma)$ if and only if $\delta_s\le n$ for all $s\in\sigma$.
--
--   A polynomial in $\mathbb{C}[x_s : s\in\sigma]$ all of whose monomials $x^\delta$ satisfy $\delta\in\mathcal{C}_n(\sigma)$ (for instance any polynomial of total degree at most $n$, such as the determinant of an $n\times n$ matrix of affine-linear forms) is determined by its coefficient vector in the fixed finite-dimensional space $\mathbb{C}^{\mathcal{C}_n(\sigma)}$. The cube is used to place such polynomials, sequences of them and their coefficientwise limits in a single coefficient space, so that polynomial systems can be studied as smooth functions of the coefficients.
--
--   **Formalization Note** The cube is `exponentCube n : Finset (σ →₀ ℕ)`, defined as `Finset.Iic` of the constant function `n` (as a finitely supported function), and `mem_exponentCube` is the membership characterization.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SmoothInitialForm mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars
import Definitions.Def_OAI_Algebra_Determinantal_RankTransfer

namespace OAI

namespace PermanentBorder.Polar
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial
open scoped Classical
variable {τ : Type*} [Fintype τ]

end PermanentBorder.Polar

namespace PermanentBorder

open Filter
open scoped Topology

end PermanentBorder

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section FixedCoefficientSpace
variable {σ τ : Type*} [Fintype σ]

noncomputable def exponentCube (n : ℕ) : Finset (σ →₀ ℕ) :=
  by
    classical
    exact Finset.Iic (Finsupp.equivFunOnFinite.symm (fun _ : σ => n))

@[simp] theorem mem_exponentCube (n : ℕ) (d : σ →₀ ℕ) :
    d ∈ exponentCube (σ := σ) n ↔ ∀ i, d i ≤ n := by
  classical
  simp only [exponentCube, Finset.mem_Iic, Finsupp.le_def]
  rfl

end FixedCoefficientSpace

section DeterminantDegree
variable {σ : Type*} [Fintype σ]

end DeterminantDegree

section AffineSubstitution
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

end AffineSubstitution
end PermanentBorder

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section ScalarNormalization
variable {σ : Type*} [Fintype σ]

end ScalarNormalization
end PermanentBorder

end OAI


