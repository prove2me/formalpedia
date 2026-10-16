-- Prove2me | Definitions.Def_OAI_Algebra_Determinantal_GenericPolars
-- name    : OAI_Algebra_Determinantal_GenericPolars
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:14:28.890408+00:00
-- url     : https://prove2.me/theorems/99229e16-9523-4e58-ad60-bfa22f6d7ea7
-- title:
--   Polars of a form in generic directions and the bad polar system
-- statement:
--   This module introduces polars of a polynomial, the square Jacobian of the system formed by a form and its polars, generic directions, and the associated bad polar system with its degrees. Throughout, $\partial_j$ is the partial derivative with respect to $x_j$.
--
--   1. **Polar values and polar gradients.** Let $L$ be a field extension of a field $K$, $\sigma$ and $\tau$ finite sets, $f\in K[x_j:j\in\sigma]$, $w=(w_{ij})\in L^{\tau\times\sigma}$ a family of directions and $y\in L^{\sigma}$. Then
--   $$
--   \operatorname{pol}_i(y)=\sum_{j\in\sigma}w_{ij}\,\partial_jf(y),\qquad \operatorname{grad}_{ij}(y)=\sum_{k\in\sigma}w_{ik}\,\partial_j\partial_kf(y),
--   $$
--   the derivative of $f$ at $y$ in the direction $w_i$ and the gradient of that polar.
--
--   2. **Polar variables.** For a finite set $\tau$, $V_\tau=\{\star,\circ\}\sqcup\tau$, a set of $|\tau|+2$ variable indices (homogeneous coordinates on $\mathbb P^{|\tau|+1}$).
--
--   3. **Square Jacobian.** For $w\in L^{\tau\times V_\tau}$, $l\in L^{V_\tau}$, $f\in K[x_j:j\in V_\tau]$ and $y\in L^{V_\tau}$, the $V_\tau\times V_\tau$ matrix over $L$ whose row $\star$ is $\bigl(\partial_jf(y)\bigr)_j$, whose row $\circ$ is $(l_j)_j$, and whose row $i\in\tau$ is $\bigl(\operatorname{grad}_{ij}(y)\bigr)_j$.
--
--   4. **Generic directions and generic linear form.** For $K$ of characteristic zero, let $\mathbb E$ be the algebraic closure of the field of rational functions over $K$ in independent indeterminates $t_{ij}$ ($i\in\tau$, $j\in V_\tau$) and $t_{\circ j}$ ($j\in V_\tau$). The generic directions are $w_{ij}=t_{ij}$ and the generic linear form has coefficients $l_j=t_{\circ j}$.
--
--   5. **Polar polynomials and linear forms.** Over a commutative ring $R$, for $w\in R^{\tau\times\sigma}$ and $f\in R[x_j:j\in\sigma]$: $\operatorname{Pol}_i=\sum_{j}w_{ij}\,\partial_jf$, and for $l\in R^{\sigma}$, $\ell=\sum_jl_jx_j$.
--
--   6. **Square polynomial matrix and its row degrees.** For $f\in R[x_j:j\in V_\tau]$, the $V_\tau\times V_\tau$ polynomial matrix with row $\star$ equal to $(\partial_jf)_j$, row $\circ$ equal to the constants $(l_j)_j$, and row $i\in\tau$ equal to $(\partial_j\operatorname{Pol}_i)_j$. For $r\in\mathbb N$ the row-degree vector is $r-1$ at $\star$, $0$ at $\circ$ and $r-2$ at each $i\in\tau$, with natural-number subtraction truncated at $0$; these are the row degrees when $f$ is homogeneous of degree $r$.
--
--   7. **Bad polar system and its degrees.** The system indexed by $V_\tau$:
--   $$
--   \star\mapsto f,\qquad \circ\mapsto\ell\cdot\det\bigl(\text{square polynomial matrix}\bigr),\qquad i\mapsto\operatorname{Pol}_i\quad(i\in\tau),
--   $$
--   with degree vector $r$ at $\star$, $1+(r-1)+|\tau|\,(r-2)$ at $\circ$ (the sum of the row degrees plus one, with the same truncation), and $r-1$ at each $i\in\tau$.
--
--   For a form $f$ of degree $r$ in $|\tau|+2$ variables, $(f,\operatorname{Pol}_i)_{i\in\tau}$ is a system of $|\tau|+1$ forms, and the bad polar system vanishes at its nonzero common zeros that lie on the hyperplane $\ell=0$ or at which the square Jacobian is singular. For a complex form $f$ of degree $r\ge2$ that is smooth (no nonzero point where $f$ and all its partial derivatives vanish), these objects are used, first over $\mathbb E$ with generic directions and then via Macaulay certificates, to find complex directions $w$ and a linear form $\ell$ for which the polar system is good and has exactly $r(r-1)^{|\tau|}$ roots on the chart $\ell=1$.
--
--   **Formalization Note** $V_\tau$ is `PolarVars τ = Option (Option τ)` with $\star$ = `none`, $\circ$ = `some none` and $i$ = `some (some i)`. The definitions are `Polar.polarValue`, `polarGradient` (evaluated with `aeval`), `PolarVars`, `squareJacobian`, `genericDirections` and `genericLinear` (generic parameters of `GenericField K (Option τ × PolarVars τ)`, the index `(some i, j)` for $t_{ij}$ and `(none, j)` for $t_{\circ j}$), `polarPolynomial`, `linearPolynomial`, `squarePolynomial`, `squareDegrees` (with the entry `r-1-1` at $i\in\tau$), `badPolarSystem` and `badPolarDegrees`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/GenericPolars.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/GenericPolars.lean by skeleton subtraction
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

namespace OAI
namespace PermanentBorder.Polar
open MvPolynomial

section Parametric
variable {K L σ τ : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype σ] [Fintype τ]

noncomputable def polarValue (w : τ → σ → L) (f : MvPolynomial σ K)
    (y : σ → L) (i : τ) : L := ∑ j, w i j * aeval y (pderiv j f)

noncomputable def polarGradient (w : τ → σ → L) (f : MvPolynomial σ K)
    (y : σ → L) (i : τ) (j : σ) : L :=
  ∑ k, w i k * aeval y (pderiv j (pderiv k f))

end Parametric
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Square
variable {K L τ : Type*} [Field K] [Field L] [Algebra K L] [Fintype τ]
abbrev PolarVars (τ : Type*) := Option (Option τ)

noncomputable def squareJacobian (w : τ → PolarVars τ → L) (l : PolarVars τ → L)
    (f : MvPolynomial (PolarVars τ) K) (y : PolarVars τ → L) :
    Matrix (PolarVars τ) (PolarVars τ) L := fun i j => match i with
  | none => aeval y (pderiv j f)
  | some none => l j
  | some (some i) => polarGradient w f y i j

end Square

section GenericSquare
variable {K τ : Type*} [Field K] [CharZero K] [Fintype τ] [DecidableEq τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

noncomputable def genericDirections : τ → PolarVars τ → E :=
  fun i j => genericParameter K P (some i,j)
noncomputable def genericLinear : PolarVars τ → E :=
  fun j => genericParameter K P (none,j)

end GenericSquare
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Polynomials
variable {R σ τ : Type*} [CommRing R] [Fintype σ] [Fintype τ]

noncomputable def polarPolynomial (w : τ → σ → R) (f : MvPolynomial σ R) (i : τ) :
    MvPolynomial σ R := ∑ j, C (w i j) * pderiv j f

noncomputable def linearPolynomial (l : σ → R) : MvPolynomial σ R :=
  ∑ j, C (l j) * X j

noncomputable def squarePolynomial (w : τ → PolarVars τ → R) (l : PolarVars τ → R)
    (f : MvPolynomial (PolarVars τ) R) :
    Matrix (PolarVars τ) (PolarVars τ) (MvPolynomial (PolarVars τ) R) :=
  fun i j => match i with
    | none => pderiv j f
    | some none => C (l j)
    | some (some i) => pderiv j (polarPolynomial w f i)

def squareDegrees (τ : Type*) (r : ℕ) : PolarVars τ → ℕ := fun i => match i with
  | none => r-1
  | some none => 0
  | some (some _) => r-1-1

noncomputable def badPolarSystem (w : τ → PolarVars τ → R) (l : PolarVars τ → R)
    (f : MvPolynomial (PolarVars τ) R) : PolarVars τ → MvPolynomial (PolarVars τ) R := by
  classical
  exact fun i => match i with
    | none => f
    | some none => linearPolynomial l * (squarePolynomial w l f).det
    | some (some i) => polarPolynomial w f i

def badPolarDegrees (τ : Type*) [Fintype τ] (r : ℕ) : PolarVars τ → ℕ :=
  fun i => match i with
    | none => r
    | some none => 1 + ∑ i, squareDegrees τ r i
    | some (some _) => r-1

end Polynomials

section Evaluation
variable {K L σ τ : Type*} [Field K] [Field L] [Algebra K L] [Fintype σ] [Fintype τ]

end Evaluation
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Map
variable {R S σ τ : Type*} [CommRing R] [CommRing S] [Fintype σ] [Fintype τ]

end Map
end PermanentBorder.Polar

end OAI


