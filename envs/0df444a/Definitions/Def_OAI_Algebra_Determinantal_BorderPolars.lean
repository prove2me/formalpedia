-- Prove2me | Definitions.Def_OAI_Algebra_Determinantal_BorderPolars
-- name    : OAI_Algebra_Determinantal_BorderPolars
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:20:29.782713+00:00
-- url     : https://prove2.me/theorems/a3b80e24-b85c-44f3-a015-93f32de6c232
-- title:
--   Square polynomial systems, simple zeros, and polar operators in an affine chart
-- statement:
--   Throughout, $\sigma$ and $\tau$ are finite sets and $\mathbb{C}[x_\sigma]$ denotes the polynomial ring $\mathbb{C}[x_s : s\in\sigma]$.
--
--   1. **Polynomial system.** Given $\mathbb{C}$-linear maps $L_i:\mathbb{C}[x_\sigma]\to\mathbb{C}[z_\tau]$ for $i\in\tau$ and a polynomial $P\in\mathbb{C}[x_\sigma]$, the map $\Phi_{L,P}:\mathbb{C}^\tau\to\mathbb{C}^\tau$ is
--   $$\Phi_{L,P}(z)_i=(L_iP)(z)\qquad(i\in\tau),$$
--   a square system of $|\tau|$ polynomial equations in $|\tau|$ unknowns.
--   2. **Coefficient system.** For $n\in\mathbb{N}$ let $\mathcal{C}_n=\{\delta\in\mathbb{N}^\sigma : \delta_s\le n\ \text{for all}\ s\}$ be the exponent cube. The map $\Psi_{n,L}:\mathbb{C}^{\mathcal{C}_n}\times\mathbb{C}^\tau\to\mathbb{C}^\tau$ is
--   $$\Psi_{n,L}(u,z)_i=\sum_{\delta\in\mathcal{C}_n}u_\delta\,(L_ix^\delta)(z).$$
--   By linearity of the $L_i$, if $P=\sum_{\delta\in\mathcal{C}_n}u_\delta x^\delta$ then $\Psi_{n,L}(u,z)=\Phi_{L,P}(z)$; so $\Psi_{n,L}$ is the system $\Phi_{L,P}$ viewed as a function of the coefficients of $P$ and of the point jointly.
--   3. **Simple zero.** A point $z\in\mathbb{C}^\tau$ is a simple zero of $\Phi_{L,P}$ if $\Phi_{L,P}(z)=0$ and the complex derivative $D\Phi_{L,P}(z):\mathbb{C}^\tau\to\mathbb{C}^\tau$ is invertible.
--   4. **Affine chart substitution.** Let $\tau_\circ=\{\circ\}\sqcup\tau$ and $\Pi_\tau=\{\star\}\sqcup\tau_\circ$, and let $e$ be a continuous linear automorphism of $\mathbb{C}^{\Pi_\tau}$. The $\mathbb{C}$-algebra homomorphism $A_e:\mathbb{C}[y_p : p\in\Pi_\tau]\to\mathbb{C}[z_i : i\in\tau_\circ]$ is the substitution
--   $$y_p\longmapsto\bigl(e^{-1}\mathbf{1}_\star\bigr)_p+\sum_{i\in\tau_\circ}\bigl(e^{-1}\mathbf{1}_i\bigr)_p\,z_i\qquad(p\in\Pi_\tau),$$
--   where $\mathbf{1}_q$ is the standard basis vector at $q$. Equivalently $(A_ef)(z)=f\bigl(e^{-1}(1,z)\bigr)$: the polynomial $f$ is pulled back to the affine hyperplane $\{y : e(y)_\star=1\}$, parametrized by $z\in\mathbb{C}^{\tau_\circ}$.
--   5. **Polar operator.** For $w=(w_{ip})\in\mathbb{C}^{\tau\times\Pi_\tau}$ and $i\in\tau$, the linear operator $D^w_i=\sum_{p\in\Pi_\tau}w_{ip}\,\partial_p$ on $\mathbb{C}[y_p : p\in\Pi_\tau]$, the derivative in the direction $(w_{ip})_p$.
--   6. **Affine polar operators.** The family of linear maps $\mathbb{C}[y_p : p\in\Pi_\tau]\to\mathbb{C}[z_i : i\in\tau_\circ]$ indexed by $\tau_\circ$, given by $\circ\mapsto A_e$ and $i\mapsto A_e\circ D^w_i$ for $i\in\tau$. With these maps, $\Phi_{L,f}(z)=\bigl(f(e^{-1}(1,z)),\ ((D^w_if)(e^{-1}(1,z)))_{i\in\tau}\bigr)$ is the polar system of $f$ written in the affine chart: $m+1$ equations in $m+1$ unknowns, where $m=|\tau|$.
--
--   These notions organize the perturbation argument for border determinants. If a polynomial has $k$ distinct simple zeros of its chart polar system, then every polynomial whose coefficients (in a fixed exponent cube) are close enough to it also has $k$ distinct simple zeros, so zero counts pass from a limit polynomial to the exact determinants that approximate it.
--
--   **Formalization Note** The ring $\mathbb{C}[x_\sigma]$ is `Poly σ = MvPolynomial σ ℂ`. The objects are `polynomialSystem`, `coefficientSystem` (its coefficient argument is a function on the subtype of `exponentCube n`), `SimplePolynomialZero` (invertibility is `ContinuousLinearMap.IsInvertible` of `fderiv ℂ`), `affineChartSubstitution` (an instance of `affineSubstitution`), `polarOperator` and `affinePolarOperators`. Here $\Pi_\tau$ is `PolarVars τ = Option (Option τ)` with $\star$ = `none`, and $\tau_\circ$ is `Option τ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/BorderPolars.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/BorderPolars.lean by skeleton subtraction
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
import Definitions.Def_OAI_Algebra_Determinantal_Model

namespace OAI

namespace PermanentBorder.PolarAnalysis
open MvPolynomial Filter
open scoped Topology

section PolynomialSystem
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def polynomialSystem (L : τ → Poly σ →ₗ[ℂ] Poly τ)
    (P : Poly σ) (x : τ → ℂ) : τ → ℂ := fun i => MvPolynomial.eval x (L i P)

noncomputable def coefficientSystem (n : ℕ) (L : τ → Poly σ →ₗ[ℂ] Poly τ)
    (u : ((exponentCube (σ := σ) n) → ℂ) × (τ → ℂ)) : τ → ℂ :=
  fun i => ∑ d : exponentCube (σ := σ) n,
    u.1 d * MvPolynomial.eval u.2 (L i (monomial d.val 1))

def SimplePolynomialZero (L : τ → Poly σ →ₗ[ℂ] Poly τ) (P : Poly σ) (x : τ → ℂ) :=
  polynomialSystem L P x = 0 ∧ (fderiv ℂ (polynomialSystem L P) x).IsInvertible

end PolynomialSystem
end PermanentBorder.PolarAnalysis
namespace PermanentBorder.Polar
open MvPolynomial
open scoped Classical
variable {τ : Type*} [Fintype τ]

noncomputable def affineChartSubstitution
    (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ)) :
    Poly (PolarVars τ) →ₐ[ℂ] Poly (Option τ) :=
  affineSubstitution (fun j => e.symm (Pi.single none 1) j)
    (fun j i => e.symm (Pi.single (some i) 1) j)

noncomputable def polarOperator (w : τ → PolarVars τ → ℂ) (i : τ) :
    Poly (PolarVars τ) →ₗ[ℂ] Poly (PolarVars τ) :=
  ∑ j, w i j • (pderiv j).toLinearMap

noncomputable def affinePolarOperators (w : τ → PolarVars τ → ℂ)
    (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ)) :
    Option τ → Poly (PolarVars τ) →ₗ[ℂ] Poly (Option τ) :=
  Option.elim' (affineChartSubstitution e).toLinearMap
    (fun i => (affineChartSubstitution e).toLinearMap.comp (polarOperator w i))

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open MvPolynomial Matrix PolarAnalysis KernelBilinear
open scoped Classical
variable {τ : Type} [Fintype τ]

end PermanentBorder.Polar

namespace PermanentBorder.Polar

end PermanentBorder.Polar

namespace PermanentBorder
open MvPolynomial
open scoped Classical

namespace Polar

end Polar
end PermanentBorder

end OAI


