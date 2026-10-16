-- Prove2me | Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
-- name    : OAI_Algebra_Determinantal_SliceCertificates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:12:50.566846+00:00
-- url     : https://prove2.me/theorems/ac87b5c4-7851-4b4d-af57-821855cebd4c
-- title:
--   Straight-line homotopies of polynomial systems and derivations of a generic field
-- statement:
--   This module provides the straight-line homotopy between two polynomial systems and the derivations of a field of generic parameters.
--
--   1. **Straight-line homotopy.** Let $\iota$ be finite and $\hat\iota=\iota\sqcup\{\star\}$, let $H^0=(H^0_i)_{i\in\iota}$ and $H^1=(H^1_i)_{i\in\iota}$ be systems in $\mathbb C[x_j:j\in\hat\iota]$, and let $l^0,l^1\in\mathbb C^{\hat\iota}$. The line system has coefficients in the polynomial ring $\mathbb C[\mathsf t]$: its $i$-th polynomial is $H^0_i+\mathsf t\,(H^1_i-H^0_i)$, and its linear coefficients are $l^0_j+\mathsf t\,(l^1_j-l^0_j)\in\mathbb C[\mathsf t]$. Its specialization at $t\in\mathbb C$ is
--   $$
--   H_i(t)=H^0_i+t\,(H^1_i-H^0_i),\qquad l_j(t)=l^0_j+t\,(l^1_j-l^0_j),
--   $$
--   and at $t=0$ and $t=1$ it gives back $(H^0,l^0)$ and $(H^1,l^1)$.
--
--   2. **Extension of derivations along formally étale maps.** Let $K\to R\to L$ be commutative rings forming a compatible tower of algebras, with $R\to L$ formally étale, and let $D:R\to L$ be a $K$-derivation. Then $D$ induces an $R$-linear map $\Omega_{R/K}\to L$ and its $L$-linear base change $L\otimes_R\Omega_{R/K}\to L$; composing with the inverse of the canonical isomorphism $L\otimes_R\Omega_{R/K}\cong\Omega_{L/K}$ and with the universal derivation $d:L\to\Omega_{L/K}$ gives a $K$-derivation $\widetilde D:L\to L$, which extends $D$.
--
--   3. **Generic field and generic parameters.** For a field $K$ of characteristic zero and a set $\iota$, the generic field is the algebraic closure $\overline{K(t_i:i\in\iota)}$ of the field of rational functions in independent indeterminates $t_i$, and the generic parameter $t_i$ is the image of the variable $X_i$ of $K[X_i:i\in\iota]$. The map $K[X_i:i\in\iota]\to\overline{K(t_i:i\in\iota)}$ is formally étale.
--
--   4. **Parameter derivations.** For $i\in\iota$, $\partial/\partial t_i$ is the $K$-derivation of the generic field obtained by extending, as in item 2, the derivation $K[X]\to\overline{K(t)}$ that sends $X_j$ to $1$ if $j=i$ and to $0$ otherwise; thus $\partial t_j/\partial t_i=\delta_{ij}$.
--
--   If $H^0$ and $H^1$ consist of homogeneous polynomials of the same degrees and both $(H^0,l^0)$ and $(H^1,l^1)$ are good (all nonzero common zeros of the system lie off the hyperplane $\ell=0$ and have nonsingular bordered Jacobian), Macaulay matrices of the line system show that $(H(t),l(t))$ is good for all $t$ outside the zero set of a polynomial $q$ with $q(0)=q(1)=1$. Deforming a good system to the power system $x_i^{e_i}-x_\star^{e_i}$ in this way shows that its number of roots on the chart $\ell=1$ is $\prod_ie_i$. The parameter derivations differentiate polynomial identities with generic coefficients; they are used to show that polar systems in generic directions are good.
--
--   **Formalization Note** The definitions are `CI.Hline` and `CI.lline` (with coefficients in `Polynomial ℂ`), `CI.Htime` and `CI.ltime` (with `simp` lemmas `Htime_zero`, `Htime_one`, `ltime_zero`, `ltime_one`), `Polar.extendDerivation` (requiring `Algebra.FormallyEtale R L`), `Polar.GenericField K ι`, defined as `AlgebraicClosure (FractionRing (MvPolynomial ι K))`, `Polar.genericParameter`, the lemma `generic_formallyEtale` (the formal étaleness in item 3) and `Polar.parameterDerivation`; $\hat\iota$ is `Option ι`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/SliceCertificates.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/SliceCertificates.lean by skeleton subtraction
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

namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters
namespace PermanentBorder.CI
open MvPolynomial PermanentBorder.SliceParameters
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.CI
open Polynomial Matrix
open scoped Classical

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial PermanentBorder.SliceParameters
open scoped Classical
variable {ι : Type*} [Fintype ι]

noncomputable def Hline (H0 H1 : ι → MvPolynomial (Option ι) ℂ) :
    ι → MvPolynomial (Option ι) (Polynomial ℂ) := fun i =>
  map Polynomial.C (H0 i) + C Polynomial.X * (map Polynomial.C (H1 i) - map Polynomial.C (H0 i))
noncomputable def lline (l0 l1 : Option ι → ℂ) : Option ι → Polynomial ℂ := fun j =>
  Polynomial.C (l0 j) + Polynomial.X * (Polynomial.C (l1 j) - Polynomial.C (l0 j))
noncomputable def Htime (H0 H1 : ι → MvPolynomial (Option ι) ℂ) (t : ℂ) :
    ι → MvPolynomial (Option ι) ℂ := fun i => H0 i + C t * (H1 i - H0 i)
noncomputable def ltime (l0 l1 : Option ι → ℂ) (t : ℂ) : Option ι → ℂ := fun j =>
  l0 j + t * (l1 j - l0 j)

omit [Fintype ι] in
@[simp] lemma Htime_zero (H0 H1 : ι → MvPolynomial (Option ι) ℂ) : Htime H0 H1 0 = H0 := by
  funext i; simp [Htime]
omit [Fintype ι] in
@[simp] lemma Htime_one (H0 H1 : ι → MvPolynomial (Option ι) ℂ) : Htime H0 H1 1 = H1 := by
  funext i; simp [Htime]
omit [Fintype ι] in
@[simp] lemma ltime_zero (l0 l1 : Option ι → ℂ) : ltime l0 l1 0 = l0 := by
  funext i; simp [ltime]
omit [Fintype ι] in
@[simp] lemma ltime_one (l0 l1 : Option ι → ℂ) : ltime l0 l1 1 = l1 := by
  funext i; simp [ltime]

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.Polar
open MvPolynomial
open scoped TensorProduct

variable {K R L : Type*} [CommRing K] [CommRing R] [CommRing L]
  [Algebra K R] [Algebra K L] [Algebra R L] [IsScalarTower K R L]

noncomputable def extendDerivation [Algebra.FormallyEtale R L]
    (D : Derivation K R L) : Derivation K L L :=
  ((D.liftKaehlerDifferential.liftBaseChange L).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K R L).symm.toLinearMap).compDer
      (KaehlerDifferential.D K L)

section Generic
universe u v
variable (K : Type u) [Field K] [CharZero K] (ι : Type v)

abbrev GenericField := AlgebraicClosure (FractionRing (MvPolynomial ι K))

noncomputable def genericParameter (i : ι) : GenericField K ι :=
  algebraMap (MvPolynomial ι K) (GenericField K ι) (X i)

lemma generic_formallyEtale :
    Algebra.FormallyEtale (MvPolynomial ι K) (GenericField K ι) := by
  let R := MvPolynomial ι K
  let Q := FractionRing R
  have : Algebra.FormallyEtale R Q :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  have : Algebra.FormallyEtale Q (GenericField K ι) :=
    Algebra.FormallyEtale.of_isSeparable Q (GenericField K ι)
  exact Algebra.FormallyEtale.comp R Q (GenericField K ι)

noncomputable def parameterDerivation (i : ι) :
    Derivation K (GenericField K ι) (GenericField K ι) := by
  classical
  letI := generic_formallyEtale K ι
  exact extendDerivation (MvPolynomial.mkDerivation K (Pi.single i 1))

end Generic

section ChainRule
variable {K L σ : Type*} [CommRing K] [CommRing L] [Algebra K L] [Fintype σ]

end ChainRule
end PermanentBorder.Polar

end OAI


