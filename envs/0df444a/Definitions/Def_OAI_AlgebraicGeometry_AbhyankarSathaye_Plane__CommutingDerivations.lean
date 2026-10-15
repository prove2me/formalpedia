-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Plane__CommutingDerivations
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_Plane__CommutingDerivations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:29:47.937044+00:00
-- url     : https://prove2.me/theorems/36805ce2-3fe9-41a8-8727-748aebfa9732
-- title:
--   Polynomial presentation of the affine plane by $h=1+P(x,y,s)$ and $x^2+y^3=hs$
-- statement:
--   Let $K$ be a commutative ring and let $P(x,y,s)=-2s^2x+3sy^2-3s^3y$. The file introduces the following objects.
--
--   1. **Plane presentation.** The quotient $K$-algebra
--
--      $$Q_K=K[h,x,y,s]\big/\bigl(h-1-P(x,y,s),\ x^2+y^3-sh\bigr),$$
--
--      its quotient map, and the classes $\bar h,\bar x,\bar y,\bar s$ of the four variables. In $Q_K$ one has $\bar h=1+P(\bar x,\bar y,\bar s)$, $\bar x^2+\bar y^3=\bar h\bar s$, and consequently
--
--      $$(\bar x+\bar s^3)^2+(\bar y-\bar s^2)^3=\bar s .$$
--
--   2. **Parametrization by the plane.** In the polynomial ring $K[a,b]$ in two variables put
--
--      $$\hat s=a^2+b^3,\qquad \hat x=a-\hat s^3,\qquad \hat y=b+\hat s^2,\qquad \hat h=1+P(\hat x,\hat y,\hat s);$$
--
--      these satisfy $\hat x^2+\hat y^3=\hat h\hat s$.
--
--   3. **The two maps.** The $K$-algebra homomorphism $\Phi:Q_K\to K[a,b]$ with $(\bar h,\bar x,\bar y,\bar s)\mapsto(\hat h,\hat x,\hat y,\hat s)$, and the $K$-algebra homomorphism $\Psi:K[a,b]\to Q_K$ with $a\mapsto\bar x+\bar s^3$ and $b\mapsto\bar y-\bar s^2$. One has $\Psi(\hat s)=\bar s$, $\Psi(\hat x)=\bar x$, $\Psi(\hat y)=\bar y$ and $\Psi(\hat h)=\bar h$.
--
--   The maps $\Phi$ and $\Psi$ are mutually inverse (shown in accompanying results), so $Q_K$ is a polynomial algebra in the two coordinates $x+s^3$ and $y-s^2$: the affine scheme defined by $h=1+P(x,y,s)$ and $x^2+y^3=hs$ is an affine plane over $K$. For $K=\mathbb{C}$ this ring is the base over which the lifting presentation of the hypersurface $F=0$ in $\mathbb{C}^4$ is built, with $h,x,y,s$ playing the roles of $h$, $u^3+hv$, $-u^2+hw$ and $S(h,u,v,w)$.
--
--   **Formalization Note** The variables of `MvPolynomial (Fin 4) K` are ordered $h,x,y,s$ and those of `MvPolynomial (Fin 2) K` are $a,b$. Lean names: `relH`, `relCusp`, `ideal`, `Q`, `qmap`, `qvar` and the identities `relation_h`, `relation_cusp`, `shift_s` (item 1); `planeS`, `planeX`, `planeY`, `planeH`, `values` and `plane_cusp` (item 2); `forward` and `backward` with the simp lemmas `forward_qvar`, `backward_planeS`, `backward_planeX`, `backward_planeY`, `backward_planeH` (item 3).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Plane.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Plane.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CommutingDerivations mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Identities__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterBezout
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LiftingIdentities__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Reconstruction__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Quotient__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizationSetup
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_CoefficientInstances
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterBridge
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizationEquivalence
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Lifting__CommutingDerivations

namespace OAI

/-!
# A polynomial presentation of the affine plane

The relations `h = 1 + P x y s` and `x² + y³ = h * s` give a polynomial
algebra with coordinates `x + s³` and `y - s²`. The auxiliary variables are
ordered as `h, x, y, s`.
-/

noncomputable section
namespace AbhyankarSathaye.Plane
open MvPolynomial

variable (K : Type*) [CommRing K]

def relH : MvPolynomial (Fin 4) K := X 0-1-P (X 1) (X 2) (X 3)
def relCusp : MvPolynomial (Fin 4) K := X 1^2+X 2^3-X 3*X 0
def ideal : Ideal (MvPolynomial (Fin 4) K) := Ideal.span {relH K, relCusp K}
abbrev Q := MvPolynomial (Fin 4) K ⧸ ideal K
def qmap : MvPolynomial (Fin 4) K →ₐ[K] Q K := Ideal.Quotient.mkₐ K (ideal K)
def qvar (i : Fin 4) : Q K := qmap K (X i)

theorem relation_h : qvar K 0 = 1+P (qvar K 1) (qvar K 2) (qvar K 3) := by
  have hz : qmap K (relH K) = 0 := quotient_pair_left (relH K) (relCusp K)
  have hh : qvar K 0-1-P (qvar K 1) (qvar K 2) (qvar K 3) = 0 := by
    simpa [relH, qvar] using hz
  calc
    _ = (qvar K 0-1-P (qvar K 1) (qvar K 2) (qvar K 3))+
        (1+P (qvar K 1) (qvar K 2) (qvar K 3)) := by ring
    _ = _ := by rw [hh, zero_add]

theorem relation_cusp : (qvar K 1)^2+(qvar K 2)^3 = qvar K 0*qvar K 3 := by
  have hz : qmap K (relCusp K) = 0 := quotient_pair_right (relH K) (relCusp K)
  have hh : (qvar K 1)^2+(qvar K 2)^3-qvar K 3*qvar K 0 = 0 := by
    simpa [relCusp, qvar] using hz
  simpa [mul_comm] using sub_eq_zero.mp hh

theorem shift_s : (qvar K 1+(qvar K 3)^3)^2+(qvar K 2-(qvar K 3)^2)^3 = qvar K 3 := by
  rw [shift_universal, relation_cusp, relation_h]
  ring

def planeS : MvPolynomial (Fin 2) K := X 0^2+X 1^3
def planeX : MvPolynomial (Fin 2) K := X 0-(planeS K)^3
def planeY : MvPolynomial (Fin 2) K := X 1+(planeS K)^2
def planeH : MvPolynomial (Fin 2) K := 1+P (planeX K) (planeY K) (planeS K)
def values : Fin 4 → MvPolynomial (Fin 2) K :=
  ![planeH K, planeX K, planeY K, planeS K]

theorem plane_cusp : (planeX K)^2+(planeY K)^3 = planeH K*planeS K := by
  have he := shift_universal (planeX K) (planeY K) (planeS K)
  have hx : planeX K+(planeS K)^3 = X 0 := by unfold planeX; ring
  have hy : planeY K-(planeS K)^2 = X 1 := by unfold planeY; ring
  rw [hx, hy] at he
  change planeS K = (planeX K)^2+(planeY K)^3-planeS K*P (planeX K) (planeY K) (planeS K) at he
  calc
    _ = (planeS K)+planeS K*P (planeX K) (planeY K) (planeS K) := by
      exact (eq_sub_iff_add_eq.mp he).symm
    _ = _ := by unfold planeH; ring

def forward : Q K →ₐ[K] MvPolynomial (Fin 2) K :=
  lift_pair (relH K) (relCusp K) (aeval (values K))
    (by simp [relH, values, planeH])
    (by simp [relCusp, values, plane_cusp, mul_comm])

@[simp] theorem forward_qvar (i : Fin 4) : forward K (qvar K i) = values K i := by
  change aeval (values K) (X i) = values K i
  exact aeval_X _ _

def backward : MvPolynomial (Fin 2) K →ₐ[K] Q K :=
  aeval ![qvar K 1+(qvar K 3)^3, qvar K 2-(qvar K 3)^2]

@[simp] theorem backward_planeS : backward K (planeS K) = qvar K 3 := by
  simpa [backward, planeS] using shift_s K

@[simp] theorem backward_planeX : backward K (planeX K) = qvar K 1 := by
  simp only [planeX, map_sub, map_pow, backward_planeS]
  simp [backward]

@[simp] theorem backward_planeY : backward K (planeY K) = qvar K 2 := by
  simp only [planeY, map_add, map_pow, backward_planeS]
  simp [backward]

@[simp] theorem backward_planeH : backward K (planeH K) = qvar K 0 := by
  simpa [planeH] using (relation_h K).symm

end AbhyankarSathaye.Plane

end

end OAI


