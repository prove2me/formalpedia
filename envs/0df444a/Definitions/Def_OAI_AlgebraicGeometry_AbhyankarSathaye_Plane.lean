-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Plane
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_Plane
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:26:19.482464+00:00
-- url     : https://prove2.me/theorems/2773db1d-65ff-4fad-803f-58037cf5cd66
-- title:
--   A presentation of the affine plane by the relations $h=1+P(x,y,s)$ and $x^2+y^3=hs$
-- statement:
--   Let $K$ be a commutative ring, let $P(x,y,s)=-2s^2x+3sy^2-3s^3y$, and let $\alpha(x,s)=1+2s^2x+4s^5$ and $\beta(x,y,s)=(3s^3-3sy)(1+2s^2x)-4s^4y^2$ be the Bézout coefficients of the construction.
--
--   1. **Plane presentation.** Let $\mathcal P_K$ be the quotient of the polynomial ring $K[h,x,y,s]$ in four variables by the two relations $h-1-P(x,y,s)$ and $x^2+y^3-sh$:
--   $$\mathcal P_K=K[h,x,y,s]\big/\bigl(h-1-P(x,y,s),\ x^2+y^3-sh\bigr).$$
--   Writing $h,x,y,s$ also for their classes, $\mathcal P_K$ satisfies $h=1+P(x,y,s)$ and $x^2+y^3=hs$, and consequently
--   $$(x+s^3)^2+(y-s^2)^3=s,\qquad \alpha(x,s)\,h+\beta(x,y,s)\,y=1 .$$
--   2. **Plane parametrization.** In the polynomial ring $K[X,Y]$ put
--   $$\sigma=X^2+Y^3,\qquad \xi=X-\sigma^3,\qquad \eta=Y+\sigma^2,\qquad \chi=1+P(\xi,\eta,\sigma);$$
--   these satisfy $\xi^2+\eta^3=\chi\,\sigma$.
--   3. **The isomorphism.** The $K$-algebra homomorphisms
--   $$\mathcal P_K\to K[X,Y],\quad (h,x,y,s)\mapsto(\chi,\xi,\eta,\sigma),\qquad K[X,Y]\to\mathcal P_K,\quad (X,Y)\mapsto(x+s^3,\ y-s^2),$$
--   are well defined and mutually inverse; thus $\mathcal P_K\cong K[X,Y]$, with coordinates $x+s^3$ and $y-s^2$.
--
--   For $K=\mathbb{C}$ the algebra $\mathcal P_{\mathbb{C}}$ is the base over which the lifting construction is carried out: it is a polynomial ring in two variables, it satisfies the cusp relation $x^2+y^3=hs$, and in it $h$ and $y$ generate the unit ideal with the explicit coefficients $\alpha$ and $\beta$. These are exactly the hypotheses of the lifting isomorphism.
--
--   **Formalization Note** The variables of `MvPolynomial (Fin 4) K` are ordered `h, x, y, s`; the relations are `relH` and `relCusp`, the quotient is `Q K` with quotient map `qmap K` and generators `qvar K i`, and the facts in item 1 are `relation_h`, `relation_cusp`, `shift_s` and `bezout`. Item 2 consists of `planeS`, `planeX`, `planeY`, `planeH`, `values` and `plane_cusp` (in `MvPolynomial (Fin 2) K`). Item 3 consists of `forward`, `backward`, their evaluation lemmas, `forward_backward`, `backward_forward` and the equivalence `equivalence`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Plane.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Plane.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AbhyankarSathaye mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Identities
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Quotient
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LiftingIdentities
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Reconstruction
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Lifting

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

theorem bezout : Alpha (qvar K 1) (qvar K 3)*qvar K 0+
    Beta (qvar K 1) (qvar K 2) (qvar K 3)*qvar K 2 = 1 := by
  have he := bezout_certificate (qvar K 0) (qvar K 1) (qvar K 2) (qvar K 3)
  have hh : qvar K 0-1-P (qvar K 1) (qvar K 2) (qvar K 3) = 0 := by
    rw [relation_h]; ring
  have hc : (qvar K 1)^2+(qvar K 2)^3-qvar K 3*qvar K 0 = 0 := by
    rw [relation_cusp]; ring
  rw [hh, hc, mul_zero, mul_zero, sub_zero] at he
  exact sub_eq_zero.mp he

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

theorem forward_backward : (forward K).comp (backward K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [backward, values, planeX, planeY]

theorem backward_forward : (backward K).comp (forward K) = AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change backward K (forward K (qvar K i)) = qvar K i
  rw [forward_qvar]
  fin_cases i <;> simp [values]

def equivalence : Q K ≃ₐ[K] MvPolynomial (Fin 2) K :=
  AlgEquiv.ofAlgHom (forward K) (backward K) (forward_backward K) (backward_forward K)

end AbhyankarSathaye.Plane

end

end OAI


