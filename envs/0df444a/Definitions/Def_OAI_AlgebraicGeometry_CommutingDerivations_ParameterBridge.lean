-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterBridge
-- name    : OAI_AlgebraicGeometry_CommutingDerivations_ParameterBridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:27:29.134126+00:00
-- url     : https://prove2.me/theorems/0a488314-615b-4617-9c73-e8289ca02429
-- title:
--   Explicit polynomial coordinates on the fibre $h-P(x,y,s)=c$ for an invertible parameter $c$
-- statement:
--   Let $K$ be any commutative ring (the zero ring is allowed) and let $c,d\in K$. In $K[h,u,v,w]$ put $x=u^3+hv$, $y=-u^2+hw$ and $s=S(h,u,v,w)$. Let $P$ be the cubic expression $P(x,y,s)=-2s^2x+3sy^2-3s^3y$, and let $A_c$, $B_c$ be the relative Bézout coefficients. The file builds two families of objects and maps between them.
--
--   1. **The fibre ring.** $Q_c=K[h,u,v,w]/\bigl(h-P(x,y,s)-c\bigr)$, with its quotient map, its structure map $K\to Q_c$, and the classes $\bar h,\bar u,\bar v,\bar w,\bar x,\bar y,\bar s$. In $Q_c$ the file defines
--      $$\bar\alpha=d^2A_c(\bar x,\bar s),\qquad \bar\beta=d^2B_c(\bar x,\bar y,\bar s),\qquad \bar T=\bar\alpha\,\bar u+\bar\beta\,(\bar v+\bar u\bar w).$$
--      It proves $\bar h=c+P(\bar x,\bar y,\bar s)$ and $\bar x^2+\bar y^3=\bar s\,\bar h$, and, when $cd=1$, also $d\bigl((\bar x+\bar s^3)^2+(\bar y-\bar s^2)^3\bigr)=\bar s$.
--   2. **Free formulas.** In $K[X,Y,T]$ the file defines
--      $$\sigma=d\,(X^2+Y^3),\quad \xi=X-\sigma^3,\quad \eta=Y+\sigma^2,\quad \chi=c+P(\xi,\eta,\sigma),\quad a=d^2A_c(\xi,\sigma),\quad b=d^2B_c(\xi,\eta,\sigma),$$
--      and, through the reconstruction formulas, $U=\chi T-b\xi$, $G=\eta T+a\xi$, $W=a(1+b\eta)(\eta+U^2)+b^2(\sigma-\chi G^2+2U\eta G)$ and $V=G-UW$. If $cd=1$, then $\xi^2+\eta^3=\sigma\chi$ and $a\chi+b\eta=1$, and $U^3+\chi V=\xi$, $-U^2+\chi W=\eta$, $S(\chi,U,V,W)=\sigma$.
--   3. **Forward map.** The $K$-algebra map $K[h,u,v,w]\to K[X,Y,T]$ sends $(h,u,v,w)\mapsto(\chi,U,V,W)$. When $cd=1$, it sends $x\mapsto\xi$, $y\mapsto\eta$ and $s\mapsto\sigma$ and kills $h-P(x,y,s)-c$, so it induces a $K$-algebra map $Q_c\to K[X,Y,T]$.
--   4. **Backward map.** The $K$-algebra map $K[X,Y,T]\to Q_c$ sends $X\mapsto\bar x+\bar s^3$, $Y\mapsto\bar y-\bar s^2$ and $T\mapsto\bar T$. When $cd=1$, it sends $\sigma,\xi,\eta,\chi,a,b$ to $\bar s,\bar x,\bar y,\bar h,\bar\alpha,\bar\beta$.
--
--   On the fibre $h=c+P(x,y,s)$ with $c$ a unit, the functions $x+s^3$, $y-s^2$ and $\bar T$ are designed to be free coordinates, and the forward and backward maps are the two halves of the corresponding identification of $Q_c$ with $K[X,Y,T]$. The free formulas are reused with $K=\mathbb{C}[t,t^{-1}]$, $c=t$ and $d=t^{-1}$ to define the isomorphism of the localization of $\mathbb{C}[h,u,v,w]$ at $F+1$ with $\mathbb{C}[t,t^{-1}][X,Y,T]$.
--
--   **Formalization Note** Everything lives in the namespace `ParameterBridge`. The fibre ring is `Q K c` and the classes are `qH`, …, `qT`. The free formulas are `freeS`, `freeX`, `freeY`, `freeH`, `freeAlpha`, `freeBeta`, `freeU`, `freeG`, `freeW` and `freeV`. The maps are `evaluation`, `forward` and `backward`, and the inverse of $c$ is passed as $d$ with the hypothesis `c * d = 1`. This file contains the maps and their values on generators only. Neither composite is shown here to be the identity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/ParameterBridge.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/ParameterBridge.lean by skeleton subtraction
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

namespace OAI

/-!
Explicit relative polynomial coordinates with an invertible parameter.

The coefficient ring is arbitrary, including the zero ring. In the localization
application it is the Laurent coefficient ring `ℂ[c,c⁻¹]`. The relative
presentation is explicitly isomorphic to a polynomial algebra in three variables.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations.ParameterBridge
open MvPolynomial

variable (K : Type*) [CommRing K]

-- Original independent variable order: h,u,v,w.
def rawH : MvPolynomial (Fin 4) K := X 0
def rawU : MvPolynomial (Fin 4) K := X 1
def rawV : MvPolynomial (Fin 4) K := X 2
def rawW : MvPolynomial (Fin 4) K := X 3
def rawX : MvPolynomial (Fin 4) K := rawU K^3+rawH K*rawV K
def rawY : MvPolynomial (Fin 4) K := -rawU K^2+rawH K*rawW K
def rawS : MvPolynomial (Fin 4) K := S (rawH K) (rawU K) (rawV K) (rawW K)
def relation (c : K) : MvPolynomial (Fin 4) K :=
  rawH K-P (rawX K) (rawY K) (rawS K)-C c
abbrev Q (c : K) := MvPolynomial (Fin 4) K ⧸ Ideal.span {relation K c}
def qmap (c : K) : MvPolynomial (Fin 4) K →ₐ[K] Q K c :=
  Ideal.Quotient.mkₐ K (Ideal.span {relation K c})
def coeff (c : K) : K →+* Q K c := algebraMap K _
def qH (c : K) : Q K c := qmap K c (rawH K)
def qU (c : K) : Q K c := qmap K c (rawU K)
def qV (c : K) : Q K c := qmap K c (rawV K)
def qW (c : K) : Q K c := qmap K c (rawW K)
def qX (c : K) : Q K c := qmap K c (rawX K)
def qY (c : K) : Q K c := qmap K c (rawY K)
def qS (c : K) : Q K c := qmap K c (rawS K)
def qAlpha (c d : K) : Q K c :=
  coeff K c d^2*parameterA (coeff K c c) (qX K c) (qS K c)
def qBeta (c d : K) : Q K c :=
  coeff K c d^2*parameterB (coeff K c c) (qX K c) (qY K c) (qS K c)
def qT (c d : K) : Q K c :=
  parameter (qAlpha K c d) (qBeta K c d) (qU K c) (qV K c) (qW K c)

theorem quotient_relation (c : K) :
    qH K c = coeff K c c+P (qX K c) (qY K c) (qS K c) := by
  have hz : qmap K c (relation K c) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have he : qH K c-P (qX K c) (qY K c) (qS K c)-coeff K c c = 0 := by
    simpa [relation, qH, qX, qY, qS, coeff] using hz
  calc
    _ = (qH K c-P (qX K c) (qY K c) (qS K c)-coeff K c c)+
        (coeff K c c+P (qX K c) (qY K c) (qS K c)) := by ring
    _ = _ := by rw [he, zero_add]

theorem quotient_cusp (c : K) : (qX K c)^2+(qY K c)^3 = qS K c*qH K c := by
  have he := congrArg (qmap K c)
    (cusp_universal (rawH K) (rawU K) (rawV K) (rawW K))
  simpa [qX, qY, qS, qH, rawX, rawY, rawS, mul_comm] using he

theorem quotient_recover_s (c d : K) (hunit : c*d=1) :
    coeff K c d*((qX K c+(qS K c)^3)^2+(qY K c-(qS K c)^2)^3) = qS K c := by
  have hu : coeff K c c*coeff K c d=1 := by
    simpa using congrArg (coeff K c) hunit
  exact parameter_recover_s _ _ _ _ _ _
    (quotient_cusp K c) (quotient_relation K c) hu

-- Free independent variable order: X,Y,T.
def freeS (d : K) : MvPolynomial (Fin 3) K := C d*(X 0^2+X 1^3)
def freeX (d : K) : MvPolynomial (Fin 3) K := X 0-(freeS K d)^3
def freeY (d : K) : MvPolynomial (Fin 3) K := X 1+(freeS K d)^2
def freeH (c d : K) : MvPolynomial (Fin 3) K :=
  C c+P (freeX K d) (freeY K d) (freeS K d)
def freeAlpha (c d : K) : MvPolynomial (Fin 3) K :=
  C d^2*parameterA (C c) (freeX K d) (freeS K d)
def freeBeta (c d : K) : MvPolynomial (Fin 3) K :=
  C d^2*parameterB (C c) (freeX K d) (freeY K d) (freeS K d)
def freeU (c d : K) : MvPolynomial (Fin 3) K :=
  inverseU (freeH K c d) (freeX K d) (freeBeta K c d) (X 2)
def freeG (c d : K) : MvPolynomial (Fin 3) K :=
  inverseG (freeX K d) (freeY K d) (freeAlpha K c d) (X 2)
def freeW (c d : K) : MvPolynomial (Fin 3) K :=
  inverseW (freeH K c d) (freeY K d) (freeS K d) (freeAlpha K c d)
    (freeBeta K c d) (freeU K c d) (freeG K c d)
def freeV (c d : K) : MvPolynomial (Fin 3) K :=
  inverseV (freeU K c d) (freeG K c d) (freeW K c d)

theorem free_cusp (c d : K) (hunit : c*d=1) :
    (freeX K d)^2+(freeY K d)^3=freeS K d*freeH K c d := by
  have hu : (C c : MvPolynomial (Fin 3) K)*C d=1 := by
    simpa using congrArg (C : K →+* MvPolynomial (Fin 3) K) hunit
  have hs : C c*freeS K d=X 0^2+X 1^3 := by
    rw [freeS, ← mul_assoc, hu, one_mul]
  have he := shift_universal (freeX K d) (freeY K d) (freeS K d)
  have hx : freeX K d+(freeS K d)^3=X 0 := by unfold freeX; ring
  have hy : freeY K d-(freeS K d)^2=X 1 := by unfold freeY; ring
  rw [hx, hy, ← hs] at he
  calc
    _ = C c*freeS K d+freeS K d*P (freeX K d) (freeY K d) (freeS K d) :=
      (eq_sub_iff_add_eq.mp he).symm
    _ = _ := by unfold freeH; ring

theorem free_bezout (c d : K) (hunit : c*d=1) :
    freeAlpha K c d*freeH K c d+freeBeta K c d*freeY K d=1 := by
  have hu : (C c : MvPolynomial (Fin 3) K)*C d=1 := by
    simpa using congrArg (C : K →+* MvPolynomial (Fin 3) K) hunit
  exact parameter_bezout_unit _ _ _ _ _ _ (free_cusp K c d hunit) rfl hu

theorem free_relations (c d : K) (hunit : c*d=1) :
    (freeU K c d)^3+freeH K c d*freeV K c d=freeX K d ∧
    -(freeU K c d)^2+freeH K c d*freeW K c d=freeY K d ∧
    S (freeH K c d) (freeU K c d) (freeV K c d) (freeW K c d)=freeS K d := by
  exact inverse_relations _ _ _ _ _ _ _
    (by simpa [mul_comm] using free_cusp K c d hunit) (free_bezout K c d hunit)

def values (c d : K) : Fin 4 → MvPolynomial (Fin 3) K :=
  ![freeH K c d, freeU K c d, freeV K c d, freeW K c d]
def evaluation (c d : K) : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 3) K :=
  aeval (values K c d)

@[simp] theorem evaluation_h (c d : K) : evaluation K c d (rawH K)=freeH K c d := by
  simp [evaluation, values, rawH]
@[simp] theorem evaluation_u (c d : K) : evaluation K c d (rawU K)=freeU K c d := by
  simp [evaluation, values, rawU]
@[simp] theorem evaluation_v (c d : K) : evaluation K c d (rawV K)=freeV K c d := by
  simp [evaluation, values, rawV]
@[simp] theorem evaluation_w (c d : K) : evaluation K c d (rawW K)=freeW K c d := by
  simp [evaluation, values, rawW]
@[simp] theorem evaluation_x (c d : K) (hunit : c*d=1) :
    evaluation K c d (rawX K)=freeX K d := by
  simpa [rawX] using (free_relations K c d hunit).1
@[simp] theorem evaluation_y (c d : K) (hunit : c*d=1) :
    evaluation K c d (rawY K)=freeY K d := by
  simpa [rawY] using (free_relations K c d hunit).2.1
@[simp] theorem evaluation_s (c d : K) (hunit : c*d=1) :
    evaluation K c d (rawS K)=freeS K d := by
  simpa [rawS] using (free_relations K c d hunit).2.2

theorem evaluation_relation (c d : K) (hunit : c*d=1) :
    evaluation K c d (relation K c)=0 := by
  simp only [relation, map_sub, map_P, evaluation_h, evaluation_x K c d hunit,
    evaluation_y K c d hunit, evaluation_s K c d hunit]
  simp [evaluation, freeH]

def forward (c d : K) (hunit : c*d=1) : Q K c →ₐ[K] MvPolynomial (Fin 3) K := by
  have hi : Ideal.span {relation K c} ≤ RingHom.ker (evaluation K c d) := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact evaluation_relation K c d hunit
  exact Ideal.Quotient.liftₐ _ (evaluation K c d) (fun z hz => hi hz)

@[simp] theorem forward_qmap (c d : K) (hunit : c*d=1) (f) :
    forward K c d hunit (qmap K c f)=evaluation K c d f := rfl

def backward (c d : K) : MvPolynomial (Fin 3) K →ₐ[K] Q K c :=
  aeval ![qX K c+(qS K c)^3, qY K c-(qS K c)^2, qT K c d]

@[simp] theorem backward_X2 (c d : K) :
    backward K c d (X 2)=qT K c d := by simp [backward]

@[simp] theorem backward_freeS (c d : K) (hunit : c*d=1) :
    backward K c d (freeS K d)=qS K c := by
  simpa [backward, freeS, coeff] using quotient_recover_s K c d hunit
@[simp] theorem backward_freeX (c d : K) (hunit : c*d=1) :
    backward K c d (freeX K d)=qX K c := by
  simp only [freeX, map_sub, map_pow, backward_freeS K c d hunit]
  simp [backward]
@[simp] theorem backward_freeY (c d : K) (hunit : c*d=1) :
    backward K c d (freeY K d)=qY K c := by
  simp only [freeY, map_add, map_pow, backward_freeS K c d hunit]
  simp [backward]
@[simp] theorem backward_freeH (c d : K) (hunit : c*d=1) :
    backward K c d (freeH K c d)=qH K c := by
  simpa [freeH, backward_freeX K c d hunit, backward_freeY K c d hunit,
    backward_freeS K c d hunit, coeff] using (quotient_relation K c).symm
@[simp] theorem backward_freeAlpha (c d : K) (hunit : c*d=1) :
    backward K c d (freeAlpha K c d)=qAlpha K c d := by
  simp [freeAlpha, qAlpha, coeff, backward_freeX K c d hunit,
    backward_freeS K c d hunit]
@[simp] theorem backward_freeBeta (c d : K) (hunit : c*d=1) :
    backward K c d (freeBeta K c d)=qBeta K c d := by
  simp [freeBeta, qBeta, coeff, backward_freeX K c d hunit,
    backward_freeY K c d hunit, backward_freeS K c d hunit]

end AbhyankarSathaye.CommutingDerivations.ParameterBridge

end

end OAI


