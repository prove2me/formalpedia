-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Presentation__CommutingDerivations
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_Presentation__CommutingDerivations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:30:51.935794+00:00
-- url     : https://prove2.me/theorems/395d770a-a3d9-4b55-8763-43b250bc5c62
-- title:
--   Elimination maps between the lifting presentation and $\mathbb{C}[h,u,v,w]/(F)$
-- statement:
--   Let $R=\mathbb{C}[h,u,v,w]$ and put $x=u^3+hv$, $y=-u^2+hw$, $s=S(h,u,v,w)$ and $F=h-P(x,y,s)-1$ in $R$, where $S(h,u,v,w)=2u^3v+3u^4w+h(v^2-3u^2w^2)+h^2w^3$ and $P(x,y,s)=-2s^2x+3sy^2-3s^3y$. Consider the three $\mathbb{C}$-algebras
--
--   $$
--   D=R/(F),\qquad B=\mathbb{C}[h,x,y,s]\big/\bigl(h-1-P(x,y,s),\ x^2+y^3-sh\bigr),
--   $$
--
--   $$
--   L=B[U,V,W]\big/\bigl(U^3+h_BV-x_B,\ -U^2+h_BW-y_B,\ S(h_B,U,V,W)-s_B\bigr),
--   $$
--
--   where $h_B,x_B,y_B,s_B\in B$ are the classes of the variables; thus $B$ is the plane presentation and $L$ the lifting quotient over $B$. Write $[f]$ for the class in $D$ of $f\in R$ and $U_L,V_L,W_L$ for the classes of the variables in $L$. The file constructs the following $\mathbb{C}$-algebra homomorphisms (besides the quotient map $R\to D$ and the structure map $B\to L$).
--
--   1. **Auxiliary variables into $D$.** The map $B\to D$ with $h_B\mapsto[h]$, $x_B\mapsto[x]$, $y_B\mapsto[y]$, $s_B\mapsto[s]$. It is well defined because $h-1-P(x,y,s)=F$ and $x^2+y^3-sh=0$ hold in $R$.
--
--   2. **From the lifting presentation to $D$.** The map $\tau:L\to D$ that agrees with the previous map on $B$ and sends $U_L\mapsto[u]$, $V_L\mapsto[v]$, $W_L\mapsto[w]$; the three lifting relations go to $[u^3+hv-x]=0$, $[-u^2+hw-y]=0$ and $[S(h,u,v,w)-s]=0$.
--
--   3. **From $D$ to the lifting presentation.** The map $\varphi:D\to L$ induced by the homomorphism $R\to L$ with $h\mapsto h_B$, $u\mapsto U_L$, $v\mapsto V_L$, $w\mapsto W_L$. By the lifting relations this homomorphism sends $x,y,s$ to $x_B,y_B,s_B$, hence $F$ to $h_B-P(x_B,y_B,s_B)-1=0$, so it factors through $D$.
--
--   The accompanying results show that $\tau$ and $\varphi$ are mutually inverse, so the coordinate ring of the hypersurface $F=0$ in $\mathbb{C}^4$ is identified with the lifting presentation and the auxiliary variables $x,y,s$ are eliminated. Combined with the isomorphism $B\cong\mathbb{C}[a,b]$ of the plane presentation and the one-variable lifting isomorphism, this shows that $D$ is a polynomial algebra in three variables.
--
--   **Formalization Note** `B`, `hB`, `xB`, `yB`, `sB`, `L` and `D` are abbreviations; `dmap` is the quotient map $R\to D$ (with `dmap_F`), `lcoef` the structure map $B\to L$ and `lvar` the classes $U_L,V_L,W_L$. Item 1 is `auxToD` (built from `auxValues`, `auxEval` and the lemmas `auxEval_h`, `auxEval_cusp`), item 2 is `toOriginal` (built from `liftValues`, the coefficient-twisted evaluation `liftEval` and `liftEval_x`, `liftEval_y`, `liftEval_s`), and item 3 is `fromOriginal` (built from `originalValues`, `originalEval` and `originalEval_F`); the remaining members are simp lemmas evaluating these maps on generators.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Presentation.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Presentation.lean by skeleton subtraction
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
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Plane__CommutingDerivations

namespace OAI

/-!
# Elimination of auxiliary variables

Explicit mutually inverse complex algebra maps identify the lifting presentation
with the quotient of the original polynomial ring by `(F)`.
-/

noncomputable section
namespace AbhyankarSathaye.Presentation
open MvPolynomial

abbrev B := Plane.Q ℂ
abbrev hB : B := Plane.qvar ℂ 0
abbrev xB : B := Plane.qvar ℂ 1
abbrev yB : B := Plane.qvar ℂ 2
abbrev sB : B := Plane.qvar ℂ 3
abbrev L := Lifting.Q hB xB yB sB
abbrev D := R ⧸ Ideal.span {F}

def dmap : R →ₐ[ℂ] D := Ideal.Quotient.mkₐ ℂ (Ideal.span {F})
def lcoef : B →ₐ[ℂ] L := IsScalarTower.toAlgHom ℂ B L
def lvar (i : Fin 3) : L := Lifting.qvar hB xB yB sB i

theorem dmap_F : dmap F = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

def auxValues : Fin 4 → D := ![dmap h, dmap x, dmap y, dmap s]
def auxEval : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] D := aeval auxValues

theorem auxEval_h : auxEval (Plane.relH ℂ) = 0 := by
  calc
    _ = dmap (h-1-p) := by simp [Plane.relH, auxEval, auxValues, p]
    _ = dmap F := by congr 1; unfold F; ring
    _ = 0 := dmap_F

theorem auxEval_cusp : auxEval (Plane.relCusp ℂ) = 0 := by
  calc
    _ = dmap (x^2+y^3-s*h) := by simp [Plane.relCusp, auxEval, auxValues]
    _ = 0 := by rw [cusp]; simp [mul_comm]

def auxToD : B →ₐ[ℂ] D :=
  lift_pair (Plane.relH ℂ) (Plane.relCusp ℂ) auxEval auxEval_h auxEval_cusp

@[simp] theorem auxToD_qvar (i : Fin 4) : auxToD (Plane.qvar ℂ i) = auxValues i := by
  change aeval auxValues (X i) = auxValues i
  exact aeval_X _ _

def liftValues : Fin 3 → D := ![dmap u, dmap v, dmap w]
def liftEval : MvPolynomial (Fin 3) B →ₐ[ℂ] D := aevalTower auxToD liftValues

theorem liftEval_x : liftEval (Lifting.relX hB xB) = 0 := by
  simp [liftEval, Lifting.relX, liftValues, auxValues, x]

theorem liftEval_y : liftEval (Lifting.relY hB yB) = 0 := by
  simp [liftEval, Lifting.relY, liftValues, auxValues, y]

theorem liftEval_s : liftEval (Lifting.relS hB sB) = 0 := by
  simp [liftEval, Lifting.relS, liftValues, auxValues, s]

def toOriginal : L →ₐ[ℂ] D :=
  lift_triple (Lifting.relX hB xB) (Lifting.relY hB yB) (Lifting.relS hB sB)
    liftEval liftEval_x liftEval_y liftEval_s

@[simp] theorem toOriginal_lvar (i : Fin 3) : toOriginal (lvar i) = liftValues i := by
  change aevalTower auxToD liftValues (X i) = liftValues i
  exact aevalTower_X _ _ _

@[simp] theorem toOriginal_lcoef (b : B) : toOriginal (lcoef b) = auxToD b := by
  change aevalTower auxToD liftValues (C b) = auxToD b
  simp

def originalValues : Fin 4 → L := ![lcoef hB, lvar 0, lvar 1, lvar 2]
def originalEval : R →ₐ[ℂ] L := aeval originalValues

@[simp] theorem originalEval_h : originalEval h = lcoef hB := by
  simp [originalEval, originalValues, h]
@[simp] theorem originalEval_u : originalEval u = lvar 0 := by
  simp [originalEval, originalValues, u]
@[simp] theorem originalEval_v : originalEval v = lvar 1 := by
  simp [originalEval, originalValues, v]
@[simp] theorem originalEval_w : originalEval w = lvar 2 := by
  simp [originalEval, originalValues, w]

@[simp] theorem originalEval_x : originalEval x = lcoef xB := by
  simpa [x, lcoef, lvar] using (Lifting.quotient_relations hB xB yB sB).1
@[simp] theorem originalEval_y : originalEval y = lcoef yB := by
  simpa [y, lcoef, lvar] using (Lifting.quotient_relations hB xB yB sB).2.1
@[simp] theorem originalEval_s : originalEval s = lcoef sB := by
  simpa [s, lcoef, lvar] using (Lifting.quotient_relations hB xB yB sB).2.2

theorem originalEval_F : originalEval F = 0 := by
  have hh : hB = 1+P xB yB sB := Plane.relation_h ℂ
  have he : hB-P xB yB sB-1 = 0 := by rw [hh]; ring
  simpa [F, p] using congrArg lcoef he

def fromOriginal : D →ₐ[ℂ] L := by
  have hi : Ideal.span {F} ≤ RingHom.ker originalEval := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact originalEval_F
  exact Ideal.Quotient.liftₐ _ originalEval (fun z hz => hi hz)

@[simp] theorem fromOriginal_dmap (f : R) : fromOriginal (dmap f) = originalEval f := rfl

end AbhyankarSathaye.Presentation

end

end OAI


