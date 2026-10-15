-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Presentation
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_Presentation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:27:51.598891+00:00
-- url     : https://prove2.me/theorems/d4adf202-0842-4e5f-9c89-9e6572f924bb
-- title:
--   Eliminating the auxiliary variables: the lifted presentation is isomorphic to $\mathbb{C}[h,u,v,w]/(F)$
-- statement:
--   Notation: $R=\mathbb{C}[h,u,v,w]$, with $x=u^3+hv$, $y=-u^2+hw$, $s=S(h,u,v,w)$ and $F=h-P(x,y,s)-1$ the explicit polynomial, and $D=R/(F)$ is the coordinate ring of the hypersurface $F=0$. Let $\mathcal P=\mathbb{C}[h,x,y,s]/(h-1-P(x,y,s),\ x^2+y^3-sh)$ be the plane presentation, with generators $\bar h,\bar x,\bar y,\bar s$, and let
--   $$L=\mathcal P[U,V,W]\big/\bigl(U^3+\bar hV-\bar x,\ -U^2+\bar hW-\bar y,\ S(\bar h,U,V,W)-\bar s\bigr)$$
--   be the lifting quotient over $\mathcal P$. The file constructs the following $\mathbb{C}$-algebra homomorphisms.
--
--   1. **From the plane to the hypersurface.** The map $\mathcal P\to D$ sending $\bar h,\bar x,\bar y,\bar s$ to the classes of $h$, $u^3+hv$, $-u^2+hw$ and $S(h,u,v,w)$. It is well defined because $h-1-P(x,y,s)=F$ vanishes in $D$ and $x^2+y^3=hs$ already holds in $R$.
--   2. **From the lifting quotient to the hypersurface.** The extension $L\to D$ of the previous map that sends $U,V,W$ to the classes of $u,v,w$; it kills the three lifting relations by the definitions of $x$, $y$ and $s$.
--   3. **From the hypersurface to the lifting quotient.** The map $R\to L$ with $h\mapsto\bar h$ and $u,v,w\mapsto U,V,W$ sends $x,y,s$ to $\bar x,\bar y,\bar s$ (by the lifting relations) and sends $F$ to $\bar h-P(\bar x,\bar y,\bar s)-1=0$; hence it factors through a map $D\to L$.
--   4. **Elimination isomorphism.** The maps of items 2 and 3 are mutually inverse, so
--   $$L\cong R/(F)\quad\text{as }\mathbb{C}\text{-algebras}.$$
--
--   In words, the coordinate ring of the hypersurface $F=0$ is precisely the lifting quotient over the plane presentation: the auxiliary plane variables $h,x,y,s$ are eliminated by expressing them through $h,u,v,w$. Combined with the plane and lifting isomorphisms, this identifies $R/(F)$ with a polynomial ring in three variables.
--
--   **Formalization Note** `B` is `Plane.Q ℂ` with generators `hB, xB, yB, sB`, `L` is `Lifting.Q hB xB yB sB` with structure map `lcoef` and generators `lvar`, and `D` is `R ⧸ Ideal.span {F}` with quotient map `dmap`. The maps are `auxToD` (item 1, from `auxEval`), `toOriginal` (item 2, from `liftEval`), `originalEval` and `fromOriginal` (item 3), and the equivalence is `eliminationEquiv`; the remaining lemmas (`dmap_F`, `auxEval_h`, `auxEval_cusp`, `liftEval_x`, `originalEval_F`, `to_from`, `from_auxToD`, `from_to`, and the evaluation rules) are the well-definedness and computation facts.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Presentation.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Presentation.lean by skeleton subtraction
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
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Plane

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

theorem to_from : toOriginal.comp fromOriginal = AlgHom.id ℂ D := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change toOriginal (fromOriginal (dmap (X i))) = dmap (X i)
  rw [fromOriginal_dmap]
  fin_cases i <;> simp [originalEval, originalValues, auxValues, liftValues, h, u, v, w]

theorem from_auxToD : fromOriginal.comp auxToD = lcoef := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change fromOriginal (auxToD (Plane.qvar ℂ i)) = lcoef (Plane.qvar ℂ i)
  rw [auxToD_qvar]
  fin_cases i <;> simp [auxValues]

theorem from_to : fromOriginal.comp toOriginal = AlgHom.id ℂ L := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext'
  · apply AlgHom.ext
    intro b
    change fromOriginal (toOriginal (lcoef b)) = lcoef b
    rw [toOriginal_lcoef]
    exact AlgHom.congr_fun from_auxToD b
  · intro i
    change fromOriginal (toOriginal (lvar i)) = lvar i
    rw [toOriginal_lvar]
    fin_cases i <;> simp [liftValues]

def eliminationEquiv : L ≃ₐ[ℂ] D :=
  AlgEquiv.ofAlgHom toOriginal fromOriginal to_from from_to

end AbhyankarSathaye.Presentation

end

end OAI


