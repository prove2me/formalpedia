-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Quotient
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_Quotient
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:24:26.957839+00:00
-- url     : https://prove2.me/theorems/894ecff1-fba0-4094-9f2d-45f240b6c65f
-- title:
--   Ring maps preserve the auxiliary polynomials, and algebra maps descend to quotients by two or three relations
-- statement:
--   This file provides two pieces of general algebra used throughout the construction. Recall the auxiliary expressions $S(h,u,v,w)=2u^3v+3u^4w+h(v^2-3u^2w^2)+h^2w^3$, $P(x,y,s)=-2s^2x+3sy^2-3s^3y$, $\alpha(x,s)=1+2s^2x+4s^5$ and $\beta(x,y,s)=(3s^3-3sy)(1+2s^2x)-4s^4y^2$, defined in any commutative ring.
--
--   1. **Compatibility with ring homomorphisms.** If $f:B\to D$ is a ring homomorphism between commutative rings, then
--   $$f\bigl(S(h,u,v,w)\bigr)=S\bigl(f(h),f(u),f(v),f(w)\bigr),\qquad f\bigl(P(x,y,s)\bigr)=P\bigl(f(x),f(y),f(s)\bigr),$$
--   and likewise $f(\alpha(x,s))=\alpha(f(x),f(s))$ and $f(\beta(x,y,s))=\beta(f(x),f(y),f(s))$.
--   2. **Descending to a quotient by two relations.** Let $B$ be a commutative ring and $A$, $D$ commutative $B$-algebras. Given $a,b\in A$ and a $B$-algebra homomorphism $f:A\to D$ with $f(a)=f(b)=0$, there is an induced $B$-algebra homomorphism
--   $$\bar f:\ A/(a,b)\to D,\qquad \bar f\bigl(z+(a,b)\bigr)=f(z)\quad(z\in A).$$
--   3. **Descending to a quotient by three relations.** In the same setting, given $a,b,c\in A$ and $f$ with $f(a)=f(b)=f(c)=0$, there is an induced $B$-algebra homomorphism $\bar f:A/(a,b,c)\to D$ with $\bar f(z+(a,b,c))=f(z)$.
--
--   The file also records that the generators vanish in the quotient: the classes of $a$ and $b$ in $A/(a,b)$, and the classes of $a$, $b$, $c$ in $A/(a,b,c)$, are $0$.
--
--   These are the universal properties from which every explicit algebra map of the construction is built: the plane presentation is a quotient by two relations and the lifting presentation is a quotient by three relations, and maps out of them are obtained by checking that the relations are sent to $0$.
--
--   **Formalization Note** Item 1 consists of the simp lemmas `map_S`, `map_P`, `map_Alpha`, `map_Beta`, stated for any `RingHomClass`. Items 2 and 3 are `lift_pair` and `lift_triple` (built from `Ideal.Quotient.liftₐ` on `Ideal.span {a,b}` and `Ideal.span {a,b,c}`) with computation rules `lift_pair_mk` and `lift_triple_mk`; the vanishing statements are `quotient_pair_left`, `quotient_pair_right`, `quotient_triple_first`, `quotient_triple_second` and `quotient_triple_third`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Quotient.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Quotient.lean by skeleton subtraction
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

namespace OAI

/-!
# Polynomial maps and finitely presented quotients

Ring homomorphisms preserve the defining polynomial expressions. Algebra maps
annihilating two or three relations descend to the corresponding quotient.
-/

noncomputable section
namespace AbhyankarSathaye

section Maps
variable {B D H : Type*} [CommRing B] [CommRing D]
variable [FunLike H B D] [RingHomClass H B D]

@[simp] theorem map_S (f : H) (h u v w : B) :
    f (S h u v w) = S (f h) (f u) (f v) (f w) := by simp [S, map_ofNat]

@[simp] theorem map_P (f : H) (x y s : B) :
    f (P x y s) = P (f x) (f y) (f s) := by simp [P, map_ofNat]

@[simp] theorem map_Alpha (f : H) (x s : B) :
    f (Alpha x s) = Alpha (f x) (f s) := by simp [Alpha, map_ofNat]

@[simp] theorem map_Beta (f : H) (x y s : B) :
    f (Beta x y s) = Beta (f x) (f y) (f s) := by simp [Beta, map_ofNat]

end Maps

section Presentations
variable {B A D : Type*} [CommRing B] [CommRing A] [CommRing D]
variable [Algebra B A] [Algebra B D]

def lift_pair (a b : A) (f : A →ₐ[B] D) (ha : f a = 0) (hb : f b = 0) :
    (A ⧸ Ideal.span {a,b}) →ₐ[B] D := by
  have hi : Ideal.span {a,b} ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ha
    · exact hb
  exact Ideal.Quotient.liftₐ _ f (fun z hz => hi hz)

@[simp] theorem lift_pair_mk (a b : A) (f : A →ₐ[B] D) (ha hb) (z : A) :
    lift_pair a b f ha hb (Ideal.Quotient.mk _ z) = f z := rfl

def lift_triple (a b c : A) (f : A →ₐ[B] D)
    (ha : f a = 0) (hb : f b = 0) (hc : f c = 0) :
    (A ⧸ Ideal.span {a,b,c}) →ₐ[B] D := by
  have hi : Ideal.span {a,b,c} ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  exact Ideal.Quotient.liftₐ _ f (fun z hz => hi hz)

@[simp] theorem lift_triple_mk (a b c : A) (f : A →ₐ[B] D) (ha hb hc) (z : A) :
    lift_triple a b c f ha hb hc (Ideal.Quotient.mk _ z) = f z := rfl

theorem quotient_pair_left (a b : A) : Ideal.Quotient.mk (Ideal.span {a,b}) a = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem quotient_pair_right (a b : A) : Ideal.Quotient.mk (Ideal.span {a,b}) b = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem quotient_triple_first (a b c : A) :
    Ideal.Quotient.mk (Ideal.span {a,b,c}) a = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem quotient_triple_second (a b c : A) :
    Ideal.Quotient.mk (Ideal.span {a,b,c}) b = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem quotient_triple_third (a b c : A) :
    Ideal.Quotient.mk (Ideal.span {a,b,c}) c = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

end Presentations
end AbhyankarSathaye

end

end OAI


