-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Quotient__CommutingDerivations
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_Quotient__CommutingDerivations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:25:44.13488+00:00
-- url     : https://prove2.me/theorems/b63670b0-9282-463c-9900-7a237396f2c6
-- title:
--   Ring maps preserve $S$, $P$, $\alpha$, $\beta$; algebra maps killing two or three elements factor through the quotient
-- statement:
--   Recall the polynomial expressions $S(h,u,v,w)=2u^3v+3u^4w+h(v^2-3u^2w^2)+h^2w^3$, $P(x,y,s)=-2s^2x+3sy^2-3s^3y$, $\alpha(x,s)=1+2s^2x+4s^5$ and $\beta(x,y,s)=(3s^3-3sy)(1+2s^2x)-4s^4y^2$. The file collects two kinds of general facts.
--
--   1. **Compatibility with ring maps.** For commutative rings $B,D$ and every ring homomorphism $f\colon B\to D$,
--      $$f\bigl(S(h,u,v,w)\bigr)=S\bigl(f(h),f(u),f(v),f(w)\bigr),\qquad f\bigl(P(x,y,s)\bigr)=P\bigl(f(x),f(y),f(s)\bigr),$$
--      and likewise $f(\alpha(x,s))=\alpha(f(x),f(s))$ and $f(\beta(x,y,s))=\beta(f(x),f(y),f(s))$.
--   2. **Lifting through a quotient by two elements.** Let $B$ be a commutative ring, let $A$ and $D$ be commutative $B$-algebras, let $a,b\in A$, and let $f\colon A\to D$ be a $B$-algebra homomorphism with $f(a)=f(b)=0$. There is an induced $B$-algebra homomorphism $\bar f\colon A/(a,b)\to D$ with $\bar f(z+(a,b))=f(z)$ for every $z\in A$.
--   3. **Three elements.** In the same way, $f$ with $f(a)=f(b)=f(c)=0$ induces $\bar f\colon A/(a,b,c)\to D$ with $\bar f(z+(a,b,c))=f(z)$.
--   4. **The relations vanish in the quotient.** The classes of $a$ and $b$ are zero in $A/(a,b)$, and the classes of $a$, $b$ and $c$ are zero in $A/(a,b,c)$.
--
--   These lemmas let the defining identities be pushed through evaluation maps, localizations and quotient maps without expanding the polynomials again. They also let algebra maps be defined out of the finitely presented quotient rings that appear in the coordinate constructions for the hypersurface $F=0$.
--
--   **Formalization Note** The induced maps are `lift_pair` and `lift_triple`, built from `Ideal.Quotient.liftₐ`. Their defining equations `lift_pair_mk` and `lift_triple_mk` hold by `rfl`. The ideals are `Ideal.span {a,b}` and `Ideal.span {a,b,c}`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Quotient.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Quotient.lean by skeleton subtraction
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


