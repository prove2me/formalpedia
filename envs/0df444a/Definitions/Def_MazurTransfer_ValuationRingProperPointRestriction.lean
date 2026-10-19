-- Prove2me | Definitions.Def_MazurTransfer_ValuationRingProperPointRestriction
-- name    : MazurTransfer_ValuationRingProperPointRestriction
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T08:58:24.682649+00:00
-- url     : https://prove2.me/theorems/d939006d-1a32-4f7a-94c0-e58e655417d6
-- title:
--   Proper valuation-ring points and fraction-field points of the same family
-- statement:
--   Let $f:X\to\operatorname{Spec}R$ be proper. Let $B$ be a valuation ring that is an integral domain, let $K$ be its fraction field with the specified $B$-algebra structure, and let $t:\operatorname{Spec}B\to\operatorname{Spec}R$. Restriction induces a specified equivalence $$X(B)_t\simeq X(K)_{t_K}.$$ Its inverse is the unique proper extension, and the construction retains the exact structural maps and the equation identifying its restriction with the original fraction-field point. This supplies actual local integral extensions in rational Picard specialization.
-- source:
--   Original complete ValuationRingProperPointRestriction.lean from MazurTheorem, Apache-2.0, Vas and contributors. The original source is byte-for-byte unchanged and already passes native, strict and full frontend checks; its proof is reused without rerunning native verification. Five original closed types and three construction values are kernel-compared through the public Definition import alias. The eighteen-line bijectivity proof is embedded because it is directly required by the point-equivalence data constructor. Uses Mathlib valuative criterion for properness and the original official Anthropic FLT relative-point interface at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Named downstream consumer: proper relative group valuation specialization and the actual rational Picard reduction maps.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: properness extends each fraction-field point uniquely to
a valuation-ring point of the same family, with its structural map retained.
Named downstream consumer: actual rational Picard specialization maps.
-/
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

noncomputable section
universe u
namespace MazurTransfer.ValuationRingProperPointRestriction
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
variable (B K : Type u) [CommRing B] [IsDomain B] [ValuationRing B]
variable [Field K] [Algebra B K] [IsFractionRing B K]

def fractionInclusion : Spec (.of K) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B K))

def pointRestrict (t : Spec (.of B) ⟶ Spec (.of R)) :
    SchemeHomOver t f → SchemeHomOver (fractionInclusion B K ≫ t) f :=
  schemeHomOverComp (fractionInclusion B K) rfl

theorem pointRestrict_bijective [IsProper f] (t : Spec (.of B) ⟶ Spec (.of R)) :
    Function.Bijective (pointRestrict f B K t) := by
  have H : ValuativeCriterion f := by
    have h : IsProper f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  constructor
  · intro a b hab
    let S : ValuativeCommSq f :=
      { R := B, K := K, i₁ := (pointRestrict f B K t a).val, i₂ := t,
        commSq := ⟨(pointRestrict f B K t a).property⟩ }
    letI := (H S).some
    let la : S.commSq.LiftStruct := ⟨a.val,rfl,a.property⟩
    let lb : S.commSq.LiftStruct := ⟨b.val,(congrArg Subtype.val hab).symm,b.property⟩
    exact Subtype.ext (congrArg CommSq.LiftStruct.l (Subsingleton.elim la lb))
  · intro a
    let S : ValuativeCommSq f :=
      { R := B, K := K, i₁ := a.val, i₂ := t, commSq := ⟨a.property⟩ }
    let l := (H S).some.default
    exact ⟨⟨l.l,l.fac_right⟩,Subtype.ext l.fac_left⟩

def pointEquiv [IsProper f] (t : Spec (.of B) ⟶ Spec (.of R)) :
    SchemeHomOver t f ≃ SchemeHomOver (fractionInclusion B K ≫ t) f :=
  Equiv.ofBijective (pointRestrict f B K t) (pointRestrict_bijective f B K t)

theorem pointEquiv_extension [IsProper f] (t : Spec (.of B) ⟶ Spec (.of R))
    (a : SchemeHomOver (fractionInclusion B K ≫ t) f) :
    fractionInclusion B K ≫ ((pointEquiv f B K t).symm a).val = a.val :=
  congrArg Subtype.val ((pointEquiv f B K t).apply_symm_apply a)

end MazurTransfer.ValuationRingProperPointRestriction
#print axioms MazurTransfer.ValuationRingProperPointRestriction.pointRestrict_bijective
#print axioms MazurTransfer.ValuationRingProperPointRestriction.pointEquiv_extension


