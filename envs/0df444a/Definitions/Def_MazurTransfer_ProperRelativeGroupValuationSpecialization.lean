-- Prove2me | Definitions.Def_MazurTransfer_ProperRelativeGroupValuationSpecialization
-- name    : MazurTransfer_ProperRelativeGroupValuationSpecialization
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T09:00:12.705232+00:00
-- url     : https://prove2.me/theorems/873e1109-678c-4f37-9ad4-4b37bca6d143
-- title:
--   Group specialization through unique proper valuation-ring extension
-- statement:
--   Let a proper scheme over a commutative ring $R$ carry the specified relative group law. Let $B$ be a valuation domain over the base, with specified fraction field $K$, and let $\psi:B\to k$ be a map to a field. Unique proper extension from $K$ to $B$, followed by restriction through $\psi$, defines a group homomorphism $$X(K)\longrightarrow X(k).$$ The construction also gives the group equivalence between integral and fraction-field points and records the exact formula for the underlying specialized morphism. It is used for the actual rational-to-mod-3/mod-5 Picard reduction maps.
-- source:
--   Original complete ProperRelativeGroupValuationSpecialization.lean from MazurTheorem, Apache-2.0, Vas and contributors. All four original declarations and bodies are unchanged; the project import alone changes to the public proper valuation-point Definition. Four complete original closed types and all three data construction values are kernel-compared. Native, strict and full frontend checks pass with standard axioms only. The group operations are the original RelativeGroupLaw operations, with the specified fraction-field and residue-field structural maps. Reuses original official Anthropic FLT group-law interfaces at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Named downstream consumer: the same actual integral Picard family’s rational specialization homomorphisms.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: unique extension of fraction-field points of a proper
relative group gives a genuine group homomorphism to any residue field.
Named downstream consumer: same-family rational Picard reduction maps.
-/
import Definitions.Def_MazurTransfer_ValuationRingProperPointRestriction

noncomputable section
universe u
namespace MazurTransfer.ProperRelativeGroupValuationSpecialization
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open ValuationRingProperPointRestriction
variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}

def pointPrecomposeHom (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (.of R)} {t' : T' ⟶ Spec (.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    letI := L.pointGroup t
    letI := L.pointGroup t'
    SchemeHomOver t f →* SchemeHomOver t' f := by
  letI := L.pointGroup t
  letI := L.pointGroup t'
  exact { toFun := schemeHomOverComp ψ hψ
          map_one' := L.one_natural t t' ψ hψ
          map_mul' := L.mul_natural t t' ψ hψ }

variable (B K : Type u) [CommRing B] [IsDomain B] [ValuationRing B]
variable [Field K] [Algebra B K] [IsFractionRing B K]

def fractionPointGroupEquiv (L : RelativeGroupLaw R f) [IsProper f]
    (t : Spec (.of B) ⟶ Spec (.of R)) :
    letI := L.pointGroup t
    letI := L.pointGroup (fractionInclusion B K ≫ t)
    SchemeHomOver t f ≃* SchemeHomOver (fractionInclusion B K ≫ t) f := by
  letI := L.pointGroup t
  letI := L.pointGroup (fractionInclusion B K ≫ t)
  exact { pointEquiv f B K t with map_mul' := L.mul_natural t _ (fractionInclusion B K) rfl }

def specializationHom (L : RelativeGroupLaw R f) [IsProper f]
    (t : Spec (.of B) ⟶ Spec (.of R)) (k : Type u) [Field k] (ψ : B →+* k) :
    letI := L.pointGroup (fractionInclusion B K ≫ t)
    letI := L.pointGroup (Spec.map (CommRingCat.ofHom ψ) ≫ t)
    SchemeHomOver (fractionInclusion B K ≫ t) f →*
      SchemeHomOver (Spec.map (CommRingCat.ofHom ψ) ≫ t) f := by
  letI := L.pointGroup t
  letI := L.pointGroup (fractionInclusion B K ≫ t)
  letI := L.pointGroup (Spec.map (CommRingCat.ofHom ψ) ≫ t)
  exact (pointPrecomposeHom L (Spec.map (CommRingCat.ofHom ψ)) rfl).comp
    (fractionPointGroupEquiv B K L t).symm.toMonoidHom

theorem specializationHom_coe (L : RelativeGroupLaw R f) [IsProper f]
    (t : Spec (.of B) ⟶ Spec (.of R)) (k : Type u) [Field k] (ψ : B →+* k)
    (a : SchemeHomOver (fractionInclusion B K ≫ t) f) :
    (specializationHom B K L t k ψ a).val =
      Spec.map (CommRingCat.ofHom ψ) ≫ ((pointEquiv f B K t).symm a).val := rfl

end MazurTransfer.ProperRelativeGroupValuationSpecialization
#print axioms MazurTransfer.ProperRelativeGroupValuationSpecialization.fractionPointGroupEquiv
#print axioms MazurTransfer.ProperRelativeGroupValuationSpecialization.specializationHom


