-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualRationalPicardSpecialization
-- name    : MazurTransfer_Order13ActualRationalPicardSpecialization
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T09:04:18.322324+00:00
-- url     : https://prove2.me/theorems/e040cf11-8613-4795-948b-14cc9f86c509
-- title:
--   The original rational-to-mod-three/mod-five Picard specialization homomorphisms
-- statement:
--   Let $B=\mathbb Z[1/104]$, let $q=3$ or $5$, and let a designated integral Picard scheme $D/B$ be proper and carry the specified relative group law $L$. The original construction gives a group homomorphism $$D(\mathbb Q)\longrightarrow D(\mathbf F_q),$$ with both point types taken over the specified canonical scalar maps and both group structures supplied by $L$. It extends rational points uniquely over $\mathbb Z_{(q)}$, then restricts to $\mathbf F_q$, using the proved identities between the actual structural maps. The construction also provides the group equivalence for equal base maps and its underlying-point identity. These are the actual maps for same-family torsion specialization.
-- source:
--   Five original constructors and structural identities from MazurTheorem Order13ActualRationalPicardSpecialization.lean, Apache-2.0, Vas and contributors. All selected original bodies are unchanged; the integral-lift theorem is separated as a public theorem node and project imports become public Definitions. All five complete original closed types and both construction values are kernel-compared, including the original RelativeGroupLaw point-group actions and actual local/rational/finite-field scalar maps. Native, strict and full frontend checks pass with standard axioms only. Uses original official Anthropic FLT relative-group interfaces at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2 and proper valuation extension. Named downstream consumers: the exact integral-lift formula, same-family rational reduction maps and prime-to-residue-characteristic torsion bounds.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual rational-to-mod-3/mod-5 group homomorphisms for
the original integral Picard family, obtained by unique local extension.
Named downstream consumer: prime-to-residue-characteristic torsion bounds.
No injectivity or rational rank conclusion is assumed or asserted here.
-/
import Definitions.Def_MazurTransfer_Order13LocalIntegralCoefficientMaps
import Definitions.Def_MazurTransfer_ProperRelativeGroupValuationSpecialization

noncomputable section
namespace MazurTransfer.Order13ActualRationalPicardSpecialization
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections Order13IntegralBase
open Order13SameIntegralPicardFamilyFiniteFibres Order13LocalIntegralCoefficientMaps
open ProperRelativeGroupValuationSpecialization

def pointGroupCongr {R : Type} [CommRing R] {X : Scheme} {f : X ⟶ Spec (.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme} {t t' : T ⟶ Spec (.of R)} (h : t=t') :
    letI := L.pointGroup t
    letI := L.pointGroup t'
    SchemeHomOver t f ≃* SchemeHomOver t' f := by
  letI := L.pointGroup t
  letI := L.pointGroup t'
  exact { toFun := fun a => ⟨a.val,a.property.trans h⟩
          invFun := fun a => ⟨a.val,a.property.trans h.symm⟩
          left_inv := fun _ => Subtype.ext rfl
          right_inv := fun _ => Subtype.ext rfl
          map_mul' := by subst h; intro a b; rfl }

theorem pointGroupCongr_coe {R : Type} [CommRing R] {X : Scheme} {f : X ⟶ Spec (.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme} {t t' : T ⟶ Spec (.of R)} (h : t=t')
    (a : SchemeHomOver t f) : (pointGroupCongr L h a).val = a.val := rfl

variable (q : ℕ) [Fact q.Prime] (hq : q=3 ∨ q=5)

theorem localRationalSpec_comp :
    Spec.map (CommRingCat.ofHom (algebraMap (LocalRing q) ℚ)) ≫
        Spec.map (CommRingCat.ofHom (localBaseMap q hq)) =
      Spec.map (CommRingCat.ofHom canonicalRationalMap) := by
  rw [← Spec.map_comp,← CommRingCat.ofHom_comp,localRationalMap_comp]

theorem localFiniteFieldSpec_comp :
    Spec.map (CommRingCat.ofHom (localFiniteFieldMap q)) ≫
        Spec.map (CommRingCat.ofHom (localBaseMap q hq)) =
      Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap q hq)) := by
  rw [← Spec.map_comp,← CommRingCat.ofHom_comp,localFiniteFieldMap_comp]

def rationalSpecializationHom
    (D : RelativePic0Designation BaseRing (curveToBase BaseRing))
    (L : RelativeGroupLaw BaseRing D.toBase) [IsProper D.toBase] :
    letI := L.pointGroup (Spec.map (CommRingCat.ofHom canonicalRationalMap))
    letI := L.pointGroup (Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap q hq)))
    SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase →*
      SchemeHomOver (Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap q hq))) D.toBase := by
  let t := Spec.map (CommRingCat.ofHom (localBaseMap q hq))
  let tQ := Spec.map (CommRingCat.ofHom canonicalRationalMap)
  let tk := Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap q hq))
  letI := L.pointGroup tQ
  letI := L.pointGroup tk
  letI := L.pointGroup (ValuationRingProperPointRestriction.fractionInclusion (LocalRing q) ℚ ≫ t)
  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (localFiniteFieldMap q)) ≫ t)
  let a : SchemeHomOver tQ D.toBase ≃*
      SchemeHomOver (ValuationRingProperPointRestriction.fractionInclusion (LocalRing q) ℚ ≫ t) D.toBase :=
    pointGroupCongr L (show ValuationRingProperPointRestriction.fractionInclusion (LocalRing q) ℚ ≫ t = tQ
      from localRationalSpec_comp q hq).symm
  let b := specializationHom (LocalRing q) ℚ L t (ZMod q) (localFiniteFieldMap q)
  let c : SchemeHomOver (Spec.map (CommRingCat.ofHom (localFiniteFieldMap q)) ≫ t) D.toBase ≃*
      SchemeHomOver tk D.toBase :=
    pointGroupCongr L (show Spec.map (CommRingCat.ofHom (localFiniteFieldMap q)) ≫ t = tk
      from localFiniteFieldSpec_comp q hq)
  exact c.toMonoidHom.comp (b.comp a.toMonoidHom)



end MazurTransfer.Order13ActualRationalPicardSpecialization
#print axioms MazurTransfer.Order13ActualRationalPicardSpecialization.rationalSpecializationHom


