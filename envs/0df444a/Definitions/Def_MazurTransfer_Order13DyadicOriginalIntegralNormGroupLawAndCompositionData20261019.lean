-- Prove2me | Definitions.Def_MazurTransfer_Order13DyadicOriginalIntegralNormGroupLawAndCompositionData20261019
-- name    : MazurTransfer_Order13DyadicOriginalIntegralNormGroupLawAndCompositionData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T09:59:12.601356+00:00
-- url     : https://prove2.me/theorems/d913cd22-632e-44dc-81b4-dbc28a53a6ca
-- title:
--   Original integral dyadic norm group laws and composition
-- statement:
--   Let $N_\phi$ be the original unique integral extension of an arithmetic endomorphism $\phi$. Extension preserves every composition and identity, and the group endomorphisms preserve zero and multiplication. For the two actual norm factors,
--
--   $$N_\pi\circ N_{\pi^{\ast}}=N_{\pi^{\ast}}\circ N_\pi=\widetilde{[19]}.$$
--
--   Here $\widetilde{[19]}$ denotes the original chosen integral extension of rational multiplication by nineteen. Its comparison with multiplication for the local relative law is the next theorem. Named downstream consumer: that scalar comparison and finite etale norm fibres at two.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: The same original integral norm extensions preserve the original zero and multiplication, and Neron uniqueness preserves every composition and identity. Both actual norm composites are the same chosen integral scalar nineteen.
Named downstream consumer: Original comparison with local scalar nineteen, finite etale actual norm maps and inertia at two.
Original per-file headers and attribution are retained below.
-/
import Definitions.Def_MazurTransfer_Order13DyadicOriginalGenericNormGroupLawData20261019
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_genericFibre
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNineteenNorm_schemePi_comp_schemePiConjugate
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNineteenNorm_schemePiConjugate_comp_schemePi

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the following checked good-prime proof is adapted to the
SAME selected actual dyadic Picard, its represented group law and actual
rational norm maps. No unit assumption on two or 104 is added.
Named downstream consumer: finite etale dyadic norm fibres and their
arithmetic inertia/Kummer condition. Original method and attribution follow.
-/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: descend zero preservation of the SAME generic norm to
its already selected integral extension. The generic-density argument
uses the pinned FLT generic-fibre restriction proof.
Named downstream consumer: actual integral norm group morphisms.
-/

noncomputable section
namespace MazurTransfer.Order13DyadicMixedIntegralNormUnit
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedGenericGroupIdentity Order13DyadicMixedRationalPicardComparison
open Order13DyadicMixedGenericNormUnit Order13DyadicMixedIntegralNormExtensions
open Order13ActualDyadicMixedPicardNeronModel Order13DyadicMixedQuadraticCharts
open Order13ActualPicardDiamondSchemeEndomorphism Order13DyadicMixedRationalPicardComparison
open scoped CategoryTheory.MonObj
open Order13DyadicMixedGenericNorms Order13DyadicMixedPicardGeometry
local instance instFactPrimeOfNatNat_order13DyadicMixedIntegralNormUnit : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormUnit : GrpObj (Over.mk actualPicard.toBase) := actualGroup

theorem localGenericInclusion_dominant : IsDominant (specGenericFibreInclusion (BaseRing) ℚ) := by
  rw [isDominant_iff, specGenericFibreInclusion]
  have hker : RingHom.ker (algebraMap (BaseRing) ℚ) ≤ nilradical (BaseRing) := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective (BaseRing) ℚ)]
    exact bot_le
  have hd := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    (algebraMap (BaseRing) ℚ)).mpr hker
  simp at hd ⊢
  exact hd

theorem integralNorm_preserves_unit
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] :
    NeronModelInfra.schemeHomOverComp ((dyadicLaw).one (𝟙 _))
      (integralNorm φ) = (dyadicLaw).one (𝟙 _) := by
  letI := (dyadicPicard_geometry).2.1
  letI := localGenericInclusion_dominant
  have h := localGenericNorm_preserves_unit φ
  rw [← integralNorm_restrict φ] at h
  have hb := congrArg (RelativeGroupLaw.baseChangePointToBase
    (specGenericFibreInclusion (BaseRing) ℚ)) h
  dsimp only [genericLocalLaw] at hb
  change RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion (BaseRing) ℚ)
    (NeronModelInfra.schemeHomOverComp
      (((dyadicLaw).baseChange (specGenericFibreInclusion (BaseRing) ℚ)).one (𝟙 _))
      (genericFibreRestrict (BaseRing) ℚ (dyadicPicard).toBase
        (dyadicPicard).toBase (integralNorm φ))) = _ at hb
  rw [RelativeGroupLaw.baseChangePointToBase_comp_genericFibreRestrict,
    RelativeGroupLaw.baseChangePointToBase_one] at hb
  have hn := congrArg Subtype.val ((dyadicLaw).one_natural
    (𝟙 _) (𝟙 _ ≫ specGenericFibreInclusion (BaseRing) ℚ)
    (𝟙 _ ≫ specGenericFibreInclusion (BaseRing) ℚ) (by simp))
  change (𝟙 _ ≫ specGenericFibreInclusion (BaseRing) ℚ) ≫
    ((dyadicLaw).one (𝟙 _)).val =
      ((dyadicLaw).one (𝟙 _ ≫ specGenericFibreInclusion (BaseRing) ℚ)).val at hn
  have hb' := congrArg Subtype.val hb
  change ((dyadicLaw).one (𝟙 _ ≫ specGenericFibreInclusion (BaseRing) ℚ)).val ≫
    (integralNorm φ).val =
      ((dyadicLaw).one (𝟙 _ ≫ specGenericFibreInclusion (BaseRing) ℚ)).val at hb'
  rw [← hn] at hb'
  apply Subtype.ext
  apply ext_of_isDominant_of_isSeparated (dyadicPicard).toBase
    (by simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc,
      (integralNorm φ).property, ((dyadicLaw).one (𝟙 _)).property])
    (specGenericFibreInclusion (BaseRing) ℚ)
  simpa only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, Category.id_comp] using hb'

end MazurTransfer.Order13DyadicMixedIntegralNormUnit
#print axioms MazurTransfer.Order13DyadicMixedIntegralNormUnit.localGenericInclusion_dominant
#print axioms MazurTransfer.Order13DyadicMixedIntegralNormUnit.integralNorm_preserves_unit

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the following checked good-prime proof is adapted to the
SAME selected actual dyadic Picard, its represented group law and actual
rational norm maps. No unit assumption on two or 104 is added.
Named downstream consumer: finite etale dyadic norm fibres and their
arithmetic inertia/Kummer condition. Original method and attribution follow.
-/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: zero preservation for the SAME integral norm extension
holds on points over every test scheme by naturality of the local law.
Named downstream consumer: the accepted public pointwise group-morphism
contract for actual integral norm morphisms.
-/

noncomputable section
namespace MazurTransfer.Order13DyadicMixedIntegralNormPointwiseUnit
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedIntegralNormUnit Order13DyadicMixedIntegralNormExtensions
open Order13ActualDyadicMixedPicardNeronModel Order13DyadicMixedQuadraticCharts
open Order13ActualPicardDiamondSchemeEndomorphism Order13DyadicMixedRationalPicardComparison
open scoped CategoryTheory.MonObj
open Order13DyadicMixedGenericNorms Order13DyadicMixedPicardGeometry
local instance instFactPrimeOfNatNat_order13DyadicMixedIntegralNormPointwiseUnit : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormPointwiseUnit : GrpObj (Over.mk actualPicard.toBase) := actualGroup

theorem integralNorm_preserves_all_units
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (BaseRing))) :
    NeronModelInfra.schemeHomOverComp ((dyadicLaw).one t) (integralNorm φ) =
      (dyadicLaw).one t := by
  have h := congrArg Subtype.val (integralNorm_preserves_unit φ)
  change ((dyadicLaw).one (𝟙 _)).val ≫ (integralNorm φ).val =
    ((dyadicLaw).one (𝟙 _)).val at h
  have hn := congrArg Subtype.val ((dyadicLaw).one_natural (𝟙 _) t t (by simp))
  change t ≫ ((dyadicLaw).one (𝟙 _)).val = ((dyadicLaw).one t).val at hn
  apply Subtype.ext
  change ((dyadicLaw).one t).val ≫ (integralNorm φ).val =
    ((dyadicLaw).one t).val
  rw [← hn, Category.assoc, h]

end MazurTransfer.Order13DyadicMixedIntegralNormPointwiseUnit
#print axioms MazurTransfer.Order13DyadicMixedIntegralNormPointwiseUnit.integralNorm_preserves_all_units

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: multiplication preservation on the generic base-change
law descends to a flat source and separated target over a domain.
Named downstream consumer: the SAME selected integral order-13 norms.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u
namespace MazurTransfer.OriginalDyadicIntegralNormGenericMultiplicationDescent20261019

variable {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K]
  [Algebra R K] [IsFractionRing R K] {A B : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {g : B ⟶ Spec (CommRingCat.of R)}
  [Flat f] [IsSeparated g]
  (G : RelativeGroupLaw R f) (H : RelativeGroupLaw R g) (φ : SchemeHomOver f g)

theorem mul_of_genericFibre
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (RelativeGroupLaw.genericFibreStr K f)),
      NeronModelInfra.schemeHomOverComp ((G.genericFibre K).mul t x y)
        (genericFibreRestrict R K g f φ) =
      (H.genericFibre K).mul t
        (NeronModelInfra.schemeHomOverComp x (genericFibreRestrict R K g f φ))
        (NeronModelInfra.schemeHomOverComp y (genericFibreRestrict R K g f φ)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (G.mul t x y) φ =
      H.mul t (NeronModelInfra.schemeHomOverComp x φ)
        (NeronModelInfra.schemeHomOverComp y φ) := by
  apply Subtype.ext
  apply RelativeGroupLaw.comp_mul_eq_mul_comp_of_genericFibre R K H G φ
  intro S s a b
  let ι := specGenericFibreInclusion R K
  let a' : SchemeHomOver s (RelativeGroupLaw.genericFibreStr K f) :=
    RelativeGroupLaw.baseChangePointOfBase ι a
  let b' : SchemeHomOver s (RelativeGroupLaw.genericFibreStr K f) :=
    RelativeGroupLaw.baseChangePointOfBase ι b
  let φ' := genericFibreRestrict R K g f φ
  have h := hφ s a' b'
  have hh := congrArg (RelativeGroupLaw.baseChangePointToBase (f := g) ι) h
  have hG := RelativeGroupLaw.baseChangePointToBase_mul ι G s a' b'
  have hH := RelativeGroupLaw.baseChangePointToBase_mul ι H s
    (NeronModelInfra.schemeHomOverComp a' φ') (NeronModelInfra.schemeHomOverComp b' φ')
  have hleft := RelativeGroupLaw.baseChangePointToBase_comp_genericFibreRestrict K φ
    ((G.genericFibre K).mul s a' b')
  have ha := RelativeGroupLaw.baseChangePointToBase_ofBase ι a
  have hb := RelativeGroupLaw.baseChangePointToBase_ofBase ι b
  have hfa := RelativeGroupLaw.baseChangePointToBase_comp_genericFibreRestrict K φ a'
  have hfb := RelativeGroupLaw.baseChangePointToBase_comp_genericFibreRestrict K φ b'
  change RelativeGroupLaw.baseChangePointToBase ι a' = a at ha
  change RelativeGroupLaw.baseChangePointToBase ι b' = b at hb
  rw [ha, hb] at hG
  rw [ha] at hfa
  rw [hb] at hfb
  rw [hfa, hfb] at hH
  erw [hleft, hG, hH] at hh
  exact congrArg Subtype.val hh

end MazurTransfer.OriginalDyadicIntegralNormGenericMultiplicationDescent20261019
#print axioms MazurTransfer.OriginalDyadicIntegralNormGenericMultiplicationDescent20261019.mul_of_genericFibre

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the following checked good-prime proof is adapted to the
SAME selected actual dyadic Picard, its represented group law and actual
rational norm maps. No unit assumption on two or 104 is added.
Named downstream consumer: finite etale dyadic norm fibres and their
arithmetic inertia/Kummer condition. Original method and attribution follow.
-/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME selected integral norm extensions preserve
multiplication on points over arbitrary schemes, by flat generic descent.
Named downstream consumer: local integral norm group homomorphisms and
finite etale norm fibres away from nineteen.
-/

noncomputable section
namespace MazurTransfer.Order13DyadicMixedIntegralNormGroupLaws
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedGenericGroupIdentity Order13DyadicMixedRationalPicardComparison
open Order13DyadicMixedGenericNormGroupLaws Order13DyadicMixedIntegralNormExtensions
open Order13DyadicMixedIntegralNormUnit Order13ActualDyadicMixedPicardNeronModel
open Order13DyadicMixedQuadraticCharts Order13ActualPicardDiamondSchemeEndomorphism
open Order13DyadicMixedRationalPicardComparison
open scoped CategoryTheory.MonObj
open Order13DyadicMixedGenericNorms Order13DyadicMixedPicardGeometry
local instance instFactPrimeOfNatNat_order13DyadicMixedIntegralNormGroupLaws : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormGroupLaws : GrpObj (Over.mk actualPicard.toBase) := actualGroup

theorem integralNorm_preserves_mul
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (BaseRing)))
    (x y : SchemeHomOver t (dyadicPicard).toBase) :
    NeronModelInfra.schemeHomOverComp ((dyadicLaw).mul t x y) (integralNorm φ) =
    (dyadicLaw).mul t
      (NeronModelInfra.schemeHomOverComp x (integralNorm φ))
      (NeronModelInfra.schemeHomOverComp y (integralNorm φ)) := by
  letI := (dyadicPicard_geometry).1
  letI := (dyadicPicard_geometry).2.1
  apply OriginalDyadicIntegralNormGenericMultiplicationDescent20261019.mul_of_genericFibre ℚ
    (dyadicLaw) (dyadicLaw) (integralNorm φ)
  intro S s a b
  rw [integralNorm_restrict]
  exact localGenericNorm_preserves_mul φ s a b

end MazurTransfer.Order13DyadicMixedIntegralNormGroupLaws
#print axioms MazurTransfer.Order13DyadicMixedIntegralNormGroupLaws.integralNorm_preserves_mul

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the following checked good-prime proof is adapted to the
SAME selected actual dyadic Picard, its represented group law and actual
rational norm maps. No unit assumption on two or 104 is added.
Named downstream consumer: finite etale dyadic norm fibres and their
arithmetic inertia/Kummer condition. Original method and attribution follow.
-/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: uniqueness of Neron extension preserves identities and
composition for the SAME actual rational Picard endomorphisms.
Named downstream consumer: integral norm factorization and its good-prime
kernel fibres. The scalar nineteen here is defined as the unique integral
extension of the actual rational scalar map; its comparison with the
local relative group law is a separate downstream obligation.
-/

noncomputable section
namespace MazurTransfer.Order13DyadicMixedIntegralNormComposition
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian
open Order13ActualDyadicMixedPicardNeronModel Order13DyadicMixedQuadraticCharts
open Order13DyadicMixedRationalPicardComparison
open Order13DyadicMixedIntegralNormExtensions
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13DyadicMixedRationalPicardComparison
open scoped CategoryTheory.MonObj
open Order13DyadicMixedGenericNorms Order13DyadicMixedPicardGeometry
local instance instFactPrimeOfNatNat_order13DyadicMixedIntegralNormComposition : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormComposition : GrpObj (Over.mk actualPicard.toBase) := actualGroup

theorem localGenericNorm_comp
    (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) :
    genericNorm (φ ≫ ψ) =
      schemeHomOverComp (genericNorm φ) (genericNorm ψ) := by
  apply Subtype.ext
  change (((actualDyadicRationalOverIso).inv ≫ (φ ≫ ψ) ≫
    (actualDyadicRationalOverIso).hom).left) =
    (((actualDyadicRationalOverIso).inv ≫ φ ≫
      (actualDyadicRationalOverIso).hom).left ≫
      ((actualDyadicRationalOverIso).inv ≫ ψ ≫
      (actualDyadicRationalOverIso).hom).left)
  rw [← Over.comp_left]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

theorem localGenericNorm_id :
    genericNorm (𝟙 (Over.mk actualPicard.toBase)) =
      schemeHomOverId (rationalPicard).toBase := by
  apply Subtype.ext
  change (((actualDyadicRationalOverIso).inv ≫ 𝟙 _ ≫
    (actualDyadicRationalOverIso).hom).left) = 𝟙 _
  simp only [Category.id_comp, Iso.inv_hom_id, Over.id_left]

theorem integralNorm_comp
    (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) :
    integralNorm (φ ≫ ψ) =
      schemeHomOverComp (integralNorm φ) (integralNorm ψ) := by
  symm
  apply integralNorm_unique
  rw [genericFibreRestrict_endComp, integralNorm_restrict, integralNorm_restrict,
    ← localGenericNorm_comp]

theorem integralNorm_id :
    integralNorm (𝟙 (Over.mk actualPicard.toBase)) =
      schemeHomOverId (dyadicPicard).toBase := by
  symm
  apply integralNorm_unique
  rw [genericFibreRestrict_schemeHomOverId, localGenericNorm_id]
  rfl

def integralScalarNineteen :=
  integralNorm ((𝟙 (Over.mk actualPicard.toBase)) ^ 19)

theorem integralPi_comp_integralPiConjugate :
    schemeHomOverComp (integralPi) (integralPiConjugate) =
      integralScalarNineteen := by
  change schemeHomOverComp (integralNorm schemePi)
    (integralNorm schemePiConjugate) = _
  rw [← integralNorm_comp, schemePi_comp_schemePiConjugate]
  rfl

theorem integralPiConjugate_comp_integralPi :
    schemeHomOverComp (integralPiConjugate) (integralPi) =
      integralScalarNineteen := by
  change schemeHomOverComp (integralNorm schemePiConjugate)
    (integralNorm schemePi) = _
  rw [← integralNorm_comp, schemePiConjugate_comp_schemePi]
  rfl

theorem integralNorms_commute :
    schemeHomOverComp (integralPi) (integralPiConjugate) =
      schemeHomOverComp (integralPiConjugate) (integralPi) :=
  (integralPi_comp_integralPiConjugate).trans
    (integralPiConjugate_comp_integralPi).symm

end MazurTransfer.Order13DyadicMixedIntegralNormComposition
#print axioms MazurTransfer.Order13DyadicMixedIntegralNormComposition.integralNorm_comp
#print axioms MazurTransfer.Order13DyadicMixedIntegralNormComposition.integralNorm_id
#print axioms MazurTransfer.Order13DyadicMixedIntegralNormComposition.integralPi_comp_integralPiConjugate
#print axioms MazurTransfer.Order13DyadicMixedIntegralNormComposition.integralPiConjugate_comp_integralPi
#print axioms MazurTransfer.Order13DyadicMixedIntegralNormComposition.integralNorms_commute

end


