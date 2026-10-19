-- Prove2me | Definitions.Def_MazurTransfer_Order13DyadicOriginalPicardGeometryAndUniqueNormExtensionsData20261019
-- name    : MazurTransfer_Order13DyadicOriginalPicardGeometryAndUniqueNormExtensionsData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T09:13:27.839+00:00
-- url     : https://prove2.me/theorems/43462126-1274-41e6-ae5b-92dbddd7ddba
-- title:
--   Original dyadic Picard geometry and unique norm extensions
-- statement:
--   Let $R=\mathbf{Z}_{(2)}$ and let $J/R$ be the same original chosen dyadic Picard scheme, with generic fibre $J_\eta$. Its dyadic and rational fibres are smooth, proper and geometrically connected. Every arithmetic Picard endomorphism $\phi$ has a transported generic-fibre endomorphism $\phi_\eta$ with a unique integral extension:
--
--   $$\exists!\,N_\phi:J\longrightarrow_R J,\qquad (N_\phi)_\eta=\phi_\eta.$$
--
--   The original chosen extensions, including both actual norm factors, retain their whole constructor values. Named downstream consumer: the integral norm group laws and scalar composition identities.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: geometry of the same chosen dyadic Picard scheme and unique extensions of every transported rational endomorphism, including both actual norm factors.
Named downstream consumer: actual integral norm group laws, scalar nineteen composition, finite etale fibres and inertia at two.
Original per-file attribution is retained below.
-/
import Definitions.Def_MazurTransfer_Order13DyadicOriginalChosenRationalPicardComparisonData20261019
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData
import Theorems.Thm_MazurTransfer_order13_actual_dyadic_integral_picard_representation_original

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: smooth, proper and geometrically connected geometry of
ONE selected dyadic Picard and its SAME rational fibre; the latter is an
original abelian scheme. Named downstream consumer: group-law rigidity
and finite etale actual norm maps at two.
-/

noncomputable section
namespace MazurTransfer.Order13DyadicMixedPicardGeometry
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13ActualDyadicMixedPicardNeronModel Order13DyadicMixedRationalPicardComparison
open Order13DyadicMixedQuadraticPicardGeometryInputs PicardCanonicalRepresentationGroupIsomorphism
local instance instFactPrimeOfNatNat_order13DyadicMixedPicardGeometry : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem dyadicPicard_geometry : Smooth dyadicPicard.toBase ∧ IsProper dyadicPicard.toBase ∧
    GeometricallyConnected dyadicPicard.toBase := by
  obtain ⟨E,⟨hE⟩,hs,hp,hg⟩ :=
    MazurTransfer.order13_actual_dyadic_integral_picard_representation_original
  letI := hs
  letI := hp
  letI := hg
  let e := canonicalSchemeIso (P := algEquivZeroGroupCut (curveToBase BaseRing) zeroSection)
    dyadicRepresentation hE
  have he : e.hom ≫ E.toBase = dyadicPicard.toBase := canonicalSchemeIso_over _ _
  rw [← he]
  refine ⟨inferInstance,inferInstance,?_⟩
  rw [GeometricallyConnected.eq_geometrically] at hg ⊢
  exact (MorphismProperty.cancel_left_of_respectsIso (P := geometrically (ConnectedSpace ·))
    e.hom E.toBase).2 hg

theorem rationalPicard_geometry : Smooth rationalPicard.toBase ∧ IsProper rationalPicard.toBase ∧
    GeometricallyConnected rationalPicard.toBase := by
  obtain ⟨hs,hp,hg⟩ := dyadicPicard_geometry
  letI := hs
  letI := hp
  letI := hg
  change Smooth (dyadicPicard.baseChange ℚ).toBase ∧ IsProper (dyadicPicard.baseChange ℚ).toBase ∧
    GeometricallyConnected (dyadicPicard.baseChange ℚ).toBase
  exact ⟨inferInstance,inferInstance,inferInstance⟩

theorem rationalPicard_connected : ConnectedSpace rationalPicard.P := by
  letI := rationalPicard_geometry.2.2
  exact GeometricallyConnected.connectedSpace_of_subsingleton (f := rationalPicard.toBase)

theorem rationalPicard_abelian : AbelianSchemePropertyBundle ℚ rationalPicard.toBase := by
  obtain ⟨hs,hp,hg⟩ := rationalPicard_geometry
  letI := hg
  exact ⟨hs,hp,fun s => rationalPicard.toBase.isConnected_preimage_singleton s,
    ⟨(show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ)
      Order13ActualPicardDiamondSchemeEndomorphism.infinitySection
      (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ)
        Order13ActualPicardDiamondSchemeEndomorphism.infinitySection).toSubPicCondition
          rationalPicard from rationalRepresentation).relativeGroupLaw⟩⟩

end MazurTransfer.Order13DyadicMixedPicardGeometry
#print axioms MazurTransfer.Order13DyadicMixedPicardGeometry.dyadicPicard_geometry
#print axioms MazurTransfer.Order13DyadicMixedPicardGeometry.rationalPicard_abelian

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: transport the fixed actual rational Picard endomorphisms
onto the SAME selected dyadic Picard generic fibre, retaining intertwining
with the pointed canonical group isomorphism. Named downstream consumer:
unique Neron extensions of the actual two nineteen norm factors at two.
-/

noncomputable section
namespace MazurTransfer.Order13DyadicMixedGenericNorms
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13ActualDyadicMixedPicardNeronModel
open Order13DyadicMixedRationalPicardComparison
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
local instance instFactPrimeOfNatNat_order13DyadicMixedGenericNorms : Fact (Nat.Prime 2) := ⟨by decide⟩

def genericNorm (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) :
    SchemeHomOver (pullback.snd dyadicPicard.toBase (specGenericFibreInclusion BaseRing ℚ))
      (pullback.snd dyadicPicard.toBase (specGenericFibreInclusion BaseRing ℚ)) :=
  overHomToSchemeHomOver (actualDyadicRationalOverIso.inv ≫ φ ≫ actualDyadicRationalOverIso.hom)

theorem genericNorm_intertwine
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) :
    actualDyadicRationalOverIso.hom.left ≫ (genericNorm φ).val =
      φ.left ≫ actualDyadicRationalOverIso.hom.left := by
  change (actualDyadicRationalOverIso.hom ≫ actualDyadicRationalOverIso.inv ≫ φ ≫
    actualDyadicRationalOverIso.hom).left = _
  simp only [Iso.hom_inv_id_assoc]
  rfl

def genericPi := genericNorm schemePi
def genericPiConjugate := genericNorm schemePiConjugate

end MazurTransfer.Order13DyadicMixedGenericNorms
#print axioms MazurTransfer.Order13DyadicMixedGenericNorms.genericNorm_intertwine

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME fixed arithmetic rational Picard endomorphisms
have unique actual extensions over the selected represented Picard scheme
at two, via its proved original Neron mapping property.
Named downstream consumer: integral norm group laws, scalar composition,
finite etale norm fibres and the actual Kummer condition at two.
-/

noncomputable section
namespace MazurTransfer.Order13DyadicMixedIntegralNormExtensions
open CategoryTheory AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13ActualDyadicMixedPicardNeronModel
open Order13DyadicMixedGenericNorms
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
local instance instFactPrimeOfNatNat_order13DyadicMixedIntegralNormExtensions : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem norm_unique_extension
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) :
    ∃! ψ : SchemeHomOver dyadicPicard.toBase dyadicPicard.toBase,
      genericFibreRestrict BaseRing ℚ dyadicPicard.toBase dyadicPicard.toBase ψ = genericNorm φ :=
  dyadicPicard_neron.existsUnique_extension dyadicPicard_abelian.1 (genericNorm φ)

def integralNorm (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) :
    SchemeHomOver dyadicPicard.toBase dyadicPicard.toBase :=
  (norm_unique_extension φ).choose

theorem integralNorm_restrict
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) :
    genericFibreRestrict BaseRing ℚ dyadicPicard.toBase dyadicPicard.toBase
      (integralNorm φ) = genericNorm φ :=
  (norm_unique_extension φ).choose_spec.1

theorem integralNorm_unique (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (ψ : SchemeHomOver dyadicPicard.toBase dyadicPicard.toBase)
    (hψ : genericFibreRestrict BaseRing ℚ dyadicPicard.toBase dyadicPicard.toBase ψ = genericNorm φ) :
    ψ = integralNorm φ :=
  (norm_unique_extension φ).choose_spec.2 ψ hψ

def integralPi := integralNorm schemePi
def integralPiConjugate := integralNorm schemePiConjugate

theorem actual_norms_have_unique_dyadic_integral_extensions :
    (∃! ψ : SchemeHomOver dyadicPicard.toBase dyadicPicard.toBase,
      genericFibreRestrict BaseRing ℚ dyadicPicard.toBase dyadicPicard.toBase ψ = genericPi) ∧
    (∃! ψ : SchemeHomOver dyadicPicard.toBase dyadicPicard.toBase,
      genericFibreRestrict BaseRing ℚ dyadicPicard.toBase dyadicPicard.toBase ψ = genericPiConjugate) :=
  ⟨norm_unique_extension schemePi, norm_unique_extension schemePiConjugate⟩

end MazurTransfer.Order13DyadicMixedIntegralNormExtensions
#print axioms MazurTransfer.Order13DyadicMixedIntegralNormExtensions.integralNorm_restrict
#print axioms MazurTransfer.Order13DyadicMixedIntegralNormExtensions.actual_norms_have_unique_dyadic_integral_extensions

end


