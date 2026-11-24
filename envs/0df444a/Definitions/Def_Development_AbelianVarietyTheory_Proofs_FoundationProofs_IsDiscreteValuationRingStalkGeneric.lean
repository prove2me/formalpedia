-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T19:43:10.253801+00:00
-- url     : https://prove2.me/theorems/c2f6e441-e165-4d25-9a51-b9cb3f819713
-- title:
--   Is Discrete Valuation Ring Stalk Generic
-- statement:
--   Definitions and structural lemmas for Is Discrete Valuation Ring Stalk Generic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.DvrModel
open PrimeSection
variable {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {K : Type u} [Field K] [Algebra V K] [IsFractionRing V K] {ϖ : V}
  {H : Scheme.{u}} {f : H ⟶ Spec (.of V)}
  {HK : Scheme.{u}} {j : HK ⟶ H} {fK : HK ⟶ Spec (.of K)}
  {Hs : Scheme.{u}} {i : Hs ⟶ H} {fs : Hs ⟶ Spec (.of (ResidueField V))}
local notation "cst[" f ", " R ", " c "]" =>
  ConcreteCategory.hom (Scheme.Hom.appTop f)
    (ConcreteCategory.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of R))) c)
theorem pull_U {X Y : Scheme.{u}} (L : LB X) (φ : Y ⟶ X) (a : PUnit → L.ι) :
    (L.pull φ).U a = φ ⁻¹ᵁ L.U (a ⟨⟩) :=
  le_antisymm (LB.wchart_le L (fun _ ↦ φ) a ⟨⟩) fun _ hy ↦ Set.mem_iInter.2 fun _ ↦ hy
section Main
variable [Flat f] [LocallyOfFiniteType f] [IsIntegral HK] [IsIntegral Hs]
  (hK : IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K))))
  (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V))))
include hK hs
end Main
theorem isIntegral_of_geometricallyIntegral {X S Z : Scheme.{u}} {q : X ⟶ S}
    [GeometricallyIntegral q] {F : Type u} [Field F] {y : Spec (.of F) ⟶ S} {k : Z ⟶ X}
    {p : Z ⟶ Spec (.of F)} (h : IsPullback k p q y) : IsIntegral Z :=
  GeometricallyIntegral.geometrically_isIntegral _ _ _ h
example (n : Type u) [Finite n] :
    let q := 𝔸(n; Spec (.of V)) ↘ Spec (.of V)
    Flat q ∧ LocallyOfFiniteType q ∧
      IsIntegral (pullback q (Spec.map (CommRingCat.ofHom (algebraMap V K)))) ∧
      IsIntegral (pullback q (Spec.map (CommRingCat.ofHom (residue V)))) ∧
      ∃ e : Spec (.of V) ⟶ 𝔸(n; Spec (.of V)), e ≫ q = 𝟙 _ := by
  refine ⟨?_, inferInstance, isIntegral_of_geometricallyIntegral (.of_hasPullback _ _),
    isIntegral_of_geometricallyIntegral (.of_hasPullback _ _),
    AffineSpace.homOfVector (𝟙 _) 0, AffineSpace.homOfVector_over _ _⟩
  rw [(Iso.inv_comp_eq _).1 (AffineSpace.SpecIso_inv_over (n := n) (.of V))]
  have : Flat (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := n) (R := V)))) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2
      (inferInstanceAs (Module.Flat V (MvPolynomial n V))))
  infer_instance
end GlobalTheory.DvrModel
namespace GlobalTheory.PrimeElement
end GlobalTheory.PrimeElement
namespace GlobalTheory.DvrModel
end GlobalTheory.DvrModel


