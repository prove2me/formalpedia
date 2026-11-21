-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.isZero_relative_constant_etale_higher_direct_image_stalk_at_proper_excision_center
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-21T03:56:22.549228+00:00
-- url     : https://prove2.me/submissions/3c712751-6da3-44f1-b412-76c4b76fa335
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSites
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.ZMod
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_iso_closed_fiber_of_strictly_henselian
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_higher_stalk_iso_strict_local_cohomology

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etaleHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleRelativeCohomology (relativeConstant)
open PhilipponEtaleRelativeStalks (isZero_pullback_relativeConstant_of_range_subset)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStrictHenselization (closedPointInclusion closedPoint_range_subset toBase)


namespace PhilipponEtaleClosedCenterLocal

universe u

variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) (i : Z ⟶ X)
  {K : Type u} [Field K] [IsSepClosed K] (s : Spec (CommRingCat.of K) ⟶ X)

private abbrev localProjection := pullback.snd (toBase s) f

private abbrev residueProjection := pullback.snd (closedPointInclusion s) (pullback.fst (toBase s) f)

private abbrev localCoefficients (A : Type u) [AddCommGroup A] :=
  (pullbackSheaves (localProjection f s)).obj (relativeConstant (pullback.fst f i) A)

private abbrev residueCoefficients (A : Type u) [AddCommGroup A] :=
  (pullbackSheaves (residueProjection f s)).obj (localCoefficients f i s A)

/-- Over a point of the center, the relative coefficient sheaf vanishes on
the closed fiber after base change to the spectrum of the étale local ring. -/
theorem isZero_residueCoefficients (A : Type u) [AddCommGroup A]
    (hs : s default ∈ Set.range i) : IsZero (residueCoefficients f i s A) := by
  let p := localProjection f s
  let k := residueProjection f s
  let b := pullback.fst (closedPointInclusion s) (pullback.fst (toBase s) f)
  have h : (k ≫ p) ≫ f = b ≫ closedPointInclusion s ≫ toBase s := by
    change (k ≫ pullback.snd (toBase s) f) ≫ f = b ≫ closedPointInclusion s ≫ toBase s
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    change k ≫ pullback.fst (toBase s) f ≫ toBase s = _
    rw [← pullback.condition_assoc]
  have hr : Set.range (k ≫ p) ⊆ Set.range (pullback.fst f i) := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Pullback.range_fst]
    change f ((k ≫ p) z) ∈ Set.range i
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
    exact closedPoint_range_subset s i hs (Set.mem_range_self _)
  have hZero := isZero_pullback_relativeConstant_of_range_subset (k ≫ p) (pullback.fst f i) A hr
  let adj := ((pullbackAdjunction p).comp (pullbackAdjunction k)).ofNatIsoRight (pushforwardCompIso p k)
  exact hZero.of_iso ((adj.leftAdjointUniq (pullbackAdjunction (k ≫ p))).app _)

/-- Once the two cohomology comparisons are available, the closed-center
stalk vanishes because its coefficient sheaf on the residue fiber is zero. -/
theorem isZero_higherImageStalk_of_localComparisons (A : Type u) [AddCommGroup A]
    (hs : s default ∈ Set.range i) (q : ℕ)
    (hLimit : Nonempty ((Scheme.pointSmallEtale s).sheafFiber.obj
        (((pushforward f).rightDerived (q + 1)).obj (relativeConstant (pullback.fst f i) A)) ≅
      AddCommGrpCat.of ((localCoefficients f i s A).H (q + 1))))
    (hFiber : Nonempty (AddCommGrpCat.of ((localCoefficients f i s A).H (q + 1)) ≅
      AddCommGrpCat.of ((residueCoefficients f i s A).H (q + 1)))) :
    IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj
      (((pushforward f).rightDerived (q + 1)).obj (relativeConstant (pullback.fst f i) A))) := by
  have hz := Sheaf.subsingleton_H_of_isZero (isZero_residueCoefficients f i s A hs) (q + 1)
  exact (AddCommGrpCat.isZero_iff_subsingleton.mpr hz).of_iso
    (Classical.choice hLimit ≪≫ Classical.choice hFiber)

end PhilipponEtaleClosedCenterLocal

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleRelativeDirectImage (sectionFunctions)
open PhilipponEtaleRelativeCohomology (relativeConstant relativeSheaf)


namespace PhilipponEtaleRelativeCoefficients

universe u

/-- The cardinality of the finite coefficient group annihilates every
section of the relative constant sheaf. -/
theorem card_nsmul_section_eq_zero {X Z : Scheme.{u}} (i : Z ⟶ X)
    (A : Type u) [AddCommGroup A] [Finite A] (W : X.Etaleᵒᵖ)
    (a : ↥((relativeConstant i A).obj.obj W)) : Nat.card A • a = 0 := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let : Fintype A := Fintype.ofFinite A
  change Nat.card A • a = (0 : (relativeSheaf i A).obj.obj (op W.unop))
  apply (sectionFunctions A i W.unop).injective
  rw [map_nsmul, map_zero]
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change Nat.card A • (sectionFunctions A i W.unop a).val x = 0
  rw [Nat.card_eq_fintype_card]
  exact card_nsmul_eq_zero

/-- The same cardinality annihilates the identity morphism of the sheaf. -/
theorem card_nsmul_id_eq_zero {X Z : Scheme.{u}} (i : Z ⟶ X)
    (A : Type u) [AddCommGroup A] [Finite A] :
    Nat.card A • 𝟙 (relativeConstant i A) = 0 := by
  apply Sheaf.hom_ext
  ext W a
  change Nat.card A • a = 0
  exact card_nsmul_section_eq_zero i A W a

end PhilipponEtaleRelativeCoefficients

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (A : Type u) [AddCommGroup A] [Finite A] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Set.range i = (U : Set X)ᶜ)
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (CommRingCat.of K) ⟶ X)
    (hs : s default ∈ Set.range i) (q : ℕ) :
    IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj
      (((PhilipponEtaleClosedPushforward.pushforward f).rightDerived (q + 1)).obj (PhilipponEtaleRelativeCohomology.relativeConstant (pullback.fst f i) A))) := by
  let R : Type u := PhilipponEtaleLocalRing.stalkRing s
  let hR : HenselianLocalRing R := PhilipponEtaleHenselianStalk.henselianLocalRing s
  letI := hR
  let hK : IsSepClosed (IsLocalRing.ResidueField R) :=
    PhilipponEtaleHenselianStalk.residueFieldIsSepClosed s
  let g := pullback.fst (PhilipponEtaleStrictHenselization.toBase s) f
  let p := pullback.snd (PhilipponEtaleStrictHenselization.toBase s) f
  let j := pullback.snd (PhilipponEtaleStrictHenselization.closedPointInclusion s) g
  let F := PhilipponEtaleRelativeCohomology.relativeConstant (pullback.fst f i) A
  let P := PhilipponEtaleSmallSite.pullbackSheaves p
  let : P.Additive := (PhilipponEtaleSmallSite.pullbackAdjunction p).left_adjoint_additive
  have htors : Nat.card A • 𝟙 (P.obj F) = 0 := by
    have hF : Nat.card A • 𝟙 F = 0 :=
      PhilipponEtaleRelativeCoefficients.card_nsmul_id_eq_zero (pullback.fst f i) A
    calc
      Nat.card A • 𝟙 (P.obj F) = P.map (Nat.card A • 𝟙 F) := by
        rw [Functor.map_nsmul, P.map_id]
      _ = 0 := by rw [hF, P.map_zero]
  apply PhilipponEtaleClosedCenterLocal.isZero_higherImageStalk_of_localComparisons f i s A hs q
  · exact AlgebraicGeometry.Scheme.nonempty_etale_higher_stalk_iso_strict_local_cohomology f s F q
  · exact @AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_closed_fiber_of_strictly_henselian R _ hR hK _ g _ (PhilipponEtaleSmallSite.pullbackSheaves j)
      (PhilipponEtaleSmallSite.pullbackAdjunction j) (P.obj F)
      (Nat.card A) (Nat.ne_of_gt Nat.card_pos) htors q

end

end
