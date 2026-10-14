-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.IsAlgEquivZero.eulerChar_pullback_tensor_eq_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-11T13:24:26.230134+00:00
-- url     : https://prove2.me/submissions/f9459b1e-3022-4ee8-a6b9-23b4333e64d8

import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Mathlib.RingTheory.Localization.FractionRing
import Theorems.Thm_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_notMem_forall_eulerChar_baseChange_eq_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

section
-- Reused implementation: Solutions.PhilipponSheafEulerFiltration

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.SchemeEuler
open AlgebraicGeometry CategoryTheory MonoidalCategory Topology
open scoped BigOperators
universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))

/-- Reuse the existing comparison of actual Čech cohomology under a module
isomorphism. This proof works in the universe of the mission's base field. -/
theorem euler_iso {M N : X.Modules} (e : M ≅ N) (U : X.OrderedAffineCover) :
    (OModulePresheaf.ofModules π M).eulerChar U =
      (OModulePresheaf.ofModules π N).eulerChar U := by
  obtain ⟨⟨e0⟩, hS, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso π e U
  have h : ∀ i, (OModulePresheaf.ofModules π M).cechFinrank U i =
      (OModulePresheaf.ofModules π N).cechFinrank U i := by
    intro i
    cases i with
    | zero => exact e0.finrank_eq
    | succ j => obtain ⟨e⟩ := hS j; exact e.finrank_eq
  rw [OModulePresheaf.eulerChar_def, OModulePresheaf.eulerChar_def]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

end PhilipponMultiplicity.SchemeEuler
end
end

section
-- Reused implementation: Solutions.PhilipponEulerSchemeIsomorphism

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.SchemeEuler
open AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] [Nontrivial R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)}

/-- An ordered Čech complex has no terms at or beyond the number of its
charts. This also covers the empty scheme with the empty affine cover. -/
theorem cechFinrank_eq_zero_of_card_le (F : OModulePresheaf π)
    (U : X.OrderedAffineCover) (n : ℕ) (hn : Fintype.card U.ι ≤ n) :
    F.cechFinrank U n = 0 := by
  have hidx : IsEmpty (U.Idx n) := ⟨fun s => by
    have h := Fintype.card_le_of_injective s.val s.property.injective
    rw [Fintype.card_fin] at h
    omega⟩
  cases n with
  | zero =>
      letI := hidx
      exact Module.finrank_zero_of_subsingleton
  | succ n =>
      letI := hidx
      exact Module.finrank_zero_of_subsingleton

theorem euler_eq_sum_range_of_card_le (F : OModulePresheaf π)
    (U : X.OrderedAffineCover) (n : ℕ) (hn : Fintype.card U.ι ≤ n) :
    F.eulerChar U = ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * (F.cechFinrank U i : ℤ) := by
  rw [OModulePresheaf.eulerChar_def]
  apply Finset.sum_subset (Finset.range_mono hn)
  intro i hi hin
  have hbound : Fintype.card U.ι ≤ i := by simpa only [Finset.mem_range, not_lt] using hin
  rw [cechFinrank_eq_zero_of_card_le F U i hbound, Nat.cast_zero, mul_zero]

/-- Pullback through a scheme isomorphism preserves the actual Euler
characteristic, even when the two chosen affine covers have different sizes. -/
theorem euler_pullback_iso {Y : Scheme.{u}} (πY : Y ⟶ Spec (.of R))
    [IsSeparated πY] (f : X ⟶ Y) [IsIso f] (M : Y.Modules)
    (hM : Scheme.Modules.IsInvertible M) (U : X.OrderedAffineCover)
    (W : Y.OrderedAffineCover) :
    (OModulePresheaf.ofModules (f ≫ πY) ((Scheme.Modules.pullback f).obj M)).eulerChar U =
      (OModulePresheaf.ofModules πY M).eulerChar W := by
  let n := max (Fintype.card U.ι) (Fintype.card W.ι)
  rw [euler_eq_sum_range_of_card_le _ U n (le_max_left _ _),
    euler_eq_sum_range_of_card_le _ W n (le_max_right _ _)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [OModulePresheaf.cechFinrank_ofModules_pullback_eq_of_isIso πY f M hM U W i]

theorem euler_pullback_iso_over {Y : Scheme.{u}} (πX : X ⟶ Spec (.of R))
    (πY : Y ⟶ Spec (.of R)) [IsSeparated πY] (f : X ⟶ Y) [IsIso f]
    (hf : f ≫ πY = πX) (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M)
    (U : X.OrderedAffineCover) (W : Y.OrderedAffineCover) :
    (OModulePresheaf.ofModules πX ((Scheme.Modules.pullback f).obj M)).eulerChar U =
      (OModulePresheaf.ofModules πY M).eulerChar W := by
  exact (congrArg (fun θ =>
    (OModulePresheaf.ofModules θ ((Scheme.Modules.pullback f).obj M)).eulerChar U) hf).symm.trans
      (euler_pullback_iso πY f M hM U W)

end PhilipponMultiplicity.SchemeEuler
end
end

section
-- Reused implementation: Solutions.PhilipponAffineFamilyEuler

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.AffineFamilyEuler
open AlgebraicGeometry CategoryTheory Topology
universe u

variable {S K : Type u} [CommRing S] [Field K]

/-- A field-valued parameter determines its actual prime ideal in the affine
parameter scheme. -/
def parameterPoint (φ : S →+* K) : PrimeSpectrum S :=
  ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩

variable {X : Scheme.{u}} (π : X ⟶ Spec (.of S)) (M : X.Modules)
    (U : X.OrderedAffineCover)

/-- The existing Čech Euler characteristic of the actual base-changed sheaf. -/
def fibreEuler (φ : S →+* K) : ℤ := by
  letI : Algebra S K := φ.toAlgebra
  exact (OModulePresheaf.ofModules
    (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap S K))
    ((Scheme.Modules.pullback
      (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap S K))).obj M)).eulerChar
        (U.baseChange π K)

end PhilipponMultiplicity.AffineFamilyEuler
end
end

section
-- Reused implementation: Solutions.PhilipponIntegralFamilyEuler

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.AffineFamilyEuler
open AlgebraicGeometry CategoryTheory
universe u

/-- Over an integral affine parameter scheme all field-valued fibres have
one Euler characteristic, even when their residue fields differ. Each local
constant is compared with the same fraction-field fibre. -/
theorem fibreEuler_eq_over_domain
    {S : Type u} [CommRing S] [IsDomain S] [IsNoetherianRing S]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of S)) [IsProper π] [Flat π]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (U : X.OrderedAffineCover)
    (K₁ K₂ : Type u) [Field K₁] [Field K₂] [Algebra S K₁] [Algebra S K₂] :
    fibreEuler π M U (algebraMap S K₁) = fibreEuler π M U (algebraMap S K₂) := by
  obtain ⟨g₁, hg₁, χ₁, hχ₁⟩ :=
    OModulePresheaf.exists_notMem_forall_eulerChar_baseChange_eq_of_locallyTrivial
      π M hM.exists_trivialization U (parameterPoint (algebraMap S K₁))
  obtain ⟨g₂, hg₂, χ₂, hχ₂⟩ :=
    OModulePresheaf.exists_notMem_forall_eulerChar_baseChange_eq_of_locallyTrivial
      π M hM.exists_trivialization U (parameterPoint (algebraMap S K₂))
  have hn₁ : g₁ ≠ 0 := by intro h; apply hg₁; simp [h]
  have hn₂ : g₂ ≠ 0 := by intro h; apply hg₂; simp [h]
  have hf₁ : algebraMap S (FractionRing S) g₁ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr hn₁
  have hf₂ : algebraMap S (FractionRing S) g₂ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr hn₂
  have hχ : χ₁ = χ₂ := (hχ₁ (FractionRing S) hf₁).symm.trans (hχ₂ (FractionRing S) hf₂)
  exact (hχ₁ K₁ hg₁).trans (hχ.trans (hχ₂ K₂ hg₂).symm)

end PhilipponMultiplicity.AffineFamilyEuler
end
end

section
-- Reused implementation: Solutions.PhilipponGeometricFamilyEuler

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.GeometricFamilyEuler
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RelPicard NeronModelInfra
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    (U : X.OrderedAffineCover) {T : Scheme.{u}} (h : T ⟶ Spec (.of k))
    (F : (pullback a h).Modules)

def fibre {K : Type u} [Field K] [Algebra k K]
    (s : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k K) h) : ℤ :=
  (OModulePresheaf.ofModules (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k K))
    ((Scheme.Modules.pullback (baseChangeSnd a s)).obj F)).eulerChar (U.baseChange a K)

/-- The base-change diagram is adapted from the accepted proof of
RelPicard.IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq (submission
f9a53e0a-3fc0-5fa5-b07d-98f2b9ba8075). Euler comparison here uses arbitrary
ordered affine covers and the already proved scheme-isomorphism comparison. -/
theorem specMap_comp_specMap (B K : Type u) [CommRing B] [CommRing K]
    [Algebra k B] [Algebra k K] [Algebra B K] [IsScalarTower k B K] :
    Scheme.TwoAffineOpenCover.specMap B K ≫ Scheme.TwoAffineOpenCover.specMap k B =
      Scheme.TwoAffineOpenCover.specMap k K := by
  rw [Scheme.TwoAffineOpenCover.specMap, Scheme.TwoAffineOpenCover.specMap,
    Scheme.TwoAffineOpenCover.specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

theorem congrHom_hom_fst {X Y Z : Scheme.{u}} (f : X ⟶ Z) {g g' : Y ⟶ Z} (hg : g = g') :
    (pullback.congrHom (rfl : f = f) hg).hom ≫ pullback.fst f g' = pullback.fst f g := by
  subst hg
  simp

theorem congrHom_hom_snd {X Y Z : Scheme.{u}} (f : X ⟶ Z) {g g' : Y ⟶ Z} (hg : g = g') :
    (pullback.congrHom (rfl : f = f) hg).hom ≫ pullback.snd f g' = pullback.snd f g := by
  subst hg
  simp

variable [IsProper a] (hF : Scheme.Modules.IsInvertible F)

include hF in
/-- Computing a parameter fibre after restricting the family to an affine
chart gives its original Euler characteristic, with no fixed cover size. -/
theorem fibre_eq_affine_baseChange (B : Type u) [CommRing B] [Algebra k B]
    (sB : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k B) h)
    (K : Type u) [Field K] [Algebra k K] [Algebra B K] [IsScalarTower k B K]
    (sK : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k K) h)
    (hsK : sK.1 = Scheme.TwoAffineOpenCover.specMap B K ≫ sB.1) :
    fibre a U h F sK = AffineFamilyEuler.fibreEuler
      (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B))
      ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)
      (U.baseChange a B) (algebraMap B K) := by
  have hg := specMap_comp_specMap (k := k) B K
  let ψ : pullback (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B))
      (Scheme.TwoAffineOpenCover.specMap B K) ≅
      pullback a (Scheme.TwoAffineOpenCover.specMap k K) :=
    pullbackLeftPullbackSndIso a (Scheme.TwoAffineOpenCover.specMap k B)
      (Scheme.TwoAffineOpenCover.specMap B K) ≪≫ pullback.congrHom rfl hg
  have hψfst : ψ.hom ≫ pullback.fst a (Scheme.TwoAffineOpenCover.specMap k K) =
      pullback.fst (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B))
        (Scheme.TwoAffineOpenCover.specMap B K) ≫
          pullback.fst a (Scheme.TwoAffineOpenCover.specMap k B) := by
    simp only [ψ, Iso.trans_hom, Category.assoc, congrHom_hom_fst,
      pullbackLeftPullbackSndIso_hom_fst]
  have hψsnd : ψ.hom ≫ pullback.snd a (Scheme.TwoAffineOpenCover.specMap k K) =
      pullback.snd (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B))
        (Scheme.TwoAffineOpenCover.specMap B K) := by
    simp only [ψ, Iso.trans_hom, Category.assoc, congrHom_hom_snd,
      pullbackLeftPullbackSndIso_hom_snd]
  let φ := ψ.inv
  have hφfst : φ ≫ pullback.fst (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B))
      (Scheme.TwoAffineOpenCover.specMap B K) ≫
        pullback.fst a (Scheme.TwoAffineOpenCover.specMap k B) =
      pullback.fst a (Scheme.TwoAffineOpenCover.specMap k K) := by
    rw [← hψfst, Iso.inv_hom_id_assoc]
  have hφsnd : φ ≫ pullback.snd (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B))
      (Scheme.TwoAffineOpenCover.specMap B K) =
      pullback.snd a (Scheme.TwoAffineOpenCover.specMap k K) := by
    rw [← hψsnd, Iso.inv_hom_id_assoc]
  have hmap : (φ ≫ pullback.fst (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B))
      (Scheme.TwoAffineOpenCover.specMap B K)) ≫ baseChangeSnd a sB = baseChangeSnd a sK := by
    apply pullback.hom_ext
    · unfold baseChangeSnd
      simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
      exact hφfst
    · unfold baseChangeSnd
      simp only [Category.assoc, pullback.lift_snd]
      rw [hsK, pullback.condition_assoc, ← Category.assoc φ, hφsnd]
  let e : (Scheme.Modules.pullback (baseChangeSnd a sK)).obj F ≅
      (Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback
        (pullback.fst (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B))
          (Scheme.TwoAffineOpenCover.specMap B K))).obj
            ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)) :=
    ((Scheme.Modules.pullbackCongr hmap).app F).symm ≪≫
      ((Scheme.Modules.pullbackComp
        (φ ≫ pullback.fst (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B))
          (Scheme.TwoAffineOpenCover.specMap B K)) (baseChangeSnd a sB)).app F).symm ≪≫
      ((Scheme.Modules.pullbackComp φ
        (pullback.fst (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B))
          (Scheme.TwoAffineOpenCover.specMap B K))).app _).symm
  letI : IsProper (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  letI : IsProper (pullback.snd (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B))
      (Scheme.TwoAffineOpenCover.specMap B K)) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  exact (SchemeEuler.euler_iso _ e (U.baseChange a K)).trans
    (SchemeEuler.euler_pullback_iso_over _ _ φ hφsnd _
      ((hF.pullback _).pullback _) (U.baseChange a K) ((U.baseChange a B).baseChange _ K))

end PhilipponMultiplicity.GeometricFamilyEuler
end
end

section
-- Reused implementation: Solutions.PhilipponIntegralParameterEuler

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.GeometricFamilyEuler
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RelPicard NeronModelInfra
universe u
variable {k : Type u} [Field k] {T : Scheme.{u}} (h : T ⟶ Spec (.of k))

/-- Affine-chart identifications reused from the accepted proof of
RelPicard.IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq,
submission f9a53e0a-3fc0-5fa5-b07d-98f2b9ba8075. -/
theorem fromSpec_comp_eq_specMap (W : T.Opens) (hW : IsAffineOpen W) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom h W
    hW.fromSpec ≫ h = Scheme.TwoAffineOpenCover.specMap k Γ(T, W) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom h W
  have e1 : CommRingCat.ofHom (algebraMap k Γ(T, W)) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ h.appLE ⊤ W le_top := rfl
  rw [Scheme.TwoAffineOpenCover.specMap, e1, Spec.map_comp, ← Scheme.isoSpec_Spec_inv,
    ← IsAffineOpen.fromSpec_top, IsAffineOpen.SpecMap_appLE_fromSpec h (isAffineOpen_top _) hW]

theorem exists_algebra_of_range_subset (W : T.Opens) (hW : IsAffineOpen W)
    (K : Type u) [Field K] [Algebra k K]
    (s : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k K) h)
    (hs : Set.range ⇑s.1 ⊆ (W : Set T)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom h W
    ∃ (_ : Algebra Γ(T, W) K) (_ : IsScalarTower k Γ(T, W) K),
      s.1 = Scheme.TwoAffineOpenCover.specMap Γ(T, W) K ≫ hW.fromSpec := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom h W
  haveI := hW.isOpenImmersion_fromSpec
  let τ : Spec (.of K) ⟶ Spec Γ(T, W) := IsOpenImmersion.lift hW.fromSpec s.1 (by
    rw [IsAffineOpen.range_fromSpec]; exact hs)
  have hτ : τ ≫ hW.fromSpec = s.1 := IsOpenImmersion.lift_fac _ _ _
  let θ : Γ(T, W) ⟶ CommRingCat.of K := Spec.preimage τ
  have hθ : Spec.map θ = τ := Spec.map_preimage τ
  letI : Algebra Γ(T, W) K := θ.hom.toAlgebra
  have hspec : Scheme.TwoAffineOpenCover.specMap Γ(T, W) K = τ := by rw [← hθ]; rfl
  refine ⟨inferInstance, IsScalarTower.of_algebraMap_eq fun x => ?_, by rw [hspec, hτ]⟩
  have key : CommRingCat.ofHom (algebraMap k K) =
      CommRingCat.ofHom (algebraMap k Γ(T, W)) ≫ θ := by
    apply Spec.map_injective
    change Scheme.TwoAffineOpenCover.specMap k K = _
    rw [Spec.map_comp, hθ, ← s.2, ← hτ, Category.assoc, fromSpec_comp_eq_specMap h W hW]
  have key' := congrArg CommRingCat.Hom.hom key
  rw [CommRingCat.hom_ofHom, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at key'
  exact RingHom.congr_fun key' x

variable {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [IsProper a]
    (U : X.OrderedAffineCover) (F : (pullback a h).Modules)
    (hF : Scheme.Modules.IsInvertible F) [LocallyOfFiniteType h] [GeometricallyIntegral h]

include hF in
/-- Constancy on an integral affine parameter chart for arbitrary finite
affine covers of the proper fibre, allowing different residue fields. -/
theorem fibre_eq_of_range_subset (W : T.Opens) (hW : IsAffineOpen W)
    (K₁ : Type u) [Field K₁] [Algebra k K₁]
    (s₁ : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k K₁) h)
    (hs₁ : Set.range ⇑s₁.1 ⊆ (W : Set T))
    (K₂ : Type u) [Field K₂] [Algebra k K₂]
    (s₂ : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k K₂) h)
    (hs₂ : Set.range ⇑s₂.1 ⊆ (W : Set T)) :
    fibre a U h F s₁ = fibre a U h F s₂ := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom h W
  haveI : Nonempty W := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of K₁)))
    exact ⟨⟨s₁.1.base x, hs₁ ⟨x, rfl⟩⟩⟩
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian h
  haveI : IsNoetherianRing Γ(T, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  haveI : IsIntegral T := GeometricallyIntegral.isIntegral_of_flat_of_universallyOpen h
  haveI : IsDomain Γ(T, W) := IsIntegral.component_integral W
  let sB : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k Γ(T, W)) h :=
    ⟨hW.fromSpec, fromSpec_comp_eq_specMap h W hW⟩
  have hFB := hF.pullback (baseChangeSnd a sB)
  haveI : Flat (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T, W))) :=
    MorphismProperty.pullback_snd (P := @Flat) _ _ inferInstance
  haveI : IsProper (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T, W))) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  obtain ⟨i₁, t₁, hsK₁⟩ := exists_algebra_of_range_subset h W hW K₁ s₁ hs₁
  obtain ⟨i₂, t₂, hsK₂⟩ := exists_algebra_of_range_subset h W hW K₂ s₂ hs₂
  rw [fibre_eq_affine_baseChange a U h F hF Γ(T, W) sB K₁ s₁ hsK₁,
    fibre_eq_affine_baseChange a U h F hF Γ(T, W) sB K₂ s₂ hsK₂]
  exact AffineFamilyEuler.fibreEuler_eq_over_domain _ _ hFB (U.baseChange a Γ(T, W)) K₁ K₂

include hF in
/-- Any two parameter points in a geometrically integral locally finite-type
family have equal Euler characteristic. Affine charts are connected through
an actual residue-field point in their nonempty intersection. -/
theorem fibre_eq (K₁ : Type u) [Field K₁] [Algebra k K₁]
    (s₁ : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k K₁) h)
    (K₂ : Type u) [Field K₂] [Algebra k K₂]
    (s₂ : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k K₂) h) :
    fibre a U h F s₁ = fibre a U h F s₂ := by
  obtain ⟨W₁, hW₁, hx₁, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := s₁.1.base default) (U := (⊤ : T.Opens)) trivial
  obtain ⟨W₂, hW₂, hx₂, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := s₂.1.base default) (U := (⊤ : T.Opens)) trivial
  have hr₁ : Set.range ⇑s₁.1 ⊆ (W₁ : Set T) :=
    Set.range_subset_iff.mpr fun y => by rw [Unique.eq_default y]; exact hx₁
  have hr₂ : Set.range ⇑s₂.1 ⊆ (W₂ : Set T) :=
    Set.range_subset_iff.mpr fun y => by rw [Unique.eq_default y]; exact hx₂
  haveI : IsIntegral T := GeometricallyIntegral.isIntegral_of_flat_of_universallyOpen h
  obtain ⟨y, hy₁, hy₂⟩ := nonempty_preirreducible_inter
    W₁.isOpen W₂.isOpen ⟨_, hx₁⟩ ⟨_, hx₂⟩
  letI : Algebra k (T.residueField y) := (Spec.preimage (T.fromSpecResidueField y ≫ h)).hom.toAlgebra
  have hσ : T.fromSpecResidueField y ≫ h = Scheme.TwoAffineOpenCover.specMap k (T.residueField y) := by
    change T.fromSpecResidueField y ≫ h = Spec.map
      (CommRingCat.ofHom (Spec.preimage (T.fromSpecResidueField y ≫ h)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let sy : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k (T.residueField y)) h :=
    ⟨T.fromSpecResidueField y, hσ⟩
  have hry : Set.range ⇑sy.1 = {y} := Scheme.range_fromSpecResidueField y
  have hy₁' : Set.range ⇑sy.1 ⊆ (W₁ : Set T) := by
    rw [hry]; exact Set.singleton_subset_iff.mpr hy₁
  have hy₂' : Set.range ⇑sy.1 ⊆ (W₂ : Set T) := by
    rw [hry]; exact Set.singleton_subset_iff.mpr hy₂
  exact (fibre_eq_of_range_subset h a U F hF W₁ hW₁ K₁ s₁ hr₁ (T.residueField y) sy hy₁').trans
    (fibre_eq_of_range_subset h a U F hF W₂ hW₂ (T.residueField y) sy hy₂' K₂ s₂ hr₂)

end PhilipponMultiplicity.GeometricFamilyEuler
end
end

section
-- Reused implementation: Solutions.PhilipponAlgebraicEquivalenceEuler

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.GeometricFamilyEuler
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory RelPicard NeronModelInfra
universe u

/-- Endpoint bundle comparisons follow the existing two-chart proof, but the
Euler comparison now uses arbitrary finite ordered affine covers. -/
theorem euler_tensor_eq_of_family
    {k : Type u} [Field k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [IsProper a]
    (U : X.OrderedAffineCover) (L M : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    {T : Scheme.{u}} (h : T ⟶ Spec (.of k)) [LocallyOfFiniteType h] [GeometricallyIntegral h]
    (N : (pullback a h).Modules) (hN : Scheme.Modules.IsInvertible N)
    (g : Spec (.of k) ⟶ Spec (.of k))
    (hg : g = Scheme.TwoAffineOpenCover.specMap k k) (hg1 : g = 𝟙 _)
    (t₀ t₁ : SchemeHomOver g h)
    (e₀ : Nonempty ((Scheme.Modules.pullback (baseChangeSnd a t₀)).obj N ≅
      SheafOfModules.unit (pullback a g).ringCatSheaf))
    (e₁ : Nonempty ((Scheme.Modules.pullback (baseChangeSnd a t₁)).obj N ≅
      (Scheme.Modules.pullback (pullback.fst a g)).obj L)) :
    (OModulePresheaf.ofModules a (L ⊗ M)).eulerChar U =
      (OModulePresheaf.ofModules a M).eulerChar U := by
  subst hg
  have hF : Scheme.Modules.IsInvertible (N ⊗ (Scheme.Modules.pullback (pullback.fst a h)).obj M) :=
    hN.tensor_monoidalV2 (hM.pullback _)
  haveI : IsIso (Scheme.TwoAffineOpenCover.specMap k k) := by rw [hg1]; infer_instance
  have hcomp : ∀ {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)),
      f ≫ Scheme.TwoAffineOpenCover.specMap k k = f := fun f => by
    rw [hg1]; exact Category.comp_id f
  have hc : pullback.fst a (Scheme.TwoAffineOpenCover.specMap k k) ≫ a =
      pullback.snd a (Scheme.TwoAffineOpenCover.specMap k k) :=
    pullback.condition.trans (hcomp _)
  have hbcs : ∀ t : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k k) h,
      baseChangeSnd a t ≫ pullback.fst a h =
        pullback.fst a (Scheme.TwoAffineOpenCover.specMap k k) := by
    intro t
    unfold baseChangeSnd
    simp only [pullback.lift_fst, Category.comp_id]
  let E₁ : (Scheme.Modules.pullback (baseChangeSnd a t₁)).obj
      (N ⊗ (Scheme.Modules.pullback (pullback.fst a h)).obj M) ≅
      (Scheme.Modules.pullback (pullback.fst a (Scheme.TwoAffineOpenCover.specMap k k))).obj (L ⊗ M) :=
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (e₁.some ⊗ᵢ ((Scheme.Modules.pullbackComp (baseChangeSnd a t₁) (pullback.fst a h)).app M ≪≫
        (Scheme.Modules.pullbackCongr (hbcs t₁)).app M)) ≪≫
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm
  let E₀ : (Scheme.Modules.pullback (baseChangeSnd a t₀)).obj
      (N ⊗ (Scheme.Modules.pullback (pullback.fst a h)).obj M) ≅
      (Scheme.Modules.pullback (pullback.fst a (Scheme.TwoAffineOpenCover.specMap k k))).obj M :=
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (e₀.some ⊗ᵢ ((Scheme.Modules.pullbackComp (baseChangeSnd a t₀) (pullback.fst a h)).app M ≪≫
        (Scheme.Modules.pullbackCongr (hbcs t₀)).app M)) ≪≫ λ_ _
  have he₁ : fibre a U h (N ⊗ (Scheme.Modules.pullback (pullback.fst a h)).obj M) t₁ =
      (OModulePresheaf.ofModules a (L ⊗ M)).eulerChar U :=
    (SchemeEuler.euler_iso _ E₁ (U.baseChange a k)).trans
      (SchemeEuler.euler_pullback_iso_over _ a _ hc (L ⊗ M)
        (hL.tensor_monoidalV2 hM) (U.baseChange a k) U)
  have he₀ : fibre a U h (N ⊗ (Scheme.Modules.pullback (pullback.fst a h)).obj M) t₀ =
      (OModulePresheaf.ofModules a M).eulerChar U :=
    (SchemeEuler.euler_iso _ E₀ (U.baseChange a k)).trans
      (SchemeEuler.euler_pullback_iso_over _ a _ hc M hM (U.baseChange a k) U)
  exact he₁.symm.trans ((fibre_eq h a U _ hF k t₁ k t₀).trans he₀)

end PhilipponMultiplicity.GeometricFamilyEuler

namespace AlgebraicGeometry.RelPicard
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open PhilipponMultiplicity PhilipponMultiplicity.GeometricFamilyEuler
universe u

/-- Algebraic equivalence to zero preserves the actual Euler characteristic
of every invertible twist on any proper scheme, for any ordered affine cover. -/
theorem IsAlgEquivZero.eulerChar_tensor_eq_monoidalV2
    {k : Type u} [Field k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [IsProper a]
    (U : X.OrderedAffineCover) (L M : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (h0 : IsAlgEquivZero a L) :
    (OModulePresheaf.ofModules a (L ⊗ M)).eulerChar U =
      (OModulePresheaf.ofModules a M).eulerChar U := by
  obtain ⟨T, h, hft, hgi, N, hN, t₀, t₁, e₀, e₁⟩ := h0
  letI := hft
  letI := hgi
  have hk : Scheme.TwoAffineOpenCover.specMap k k = 𝟙 (Spec (.of k)) := by
    change Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _
    rw [CommRingCat.ofHom_id, Spec.map_id]
  exact euler_tensor_eq_of_family a U L M hL hM h N hN (𝟙 _) hk.symm rfl t₀ t₁ e₀ e₁

/-- The same equality holds after restriction to every closed subscheme;
properness is inherited and algebraic equivalence is preserved by pullback. -/
theorem IsAlgEquivZero.eulerChar_pullback_tensor_eq_monoidalV2_proof
    {k : Type u} [Field k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [IsProper a]
    (L M : X.Modules) (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (h0 : IsAlgEquivZero a L) {Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f]
    (U : Y.OrderedAffineCover) :
    (OModulePresheaf.ofModules (f ≫ a) ((Scheme.Modules.pullback f).obj (L ⊗ M))).eulerChar U =
      (OModulePresheaf.ofModules (f ≫ a) ((Scheme.Modules.pullback f).obj M)).eulerChar U := by
  exact (SchemeEuler.euler_iso (f ≫ a) (Scheme.Modules.pullbackTensorObjIso f L M) U).trans
    (IsAlgEquivZero.eulerChar_tensor_eq_monoidalV2 (f ≫ a) U _ _ (hL.pullback f) (hM.pullback f)
      (h0.pullback f rfl))

end AlgebraicGeometry.RelPicard
end
end

open AlgebraicGeometry AlgebraicGeometry.RelPicard CategoryTheory MonoidalCategory
universe u

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [IsProper a]
    (L M : X.Modules) (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (h0 : IsAlgEquivZero a L) {Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f]
    (U : Y.OrderedAffineCover) :
    (OModulePresheaf.ofModules (f ≫ a) ((Scheme.Modules.pullback f).obj (L ⊗ M))).eulerChar U =
      (OModulePresheaf.ofModules (f ≫ a) ((Scheme.Modules.pullback f).obj M)).eulerChar U := by
  exact IsAlgEquivZero.eulerChar_pullback_tensor_eq_monoidalV2_proof a L M hL hM h0 f U
