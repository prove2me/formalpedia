-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
-- name    : Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:28:03.970801+00:00
-- url     : https://prove2.me/theorems/974e440b-53fb-47f9-9615-4b820045842e
-- title:
--   Exists Unique Partner
-- statement:
--   Definitions and structural lemmas for Exists Unique Partner, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/ExistsUniquePartner.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.LN
open GlobalTheory.UU
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
  {D : DegPre R} {D' : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G'] [IsCommMonObj G']
structure Cmp (φ : R →+* V) (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) where

  pb : IsGrpPullback G' G (spMap φ) F

  wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)

  wL_map : IsCPMap U'.P U.P (spMap φ) F pb.1.w wL

  β : D'.P.A.left ⟶ D.P.A.left

  pbB : IsGrpPullback D'.P.A D.P.A (spMap φ) β

  v : LB.Iso D'.P.L (D.P.L.pull β)

  v_gen : v.IsGen

  xe : D'.X ≃+ D.X

  c_pr : ∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left

  lev : ∀ (e : ℕ) (Z : Scheme.{0}) (x' : Z ⟶ (thickObj V I' e G').left) (x : Z ⟶ (thickObj R I e G).left),
    x ≫ (fstG I e G).left = x' ≫ (fstG I' e G').left ≫ F →
    x' ≫ (U'.gt e).pG.left ≫ β = x ≫ (U.gt e).pG.left ∧
    ∀ (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' →
      (∀ χ : D'.X, val ((U.gt e).t (xe χ)) x z J = val ((U'.gt e).t χ) x' z J' *
        ∏ k : Fin 4, gw v (x' ≫ D'.Oφ (U'.gt e).pG χ k) z (J (x' ≫ D'.Oφ (U'.gt e).pG χ k ≫ β))
          (J' (x' ≫ D'.Oφ (U'.gt e).pG χ k)) ^ Oinvε k) ∧
      ∀ (k : U.P.L.L.ι) (k' : U'.P.L.L.ι), (fstG I e G).left (x z) ∈ U.P.L.L.U k → (fstG I' e G').left (x' z) ∈ U'.P.L.L.U k' →
        gw v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG.left)) (J' (x' ≫ (U'.gt e).pG.left)) *
            gw (U'.w e) x' z (J' (x' ≫ (U'.gt e).pG.left)) (fun _ => k') =
          gw (U.w e) x z (J (x ≫ (U.gt e).pG.left)) (fun _ => k) * gw wL (x' ≫ (fstG I' e G').left) z k k'

  map_le : I.map φ ≤ I' := by first | assumption | exact (Ideal.map_id _).le
def Under {D₀ : DegData R I} (U : PreU I D₀.toPre A G) (U₀ : UnifPre I D₀ A G) : Prop :=
  U.gen = U₀.gen ∧ U.P.L = U₀.LG ∧ HEq U.P.c U₀.cubG ∧ HEq U.P.sym U₀.symG ∧ U.gt = U₀.gt ∧ HEq U.w U₀.w
abbrev withPsi (D : DegPre R) (psi : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1)))
    (h : ∀ χ, (psi χ).IsGen) : DegPre R := setPsi D psi h
namespace Cmp
omit [IsDomain R] in

theorem spMap_ringHom_id : spMap (RingHom.id R) = 𝟙 _ := by
  simp [spMap]
theorem grpPullback_id {S : Scheme.{0}} (H : Over S) [GrpObj H] {f : S ⟶ S} (hf : f = 𝟙 S) :
    IsGrpPullback H H f (𝟙 H.left) := by
  subst hf
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  have hq : (𝟙 H : H ⟶ H).left ≫ H.hom = H.hom ≫ 𝟙 S := by simp
  have e₁ : x₀ = toBase hq x := Over.OverMorphism.ext hx
  have e₂ : y₀ = toBase hq y := Over.OverMorphism.ext hy
  rw [e₁, e₂, ← toBase_mul_of_isMonHom (𝟙 H) hq]
  rfl
theorem cpMap_id {S : Scheme.{0}} {H : Over S} [GrpObj H] [IsCommMonObj H] (P : CP H) {f : S ⟶ S} (hf : f = 𝟙 S)
    (hw : 𝟙 H.left ≫ H.hom = H.hom ≫ f) : IsCPMap P P f (𝟙 H.left) hw (idIso P.L.L) := by
  subst hf
  exact IsCPMap.id P
theorem mono_fstG (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) : Mono (fstG I e G).left := by
  have hs : Function.Surjective (Ideal.Quotient.mk (I ^ (e + 1))) := Ideal.Quotient.mk_surjective
  have : Epi (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))) := ConcreteCategory.epi_of_surjective _ hs
  have : Mono (thick R I e) := Scheme.Spec.map_mono (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))).op
  exact (inferInstance : Mono (pullback.fst G.hom (thick R I e)))
def refl (U : PreU I D A G) : Cmp (RingHom.id R) U U (𝟙 G.left) where
  pb := grpPullback_id G spMap_ringHom_id
  wL := idIso U.P.L.L
  wL_map := cpMap_id U.P spMap_ringHom_id _
  β := 𝟙 _
  pbB := grpPullback_id D.P.A spMap_ringHom_id
  v := idIso D.P.L
  v_gen := idIso_isGen D.P.isLB
  xe := AddEquiv.refl _
  c_pr x := by rw [spMap_ringHom_id]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  lev e Z x' x hx := by
    have := mono_fstG I e G
    rw [Category.comp_id, cancel_mono] at hx
    subst hx
    refine ⟨by rw [Category.comp_id], fun z J J' hJ hJ' => ⟨fun χ => ?_, fun k k' hk hk' => ?_⟩⟩
    · refine (val_change ((U.gt e).t_gen χ) x hJ hJ').trans ((mul_comm _ _).trans (congrArg _ ?_))
      refine Finset.prod_congr rfl fun k _ => congrArg (· ^ _) ?_
      rw [Category.comp_id, gw_idIso _ _ _ (hJ _) (hJ' _)]
    · rw [gw_idIso _ _ _ (hJ _) (hJ' _), gw_idIso U.P.L.L (x ≫ (fstG I e G).left) z hk hk']
      have h := (isGen_iff (U.w e)).1 (U.w_gen e) Z x z (J (x ≫ (U.gt e).pG.left)) (J' (x ≫ (U.gt e).pG.left))
        (fun _ => k) (fun _ => k') (hJ (x ≫ (U.gt e).pG.left)) (hJ' (x ≫ (U.gt e).pG.left))
        (mem_pull.2 hk) (mem_pull.2 hk')
      have g := gm_pull_g U.P.L.L (fstG I e G).left x z (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')
      rw [h, g]
      exact (congrArg (· * _) (inv_mul_cancel_right _ _).symm).trans (mul_right_comm _ _ _)
variable {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left}
theorem pow_le (C : Cmp φ U U' F) (e : ℕ) : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono C.map_le _
def baseMap (C : Cmp φ U U' F) (e : ℕ) :
    Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
  spMap (Ideal.quotientMap (I' ^ (e + 1)) φ (C.pow_le e))
theorem baseMap_thick (C : Cmp φ U U' F) (e : ℕ) : C.baseMap e ≫ thick R I e = thick V I' e ≫ spMap φ := by
  simp only [baseMap, thick, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]
def levMap (C : Cmp φ U U' F) (e : ℕ) : (thickObj V I' e G').left ⟶ (thickObj R I e G).left :=
  pullback.lift ((fstG I' e G').left ≫ F) (pullback.snd G'.hom (thick V I' e) ≫ C.baseMap e) (by
    simp only [Category.assoc]
    rw [C.pb.1.w, C.baseMap_thick]
    exact pullback.condition_assoc (f := G'.hom) (g := thick V I' e) _)
theorem levMap_fst (C : Cmp φ U U' F) (e : ℕ) : C.levMap e ≫ (fstG I e G).left = (fstG I' e G').left ≫ F :=
  pullback.lift_fst _ _ _
end Cmp
example (U : PreU I D A G) (e : ℕ) : (Cmp.refl U).levMap e = 𝟙 _ :=
  have := Cmp.mono_fstG I e G
  (cancel_mono (fstG I e G).left).1 (((Cmp.refl U).levMap_fst e).trans (by simp))
example {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left} (hI' : I' ≠ ⊤)
    (h : I.map φ ⊔ I' = ⊤) : IsEmpty (Cmp φ U U' F) :=
  ⟨fun C => hI' ((sup_eq_right.2 C.map_le).symm.trans h)⟩
example (D : DegPre R) : withPsi D D.psi D.psi_gen = D := rfl
end GlobalTheory.LN
end


