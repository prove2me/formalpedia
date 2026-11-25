-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_CupTateShift
-- name    : GroundTheory_TateCohomology_CupTateShift
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:23:18.78492+00:00
-- url     : https://prove2.me/theorems/663e14ca-c6ef-440c-80e6-0435c0e1819c
-- title:
--   Cup Tate Shift
-- statement:
--   Definitions and structural lemmas for Cup Tate Shift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Theorems.Thm_GroundTheory_GroupCoh_augSES_shortExact
import Theorems.Thm_GroundTheory_GroupCoh_augSES_tensorLeft_shortExact
import Theorems.Thm_GroundTheory_GroupCoh_augSES_tensorRight_shortExact
import Theorems.Thm_GroundTheory_GroupCoh_injective_tensor_whiskerLeft_of_flat
import Theorems.Thm_GroundTheory_GroupCoh_injective_whiskerLeft_of_flat
import Theorems.Thm_GroundTheory_GroupCoh_injective_whiskerLeft_whiskerLeft_of_flat
import Theorems.Thm_GroundTheory_GroupCoh_injective_whiskerLeft_whiskerRight_of_flat
import Theorems.Thm_GroundTheory_GroupCoh_injective_whiskerRight_tensor_of_flat
import Theorems.Thm_GroundTheory_GroupCoh_shortExact_map_tensorLeft
import Theorems.Thm_GroundTheory_GroupCoh_shortExact_map_tensorRight
import Theorems.Thm_P2M_GroundTheory_GroupCoh_isIso_t__of_tateAcyclic_70d2ebbe40a6
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tateAcyclic_augSES_tensorLeft_X__fbb3989e91cd
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tateAcyclic_augSES_tensorRight_X__2ee3f5d8edb9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory groupCohomology
namespace GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
section Exactness
variable {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact)
include hE
theorem shortExact_tensorRight_tensor (B V : Rep.{u} k G) [Module.Flat k V.V]
    (hEB : (E.map (tensorRight B)).ShortExact) : (E.map (tensorRight (V ⊗ B))).ShortExact :=
  shortExact_map_tensorRight hE (V ⊗ B) (injective_whiskerRight_tensor_of_flat V E.f B
    ((Rep.mono_iff_injective _).1 hEB.mono_f))
theorem shortExact_tensorLeft_of_flat (V : Rep.{u} k G) [Module.Flat k V.V] :
    (E.map (tensorLeft V)).ShortExact :=
  shortExact_map_tensorLeft hE V (injective_whiskerLeft_of_flat V E.f
    ((Rep.mono_iff_injective _).1 hE.mono_f))
theorem shortExact_tensorLeft_tensorRight (B V : Rep.{u} k G) [Module.Flat k V.V]
    (hEB : (E.map (tensorRight B)).ShortExact) :
    ((E.map (tensorLeft V)).map (tensorRight B)).ShortExact :=
  shortExact_map_tensorRight (shortExact_tensorLeft_of_flat hE V) B
    (injective_whiskerLeft_whiskerRight_of_flat V E.f B ((Rep.mono_iff_injective _).1 hEB.mono_f))
theorem shortExact_tensorLeft_tensor (A V : Rep.{u} k G) [Module.Flat k V.V]
    (hAE : (E.map (tensorLeft A)).ShortExact) : (E.map (tensorLeft (V ⊗ A))).ShortExact :=
  shortExact_map_tensorLeft hE (V ⊗ A) (injective_tensor_whiskerLeft_of_flat V E.f A
    ((Rep.mono_iff_injective _).1 hAE.mono_f))
theorem shortExact_tensorLeft_tensorLeft (A V : Rep.{u} k G) [Module.Flat k V.V]
    (hAE : (E.map (tensorLeft A)).ShortExact) :
    ((E.map (tensorLeft V)).map (tensorLeft A)).ShortExact :=
  shortExact_map_tensorLeft (shortExact_tensorLeft_of_flat hE V) A
    (injective_whiskerLeft_whiskerLeft_of_flat V E.f A ((Rep.mono_iff_injective _).1 hAE.mono_f))
end Exactness
variable [Fintype G]
def tsgn (k : Type u) [CommRing k] (p : ℤ) : k := ((p.negOnePow : ℤˣ) : ℤ)
abbrev TateCupFam (k G : Type u) [CommRing k] [Group G] [Fintype G] (p q : ℤ) : Type (u + 1) :=
  ∀ (A B : Rep.{u} k G) (r : ℤ), p + q = r →
    tateCohomology A p →ₗ[k] tateCohomology B q →ₗ[k] tateCohomology (A ⊗ B) r
noncomputable def tateLeftIso (A B : Rep.{u} k G) (r : ℤ) :
    tateCohomology (A ⊗ B) r ≅ tateCohomology ((augIdeal k G ⊗ A) ⊗ B) (r + 1) :=
  @asIso _ _ _ _ (tδ (augSES_tensorRight_shortExact A B) r (r + 1) rfl)
    (isIso_tδ_of_tateAcyclic (augSES_tensorRight_shortExact A B)
      (tateAcyclic_augSES_tensorRight_X₂ A B) r (r + 1) rfl)
noncomputable def tateRightIso (A B : Rep.{u} k G) (r : ℤ) :
    tateCohomology (A ⊗ B) r ≅ tateCohomology (A ⊗ (augIdeal k G ⊗ B)) (r + 1) :=
  @asIso _ _ _ _ (tδ (augSES_tensorLeft_shortExact A B) r (r + 1) rfl)
    (isIso_tδ_of_tateAcyclic (augSES_tensorLeft_shortExact A B)
      (tateAcyclic_augSES_tensorLeft_X₂ A B) r (r + 1) rfl)
noncomputable abbrev augShiftδ (A : Rep.{u} k G) (p : ℤ) :
    tateCohomology A p ⟶ tateCohomology (augIdeal k G ⊗ A) (p + 1) :=
  tδ (augSES_shortExact A) p (p + 1) rfl
noncomputable def tateCupL {p q : ℤ} (μ : TateCupFam k G (p + 1) q) : TateCupFam k G p q := fun A B r h =>
  ((μ (augIdeal k G ⊗ A) B (r + 1) (by omega)).comp (augShiftδ A p).hom).compr₂ (tateLeftIso A B r).inv.hom
noncomputable def tateCupR {p q : ℤ} (μ : TateCupFam k G p (q + 1)) : TateCupFam k G p q := fun A B r h =>
  tsgn k p • ((μ A (augIdeal k G ⊗ B) (r + 1) (by omega)).compl₂ (augShiftδ B q).hom).compr₂
    (tateRightIso A B r).inv.hom
noncomputable def tateCupBase (p q : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q) : TateCupFam k G p q := fun A B r h =>
  haveI : NeZero p.toNat := ⟨by omega⟩
  haveI : NeZero q.toNat := ⟨by omega⟩
  haveI : NeZero r.toNat := ⟨by omega⟩
  ((cupH (A := A) (B := B) (show p.toNat + q.toNat = r.toNat by omega)).compl₁₂
    (tateIsoH A p p.toNat (by omega)).hom.hom (tateIsoH B q q.toNat (by omega)).hom.hom).compr₂
    (tateIsoH (A ⊗ B) r r.toNat (by omega)).inv.hom
noncomputable def tateCup (p q : ℤ) : TateCupFam k G p q :=
  if hp : p ≤ 0 then tateCupL (tateCup (p + 1) q)
  else if hq : q ≤ 0 then tateCupR (tateCup p (q + 1))
  else tateCupBase p q (by omega) (by omega)
termination_by (1 - p).toNat + (1 - q).toNat
decreasing_by all_goals omega
noncomputable def tensorShortComplex (E S : ShortComplex (Rep.{u} k G)) :
    ShortComplex (ShortComplex (Rep.{u} k G)) where
  X₁ := S.map (tensorLeft E.X₁)
  X₂ := S.map (tensorLeft E.X₂)
  X₃ := S.map (tensorLeft E.X₃)
  f :=
    { τ₁ := E.f ▷ S.X₁
      τ₂ := E.f ▷ S.X₂
      τ₃ := E.f ▷ S.X₃
      comm₁₂ := (whisker_exchange E.f S.f).symm
      comm₂₃ := (whisker_exchange E.f S.g).symm }
  g :=
    { τ₁ := E.g ▷ S.X₁
      τ₂ := E.g ▷ S.X₂
      τ₃ := E.g ▷ S.X₃
      comm₁₂ := (whisker_exchange E.g S.f).symm
      comm₂₃ := (whisker_exchange E.g S.g).symm }
  zero := by
    ext : 1
    · change E.f ▷ S.X₁ ≫ E.g ▷ S.X₁ = 0
      rw [← comp_whiskerRight, E.zero, MonoidalPreadditive.zero_whiskerRight]
    · change E.f ▷ S.X₂ ≫ E.g ▷ S.X₂ = 0
      rw [← comp_whiskerRight, E.zero, MonoidalPreadditive.zero_whiskerRight]
    · change E.f ▷ S.X₃ ≫ E.g ▷ S.X₃ = 0
      rw [← comp_whiskerRight, E.zero, MonoidalPreadditive.zero_whiskerRight]
instance : (augSES k G).PreservesZeroMorphisms where
  map_zero _ _ := ShortComplex.hom_ext _ _ (MonoidalPreadditive.whiskerLeft_zero)
    (MonoidalPreadditive.whiskerLeft_zero) rfl
instance (B : Rep.{u} k G) : (tensorRight B).mapShortComplex.PreservesZeroMorphisms where
  map_zero _ _ := ShortComplex.hom_ext _ _ (MonoidalPreadditive.zero_whiskerRight)
    (MonoidalPreadditive.zero_whiskerRight) (MonoidalPreadditive.zero_whiskerRight)
instance (A : Rep.{u} k G) : (tensorLeft A).mapShortComplex.PreservesZeroMorphisms where
  map_zero _ _ := ShortComplex.hom_ext _ _ (MonoidalPreadditive.whiskerLeft_zero)
    (MonoidalPreadditive.whiskerLeft_zero) (MonoidalPreadditive.whiskerLeft_zero)
section Anticomm
variable {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact)
end Anticomm
end GroundTheory.GroupCoh


