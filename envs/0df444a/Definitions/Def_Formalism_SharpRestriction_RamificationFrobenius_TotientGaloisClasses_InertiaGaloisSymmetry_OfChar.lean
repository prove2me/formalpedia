-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfChar
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfChar
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T19:16:22.988523+00:00
-- url     : https://prove2.me/theorems/5a874da1-6a0d-4be2-866f-53b877df7613
-- title:
--   Of Char
-- statement:
--   Definitions and structural lemmas for Of Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfChar.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_sqrt_exists
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_z_spec
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
namespace Formalism.HC
open Formalism.FrobeniusOrbits
structure CharData (φ : Frame) where
  q : ℕ
  d : ℕ
  QS : ℕ
  hyp : HostHyp q d
  two_le_e : 2 ≤ φ.e
  QS_pos : 0 < QS
  tower_dvd : 2 ^ (φ.e + 2) ∣ QS
  QS_coprime : Nat.Coprime QS (q * d)
  QS_split : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ QS → jacobiSym (-(d : ℤ)) l = 1
  art : (ZMod (QS * q * d))ˣ →* φ.GG
  art_surj : Function.Surjective art
  art_neg_one : art (-1) = φ.cc
  art_h : ∀ (u : (ZMod (QS * q * d))ˣ) (v : (ZMod (2 ^ (φ.e + 2)))ˣ),
    (v : ZMod (2 ^ (φ.e + 2))) = (((u : ZMod (QS * q * d)).val : ℕ) : ZMod (2 ^ (φ.e + 2))) →
    φ.hH (art u).2 = hcl φ.e v
  art_d : ∀ u : (ZMod (QS * q * d))ˣ, (u : ZMod (QS * q * d)).val ≡ 1 [MOD QS * q] → art u = 1 ∨ art u = φ.iod
  art_q : ∀ u : (ZMod (QS * q * d))ˣ, (u : ZMod (QS * q * d)).val ≡ 1 [MOD QS * d] → art u ^ 2 = 1
  art_ch : ∀ u : (ZMod (QS * q * d))ˣ, (((art u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (QS * q * d)).val : ℕ) : ℤ) d
namespace CharData
variable {φ : Frame} (D : CharData φ)
instance neZeroN : NeZero (D.QS * D.q * D.d) :=
  ⟨by have := D.hyp.1.pos; have := D.hyp.2.1.pos; have := D.QS_pos; positivity⟩
abbrev L : Type := Cond.Cyc (D.QS * D.q * D.d)
instance galL : IsGalois ℚ D.L := IsCyclotomicExtension.isGalois {D.QS * D.q * D.d} ℚ D.L
def cyc : (D.L ≃ₐ[ℚ] D.L) ≃* (ZMod (D.QS * D.q * D.d))ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod (D.QS * D.q * D.d) D.L
theorem cyc_apply (τ : D.L ≃ₐ[ℚ] D.L) (w : D.L) (hw : w ^ (D.QS * D.q * D.d) = 1) :
    τ w = w ^ ((D.cyc τ : (ZMod (D.QS * D.q * D.d))ˣ) : ZMod (D.QS * D.q * D.d)).val :=
  IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq _ _ τ hw
theorem cyc_eq (u : (ZMod (D.QS * D.q * D.d))ˣ) (τ : D.L ≃ₐ[ℚ] D.L)
    (hτ : τ (Cond.z _) = Cond.z _ ^ (u : ZMod (D.QS * D.q * D.d)).val) : D.cyc τ = u := by
  have h1 := D.cyc_apply τ (Cond.z _) (Cond.z_spec _).pow_eq_one
  rw [hτ] at h1
  have h2 : (u : ZMod (D.QS * D.q * D.d)).val = (D.cyc τ : ZMod (D.QS * D.q * D.d)).val :=
    (Cond.z_spec _).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h1
  exact Units.ext (ZMod.val_injective _ h2).symm
def res : (D.L ≃ₐ[ℚ] D.L) →* φ.GG := D.art.comp D.cyc.toMonoidHom
theorem res_apply (τ : D.L ≃ₐ[ℚ] D.L) : D.res τ = D.art (D.cyc τ) := rfl
theorem res_surj : Function.Surjective D.res :=
  D.art_surj.comp D.cyc.surjective
def E : IntermediateField ℚ D.L := fixedField D.res.ker
instance galE : IsGalois ℚ D.E := IsGalois.of_fixedField_normal_subgroup D.res.ker
def gal : (D.E ≃ₐ[ℚ] D.E) ≃* φ.GG :=
  (IsGalois.normalAutEquivQuotient D.res.ker).symm.trans (QuotientGroup.quotientKerEquivOfSurjective D.res D.res_surj)
theorem gal_restrict (τ : D.L ≃ₐ[ℚ] D.L) : D.gal (τ.restrictNormal D.E) = D.res τ := by
  have h : (IsGalois.normalAutEquivQuotient D.res.ker).symm (τ.restrictNormal D.E) =
      (τ : (D.L ≃ₐ[ℚ] D.L) ⧸ D.res.ker) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  show QuotientGroup.quotientKerEquivOfSurjective D.res D.res_surj
    ((IsGalois.normalAutEquivQuotient D.res.ker).symm (τ.restrictNormal D.E)) = D.res τ
  rw [h]
  rfl
theorem gal_symm_apply (τ : D.L ≃ₐ[ℚ] D.L) (x : D.E) : ((D.gal.symm (D.res τ) x : D.E) : D.L) = τ x := by
  rw [← D.gal_restrict τ, MulEquiv.symm_apply_apply]
  exact AlgEquiv.restrictNormal_commutes τ D.E x
theorem exists_root {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (hN : p ∣ D.QS * D.q * D.d) (s : φ.GG →* ℤˣ)
    (hs : ∀ u : (ZMod (D.QS * D.q * D.d))ˣ,
      ((s (D.art u) : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (D.QS * D.q * D.d)).val : ℕ) : ℤ) p) :
    ∃ y : D.E, y ^ 2 = -(p : D.E) ∧ ∀ σ : D.E ≃ₐ[ℚ] D.E, σ y = (((s (D.gal σ) : ℤˣ) : ℤ) : D.E) * y := by
  have := Fact.mk hp
  obtain ⟨g, hg⟩ := Cond.sqrt_exists hp4 hN
  have key : ∀ τ : D.L ≃ₐ[ℚ] D.L, τ g = (((s (D.res τ) : ℤˣ) : ℤ) : D.L) * g := fun τ => by
    rw [D7.sqrt_act hp hp4 hN (D.cyc τ) τ (D.cyc_apply τ) g hg, D7.sgnN_val, res_apply, hs]
  have hm : g ∈ D.E := by
    rw [E, mem_fixedField_iff]
    intro τ hτ
    rw [key, MonoidHom.mem_ker.mp hτ]
    simp
  refine ⟨⟨g, hm⟩, ?_, fun σ => ?_⟩
  · apply Subtype.ext
    push_cast
    exact hg
  · obtain ⟨τ, hτ⟩ := D.res_surj (D.gal σ)
    apply Subtype.ext
    have h1 := D.gal_symm_apply τ ⟨g, hm⟩
    rw [hτ, MulEquiv.symm_apply_apply] at h1
    rw [h1, key, hτ]
    push_cast
    rfl
theorem exists_sqd : ∃ y : D.E, y ^ 2 = -(D.d : D.E) ∧
    ∀ σ : D.E ≃ₐ[ℚ] D.E, σ y = ((((D.gal σ).1.2 : ℤˣ) : ℤ) : D.E) * y :=
  D.exists_root D.hyp.2.1 (by have := D.hyp.2.2.2.1; omega) (dvd_mul_left _ _) φ.chD D.art_ch
def toHostRaw : HostRaw φ where
  q := D.q
  d := D.d
  QS := D.QS
  hyp := D.hyp
  two_le_e := D.two_le_e
  QS_pos := D.QS_pos
  tower_dvd := D.tower_dvd
  QS_coprime := D.QS_coprime
  QS_split := D.QS_split
  E := D.E
  galois := D.galE
  gal := D.gal
  sqd := D.exists_sqd.choose
  sqd_sq := D.exists_sqd.choose_spec.1
  gal_sqd := D.exists_sqd.choose_spec.2
  cycEmb := D.E.val
  cycZeta := Cond.z _
  cycZeta_prim := Cond.z_spec _
  art := D.art
  art_spec := fun u τ hτ x => by
    rw [← D.cyc_eq u τ hτ]
    exact D.gal_symm_apply τ x
  art_neg_one := D.art_neg_one
  art_h := D.art_h
  art_d := D.art_d
  art_q := D.art_q
end CharData
end Formalism.HC
end


