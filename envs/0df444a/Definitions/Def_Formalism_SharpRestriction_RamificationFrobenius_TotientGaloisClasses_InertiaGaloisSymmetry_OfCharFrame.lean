-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T20:16:08.622491+00:00
-- url     : https://prove2.me/theorems/48f93663-a7c3-4175-a339-fca6c7d04894
-- title:
--   Of Char Frame
-- statement:
--   Definitions and structural lemmas for Of Char Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfCharFrame.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfChar
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_D7_d4
import Theorems.Thm_Formalism_HC_D7_q4
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_unitsMap_neg_one
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_towerProperties
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
noncomputable section
namespace Formalism.HC
open Formalism.FrobeniusOrbits
theorem unitsMap_eq_iff {M N : ℕ} [NeZero N] [NeZero M] (h : M ∣ N) (u : (ZMod N)ˣ) (v : (ZMod M)ˣ) :
    ZMod.unitsMap h u = v ↔ (u : ZMod N).val ≡ (v : ZMod M).val [MOD M] := by
  rw [Units.ext_iff, D7.unitsMap_val, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
theorem unitsMap_eq_one_iff {M N : ℕ} [NeZero N] (h : M ∣ N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h u = 1 ↔ (u : ZMod N).val ≡ 1 [MOD M] := by
  haveI : NeZero M := ⟨by
    rintro rfl
    exact NeZero.ne N (Nat.eq_zero_of_zero_dvd h)⟩
  rw [unitsMap_eq_iff h u 1, Units.val_one, ZMod.val_one_eq_one_mod]
  exact ⟨fun h1 => h1.trans (Nat.mod_modEq 1 M), fun h1 => h1.trans (Nat.mod_modEq 1 M).symm⟩
theorem exists_unit_three {a b c : ℕ} [NeZero (a * b * c)] (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (x y z : ℕ) (hx : Nat.Coprime x a) (hy : Nat.Coprime y b) (hz : Nat.Coprime z c) :
    ∃ u : (ZMod (a * b * c))ˣ, (u : ZMod (a * b * c)).val ≡ x [MOD a] ∧
      (u : ZMod (a * b * c)).val ≡ y [MOD b] ∧ (u : ZMod (a * b * c)).val ≡ z [MOD c] := by
  obtain ⟨t1, h1a, h1b⟩ := Nat.chineseRemainder hab x y
  obtain ⟨t, h2ab, h2c⟩ := Nat.chineseRemainder (Nat.Coprime.mul hac hbc) t1 z
  have hta : t ≡ x [MOD a] := (h2ab.of_mul_right b).trans h1a
  have htb : t ≡ y [MOD b] := (h2ab.of_mul_left a).trans h1b
  have hca : Nat.Coprime t a := hta.gcd_eq.trans hx
  have hcb : Nat.Coprime t b := htb.gcd_eq.trans hy
  have hcc : Nat.Coprime t c := h2c.gcd_eq.trans hz
  have hcop : Nat.Coprime t (a * b * c) := Nat.Coprime.mul_right (Nat.Coprime.mul_right hca hcb) hcc
  have hm := Nat.mod_modEq t (a * b * c)
  refine ⟨ZMod.unitOfCoprime t hcop, ?_, ?_, ?_⟩ <;> rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  · exact ((hm.of_mul_right c).of_mul_right b).trans hta
  · exact ((hm.of_mul_right c).of_mul_left a).trans htb
  · exact (hm.of_mul_left (a * b)).trans h2c
structure EvenData where
  e : ℕ
  m : ℕ
  m_pos : 0 < m
  tower : 2 ^ (e + 2) ∣ m
  B : Type
  [grp : CommGroup B]
  ξ : (ZMod m)ˣ →* B
  even : ξ (-1) = 1
attribute [instance] EvenData.grp
namespace EvenData
variable (D : EvenData)
instance neZero : NeZero D.m := ⟨D.m_pos.ne'⟩
def cl : (ZMod D.m)ˣ →* HGrp D.e := (QuotientGroup.mk' _).comp (ZMod.unitsMap D.tower)
theorem cl_apply (u : (ZMod D.m)ˣ) : D.cl u = hcl D.e (ZMod.unitsMap D.tower u) := rfl
def eta : (ZMod D.m)ˣ →* HGrp D.e × D.B := D.cl.prod D.ξ
theorem eta_neg_one : D.eta (-1) = 1 := by
  refine Prod.ext ?_ D.even
  show (QuotientGroup.mk' _) (ZMod.unitsMap D.tower (-1)) = 1
  rw [D7.unitsMap_neg_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_zpowers _
abbrev R : Type := D.eta.range
instance : Finite D.R := Finite.of_surjective _ D.eta.rangeRestrict_surjective
instance : Fintype (Additive D.R) := Fintype.ofFinite _
def p1 : D.R →* HGrp D.e := (MonoidHom.fst _ _).comp D.eta.range.subtype
def p2 : D.R →* D.B := (MonoidHom.snd _ _).comp D.eta.range.subtype
theorem eq_one_of {x : D.R} (h1 : D.p1 x = 1) (h2 : D.p2 x = 1) : x = 1 := by
  apply Subtype.ext
  exact Prod.ext h1 h2
theorem projection_surjective : Function.Surjective D.p1 := by
  intro h
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ h
  obtain ⟨u, rfl⟩ := ZMod.unitsMap_surjective D.tower w
  exact ⟨⟨D.eta u, u, rfl⟩, rfl⟩
theorem exists_gen : ∃ a : D.R, ∀ x : D.R, D.p2 x = 1 ↔ x ∈ Subgroup.zpowers a := by
  haveI : IsCyclic (HGrp D.e) := (Formalism.TwoAdicCyclotomicDecomposition.towerProperties.1.2.1 D.e).1
  let f : D.p2.ker →* HGrp D.e := D.p1.comp D.p2.ker.subtype
  have hf : Function.Injective f := (injective_iff_map_eq_one f).mpr fun x hx =>
    Subtype.ext (D.eq_one_of hx (MonoidHom.mem_ker.mp x.2))
  haveI : IsCyclic D.p2.ker := isCyclic_of_surjective (MonoidHom.ofInjective hf).symm (MulEquiv.surjective _)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D.p2.ker)
  refine ⟨g, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, MonoidHom.mem_ker.mpr hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact MonoidHom.mem_ker.mp (D.p2.ker.zpow_mem g.2 k)
def gen : D.R := D.exists_gen.choose
theorem gen_spec (x : D.R) : D.p2 x = 1 ↔ x ∈ Subgroup.zpowers D.gen := D.exists_gen.choose_spec x
def hA : Additive D.R →+ Additive (HGrp D.e) := MonoidHom.toAdditive D.p1
theorem hA_surj : Function.Surjective D.hA := by
  intro y
  obtain ⟨x, hx⟩ := D.projection_surjective (Additive.toMul y)
  exact ⟨Additive.ofMul x, hx⟩
theorem hA_ker (k : ℤ) (hk : D.hA (k • Additive.ofMul D.gen) = 0) : k • Additive.ofMul D.gen = 0 := by
  have h2 : D.p2 D.gen = 1 := (D.gen_spec D.gen).mpr (Subgroup.mem_zpowers _)
  have hk' : D.p1 (D.gen ^ k) = 1 := hk
  have h3 := D.eq_one_of hk' (by rw [map_zpow, h2, one_zpow])
  show Additive.ofMul (D.gen ^ k) = 0
  rw [h3]
  rfl
def frame : Frame := Frame.ofGroup D.e D.hA D.hA_surj (Additive.ofMul D.gen) D.hA_ker
def isoA : D.frame.A ≃+ Additive D.R := Frame.ofGroupIso D.e D.hA D.hA_surj (Additive.ofMul D.gen) D.hA_ker
def iso : D.frame.MA ≃* D.R where
  toFun a := (D.isoA a.toAdd).toMul
  invFun x := Multiplicative.ofAdd (D.isoA.symm (Additive.ofMul x))
  left_inv a := by simp
  right_inv x := by simp
  map_mul' a b := by simp
theorem hH_eq (a : D.frame.MA) : D.frame.hH a = D.p1 (D.iso a) := rfl
def toA : (ZMod D.m)ˣ →* D.frame.MA := D.iso.symm.toMonoidHom.comp D.eta.rangeRestrict
theorem iso_toA (u : (ZMod D.m)ˣ) : D.iso (D.toA u) = D.eta.rangeRestrict u :=
  D.iso.apply_symm_apply _
theorem toA_surj : Function.Surjective D.toA :=
  D.iso.symm.surjective.comp D.eta.rangeRestrict_surjective
theorem toA_eq_one_iff (u : (ZMod D.m)ˣ) : D.toA u = 1 ↔ D.eta u = 1 := by
  rw [← D.iso.map_eq_one_iff, iso_toA, Subtype.ext_iff, MonoidHom.coe_rangeRestrict, OneMemClass.coe_one]
theorem hH_toA (u : (ZMod D.m)ˣ) : D.frame.hH (D.toA u) = D.cl u := by
  rw [hH_eq, iso_toA]
  rfl
def xiA : D.frame.MA →* D.B := D.p2.comp D.iso.toMonoidHom
section Host
variable {q d : ℕ} (hH : HostHyp q d)
theorem m_dvd (q d : ℕ) : D.m ∣ D.m * q * d := ⟨q * d, by ring⟩
theorem q_dvd (q d : ℕ) : q ∣ D.m * q * d := ⟨D.m * d, by ring⟩
theorem d_dvd (q d : ℕ) : d ∣ D.m * q * d := ⟨D.m * q, by ring⟩
include hH in
theorem neZeroN : NeZero (D.m * q * d) :=
  ⟨Nat.mul_ne_zero (Nat.mul_ne_zero D.m_pos.ne' hH.1.ne_zero) hH.2.1.ne_zero⟩
def art : (ZMod (D.m * q * d))ˣ →* D.frame.GG :=
  ((D7.sgnN hH.1 (D.q_dvd q d)).prod (D7.sgnN hH.2.1 (D.d_dvd q d))).prod (D.toA.comp (ZMod.unitsMap (D.m_dvd q d)))
theorem art_snd (u : (ZMod (D.m * q * d))ˣ) : (D.art hH u).2 = D.toA (ZMod.unitsMap (D.m_dvd q d) u) := rfl
theorem art_ps (u : (ZMod (D.m * q * d))ˣ) :
    (((D.art hH u).1.1 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) q := by
  haveI := D.neZeroN hH
  haveI := Fact.mk hH.1
  show ((D7.sgnN hH.1 (D.q_dvd q d) u : ℤˣ) : ℤ) = _
  simp only [D7.sgnN, MonoidHom.coe_comp, Function.comp_apply, MulChar.coe_toUnitHom, D7.unitsMap_val]
  rw [← jacobiSym.legendreSym.to_jacobiSym q (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ)]
  simp [legendreSym]
theorem art_ch (u : (ZMod (D.m * q * d))ˣ) :
    (((D.art hH u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) d := by
  haveI := D.neZeroN hH
  haveI := Fact.mk hH.2.1
  show ((D7.sgnN hH.2.1 (D.d_dvd q d) u : ℤˣ) : ℤ) = _
  simp only [D7.sgnN, MonoidHom.coe_comp, Function.comp_apply, MulChar.coe_toUnitHom, D7.unitsMap_val]
  rw [← jacobiSym.legendreSym.to_jacobiSym d (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ)]
  simp [legendreSym]
theorem art_ps_one (u : (ZMod (D.m * q * d))ˣ) {y : ℕ} (hu : (u : ZMod (D.m * q * d)).val ≡ y [MOD q])
    (hy : jacobiSym (y : ℤ) q = 1) : (D.art hH u).1.1 = 1 := by
  have h1 := D.art_ps hH u
  have h2 : jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) q = jacobiSym (y : ℤ) q := by
    rw [jacobiSym.mod_left, jacobiSym.mod_left (y : ℤ)]
    congr 1
    exact_mod_cast (hu : _ % q = _ % q)
  rw [h2, hy] at h1
  exact Units.ext h1
theorem art_snd_one (u : (ZMod (D.m * q * d))ˣ) (hu : (u : ZMod (D.m * q * d)).val ≡ 1 [MOD D.m]) : (D.art hH u).2 = 1 := by
  haveI := D.neZeroN hH
  rw [art_snd, (unitsMap_eq_one_iff _ u).mpr hu, map_one]
variable (hc : Nat.Coprime D.m (q * d))
include hc in
theorem art_surj : Function.Surjective (D.art hH) := by
  have hsgn : ∀ {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (s : ℤˣ),
      ∃ y : ℕ, Nat.Coprime y p ∧ jacobiSym (y : ℤ) p = (s : ℤ) := by
    intro p hp hp4 s
    rcases Int.units_eq_one_or s with rfl | rfl
    · exact ⟨1, Nat.coprime_one_left p, by simp⟩
    · have h2 := hp.two_le
      refine ⟨p - 1, ?_, ?_⟩
      · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      · have hodd : Odd p := hp.odd_of_ne_two (by omega)
        have e : ((p - 1 : ℕ) : ℤ) % (p : ℤ) = (-1 : ℤ) % (p : ℤ) := by
          rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
          push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
          simp
        rw [jacobiSym.mod_left, e, ← jacobiSym.mod_left, jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_three_mod_four hp4]
        simp
  haveI := D.neZeroN hH
  rintro ⟨⟨s1, s2⟩, a⟩
  obtain ⟨w, rfl⟩ := D.toA_surj a
  obtain ⟨y, hy, hys⟩ := hsgn hH.1 (D7.q4 hH) s1
  obtain ⟨z, hz, hzs⟩ := hsgn hH.2.1 (D7.d4 hH) s2
  have hqd : Nat.Coprime q d := (Nat.coprime_primes hH.1 hH.2.1).mpr (by
    intro h
    have h1 := hH.2.2.1
    have h2 := hH.2.2.2.1
    subst h
    omega)
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_unit_three (a := D.m) (b := q) (c := d)
    (Nat.Coprime.coprime_dvd_right (dvd_mul_right q d) hc) (Nat.Coprime.coprime_dvd_right (dvd_mul_left d q) hc) hqd
    _ y z (ZMod.val_coe_unit_coprime w) hy hz
  refine ⟨u, Prod.ext (Prod.ext ?_ ?_) ?_⟩
  · show (D.art hH u).1.1 = s1
    apply Units.ext
    rw [D.art_ps hH u, jacobiSym.mod_left, ← hys, jacobiSym.mod_left (y : ℤ)]
    congr 1
    exact_mod_cast (hu2 : _ % q = _ % q)
  · show (D.art hH u).1.2 = s2
    apply Units.ext
    rw [D.art_ch hH u, jacobiSym.mod_left, ← hzs, jacobiSym.mod_left (z : ℤ)]
    congr 1
    exact_mod_cast (hu3 : _ % d = _ % d)
  · show D.toA (ZMod.unitsMap (D.m_dvd q d) u) = D.toA w
    rw [(unitsMap_eq_iff _ u w).mpr hu1]
variable (he : 2 ≤ D.e) (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ D.m → jacobiSym (-(d : ℤ)) l = 1)
def charData : CharData D.frame where
  q := q
  d := d
  QS := D.m
  hyp := hH
  two_le_e := he
  QS_pos := D.m_pos
  tower_dvd := D.tower
  QS_coprime := hc
  QS_split := hs
  art := D.art hH
  art_surj := D.art_surj hH hc
  art_neg_one := by
    refine Prod.ext (Prod.ext (D7.sgnN_neg_one hH.1 (D7.q4 hH) _) (D7.sgnN_neg_one hH.2.1 (D7.d4 hH) _)) ?_
    rw [art_snd, D7.unitsMap_neg_one]
    exact (D.toA_eq_one_iff _).mpr D.eta_neg_one
  art_h := fun u v hv => by
    have := D.neZeroN hH
    rw [art_snd, hH_toA, cl_apply, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
    exact congrArg (hcl D.e) (Units.ext ((D7.unitsMap_val _ u).trans hv.symm))
  art_d := fun u hu => by
    have h1 := D.art_ps_one hH u (hu.of_dvd (dvd_mul_left _ _)) (by simp)
    have h2 := D.art_snd_one hH u (hu.of_dvd (dvd_mul_right _ _))
    rcases Int.units_eq_one_or (D.art hH u).1.2 with h3 | h3
    · exact Or.inl (Prod.ext (Prod.ext h1 h3) h2)
    · exact Or.inr (Prod.ext (Prod.ext h1 h3) h2)
  art_q := fun u hu => by
    have h2 := D.art_snd_one hH u (hu.of_dvd (dvd_mul_right _ _))
    refine Prod.ext (Prod.ext (Int.units_sq _) (Int.units_sq _)) ?_
    show (D.art hH u).2 ^ 2 = 1
    rw [h2, one_pow]
  art_ch := D.art_ch hH
def host : HostRaw D.frame := (D.charData hH hc he hs).toHostRaw
end Host
end EvenData
end Formalism.HC
end


