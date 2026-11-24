-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T18:51:40.662208+00:00
-- url     : https://prove2.me/theorems/55057272-8184-4b93-95ee-5cc028d17302
-- title:
--   Artin Map Second Eq Jacobi Sym
-- statement:
--   Definitions and structural lemmas for Artin Map Second Eq Jacobi Sym, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSym.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_gs_sq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_layer_emb
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_pow_mod_of
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_prim_pow
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_ringChar_ne_two
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_two_dvd
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_z_spec
import Theorems.Thm_Formalism_FrobeniusOrbits_ConjReal_hcl_neg_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_hcl_one
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_aE
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_bE
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_snd_eq_hcl_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_hcl_neg_one
import Theorems.Thm_Formalism_FrobeniusOrbits_hcl_one
import Theorems.Thm_Formalism_FrobeniusOrbits_hostE_isGalois
import Theorems.Thm_Formalism_FrobeniusOrbits_hostFixed
import Theorems.Thm_Formalism_HC_Frame_h_surj
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostAx_galE_bE
import Theorems.Thm_Formalism_HC_HostAx_hostE_isGalois
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_unitsMap_neg_one
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
open NumberField IntermediateField Ideal
noncomputable section
namespace Formalism.HC
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace D7
def sgnN {p N : ℕ} (hp : p.Prime) (h : p ∣ N) : (ZMod N)ˣ →* ℤˣ :=
  haveI := Fact.mk hp
  (quadraticChar (ZMod p)).toUnitHom.comp (ZMod.unitsMap h)
theorem unitsMap_val {M N : ℕ} [NeZero N] (h : M ∣ N) (u : (ZMod N)ˣ) :
    ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M) = (((u : ZMod N).val : ℕ) : ZMod M) := by
  rw [ZMod.unitsMap_def, Units.coe_map]
  show ZMod.castHom h (ZMod M) (u : ZMod N) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
theorem unitsMap_neg_one {M N : ℕ} (h : M ∣ N) : ZMod.unitsMap h (-1) = -1 := by
  apply Units.ext
  rw [ZMod.unitsMap_def, Units.coe_map]
  show ZMod.castHom h (ZMod M) (-1) = -1
  rw [map_neg, map_one]
theorem sgnN_val {p N : ℕ} [NeZero N] (hp : p.Prime) (h : p ∣ N) (u : (ZMod N)ˣ) :
    ((sgnN hp h u : ℤˣ) : ℤ) = jacobiSym (((u : ZMod N).val : ℕ) : ℤ) p := by
  have := Fact.mk hp
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, ← unitsMap_val h u]
  exact MulChar.coe_toUnitHom _ _
theorem gs_act {K : Type*} [Field K] [CharZero K] {p : ℕ} [Fact p.Prime] {x : K} (hx : x ^ p = 1) (σ : K →+* K)
    (v : ℕ) (hσ : σ x = x ^ v) (hv : Nat.Coprime v p) :
    σ (Cond.gs p hx) = ((jacobiSym (v : ℤ) p : ℤ) : K) * Cond.gs p hx := by
  set w : (ZMod p)ˣ := ZMod.unitOfCoprime v hv with hw
  have hwv : (w : ZMod p) = (v : ZMod p) := ZMod.coe_unitOfCoprime v hv
  have hψ : ∀ a : ZMod p, σ (AddChar.zmodChar p hx a) = AddChar.zmodChar p hx ((w : ZMod p) * a) := by
    intro a
    rw [AddChar.zmodChar_apply, map_pow, hσ, ← pow_mul]
    have : (w : ZMod p) * a = (((v * a.val : ℕ)) : ZMod p) := by
      push_cast; rw [hwv, ZMod.natCast_zmod_val]
    rw [this, AddChar.zmodChar_apply']
  have hχ : ∀ a : ZMod p, σ (Cond.chi p K a) = Cond.chi p K a := by
    intro a; simp [Cond.chi, MulChar.ringHomComp_apply]
  have h1 : σ (Cond.gs p hx) = gaussSum (Cond.chi p K) (AddChar.mulShift (AddChar.zmodChar p hx) (w : ZMod p)) := by
    simp only [Cond.gs, gaussSum, map_sum, map_mul, hψ, hχ, AddChar.mulShift_apply]
  have h2 := gaussSum_mulShift (Cond.chi p K) (AddChar.zmodChar p hx) w
  have h3 : Cond.chi p K (w : ZMod p) = ((jacobiSym (v : ℤ) p : ℤ) : K) := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, hwv]
    rfl
  have h4 : jacobiSym (v : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (by simpa using hv)
  have h5 : ((jacobiSym (v : ℤ) p : ℤ) : K) ^ 2 = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) h4
  rw [h3, ← h1] at h2
  have h6 : Cond.gs p hx = ((jacobiSym (v : ℤ) p : ℤ) : K) * σ (Cond.gs p hx) := h2.symm
  linear_combination (-σ (Cond.gs p hx)) * h5 - ((jacobiSym (v : ℤ) p : ℤ) : K) * h6
theorem sqrt_act {p N : ℕ} [NeZero N] (hp : p.Prime) (hp4 : p % 4 = 3) (h : p ∣ N) (u : (ZMod N)ˣ)
    (τ : Cond.Cyc N ≃ₐ[ℚ] Cond.Cyc N) (hτ : ∀ w : Cond.Cyc N, w ^ N = 1 → τ w = w ^ (u : ZMod N).val)
    (y : Cond.Cyc N) (hy : y ^ 2 = -(p : Cond.Cyc N)) :
    τ y = (((sgnN hp h u : ℤˣ) : ℤ) : Cond.Cyc N) * y := by
  have := Fact.mk hp
  have hx := Cond.prim_pow (N := N) h
  have hxN : (Cond.z N ^ (N / p)) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, (Cond.z_spec N).pow_eq_one, one_pow]
  have hg := gs_act hx.pow_eq_one (τ : Cond.Cyc N →+* Cond.Cyc N) _ (hτ _ hxN)
    ((ZMod.val_coe_unit_coprime u).coprime_dvd_right h)
  have hg' : τ (Cond.gs p hx.pow_eq_one) = _ := hg
  rw [sgnN_val]
  have hsq : y ^ 2 = Cond.gs p hx.pow_eq_one ^ 2 := by rw [hy, Cond.gs_sq hp4 hx]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
  · rw [h1, hg']
  · rw [h1, map_neg, hg']; ring
variable (φ : Frame) (hinj : Function.Injective φ.h)
def hIso : φ.MA ≃* HGrp φ.e :=
  MulEquiv.ofBijective φ.hH
    ⟨fun _ _ hab => Multiplicative.toAdd.injective (hinj (Additive.toMul.injective hab)),
     fun y => by
      obtain ⟨t, ht⟩ := φ.h_surj (Additive.ofMul y)
      exact ⟨Multiplicative.ofAdd t, congrArg Additive.toMul ht⟩⟩
def ggIso : FrobeniusOrbits.GG φ.e ≃* φ.GG := MulEquiv.prodCongr (MulEquiv.refl G0) (hIso φ hinj).symm
theorem hH_ggIso (g : FrobeniusOrbits.GG φ.e) : φ.hH (ggIso φ hinj g).2 = g.2 := (hIso φ hinj).apply_symm_apply g.2
theorem ggIso_mk_one (s : G0) : ggIso φ hinj (s, 1) = (s, 1) :=
  Prod.ext rfl (map_one (hIso φ hinj).symm)
theorem ggIso_eq_iff (g : FrobeniusOrbits.GG φ.e) (s : G0) : ggIso φ hinj g = (s, 1) ↔ g = (s, 1) := by
  rw [← ggIso_mk_one φ hinj s]
  exact (ggIso φ hinj).injective.eq_iff
section Art
variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
theorem two_dvd (q d : ℕ) : 2 ^ (e + 2) ∣ 2 ^ (e + 2) * q * d := Dvd.intro _ (mul_assoc _ _ _).symm
theorem q_dvd (q d : ℕ) : q ∣ 2 ^ (e + 2) * q * d := Dvd.dvd.mul_right (dvd_mul_left _ _) _
theorem d_dvd (q d : ℕ) : d ∣ 2 ^ (e + 2) * q * d := dvd_mul_left _ _
include hH in
theorem neZeroN : NeZero (2 ^ (e + 2) * q * d) :=
  ⟨by have := hH.1.pos; have := hH.2.1.pos; positivity⟩
def art0 : (ZMod (2 ^ (e + 2) * q * d))ˣ →* FrobeniusOrbits.GG e :=
  ((sgnN hH.1 (q_dvd e q d)).prod (sgnN hH.2.1 (d_dvd e q d))).prod
    ((QuotientGroup.mk' _).comp (ZMod.unitsMap (two_dvd e q d)))
theorem artinMap_first_eq_jacobiSym (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) :
    (((art0 e hH u).1.1 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (2 ^ (e + 2) * q * d)).val : ℕ) : ℤ) q :=
  haveI := neZeroN e hH
  sgnN_val hH.1 (q_dvd e q d) u
theorem artinMap_dyadic_eq (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) (v : (ZMod (2 ^ (e + 2)))ˣ)
    (hv : (v : ZMod (2 ^ (e + 2))) = (((u : ZMod (2 ^ (e + 2) * q * d)).val : ℕ) : ZMod (2 ^ (e + 2)))) :
    (art0 e hH u).2 = hcl e v := by
  have := neZeroN e hH
  have h1 : v = ZMod.unitsMap (two_dvd e q d) u := Units.ext (by rw [hv, unitsMap_val])
  rw [h1]; rfl
theorem artinMap_first_eq_one (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) (hu : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD q]) :
    (art0 e hH u).1.1 = 1 := by
  apply Units.ext
  rw [artinMap_first_eq_jacobiSym, jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast Int.natCast_modEq_iff.mpr hu), jacobiSym.one_left]
  rfl
theorem artinMap_dyadic_eq_one (u : (ZMod (2 ^ (e + 2) * q * d))ˣ)
    (hu : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD 2 ^ (e + 2)]) : (art0 e hH u).2 = 1 := by
  rw [artinMap_dyadic_eq e hH u 1 (by rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hu]; simp), hcl_one]
theorem sgnN_neg_one {p N : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (h : p ∣ N) : sgnN hp h (-1) = -1 := by
  have := Fact.mk hp
  apply Units.ext
  have h1 : ((ZMod.unitsMap h (-1) : (ZMod p)ˣ) : ZMod p) = -1 := by
    rw [unitsMap_neg_one]; rfl
  have h2 : ((sgnN hp h (-1) : ℤˣ) : ℤ) = quadraticChar (ZMod p) ((ZMod.unitsMap h (-1) : (ZMod p)ˣ) : ZMod p) :=
    MulChar.coe_toUnitHom _ _
  rw [h2, h1, quadraticChar_neg_one (Cond.ringChar_ne_two hp4), ZMod.card, ZMod.χ₄_nat_three_mod_four hp4]
  rfl
theorem artinMap_neg_one : art0 e hH (-1) = cc e := by
  have hq4 : q % 4 = 3 := by have := hH.2.2.1; omega
  have hd4 : d % 4 = 3 := by have := hH.2.2.2.1; omega
  refine Prod.ext (Prod.ext (sgnN_neg_one hH.1 hq4 _) (sgnN_neg_one hH.2.1 hd4 _)) ?_
  have h1 : ZMod.unitsMap (two_dvd e q d) (-1) = -1 := unitsMap_neg_one _
  show hcl e (ZMod.unitsMap (two_dvd e q d) (-1)) = 1
  rw [h1, hcl_neg_one]
variable {e} {L : Type} [Field L] [NumberField L] {ζ a b : L} (h : IsLayer (e + 2) q d ζ a b)
def layerEmb : L →ₐ[ℚ] Cond.Cyc (2 ^ (e + 2) * q * d) :=
  haveI := neZeroN e hH
  haveI := Fact.mk hH.1
  haveI := Fact.mk hH.2.1
  Classical.choice (Cond.layer_emb (by have := hH.2.2.1; omega) (by have := hH.2.2.2.1; omega) h
    (two_dvd e q d) (q_dvd e q d) (d_dvd e q d))
include h in
theorem algEquiv_apply_eq_tau_of_galE_eq_art0 (ι : L →ₐ[ℚ] Cond.Cyc (2 ^ (e + 2) * q * d)) (u : (ZMod (2 ^ (e + 2) * q * d))ˣ)
    (τ : Cond.Cyc (2 ^ (e + 2) * q * d) ≃ₐ[ℚ] Cond.Cyc (2 ^ (e + 2) * q * d))
    (hτ : ∀ w : Cond.Cyc (2 ^ (e + 2) * q * d), w ^ (2 ^ (e + 2) * q * d) = 1 →
      τ w = w ^ (u : ZMod (2 ^ (e + 2) * q * d)).val)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : galE e ζ a b σ = art0 e hH u) (x : hostE ζ a b) :
    ι ((σ x : hostE ζ a b) : L) = τ (ι (x : L)) := by
  have := neZeroN e hH
  have hqd := hH.toHypOdd
  have hq4 : q % 4 = 3 := by have := hH.2.2.1; omega
  have hd4 : d % 4 = 3 := by have := hH.2.2.2.1; omega
  have key : (ι.comp (hostE ζ a b).val).comp (σ : hostE ζ a b →ₐ[ℚ] hostE ζ a b) =
      (τ : _ →ₐ[ℚ] _).comp (ι.comp (hostE ζ a b).val) := by
    refine algHom_ext_of_eq_adjoin ℚ (S := hostE ζ a b) (s := {ζ + ζ⁻¹, a, b})
      (hostFixed e q d hqd L ζ a b h).1 ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | hy | hy
    · show ι ((σ (thE ζ a b) : hostE ζ a b) : L) = τ (ι (ζ + ζ⁻¹))
      set v := ZMod.unitsMap (two_dvd e q d) u with hv
      have h1 := (galE_snd_eq_hcl_iff hqd h σ v).mp (by rw [hσ]; rfl)
      have hz : ζ ^ 2 ^ (e + 2) = 1 := h.1.pow_eq_one
      have hz' : ζ⁻¹ ^ 2 ^ (e + 2) = 1 := by rw [inv_pow, hz, inv_one]
      have hval : (v : ZMod (2 ^ (e + 2))).val = (u : ZMod (2 ^ (e + 2) * q * d)).val % 2 ^ (e + 2) := by
        rw [hv, unitsMap_val, ZMod.val_natCast]
      have hN : ∀ w : L, w ^ 2 ^ (e + 2) = 1 → ι w ^ (2 ^ (e + 2) * q * d) = 1 := by
        intro w hw
        rw [pow_mul, pow_mul, ← map_pow, hw, map_one, one_pow, one_pow]
      rw [h1, hval, Cond.pow_mod_of hz, Cond.pow_mod_of hz', map_add, map_add, map_add, map_pow, map_pow,
        hτ _ (hN _ hz), hτ _ (hN _ hz')]
    · subst hy
      show ι ((σ (aE ζ y b) : hostE ζ y b) : L) = τ (ι y)
      rw [galE_aE hqd h σ, hσ, map_mul, map_intCast,
        sqrt_act hH.1 hq4 (q_dvd e q d) u τ hτ (ι y) (by rw [← map_pow, h.2.1, map_neg, map_natCast])]
      rfl
    · subst hy
      show ι ((σ (bE ζ a y) : hostE ζ a y) : L) = τ (ι y)
      rw [galE_bE hqd h σ, hσ, map_mul, map_intCast,
        sqrt_act hH.2.1 hd4 (d_dvd e q d) u τ hτ (ι y) (by rw [← map_pow, h.2.2.1, map_neg, map_natCast])]
      rfl
  exact DFunLike.congr_fun key x
end Art
theorem coprime_two {q d : ℕ} (hH : HostHyp q d) (k : ℕ) : Nat.Coprime (2 ^ k) (q * d) := by
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_two_left, Nat.odd_mul, Nat.odd_iff, Nat.odd_iff]
  have := hH.2.2.1
  have := hH.2.2.2.1
  omega
variable {q d : ℕ} (hH : HostHyp q d) (he : 2 ≤ φ.e) {L : Type} [Field L] [NumberField L] {ζ a b : L}
  (h : IsLayer (φ.e + 2) q d ζ a b)
def hostRaw : HostRaw φ where
  q := q
  d := d
  QS := 2 ^ (φ.e + 2)
  hyp := hH
  two_le_e := he
  QS_pos := by positivity
  tower_dvd := dvd_rfl
  QS_coprime := coprime_two hH _
  QS_split := fun l hl hl2 hd => absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow hd)) hl2
  E := hostE ζ a b
  galois := hostE_isGalois hH.toHypOdd h
  gal := (galEquiv hH.toHypOdd h).trans (ggIso φ hinj)
  sqd := bE ζ a b
  sqd_sq := by
    apply Subtype.ext
    push_cast
    exact h.2.2.1
  gal_sqd := fun σ => by
    apply Subtype.ext
    push_cast
    exact galE_bE hH.toHypOdd h σ
  cycEmb := (layerEmb hH h).comp (hostE ζ a b).val
  cycZeta := haveI := neZeroN φ.e hH; Cond.z _
  cycZeta_prim := haveI := neZeroN φ.e hH; Cond.z_spec _
  art := (ggIso φ hinj).toMonoidHom.comp (art0 φ.e hH)
  art_spec := fun u τ hτ x => by
    have := neZeroN φ.e hH
    refine algEquiv_apply_eq_tau_of_galE_eq_art0 hH h (layerEmb hH h) u τ (fun w hw => ?_) _ ?_ x
    · obtain ⟨i, -, rfl⟩ := (Cond.z_spec _).eq_pow_of_pow_eq_one hw
      rw [map_pow, hτ, ← pow_mul, ← pow_mul, mul_comm i]
    · apply (ggIso φ hinj).injective
      exact ((galEquiv hH.toHypOdd h).trans (ggIso φ hinj)).apply_symm_apply _
  art_neg_one := by
    show ggIso φ hinj (art0 φ.e hH (-1)) = _
    rw [artinMap_neg_one]
    exact ggIso_mk_one φ hinj c0
  art_h := fun u v hv => (hH_ggIso φ hinj _).trans (artinMap_dyadic_eq φ.e hH u v hv)
  art_d := fun u hu => by
    have h1 := artinMap_first_eq_one φ.e hH u (hu.of_dvd (dvd_mul_left _ _))
    have h2 := artinMap_dyadic_eq_one φ.e hH u (hu.of_dvd (dvd_mul_right _ _))
    rcases Int.units_eq_one_or (art0 φ.e hH u).1.2 with h3 | h3
    · exact Or.inl ((ggIso_eq_iff φ hinj _ 1).mpr (Prod.ext (Prod.ext h1 h3) h2))
    · exact Or.inr ((ggIso_eq_iff φ hinj _ (1, -1)).mpr (Prod.ext (Prod.ext h1 h3) h2))
  art_q := fun u hu => by
    have h2 := artinMap_dyadic_eq_one φ.e hH u (hu.of_dvd (dvd_mul_right _ _))
    show ggIso φ hinj (art0 φ.e hH u) ^ 2 = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
    refine Prod.ext (Prod.ext (Int.units_sq _) (Int.units_sq _)) ?_
    show (art0 φ.e hH u).2 ^ 2 = 1
    rw [h2, one_pow]
end D7
end Formalism.HC
end


