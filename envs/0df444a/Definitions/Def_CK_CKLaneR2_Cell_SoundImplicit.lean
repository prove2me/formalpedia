-- Prove2me | Definitions.Def_CK_CKLaneR2_Cell_SoundImplicit
-- name    : CK_CKLaneR2_Cell_SoundImplicit
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T06:17:46.470036+00:00
-- url     : https://prove2.me/theorems/5d0e6cba-ee82-4a03-8777-e891b6082749
-- title:
--   Courtade–Kumar proof module `CKLaneR2.Cell.SoundImplicit` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.Cell.SoundImplicit` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.Cell.SoundImplicit` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.Cell.SoundImplicit (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/Cell/SoundImplicit.lean)

import Definitions.Def_CK_CKLaneR2_Cell_SoundBasic

-- ===== source module CKLaneR2.Cell.SoundImplicit =====
section

/-!
# Lane C, RA-stat interior: soundness of the cell checker, part 2 (implicit quantities)

For a two-sided residual certificate `(V, ρ)` this module derives enclosures of the implicit quantities:
* the contact coordinate `dC z = 1 - 2 radialContact z 1` (with `dC 0 = 0`);
* the entropy coordinate `dE E = 1 - 2 entropyInverse E`.

The enclosures cover `δ` itself and its logs `log(δ+1)`, `log(1-δ)`.
-/

namespace CKLaneR2.Cell

open CKLaneR2.TM3 GeneralCK

/-- Contact coordinate, with the `z = 0` convention `dC 0 = 0`. -/
noncomputable def dC (z : ℝ) : ℝ := if z = 0 then 0 else 1 - 2 * radialContact z 1

/-- Entropy coordinate. -/
noncomputable def dE (E : ℝ) : ℝ := 1 - 2 * entropyInverse E

theorem dC_bounds {z : ℝ} (hz : 0 ≤ z) : 0 ≤ dC z ∧ dC z < 1 := by
  unfold dC; split_ifs with h
  · exact ⟨le_refl 0, by norm_num⟩
  · have hz' : 0 < z := lt_of_le_of_ne hz (Ne.symm h)
    have h1 := radialContact_pos hz' (by norm_num : (0 : ℝ) < 1)
    have h2 := radialContact_lt_half hz' (by norm_num : (0 : ℝ) < 1)
    constructor <;> linarith

theorem dE_bounds {E : ℝ} (h0 : 0 < E) (h1 : E ≤ 1) : 0 ≤ dE E ∧ dE E < 1 := by
  unfold dE
  obtain ⟨_, hm1, _⟩ := entropyInverse_spec h0.le h1
  have hm0 := entropyInverse_pos h0 h1
  constructor <;> linarith

theorem hdelta_nonneg {δ : ℝ} (h1 : -1 ≤ δ) (h2 : δ ≤ 1) : 0 ≤ CKLaneR2.RSEnc.hdelta δ := by
  unfold CKLaneR2.RSEnc.hdelta
  exact H_nonneg (by linarith) (by linarith)

theorem hdelta_neg (δ : ℝ) : CKLaneR2.RSEnc.hdelta (-δ) = CKLaneR2.RSEnc.hdelta δ := by
  unfold CKLaneR2.RSEnc.hdelta H
  have : (1 - -δ) / 2 = 1 - (1 - δ) / 2 := by ring
  rw [this, Real.binEntropy_one_sub]

theorem hdelta_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    CKLaneR2.RSEnc.hdelta b ≤ CKLaneR2.RSEnc.hdelta a := by
  unfold CKLaneR2.RSEnc.hdelta
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · exact (H_strictMonoOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)).le

/-- The certificate polynomial as an exact TM. -/
theorem C_poly (V : Poly) : Contains one ⟨V, 0, true⟩ (fun x y z => evalP 0 V x y z / one) := by
  intro _ x y z _ _ _; simp

section Implicit
variable {Z : TM} {zf : ℝ → ℝ → ℝ → ℝ} (V : Poly) (rho : ℕ)

/-- Shared part: containments of the `Vm/Vp` logs and `h`. -/
theorem implicit_common :
    let vmf := fun x y z => evalP 0 V x y z / one + ((-(rho : Int) : Int) : ℝ) / one
    let vpf := fun x y z => evalP 0 V x y z / one + (((rho : Int) : Int) : ℝ) / one
    Contains one (TM.addc ⟨V, 0, true⟩ (-(rho : Int))) vmf ∧
    Contains one (TM.addc ⟨V, 0, true⟩ (rho : Int)) vpf ∧
    Contains one (log (TM.addc (TM.addc ⟨V, 0, true⟩ (-(rho : Int))) ONEi)) (fun x y z => Real.log (vmf x y z + 1)) ∧
    Contains one (log (TM.addc (TM.neg (TM.addc ⟨V, 0, true⟩ (-(rho : Int)))) ONEi))
      (fun x y z => Real.log (1 - vmf x y z)) ∧
    Contains one (log (TM.addc (TM.addc ⟨V, 0, true⟩ (rho : Int)) ONEi)) (fun x y z => Real.log (vpf x y z + 1)) ∧
    Contains one (log (TM.addc (TM.neg (TM.addc ⟨V, 0, true⟩ (rho : Int))) ONEi))
      (fun x y z => Real.log (1 - vpf x y z)) := by
  intro vmf vpf
  have hVm : Contains one (TM.addc ⟨V, 0, true⟩ (-(rho : Int))) vmf := Contains.addc (C_poly V) _
  have hVp : Contains one (TM.addc ⟨V, 0, true⟩ (rho : Int)) vpf := Contains.addc (C_poly V) _
  exact ⟨hVm, hVp, C_log (C_addOne hVm), C_log (C_oneSub hVm), C_log (C_addOne hVp), C_log (C_oneSub hVp)⟩

theorem vm_le_vp (x y z : ℝ) :
    evalP 0 V x y z / one + ((-(rho : Int) : Int) : ℝ) / one ≤ evalP 0 V x y z / one + (((rho : Int) : Int) : ℝ) / one := by
  have : (0 : ℝ) ≤ (rho : ℝ) := Nat.cast_nonneg _
  have h1 : ((-(rho : Int) : Int) : ℝ) / one ≤ (((rho : Int) : Int) : ℝ) / one := by
    apply div_le_div_of_nonneg_right _ hone'.le; push_cast; linarith
  linarith

/-- Pinching step shared by contact and entropy. -/
theorem implicit_finish {Ok : Bool} {δf : ℝ → ℝ → ℝ → ℝ}
    (hpin : Ok = true → ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 →
      evalP 0 V x y z / one + ((-(rho : Int) : Int) : ℝ) / one ≤ δf x y z ∧
      δf x y z ≤ evalP 0 V x y z / one + (((rho : Int) : Int) : ℝ) / one ∧
      -1 < evalP 0 V x y z / one + ((-(rho : Int) : Int) : ℝ) / one ∧
      evalP 0 V x y z / one + (((rho : Int) : Int) : ℝ) / one < 1) :
    let vmT := TM.addc ⟨V, 0, true⟩ (-(rho : Int))
    let vpT := TM.addc ⟨V, 0, true⟩ (rho : Int)
    let lp := TM.average (log (TM.addc vmT ONEi)) (log (TM.addc vpT ONEi))
    let lm := TM.average (log (TM.addc (TM.neg vpT) ONEi)) (log (TM.addc (TM.neg vmT) ONEi))
    Contains one ⟨V, rho, Ok⟩ δf ∧
    Contains one ⟨lp.p, lp.r, lp.ok && Ok⟩ (fun x y z => Real.log (δf x y z + 1)) ∧
    Contains one ⟨lm.p, lm.r, lm.ok && Ok⟩ (fun x y z => Real.log (1 - δf x y z)) := by
  intro vmT vpT lp lm
  obtain ⟨_, _, hlpm, hlmm, hlpp, hlmp⟩ := implicit_common V rho
  refine ⟨?_, ?_, ?_⟩
  · intro hok x y z hx hy hz
    obtain ⟨h1, h2, _, _⟩ := hpin hok x y z hx hy hz
    simp only
    rw [abs_le]; push_cast at h1 h2 ⊢
    constructor
    · have : evalP 0 V x y z / one + -(rho : ℝ) / one ≤ δf x y z := h1
      rw [neg_div] at this; linarith
    · linarith
  · intro hok x y z hx hy hz
    simp only [Bool.and_eq_true] at hok
    have hav := Contains.average hone hlpm hlpp (v := fun x y z => Real.log (δf x y z + 1)) (fun x y z hx hy hz => by
      obtain ⟨h1, h2, h3, h4⟩ := hpin hok.2 x y z hx hy hz
      left
      exact ⟨Real.log_le_log (by linarith) (by linarith), Real.log_le_log (by linarith) (by linarith)⟩)
    exact hav hok.1 x y z hx hy hz
  · intro hok x y z hx hy hz
    simp only [Bool.and_eq_true] at hok
    have hav := Contains.average hone hlmp hlmm (v := fun x y z => Real.log (1 - δf x y z)) (fun x y z hx hy hz => by
      obtain ⟨h1, h2, h3, h4⟩ := hpin hok.2 x y z hx hy hz
      left
      exact ⟨Real.log_le_log (by linarith) (by linarith), Real.log_le_log (by linarith) (by linarith)⟩)
    exact hav hok.1 x y z hx hy hz

end Implicit

/-- Raw log-form of `h(δ)` (equal to `hdelta δ` for `-1 < δ < 1`). -/
noncomputable def hraw (δ : ℝ) : ℝ :=
  1 - ((δ + 1) * Real.log (δ + 1) + (1 - δ) * Real.log (1 - δ)) * (1 / Real.log 2) / 2

theorem hraw_eq {δ : ℝ} (h1 : -1 < δ) (h2 : δ < 1) : hraw δ = CKLaneR2.RSEnc.hdelta δ := by
  rw [hdelta_eq h1 h2]; rfl

theorem C_hOfLogs_raw {D lp lm : TM} {df : ℝ → ℝ → ℝ → ℝ} (hD : Contains one D df)
    (hlp : Contains one lp (fun x y z => Real.log (df x y z + 1)))
    (hlm : Contains one lm (fun x y z => Real.log (1 - df x y z))) :
    Contains one (hOfLogs D lp lm) (fun x y z => hraw (df x y z)) := by
  have hs := Contains.add (C_mul (C_addOne hD) hlp) (C_mul (C_oneSub hD) hlm)
  exact C_oneSub (C_half (C_mul hs invLc_contains))

/-- Contact implicit quantity: soundness of `checkImplicit true`. -/
theorem checkImplicit_contact {Z : TM} {zf : ℝ → ℝ → ℝ → ℝ} (hZ : Contains one Z zf)
    (hz0 : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 ≤ zf x y z) (V : Poly) (rho : ℕ) :
    Contains one (checkImplicit true Z V rho).D (fun x y z => dC (zf x y z)) ∧
    Contains one (checkImplicit true Z V rho).lp (fun x y z => Real.log (dC (zf x y z) + 1)) ∧
    Contains one (checkImplicit true Z V rho).lm (fun x y z => Real.log (1 - dC (zf x y z))) := by
  obtain ⟨hVm, hVp, hlpm, hlmm, hlpp, hlmp⟩ := implicit_common V rho
  set Vm := TM.addc ⟨V, 0, true⟩ (-(rho : Int)) with hVmdef
  set Vp := TM.addc ⟨V, 0, true⟩ (rho : Int) with hVpdef
  set vmf := fun x y z => evalP 0 V x y z / one + ((-(rho : Int) : Int) : ℝ) / one with hvmf
  set vpf := fun x y z => evalP 0 V x y z / one + (((rho : Int) : Int) : ℝ) / one with hvpf
  set hm := hOfLogs Vm (log (TM.addc Vm ONEi)) (log (TM.addc (TM.neg Vm) ONEi)) with hhmdef
  set hp := hOfLogs Vp (log (TM.addc Vp ONEi)) (log (TM.addc (TM.neg Vp) ONEi)) with hhpdef
  have hhm : Contains one hm (fun x y z => hraw (vmf x y z)) := C_hOfLogs_raw hVm hlpm hlmm
  have hhp : Contains one hp (fun x y z => hraw (vpf x y z)) := C_hOfLogs_raw hVp hlpp hlmp
  have hRm := Contains.sub (C_mul hZ hhm) hVm
  have hRp := Contains.sub (C_mul hZ hhp) hVp
  have hpin : (checkImplicit true Z V rho).D.ok = true → ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 →
      vmf x y z ≤ dC (zf x y z) ∧ dC (zf x y z) ≤ vpf x y z ∧ -1 < vmf x y z ∧ vpf x y z < 1 := by
    intro hok x y z hx hy hz
    have hok' : (Z.ok && (TM.sub (mul Z hm) Vm).ok && (TM.sub (mul Z hp) Vp).ok
        && decide (Vp.upper < ONEi) && decide (-ONEi < Vm.lower)
        && decide (0 < (TM.sub (mul Z hm) Vm).lower) && decide ((TM.sub (mul Z hp) Vp).upper < 0)) = true := hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok'
    obtain ⟨⟨⟨⟨⟨⟨_, hRmok⟩, hRpok⟩, hup⟩, hlo⟩, hRm0⟩, hRp0⟩ := hok'
    have hvp1 : vpf x y z < 1 := by
      have h1 := Contains.le_upper hone hVp rfl x y z hx hy hz
      have h2 : (Vp.upper : ℝ) / one < 1 := by
        rw [div_lt_one hone']
        have : (Vp.upper : ℝ) < ((ONEi : ℤ) : ℝ) := by exact_mod_cast hup
        unfold ONEi at this; rwa [Int.cast_natCast] at this
      linarith
    have hvm1 : -1 < vmf x y z := by
      have h1 := Contains.lower_le hone hVm rfl x y z hx hy hz
      have h2 : -1 < (Vm.lower : ℝ) / one := by
        rw [lt_div_iff₀ hone']
        have : ((-ONEi : ℤ) : ℝ) < (Vm.lower : ℝ) := by exact_mod_cast hlo
        unfold ONEi at this; rw [Int.cast_neg, Int.cast_natCast] at this; linarith
      linarith
    have hmp : vmf x y z ≤ vpf x y z := vm_le_vp V rho x y z
    have hr1 : zf x y z * CKLaneR2.RSEnc.hdelta (vmf x y z) - vmf x y z > 0 := by
      have h1 := Contains.lower_le hone hRm hRmok x y z hx hy hz
      have h2 : (0 : ℝ) < ((TM.sub (mul Z hm) Vm).lower : ℝ) / one := div_pos (by exact_mod_cast hRm0) hone'
      rw [← hraw_eq hvm1 (lt_of_le_of_lt hmp hvp1)]
      try simp only at h1
      linarith
    have hr2 : zf x y z * CKLaneR2.RSEnc.hdelta (vpf x y z) - vpf x y z < 0 := by
      have h1 := Contains.le_upper hone hRp hRpok x y z hx hy hz
      have h2 : ((TM.sub (mul Z hp) Vp).upper : ℝ) / one < 0 := div_neg_of_neg_of_pos (by exact_mod_cast hRp0) hone'
      rw [← hraw_eq (lt_of_lt_of_le hvm1 hmp) hvp1]
      try simp only at h1
      linarith
    have hzx := hz0 x y z hx hy hz
    refine ⟨?_, ?_, hvm1, hvp1⟩
    · -- lower
      unfold dC; split_ifs with hz
      · rw [hz] at hr1; linarith
      · have hzp : 0 < zf x y z := lt_of_le_of_ne hzx (Ne.symm hz)
        rcases lt_or_ge (vmf x y z) 0 with hneg | hnn
        · have h1 := radialContact_lt_half hzp (by norm_num : (0 : ℝ) < 1)
          linarith
        · exact CKLaneR2.RSEnc.contact_delta_le hzp hnn (by linarith) hr1.le
    · -- upper
      unfold dC; split_ifs with hz
      · rw [hz] at hr2; linarith
      · have hzp : 0 < zf x y z := lt_of_le_of_ne hzx (Ne.symm hz)
        have hvp0 : 0 ≤ vpf x y z := by
          by_contra hneg; push_neg at hneg
          have hh := hdelta_nonneg (δ := vpf x y z) (by linarith) (by linarith)
          nlinarith
        exact CKLaneR2.RSEnc.contact_delta_ge hzp hvp0 hvp1.le hr2.le
  have key := implicit_finish V rho hpin
  exact ⟨key.1, key.2.1, key.2.2⟩

/-- Entropy implicit quantity: soundness of `checkImplicit false`. -/
theorem checkImplicit_entropy {Z : TM} {ef : ℝ → ℝ → ℝ → ℝ} (hZ : Contains one Z ef)
    (he : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 < ef x y z ∧ ef x y z ≤ 1) (V : Poly) (rho : ℕ) :
    Contains one (checkImplicit false Z V rho).D (fun x y z => dE (ef x y z)) ∧
    Contains one (checkImplicit false Z V rho).lp (fun x y z => Real.log (dE (ef x y z) + 1)) ∧
    Contains one (checkImplicit false Z V rho).lm (fun x y z => Real.log (1 - dE (ef x y z))) := by
  obtain ⟨hVm, hVp, hlpm, hlmm, hlpp, hlmp⟩ := implicit_common V rho
  set Vm := TM.addc ⟨V, 0, true⟩ (-(rho : Int)) with hVmdef
  set Vp := TM.addc ⟨V, 0, true⟩ (rho : Int) with hVpdef
  set vmf := fun x y z => evalP 0 V x y z / one + ((-(rho : Int) : Int) : ℝ) / one with hvmf
  set vpf := fun x y z => evalP 0 V x y z / one + (((rho : Int) : Int) : ℝ) / one with hvpf
  set hm := hOfLogs Vm (log (TM.addc Vm ONEi)) (log (TM.addc (TM.neg Vm) ONEi)) with hhmdef
  set hp := hOfLogs Vp (log (TM.addc Vp ONEi)) (log (TM.addc (TM.neg Vp) ONEi)) with hhpdef
  have hhm : Contains one hm (fun x y z => hraw (vmf x y z)) := C_hOfLogs_raw hVm hlpm hlmm
  have hhp : Contains one hp (fun x y z => hraw (vpf x y z)) := C_hOfLogs_raw hVp hlpp hlmp
  have hRm := Contains.sub hhm hZ
  have hRp := Contains.sub hhp hZ
  have hpin : (checkImplicit false Z V rho).D.ok = true → ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 →
      vmf x y z ≤ dE (ef x y z) ∧ dE (ef x y z) ≤ vpf x y z ∧ -1 < vmf x y z ∧ vpf x y z < 1 := by
    intro hok x y z hx hy hz
    have hok' : (Z.ok && (TM.sub hm Z).ok && (TM.sub hp Z).ok
        && decide (Vp.upper < ONEi) && decide (-ONEi < Vm.lower)
        && decide (0 < (TM.sub hm Z).lower) && decide ((TM.sub hp Z).upper < 0)) = true := hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok'
    obtain ⟨⟨⟨⟨⟨⟨_, hRmok⟩, hRpok⟩, hup⟩, hlo⟩, hRm0⟩, hRp0⟩ := hok'
    have hvp1 : vpf x y z < 1 := by
      have h1 := Contains.le_upper hone hVp rfl x y z hx hy hz
      have h2 : (Vp.upper : ℝ) / one < 1 := by
        rw [div_lt_one hone']
        have : (Vp.upper : ℝ) < ((ONEi : ℤ) : ℝ) := by exact_mod_cast hup
        unfold ONEi at this; rwa [Int.cast_natCast] at this
      linarith
    have hvm1 : -1 < vmf x y z := by
      have h1 := Contains.lower_le hone hVm rfl x y z hx hy hz
      have h2 : -1 < (Vm.lower : ℝ) / one := by
        rw [lt_div_iff₀ hone']
        have : ((-ONEi : ℤ) : ℝ) < (Vm.lower : ℝ) := by exact_mod_cast hlo
        unfold ONEi at this; rw [Int.cast_neg, Int.cast_natCast] at this; linarith
      linarith
    have hmp : vmf x y z ≤ vpf x y z := vm_le_vp V rho x y z
    have hr1 : CKLaneR2.RSEnc.hdelta (vmf x y z) - ef x y z > 0 := by
      have h1 := Contains.lower_le hone hRm hRmok x y z hx hy hz
      have h2 : (0 : ℝ) < ((TM.sub hm Z).lower : ℝ) / one := div_pos (by exact_mod_cast hRm0) hone'
      rw [← hraw_eq hvm1 (lt_of_le_of_lt hmp hvp1)]
      try simp only at h1
      linarith
    have hr2 : CKLaneR2.RSEnc.hdelta (vpf x y z) - ef x y z < 0 := by
      have h1 := Contains.le_upper hone hRp hRpok x y z hx hy hz
      have h2 : ((TM.sub hp Z).upper : ℝ) / one < 0 := div_neg_of_neg_of_pos (by exact_mod_cast hRp0) hone'
      rw [← hraw_eq (lt_of_lt_of_le hvm1 hmp) hvp1]
      try simp only at h1
      linarith
    obtain ⟨he0, he1⟩ := he x y z hx hy hz
    obtain ⟨hd0, hd1⟩ := dE_bounds he0 he1
    refine ⟨?_, ?_, hvm1, hvp1⟩
    · rcases lt_or_ge (vmf x y z) 0 with hneg | hnn
      · linarith
      · exact CKLaneR2.RSEnc.entropy_delta_le he0.le hnn (by linarith) hr1.le
    · have hvp0 : 0 ≤ vpf x y z := by
        by_contra hneg; push_neg at hneg
        -- then vm ≤ vp < 0 and h(vm) ≤ h(vp), contradicting h(vm) > E > h(vp)
        have hanti := hdelta_anti (a := -vpf x y z) (b := -vmf x y z) (by linarith) (by linarith) (by linarith)
        rw [hdelta_neg, hdelta_neg] at hanti
        linarith
      exact CKLaneR2.RSEnc.entropy_delta_ge he1 hvp0 hvp1.le hr2.le
  have key := implicit_finish V rho hpin
  exact ⟨key.1, key.2.1, key.2.2⟩

end CKLaneR2.Cell

end


