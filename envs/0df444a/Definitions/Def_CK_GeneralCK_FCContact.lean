-- Prove2me | Definitions.Def_CK_GeneralCK_FCContact
-- name    : CK_GeneralCK_FCContact
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:52:18.487726+00:00
-- url     : https://prove2.me/theorems/a58ca5c0-0e6e-46e2-a205-c37f4ab0dcfc
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCContact` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCContact` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCContact` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCContact (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCContact.lean)

import Definitions.Def_CK_GeneralCK_FCCapped

-- ===== source module GeneralCK.FCContact =====
section

/-!
# Lane F-C: contact-point tools for the remaining scalar inequality

Reusable, region-independent:

* `H_ge_mul_J`            — `q · J q ≤ H q` (the defect is exactly `log2 (1/(1-q))`);
* `radialContact_le_of_entropy` — a sufficient rational criterion for `radialContact z h ≤ v`;
* `F_lower_of_contact`    — `z · J v ≤ F z h` whenever `h ≤ z · H v`;
* `eta_eq_F_contact`      — `eta E = F (1 - 2·entropyInverse E) E`, the contact identity
                            that lets the whole residual be written as a difference of two
                            `F`'s at the SAME entropy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCContact

open GeneralCK

/-- `q · J q ≤ H q`; the defect is `log2 (1/(1-q)) ≥ 0`. -/
theorem H_ge_mul_J {q : ℝ} (hq : 0 < q) (hq1 : q < 1) : q * J q ≤ H q := by
  have hqc : (0 : ℝ) < 1 - q := by linarith
  have hLpos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hid : H q * Real.log 2 - (q * J q) * Real.log 2 = -Real.log (1 - q) := by
    unfold H Real.binEntropy J
    rw [Real.log_div hqc.ne' hq.ne']
    simp only [Real.log_inv]
    field_simp
    ring
  have hneg : -Real.log (1 - q) ≥ 0 := by
    have := Real.log_nonpos (by linarith) (by linarith : (1 : ℝ) - q ≤ 1)
    linarith
  nlinarith only [hid, hneg, hLpos]

/-- A sufficient rational criterion for an upper bound on the contact radius. -/
theorem radialContact_le_of_entropy {z h v : ℝ} (hz : 0 < z) (hh : 0 < h)
    (hv : 0 ≤ v) (hv2 : v ≤ 1 / 2) (hcrit : h ≤ z * H v) :
    radialContact z h ≤ v := by
  apply (radialContact_le_iff hz hh hv hv2).2
  nlinarith only [hcrit, hh, hv, hv2]

/-- `F z h ≥ z · J v` as soon as `h ≤ z · H v`. -/
theorem F_lower_of_contact {z h v : ℝ} (hz : 0 < z) (hh : 0 < h)
    (hv : 0 < v) (hv2 : v ≤ 1 / 2) (hcrit : h ≤ z * H v) :
    z * J v ≤ F z h := by
  have hw := radialContact_le_of_entropy hz hh hv.le hv2 hcrit
  have hJ := J_antitone (radialContact_pos hz hh) hv2 hw
  simp only [F, hz.ne', ↓reduceIte]
  exact mul_le_mul_of_nonneg_left hJ hz.le

/-- The contact identity: `eta E` is itself a value of `F` at the same entropy. -/
theorem eta_eq_F_contact {E : ℝ} (hE : 0 < E) (hE1 : E < 1) :
    eta E = F (1 - 2 * entropyInverse E) E := by
  have hv : 0 < entropyInverse E := entropyInverse_pos hE hE1.le
  have hvhalf : entropyInverse E < 1 / 2 := entropyInverse_lt_half hE.le hE1
  have hHv : H (entropyInverse E) = E := (entropyInverse_spec hE.le hE1.le).2.2
  have hz : (0 : ℝ) < 1 - 2 * entropyInverse E := by linarith
  have hc : radialContact (1 - 2 * entropyInverse E) E = entropyInverse E := by
    have h := radialContact_H_lower hv hvhalf
    rwa [hHv] at h
  rw [eta_eq_profile hE.le hE1.le]
  simp only [F, hz.ne', ↓reduceIte, hc]

/-- **Homogeneous lower bound.**  `F z h ≥ z · eta (h/z)` whenever `h/z ≤ 1`.
This is the sharp form the capped sub-case needs: the crude `F z h ≥ (16/5) z`
is up to fifteen times weaker when `h/z` is tiny. -/
theorem F_lower_eta {z h : ℝ} (hz : 0 < z) (hh : 0 < h) (hratio : h / z < 1) :
    z * eta (h / z) ≤ F z h := by
  have hr0 : 0 < h / z := div_pos hh hz
  set v := entropyInverse (h / z) with hvdef
  have hv : 0 < v := entropyInverse_pos hr0 hratio.le
  have hvhalf : v < 1 / 2 := entropyInverse_lt_half hr0.le hratio
  have hHv : H v = h / z := (entropyInverse_spec hr0.le hratio.le).2.2
  have hcrit : h ≤ z * H v := by
    rw [hHv, mul_div_cancel₀ _ hz.ne']
  have hF := F_lower_of_contact hz hh hv hvhalf.le hcrit
  have hJ : 0 ≤ J v := J_nonneg hv hvhalf.le
  have hetav : eta (h / z) = (1 - 2 * v) * J v := eta_eq_profile hr0.le hratio.le
  have hle : eta (h / z) ≤ J v := by
    rw [hetav]
    nlinarith only [hJ, hv]
  nlinarith only [hF, hle, hz]

#check @F_lower_eta
#check @H_ge_mul_J
#check @radialContact_le_of_entropy
#check @F_lower_of_contact
#check @eta_eq_F_contact
#print axioms F_lower_eta
#print axioms H_ge_mul_J
#print axioms radialContact_le_of_entropy
#print axioms F_lower_of_contact
#print axioms eta_eq_F_contact

end GeneralCK.FCContact

end


