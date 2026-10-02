-- Prove2me | Definitions.Def_CK_GeneralCK_FCCappedScalar
-- name    : CK_GeneralCK_FCCappedScalar
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:38:06.087512+00:00
-- url     : https://prove2.me/theorems/d790ad36-2952-4f66-8462-b5f62e04d0c5
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCCappedScalar` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCCappedScalar` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCCappedScalar` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCCappedScalar (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCCappedScalar.lean)

import Definitions.Def_CK_GeneralCK_FCSharp500
import Definitions.Def_CK_GeneralCK_FCContact
import Definitions.Def_CK_GeneralCK_FCOwnerFinal

-- ===== source module GeneralCK.FCCappedScalar =====
section

/-!
# Lane F-C: the capped scalar inequality, and the owner

This closes the lane.  `FCOwnerFinal.owner_of_capped_scalar` reduced the exact target
`GeneralCK.OppositeCornerPhiAffineCertificate.CertificateOwner` to the single scalar
inequality

  `eta E − F (b−a) E ≤ F (1−a−b) E + psi b (2E)/2`

on the capped sub-case.  Here it is proved.

## The accounting, priced at the worst admissible point BEFORE it was written down

Write `Z = 1−a−b`, `r = b−a`, `L = −log Z`.  The cut gives `1 − r = a + (1−b) < 1e-4`,
hence `Z < 1e-4` and `L > 13·log 2 > 8.97`.

Cost side, all four terms measured per unit of `Z`:

| term                          | bound                     | worth at `L = 9.21` |
|-------------------------------|---------------------------|---------------------|
| `r·(eta E − eta (E/r))`       | `(21/10)(1−r)`            | `2.63 Z`            |
| `2a·eta E`                    | `4E ≤ 2Z`                 | `2.00 Z`            |
| `4E` (from the psi deficit)   | `2Z`                      | `2.00 Z`            |
| `Z·(eta E − eta (E/Z))`       | `Z·K`                     | `K`                 |

Budget side: `psi b (2E)/2 ≥ 2(H b − 2E)` and `H b = H (1−b) ≥ H Z ≥ Z(L+1−2Z)/log 2`,
so the budget is `2(L+1−2Z)/log 2 ≥ 2.885(L+1)` per unit `Z`.

`K` is case dependent.  On `E/Z ≤ 1/10` the direct integration gives `K = (21/10)L`,
which needs only `L ≥ 4.98`.  On `E/Z > 1/10` the sharp split of `FCSharp500` gives
`K = (17/10)L + 29/5`, which needs `L ≥ 8.27`.  Available: `L > 8.97`.  The binding
branch therefore holds with 8% of headroom in `L`, and the headroom GROWS as `Z → 0`
because the budget coefficient `2/log 2 = 2.885` exceeds the cost coefficient `17/10`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCCappedScalar

open GeneralCK

/-- **The capped scalar inequality, modulo a decrement bound `K` and its budget.**
Stated with `K` abstract so that the two branches of the ratio split share the whole
geometric and entropic accounting. -/
theorem scalar_of_decrement {a b E K : ℝ}
    (ha : 0 < a) (hab : a < b) (hsum : a + b < 1) (hb : 1 / 2 < b)
    (hcut : a + (1 - b) < 1 / 10000)
    (hE : 0 < E) (hEcap : E ≤ (H a + H b) / 2)
    (hactive : psi ((a + b) / 2) E ≤ phi ((a + b) / 2) E)
    (hcapped : H a ≤ E * (1 - 2 * a) / (b - a))
    (hD : eta E - eta (E / (1 - a - b)) ≤ K)
    (hbudget : (4 + K + 26253 / 10000) * Real.log 2
        ≤ 2 * (-Real.log (1 - a - b)) + 2 - 4 * (1 - a - b)) :
    eta E - F (b - a) E ≤ F (1 - a - b) E + psi b (2 * E) / 2 := by
  -- geometry
  have hb1 : b < 1 := by linarith
  have hZ : (0 : ℝ) < 1 - a - b := by linarith
  have hr : (0 : ℝ) < b - a := by linarith
  have hasmall : a < 1 / 20000 := by linarith
  have hZsmall : 1 - a - b < 1 / 10000 := by linarith
  have hrbig : (9999 : ℝ) / 10000 < b - a := by linarith
  have hr1 : b - a < 1 := by linarith
  have habpos : (0 : ℝ) < a + b := by linarith
  have hl2pos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hl2ne : Real.log 2 ≠ 0 := ne_of_gt hl2pos
  -- entropy smallness
  have hHa500 : H a ≤ 1 / 500 := FCRay.H_small_upper ha.le (by linarith)
  have hHbc : H b = H (1 - b) := (H_complement b).symm
  have hHb500 : H b ≤ 1 / 500 := by
    rw [hHbc]; exact FCRay.H_small_upper (by linarith) (by linarith)
  have hEsmall : E ≤ 1 / 500 := by
    have hHaHb : H a ≤ H b := by
      rw [hHbc]
      exact H_strictMonoOn.monotoneOn
        (show a ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨ha.le, by linarith⟩)
        (show (1 - b) ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨by linarith, by linarith⟩)
        (by linarith)
    linarith
  have h2E : 2 * E < 1 - a - b :=
    FCActive.active_forces_two_E_lt ha hb hsum hcut hE hEsmall hactive
  -- the capped hypothesis, cleared of its denominator
  have hcap' : H a * (b - a) ≤ E * (1 - 2 * a) := by
    rw [le_div_iff₀ hr] at hcapped
    exact hcapped
  have hHanneg : (0 : ℝ) ≤ H a := H_nonneg ha.le (by linarith)
  have hstep3 : E * (1 - 2 * a) ≤ E := by nlinarith only [hE, ha]
  -- `2a ≤ (2501/10000)·Z`: the capped hypothesis ties `a` to `E`, activity ties `E` to `Z`
  have hpar : 4 * a * (1 - a) < H a := H_gt_parabola ha (by linarith)
  have hu : (19999 : ℝ) / 20000 < 1 - a := by linarith
  have hprod : (99985 : ℝ) / 100000 ≤ (1 - a) * (b - a) := by
    nlinarith only [hu, hrbig]
  have hstep4 : (39994 : ℝ) / 10000 * a ≤ 4 * a * (1 - a) * (b - a) := by
    nlinarith only [hprod, ha]
  have hstep1 : 4 * a * (1 - a) * (b - a) ≤ H a * (b - a) := by
    nlinarith only [hpar, hr]
  have h2aZ : 2 * a ≤ (2501 : ℝ) / 10000 * (1 - a - b) := by
    linarith [hstep1, hcap', hstep3, hstep4, h2E]
  -- `2a·eta E ≤ 4E`, via the entropy inverse of `E`
  have hJa : (13 : ℝ) ≤ J a := by
    have hratio : (8192 : ℝ) ≤ (1 - a) / a := by
      rw [le_div_iff₀ ha]; linarith
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 8192) hratio
    have h8192 : Real.log (8192 : ℝ) = 13 * Real.log 2 := by
      rw [show (8192 : ℝ) = (2 : ℝ) ^ (13 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    unfold J
    rw [le_div_iff₀ hl2pos]
    linarith [hlog, h8192]
  have hcapE : (9998 : ℝ) / 10000 * H a ≤ E := by
    have h1 : H a * (b - a) ≤ E := by linarith [hcap', hstep3]
    have h2 : (9999 : ℝ) / 10000 * H a ≤ H a * (b - a) := by
      nlinarith only [hrbig, hHanneg]
    linarith [h1, h2, hHanneg]
  have hvge := FCConst.entropyInverse_ge_half_a ha (by linarith) hE (by linarith) hJa hcapE
  have hvpos : 0 < entropyInverse E := entropyInverse_pos hE (by linarith)
  have hvhalf : entropyInverse E < 1 / 2 := entropyInverse_lt_half hE.le (by linarith)
  have hHv : H (entropyInverse E) = E := (entropyInverse_spec hE.le (by linarith)).2.2
  have hJv : 0 ≤ J (entropyInverse E) := J_nonneg hvpos hvhalf.le
  have hvJ : entropyInverse E * J (entropyInverse E) ≤ H (entropyInverse E) :=
    FCContact.H_ge_mul_J hvpos (by linarith)
  have hetaform : eta E = (1 - 2 * entropyInverse E) * J (entropyInverse E) :=
    eta_eq_profile hE.le (by linarith)
  have hetale : eta E ≤ J (entropyInverse E) := by
    rw [hetaform]; nlinarith only [hJv, hvpos]
  have hetann : (0 : ℝ) ≤ eta E := by
    rw [hetaform]; nlinarith only [hJv, hvhalf]
  have hA1 : 2 * a * eta E ≤ 4 * entropyInverse E * eta E := by
    nlinarith only [hvge, hetann]
  have hA2 : 4 * entropyInverse E * eta E
      ≤ 4 * entropyInverse E * J (entropyInverse E) := by
    nlinarith only [hetale, hvpos]
  have hA3 : entropyInverse E * J (entropyInverse E) ≤ E := by linarith [hvJ, hHv]
  have h2aeta : 2 * a * eta E ≤ 4 * E := by linarith [hA1, hA2, hA3]
  -- the two homogeneous `F` lower bounds
  have hErlt : E / (b - a) < 1 := by rw [div_lt_one hr]; linarith
  have hFr : (b - a) * eta (E / (b - a)) ≤ F (b - a) E := FCContact.F_lower_eta hr hE hErlt
  have hEZlt : E / (1 - a - b) < 1 := by rw [div_lt_one hZ]; linarith
  have hFZ : (1 - a - b) * eta (E / (1 - a - b)) ≤ F (1 - a - b) E :=
    FCContact.F_lower_eta hZ hE hEZlt
  -- the psi deficit bound
  have hHbZ : H (1 - a - b) ≤ H b := by
    rw [hHbc]
    exact H_strictMonoOn.monotoneOn
      (show (1 - a - b) ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨hZ.le, by linarith⟩)
      (show (1 - b) ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨by linarith, by linarith⟩)
      (by linarith)
  have hHZgt : 4 * (1 - a - b) * (1 - (1 - a - b)) < H (1 - a - b) :=
    H_gt_parabola hZ (by linarith)
  have hZsq : (1 - a - b) ≤ 4 * (1 - a - b) * (1 - (1 - a - b)) := by
    nlinarith only [hZ, hZsmall]
  have h2EHb : 2 * E < H b := by linarith [hHZgt, hHbZ, h2E, hZsq]
  have hpsi : 4 * (H b - 2 * E) ≤ psi b (2 * E) :=
    FCCapped.psi_ge_four_deficit (by linarith) (by linarith)
  -- the `r` decrement
  have hEler : E ≤ E / (b - a) := by
    rw [le_div_iff₀ hr]; nlinarith only [hE, hr1]
  have hErtenth : E / (b - a) ≤ 1 / 10 := by
    rw [div_le_iff₀ hr]; linarith
  have hdecr := FCSharp.eta_decrement_tenth hE hEler hErtenth
  have hlogr : Real.log (E / (b - a)) - Real.log E = -Real.log (b - a) := by
    rw [Real.log_div hE.ne' hr.ne']; ring
  have hrlog2 : (b - a) * (-Real.log (b - a)) ≤ 1 - (b - a) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hr)
    rw [Real.log_inv] at h
    have hid : (b - a) * ((b - a)⁻¹ - 1) = 1 - (b - a) := by field_simp
    nlinarith only [h, hr, hid]
  have hrdec1 : (b - a) * (eta E - eta (E / (b - a)))
      ≤ (b - a) * ((21 / 10) * (Real.log (E / (b - a)) - Real.log E)) :=
    mul_le_mul_of_nonneg_left hdecr hr.le
  rw [hlogr] at hrdec1
  have hrdec : (b - a) * (eta E - eta (E / (b - a))) ≤ (21 / 10) * (1 - (b - a)) := by
    linarith [hrdec1, hrlog2]
  -- the `Z` decrement, scaled
  have hZD : (1 - a - b) * (eta E - eta (E / (1 - a - b))) ≤ (1 - a - b) * K :=
    mul_le_mul_of_nonneg_left hD hZ.le
  -- the budget: `H Z · log 2 ≥ Z·(L + 1 − 2Z)`
  have hJZmul : J (1 - a - b) * Real.log 2 = Real.log (a + b) - Real.log (1 - a - b) := by
    unfold J
    rw [show (1 : ℝ) - (1 - a - b) = a + b by ring,
      Real.log_div (ne_of_gt habpos) (ne_of_gt hZ),
      div_mul_eq_mul_div, mul_div_assoc, div_self hl2ne, mul_one]
  have hlogab : -(2 * (1 - a - b)) ≤ Real.log (a + b) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr habpos)
    rw [Real.log_inv] at h
    have hhalf : (1 : ℝ) / 2 ≤ a + b := by linarith
    have hb2 : (a + b)⁻¹ - 1 ≤ 2 * (1 - a - b) := by
      rw [inv_eq_one_div, div_sub_one (ne_of_gt habpos), div_le_iff₀ habpos]
      nlinarith only [hZ, hhalf]
    linarith
  have hHZsharp := FCConst.H_ge_mul_J_sharp hZ (by linarith)
  have hHZlb : (1 - a - b) * ((-Real.log (1 - a - b)) + 1 - 2 * (1 - a - b))
      ≤ H (1 - a - b) * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_right hHZsharp hl2pos.le
    have hdivcancel : (1 - a - b) / Real.log 2 * Real.log 2 = (1 - a - b) := by
      field_simp
    have hexp : ((1 - a - b) * J (1 - a - b) + (1 - a - b) / Real.log 2) * Real.log 2
        = (1 - a - b) * (J (1 - a - b) * Real.log 2)
          + ((1 - a - b) / Real.log 2 * Real.log 2) := by ring
    rw [hexp, hdivcancel, hJZmul] at hmul
    nlinarith only [hmul, hlogab, hZ]
  have hbud := mul_le_mul_of_nonneg_left hbudget hZ.le
  have hstepL : ((1 - a - b) * (4 + K + 26253 / 10000)) * Real.log 2
      ≤ (2 * H (1 - a - b)) * Real.log 2 := by
    nlinarith only [hbud, hHZlb, hZ]
  have hstep2 : (1 - a - b) * (4 + K + 26253 / 10000) ≤ 2 * H (1 - a - b) :=
    le_of_mul_le_mul_right hstepL hl2pos
  have hkey : 8 * E + (1 - a - b) * K + (21 / 10) * (1 - (b - a)) ≤ 2 * H b := by
    linarith [hstep2, hHbZ, h2E, h2aZ]
  -- assemble
  have hid : eta E - (b - a) * eta (E / (b - a))
      = 2 * a * eta E + (1 - a - b) * eta E
        + (b - a) * (eta E - eta (E / (b - a))) := by ring
  have hid2 : (1 - a - b) * eta E
      = (1 - a - b) * eta (E / (1 - a - b))
        + (1 - a - b) * (eta E - eta (E / (1 - a - b))) := by ring
  linarith [hFr, hFZ, hpsi, h2aeta, hrdec, hZD, hkey, hid, hid2]

/-- **The capped scalar inequality.** -/
theorem capped_scalar (a b E : ℝ) (ha : 0 < a) (hab : a < b) (hsum : a + b < 1)
    (_hlarge : 1 / 16 < a + b) (hb : 1 / 2 < b)
    (hcut : a + (1 - b) < SmallMeanPhiCutoff.retainedCutoff)
    (hE : 0 < E) (hEcap : E ≤ (H a + H b) / 2)
    (hactive : psi ((a + b) / 2) E ≤ phi ((a + b) / 2) E)
    (hcapped : H a ≤ E * (1 - 2 * a) / (b - a)) :
    eta E - F (b - a) E ≤ F (1 - a - b) E + psi b (2 * E) / 2 := by
  have hcut' : a + (1 - b) < 1 / 10000 := by
    rw [FCOwner.retainedCutoff_eq] at hcut; exact hcut
  have hb1 : b < 1 := by linarith
  have hZ : (0 : ℝ) < 1 - a - b := by linarith
  have hZsmall : 1 - a - b < 1 / 10000 := by linarith
  have hl2pos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hl2ub := FCAnalytic.log_two_ub
  have hl2lb := FCAnalytic.log_two_lb
  have hHa500 : H a ≤ 1 / 500 := FCRay.H_small_upper ha.le (by linarith)
  have hHbc : H b = H (1 - b) := (H_complement b).symm
  have hHb500 : H b ≤ 1 / 500 := by
    rw [hHbc]; exact FCRay.H_small_upper (by linarith) (by linarith)
  have hEsmall : E ≤ 1 / 500 := by
    have hHaHb : H a ≤ H b := by
      rw [hHbc]
      exact H_strictMonoOn.monotoneOn
        (show a ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨ha.le, by linarith⟩)
        (show (1 - b) ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨by linarith, by linarith⟩)
        (by linarith)
    linarith
  have h2E : 2 * E < 1 - a - b :=
    FCActive.active_forces_two_E_lt ha hb hsum hcut' hE hEsmall hactive
  -- `L = −log Z > 13·log 2 > 8.97`
  have hLlb : (13 : ℝ) * Real.log 2 < -Real.log (1 - a - b) := by
    have hlt : (1 - a - b) < 1 / 8192 := by linarith
    have hlog := Real.log_lt_log hZ hlt
    have h1 : Real.log (1 / 8192 : ℝ) = -(13 * Real.log 2) := by
      rw [show (1 : ℝ) / 8192 = ((2 : ℝ) ^ (13 : ℕ))⁻¹ by norm_num, Real.log_inv,
        Real.log_pow]
      push_cast; ring
    rw [h1] at hlog; linarith
  have hLpos : (0 : ℝ) < -Real.log (1 - a - b) := by linarith
  by_cases hcase : E / (1 - a - b) ≤ 1 / 10
  · -- low ratio: integrate at `21/10` over the whole stretch
    have hEleZ : E ≤ E / (1 - a - b) := by
      rw [le_div_iff₀ hZ]; nlinarith only [hE, hZ, hZsmall]
    have hD := FCSharp.eta_decrement_tenth hE hEleZ hcase
    have hlogZ : Real.log (E / (1 - a - b)) - Real.log E = -Real.log (1 - a - b) := by
      rw [Real.log_div hE.ne' hZ.ne']; ring
    rw [hlogZ] at hD
    refine scalar_of_decrement ha hab hsum hb hcut' hE hEcap hactive hcapped hD ?_
    have hprodA : (21 / 10) * (-Real.log (1 - a - b)) * Real.log 2
        ≤ (21 / 10) * (-Real.log (1 - a - b)) * (7 / 10) := by
      nlinarith only [hLpos, hl2ub]
    nlinarith only [hprodA, hLlb, hl2ub, hl2lb, hl2pos, hZ, hZsmall, hLpos]
  · -- high ratio: the sharp split of `FCSharp500`
    push_neg at hcase
    have hD := FCSharp500.eta_decrement_caseB hE hEsmall hZ h2E hcase
    refine scalar_of_decrement ha hab hsum hb hcut' hE hEcap hactive hcapped hD ?_
    have hprodB : (17 / 10) * (-Real.log (1 - a - b)) * Real.log 2
        ≤ (17 / 10) * (-Real.log (1 - a - b)) * (7 / 10) := by
      nlinarith only [hLpos, hl2ub]
    nlinarith only [hprodB, hLlb, hl2ub, hl2lb, hl2pos, hZ, hZsmall, hLpos]

/-- **The lane's target, unconditionally.** -/
theorem certificate_owner : OppositeCornerPhiAffineCertificate.CertificateOwner :=
  FCOwnerFinal.owner_of_capped_scalar capped_scalar

#check @scalar_of_decrement
#check @capped_scalar
#check @certificate_owner
#print axioms scalar_of_decrement
#print axioms capped_scalar
#print axioms certificate_owner

end GeneralCK.FCCappedScalar

end


