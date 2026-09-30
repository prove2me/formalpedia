-- Prove2me | Definitions.Def_CK_GeneralCK_PsiNormalizedLowEntropy
-- name    : CK_GeneralCK_PsiNormalizedLowEntropy
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:00:11.870691+00:00
-- url     : https://prove2.me/theorems/ad00eda3-860b-4ba8-91a5-b6db62e2964a
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiNormalizedLowEntropy` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiNormalizedLowEntropy` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiNormalizedLowEntropy` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiNormalizedLowEntropy (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiNormalizedLowEntropy.lean)

import Definitions.Def_CK_GeneralCK_PsiBoundaryAnalyticBridge
import Definitions.Def_CK_GeneralCK_Certificates_LogBounds
import Definitions.Def_CK_GeneralCK_EntropyParabola
import Definitions.Def_CK_GeneralCK_EntropyComparison
import Definitions.Def_CK_GeneralCK_ProfileConvexity

-- ===== source module GeneralCK.PsiNormalizedLowEntropy =====
section

/-!
# The normalized low-entropy residual region `q ≤ 8E`, `E ≤ 10⁻⁶`

Branch 4 of the active-psi scalar owner cluster asks for

    ResidualPsiScalarOwner normalizedLowEntropyResidualRegion,
    normalizedLowEntropyResidualRegion a b E :=
      1/2 ≤ b ∧ E ≤ 1/1000000 ∧ 1 - a - b ≤ 8 * E.

**That proposition is false, and this file proves it false.**  It is refuted by
an explicit witness at which *every* hypothesis of `ResidualPsiScalarOwner`
holds — including the psi-active hypothesis `phi < psi`, which is what rules out
the vacuity shortcut — and at which the conclusion
`residualPsiScalarBound a b E ≤ interiorCost a b` fails by a factor of about
six.  The same witness refutes `oppositeLowEntropyResidualRegion`, and a second
witness of the same shape refutes `oppositeCentralResidualRegion`.

## What is *not* claimed

This refutes the **scalar-owner form** of the statement.  It does **not**
contradict the archived `GLOBAL_EIGHT_PROOF.md`: that argument keeps `R_phi` at
the children and bounds the cost below by the endpoint quantity
`B_end ≥ F(d,E) + (d/2L) J(τ)`, which is far stronger than the log-sum floor
`interiorCost a b` used by `ResidualPsiScalarOwner`.  The defect located here is
in the three-variable reduction, not in the archived mathematics.  Concretely
the reduction is lossy in two places:

* `B(child) = max (phi, psi)` is replaced by `psi (child)`; in the low-entropy
  regime the children are strongly phi-dominated, so this discards an `O(1)`
  amount;
* the cost is replaced by the log-sum floor `interiorCost a b` at the means.

Where `eta` blows up (small entropy argument) while `interiorCost` stays
bounded, the reduction therefore cannot hold.

## The witness

    v  = 1/16   (or 1/8 for the central region)
    E  = H (2⁻²⁵)                     (so `eta E` is exact by `eta_H`)
    q  = E / (10 * H (9/20))          (so `radialContact q E = 9/20` exactly)
    a  = v - q,   b = 1 - v           (so `H b = H v` exactly and `1-a-b = q`)

`q` is irrational; this is legitimate, since `ResidualPsiScalarOwner`
quantifies over real `a b E`.  Choosing `q` by the contact equation is what
removes every contact enclosure: `F q E = q * J (9/20)` holds *exactly*.

All transcendental input is a kernel-checked rational enclosure:
`Certificates.checkLog_sound` for `log 2` and `log (11/9)`, the elementary
bounds `log x ≤ x - 1` for `H` at dyadic points, `H_gt_parabola` for the parent
entropy defect, and `eta_H` for the exact value of `eta` at `H p`.
-/

namespace GeneralCK
open Set

/-- The exact target region of the branch-4 task. -/
def normalizedLowEntropyResidualRegion (a b E : ℝ) : Prop :=
  1 / 2 ≤ b ∧ E ≤ 1 / 1000000 ∧ 1 - a - b ≤ 8 * E

/-! ## 1. Rational enclosures for the two logarithms that are needed -/

theorem log_two_lower : (6931471805 / 10000000000 : ℝ) ≤ Real.log 2 := by
  have h := Certificates.checkLog_sound (w := 1/3) (n := 14)
    (lo := 6931471805 / 10000000000) (hi := 6931471806 / 10000000000)
    (by norm_num [Certificates.checkLog, Certificates.logLower,
      Certificates.logUpper, Finset.sum_range_succ])
  norm_num at h
  linarith [h.1]

theorem log_two_upper : Real.log 2 ≤ (6931471806 / 10000000000 : ℝ) := by
  have h := Certificates.checkLog_sound (w := 1/3) (n := 14)
    (lo := 6931471805 / 10000000000) (hi := 6931471806 / 10000000000)
    (by norm_num [Certificates.checkLog, Certificates.logLower,
      Certificates.logUpper, Finset.sum_range_succ])
  norm_num at h
  linarith [h.2]

theorem log_eleven_ninths_lower : (2006706954 / 10000000000 : ℝ) ≤ Real.log (11 / 9) := by
  have h := Certificates.checkLog_sound (w := 1/10) (n := 8)
    (lo := 2006706954 / 10000000000) (hi := 2006706955 / 10000000000)
    (by norm_num [Certificates.checkLog, Certificates.logLower,
      Certificates.logUpper, Finset.sum_range_succ])
  norm_num at h
  linarith [h.1]


/-! ## 2. Elementary two-sided bounds for `H` -/

/-- `log 2 > 0`, in the form used below. -/
theorem log_two_pos' : (0:ℝ) < Real.log 2 := by linarith [log_two_lower]

/-- Upper bound on the binary entropy, cleared of the division by `log 2`. -/
theorem H_mul_log_two_eq (p : ℝ) : H p * Real.log 2 = Real.binEntropy p := by
  rw [H, div_mul_eq_mul_div, mul_div_assoc, div_self (ne_of_gt log_two_pos'), mul_one]

theorem H_mul_log_two_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    H p * Real.log 2 ≤ p * Real.log p⁻¹ + p := by
  have hlt : (0:ℝ) < 1 - p := by linarith
  have hne : (1 : ℝ) - p ≠ 0 := ne_of_gt hlt
  have h2 : (1 - p) * Real.log (1 - p)⁻¹ ≤ p := by
    have h := Real.log_le_sub_one_of_pos (x := (1 - p)⁻¹) (by positivity)
    have hmul : (1 - p) * ((1 - p)⁻¹ - 1) = p := by
      field_simp
      ring
    calc (1 - p) * Real.log (1 - p)⁻¹ ≤ (1 - p) * ((1 - p)⁻¹ - 1) :=
          mul_le_mul_of_nonneg_left h hlt.le
      _ = p := hmul
  rw [H_mul_log_two_eq, Real.binEntropy]
  linarith

/-- Lower bound on the binary entropy, cleared of the division by `log 2`. -/
theorem H_mul_log_two_ge {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    p * Real.log p⁻¹ + p * (1 - p) ≤ H p * Real.log 2 := by
  have hlt : (0:ℝ) < 1 - p := by linarith
  have h1 : p ≤ Real.log (1 - p)⁻¹ := by
    have h := Real.log_le_sub_one_of_pos (x := 1 - p) hlt
    rw [Real.log_inv]
    linarith
  have h2 : p * (1 - p) ≤ (1 - p) * Real.log (1 - p)⁻¹ := by
    have := mul_le_mul_of_nonneg_left h1 hlt.le
    linarith [this]
  rw [H_mul_log_two_eq, Real.binEntropy]
  linarith

/-! ### The four dyadic anchors and the two mean anchors -/

theorem log_inv_two_pow (k : ℕ) (x : ℝ) (hx : x⁻¹ = (2:ℝ) ^ k) :
    Real.log x⁻¹ = k * Real.log 2 := by
  rw [hx, Real.log_pow]

theorem H_pow25_le : H (1 / 33554432) ≤ 78806 / 100000000000 := by
  have hp : (0:ℝ) < 1 / 33554432 := by norm_num
  have hp1 : (1:ℝ) / 33554432 < 1 := by norm_num
  have hlog : Real.log ((1 / 33554432 : ℝ))⁻¹ = 25 * Real.log 2 :=
    log_inv_two_pow 25 _ (by norm_num)
  have h := H_mul_log_two_le hp hp1
  rw [hlog] at h
  nlinarith [log_two_lower, log_two_upper, H_nonneg hp.le hp1.le, log_two_pos']

theorem H_pow25_ge : (78805 / 100000000000 : ℝ) ≤ H (1 / 33554432) := by
  have hp : (0:ℝ) < 1 / 33554432 := by norm_num
  have hp1 : (1:ℝ) / 33554432 < 1 := by norm_num
  have hlog : Real.log ((1 / 33554432 : ℝ))⁻¹ = 25 * Real.log 2 :=
    log_inv_two_pow 25 _ (by norm_num)
  have h := H_mul_log_two_ge hp hp1
  rw [hlog] at h
  nlinarith [log_two_lower, log_two_upper, log_two_pos']

theorem H_pow26_le : H (1 / 67108864) ≤ 40893 / 100000000000 := by
  have hp : (0:ℝ) < 1 / 67108864 := by norm_num
  have hp1 : (1:ℝ) / 67108864 < 1 := by norm_num
  have hlog : Real.log ((1 / 67108864 : ℝ))⁻¹ = 26 * Real.log 2 :=
    log_inv_two_pow 26 _ (by norm_num)
  have h := H_mul_log_two_le hp hp1
  rw [hlog] at h
  nlinarith [log_two_lower, log_two_upper, H_nonneg hp.le hp1.le, log_two_pos']

theorem H_pow24_ge : (143 / 100000000 : ℝ) ≤ H (1 / 16777216) := by
  have hp : (0:ℝ) < 1 / 16777216 := by norm_num
  have hp1 : (1:ℝ) / 16777216 < 1 := by norm_num
  have hlog : Real.log ((1 / 16777216 : ℝ))⁻¹ = 24 * Real.log 2 :=
    log_inv_two_pow 24 _ (by norm_num)
  have h := H_mul_log_two_ge hp hp1
  rw [hlog] at h
  nlinarith [log_two_lower, log_two_upper, log_two_pos']

theorem H_sixteenth_le : H (1 / 16) ≤ 3402 / 10000 := by
  have hp : (0:ℝ) < 1 / 16 := by norm_num
  have hp1 : (1:ℝ) / 16 < 1 := by norm_num
  have hlog : Real.log ((1 / 16 : ℝ))⁻¹ = 4 * Real.log 2 :=
    log_inv_two_pow 4 _ (by norm_num)
  have h := H_mul_log_two_le hp hp1
  rw [hlog] at h
  nlinarith [log_two_lower, log_two_upper, H_nonneg hp.le hp1.le, log_two_pos']

theorem H_eighth_le : H (1 / 8) ≤ 5554 / 10000 := by
  have hp : (0:ℝ) < 1 / 8 := by norm_num
  have hp1 : (1:ℝ) / 8 < 1 := by norm_num
  have hlog : Real.log ((1 / 8 : ℝ))⁻¹ = 3 * Real.log 2 :=
    log_inv_two_pow 3 _ (by norm_num)
  have h := H_mul_log_two_le hp hp1
  nlinarith [log_two_lower, log_two_upper, H_nonneg hp.le hp1.le, log_two_pos', hlog ▸ h]

#print axioms H_pow25_le
#print axioms H_pow25_ge
#print axioms H_pow26_le
#print axioms H_pow24_ge
#print axioms H_sixteenth_le
#print axioms H_eighth_le


/-! ## 3. The witness scalars

`nleE` is the average child entropy, chosen as `H (2⁻²⁵)` so that `eta nleE`
is *exactly* computable by `eta_H`.  `nleQ` is the mean gap `q = 1 - a - b`,
chosen so that the radial contact of `(q, E)` is *exactly* the rational `9/20`;
this makes `F q E = q * J (9/20)` with no contact enclosure at all. -/

noncomputable def nleE : ℝ := H (1 / 33554432)

noncomputable def nleQ : ℝ := nleE / (10 * H (9 / 20))

theorem H920_gt : (99 : ℝ) / 100 < H (9 / 20) := by
  have h := H_gt_parabola (p := 9 / 20) (by norm_num) (by norm_num)
  norm_num at h
  linarith

theorem H920_le : H (9 / 20) ≤ 1 := H_le_one _

theorem nleE_pos : 0 < nleE := by
  have := H_pow25_ge
  unfold nleE
  linarith

theorem nleE_le : nleE ≤ 78806 / 100000000000 := H_pow25_le

theorem nleE_ge : (78805 : ℝ) / 100000000000 ≤ nleE := H_pow25_ge

theorem nleQ_pos : 0 < nleQ := by
  apply div_pos nleE_pos
  linarith [H920_gt]

theorem nleQ_mul : nleQ * H (9 / 20) = nleE / 10 := by
  have h : H (9 / 20) ≠ 0 := ne_of_gt (by linarith [H920_gt] : (0:ℝ) < H (9 / 20))
  unfold nleQ
  field_simp

theorem nleQ_le : nleQ ≤ 79603 / 1000000000000 := by
  have h1 : (99 : ℝ) / 100 < H (9 / 20) := H920_gt
  have h2 := nleE_le
  have h3 : (0:ℝ) < 10 * H (9 / 20) := by linarith
  unfold nleQ
  rw [div_le_iff₀ h3]
  nlinarith [nleE_pos]

theorem nleQ_ge : (78805 : ℝ) / 1000000000000 ≤ nleQ := by
  have h1 : H (9 / 20) ≤ 1 := H920_le
  have h2 := nleE_ge
  have h3 : (0:ℝ) < 10 * H (9 / 20) := by linarith [H920_gt]
  unfold nleQ
  rw [le_div_iff₀ h3]
  nlinarith [H920_gt]

/-! ### The exact radial contact and the exact value of `F` -/

theorem nle_radialContact : radialContact nleQ nleE = 9 / 20 := by
  refine radialContact_eq_of_equation nleQ_pos nleE_pos (by norm_num) (by norm_num) ?_
  have hten : nleE * (1 - 2 * (9 / 20 : ℝ)) = nleE / 10 := by ring
  rw [nleQ_mul, hten]

theorem nle_F : F nleQ nleE = nleQ * J (9 / 20) := by
  simp only [F, if_neg (ne_of_gt nleQ_pos), nle_radialContact]

theorem J920_ge : (2895 : ℝ) / 10000 ≤ J (9 / 20) := by
  have hlog : Real.log ((1 - 9 / 20) / (9 / 20) : ℝ) = Real.log (11 / 9) := by
    norm_num
  unfold J
  rw [hlog]
  rw [le_div_iff₀ log_two_pos']
  nlinarith [log_eleven_ninths_lower, log_two_upper]

#print axioms nleQ_le
#print axioms nleQ_ge
#print axioms nle_radialContact
#print axioms nle_F
#print axioms J920_ge


/-! ## 4. `eta` at the two dyadic anchors -/

theorem log_pow25 : Real.log 33554432 = 25 * Real.log 2 := by
  rw [show (33554432:ℝ) = 2 ^ (25:ℕ) by norm_num, Real.log_pow]
  norm_num

theorem log_pow26 : Real.log 67108864 = 26 * Real.log 2 := by
  rw [show (67108864:ℝ) = 2 ^ (26:ℕ) by norm_num, Real.log_pow]
  norm_num

theorem J_pow25_ge : (24999999 : ℝ) / 1000000 ≤ J (1 / 33554432) := by
  have hval : ((1 - 1 / 33554432) / (1 / 33554432) : ℝ) = 33554431 := by norm_num
  have hgap : Real.log 33554432 - Real.log 33554431 ≤ 1 / 33554431 := by
    have h := Real.log_le_sub_one_of_pos (x := (33554432 : ℝ) / 33554431) (by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num)] at h
    have he : (33554432 : ℝ) / 33554431 - 1 = 1 / 33554431 := by norm_num
    linarith [he ▸ h]
  unfold J
  rw [hval, le_div_iff₀ log_two_pos']
  nlinarith [log_two_lower, log_two_upper, log_pow25]

theorem J_pow26_le : J (1 / 67108864) ≤ 26 := by
  have hval : ((1 - 1 / 67108864) / (1 / 67108864) : ℝ) = 67108863 := by norm_num
  have hmono : Real.log 67108863 ≤ Real.log 67108864 :=
    Real.log_le_log (by norm_num) (by norm_num)
  unfold J
  rw [hval, div_le_iff₀ log_two_pos']
  nlinarith [log_two_lower, log_pow26]

theorem J_pow26_nonneg : 0 ≤ J (1 / 67108864) :=
  J_nonneg (by norm_num) (by norm_num)

theorem eta_nleE_ge : (24999997 : ℝ) / 1000000 ≤ eta nleE := by
  have h : eta (H (1 / 33554432)) = (1 - 2 * (1 / 33554432)) * J (1 / 33554432) :=
    Comparison.eta_H (by norm_num) (by norm_num)
  have hJ := J_pow25_ge
  have hJle : J (1 / 33554432) ≤ 25 := by
    have hval : ((1 - 1 / 33554432) / (1 / 33554432) : ℝ) = 33554431 := by norm_num
    have hmono : Real.log 33554431 ≤ Real.log 33554432 :=
      Real.log_le_log (by norm_num) (by norm_num)
    unfold J
    rw [hval, div_le_iff₀ log_two_pos']
    nlinarith [log_two_lower, log_pow25]
  show (24999997 : ℝ) / 1000000 ≤ eta nleE
  unfold nleE
  rw [h]
  nlinarith

theorem eta_pow26_le : eta (H (1 / 67108864)) ≤ 26 := by
  have h : eta (H (1 / 67108864)) = (1 - 2 * (1 / 67108864)) * J (1 / 67108864) :=
    Comparison.eta_H (by norm_num) (by norm_num)
  rw [h]
  nlinarith [J_pow26_le, J_pow26_nonneg]

/-! ## 5. The parent is `psi`-active at the witness

This is the step the vacuity shortcut cannot supply: at the witness the psi
branch really is the active one, so the owner hypothesis `phi < psi` holds. -/

theorem nle_active {m : ℝ} (hm : m = (1 - nleQ) / 2) :
    phi m nleE < psi m nleE := by
  subst hm
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have hEge : (78805 : ℝ) / 100000000000 ≤ nleE := nleE_ge
  have hEle : nleE ≤ 78806 / 100000000000 := nleE_le
  have hE0 : 0 < nleE := nleE_pos
  -- the parent radius is exactly `nleQ`
  have habs : |1 - 2 * ((1 - nleQ) / 2)| = nleQ := by
    rw [show (1 : ℝ) - 2 * ((1 - nleQ) / 2) = nleQ by ring, abs_of_pos hq0]
  -- the parent entropy defect
  have hm2 : (1 - nleQ) / 2 < 1 / 2 := by linarith
  have hm0 : 0 < (1 - nleQ) / 2 := by linarith
  have hHm1 : H ((1 - nleQ) / 2) < 1 := by
    have := H_strictMonoOn (a := (1 - nleQ) / 2) (b := 1 / 2)
      ⟨hm0.le, hm2.le⟩ ⟨by norm_num, le_rfl⟩ hm2
    rwa [H_half] at this
  have hc0 : 0 < 1 - H ((1 - nleQ) / 2) := by linarith
  have hcq : 1 - H ((1 - nleQ) / 2) ≤ nleQ ^ 2 := by
    have h := H_gt_parabola (p := (1 - nleQ) / 2) hm0 hm2
    nlinarith
  -- the two convexity anchors
  set p' := H (1 / 67108864) with hp'
  have hp'0 : 0 < p' := H_pos (by norm_num) (by norm_num)
  have hp'1 : p' ≤ 1 := H_le_one _
  have hp'le : p' ≤ 40893 / 100000000000 := H_pow26_le
  have hD : 0 < nleE - p' := by linarith
  have hDge : (37912 : ℝ) / 100000000000 ≤ nleE - p' := by linarith
  have hz1 : nleE + (1 - H ((1 - nleQ) / 2)) ≤ 1 := by nlinarith
  have hslope := (Scalar.eta_convexOn_Ioc).slope_mono_adjacent
    (x := p') (z := nleE + (1 - H ((1 - nleQ) / 2))) ⟨hp'0, hp'1⟩ ⟨by linarith, hz1⟩
    (show p' < nleE by linarith) (show nleE < nleE + (1 - H ((1 - nleQ) / 2)) by linarith)
  rw [show nleE + (1 - H ((1 - nleQ) / 2)) - nleE = 1 - H ((1 - nleQ) / 2) by ring] at hslope
  rw [div_le_div_iff₀ hD hc0] at hslope
  -- numerator bound on the anchor gap
  have hN : eta p' - eta nleE ≤ 1000003 / 1000000 := by
    have h1 : eta p' ≤ 26 := by rw [hp']; exact eta_pow26_le
    have h2 := eta_nleE_ge
    linarith
  -- the chain
  have hX : (eta nleE - eta (nleE + (1 - H ((1 - nleQ) / 2)))) * (nleE - p') ≤
      (1000003 / 1000000) * nleQ ^ 2 := by
    nlinarith [hslope, hcq, hc0, hN]
  have hJ := J920_ge
  have hkey : (eta nleE - eta (nleE + (1 - H ((1 - nleQ) / 2)))) * (nleE - p') <
      (nleQ * J (9 / 20)) * (nleE - p') := by
    have hstep : (1000003 / 1000000 : ℝ) * nleQ ^ 2 < (nleQ * J (9 / 20)) * (nleE - p') := by
      have hsq : nleQ ^ 2 ≤ (79603 / 1000000000000 : ℝ) * nleQ := by
        nlinarith [mul_le_mul_of_nonneg_left hqle hq0.le]
      have hJ0 : (0:ℝ) ≤ nleQ * J (9 / 20) := mul_nonneg hq0.le (by linarith)
      have hB : (nleQ * (2895 / 10000 : ℝ)) * (37912 / 100000000000) ≤
          (nleQ * J (9 / 20)) * (nleE - p') :=
        mul_le_mul (mul_le_mul_of_nonneg_left hJ hq0.le) hDge (by norm_num) hJ0
      linarith
    linarith
  have hfinal : eta nleE - eta (nleE + (1 - H ((1 - nleQ) / 2))) < nleQ * J (9 / 20) :=
    lt_of_mul_lt_mul_right hkey hD.le
  unfold phi psi
  rw [habs, nle_F]
  have hpsi : nleE + 1 - H ((1 - nleQ) / 2) = nleE + (1 - H ((1 - nleQ) / 2)) := by ring
  rw [hpsi]
  linarith

#print axioms J_pow25_ge
#print axioms eta_nleE_ge
#print axioms eta_pow26_le
#print axioms nle_active


/-! ## 6. Generic `J` enclosures at dyadic ratios -/

theorem J_le_pow {u : ℝ} (k : ℕ) (hu0 : 0 < u) (hu1 : u < 1)
    (hub : (1 - u) / u ≤ 2 ^ k) : J u ≤ k := by
  have hpos : 0 < (1 - u) / u := div_pos (by linarith) hu0
  have h := Real.log_le_log hpos hub
  rw [Real.log_pow] at h
  unfold J
  rw [div_le_iff₀ log_two_pos']
  linarith

theorem J_ge_pow {u : ℝ} (k : ℕ) (hu0 : 0 < u) (hu1 : u < 1)
    (hlb : (2 : ℝ) ^ k ≤ (1 - u) / u) : (k : ℝ) ≤ J u := by
  have h := Real.log_le_log (by positivity) hlb
  rw [Real.log_pow] at h
  unfold J
  rw [le_div_iff₀ log_two_pos']
  linarith

/-! ## 7. The parent profile value at the witness -/

theorem nle_parentDefect_pos : 0 < 1 - H ((1 - nleQ) / 2) := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have h := H_strictMonoOn (a := (1 - nleQ) / 2) (b := 1 / 2)
    ⟨by linarith, by linarith⟩ ⟨by norm_num, le_rfl⟩ (by linarith)
  rw [H_half] at h
  linarith

theorem nle_parentDefect : 1 - H ((1 - nleQ) / 2) ≤ nleQ ^ 2 := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have h := H_gt_parabola (p := (1 - nleQ) / 2) (by linarith) (by linarith)
  nlinarith

theorem eta_pow24_ge : (2299 : ℝ) / 100 ≤ eta (H (1 / 16777216)) := by
  have h : eta (H (1 / 16777216)) = (1 - 2 * (1 / 16777216)) * J (1 / 16777216) :=
    Comparison.eta_H (by norm_num) (by norm_num)
  have hJ : (23 : ℝ) ≤ J (1 / 16777216) := by
    have := J_ge_pow (u := (1 / 16777216 : ℝ)) 23 (by norm_num) (by norm_num) (by norm_num)
    simpa using this
  rw [h]
  nlinarith

theorem eta_parent_ge : (2299 : ℝ) / 100 ≤ eta (nleE + (1 - H ((1 - nleQ) / 2))) := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have hc := nle_parentDefect
  have hc0 := nle_parentDefect_pos
  have hE0 : 0 < nleE := nleE_pos
  have hEle : nleE ≤ 78806 / 100000000000 := nleE_le
  have hB := H_pow24_ge
  have hA : nleE + (1 - H ((1 - nleQ) / 2)) ≤ H (1 / 16777216) := by nlinarith
  have hA0 : 0 < nleE + (1 - H ((1 - nleQ) / 2)) := by linarith
  have hA1 : nleE + (1 - H ((1 - nleQ) / 2)) ≤ 1 := by nlinarith
  have hB0 : 0 < H (1 / 16777216) := H_pos (by norm_num) (by norm_num)
  have hB1 : H (1 / 16777216) ≤ 1 := H_le_one _
  exact le_trans eta_pow24_ge (eta_antitoneOn ⟨hA0, hA1⟩ ⟨hB0, hB1⟩ hA)

/-! ## 8. The owner conclusion is violated at the witness

`v` is the small mean; the witness pair is `a = v - q`, `b = 1 - v`, so that
`H b = H v` exactly and `1 - a - b = q`.  `w` is the rational anchor used to
bound the child profile value from above. -/

theorem nle_violation {v w : ℝ}
    (hv0 : 0 < v) (hv2 : v < 1 / 2) (hvq : nleQ < v) (hHv : 1 / 100 ≤ H v)
    (hw0 : 0 < w) (hw2 : w < 1 / 2) (hHw : H w ≤ 1 - H v)
    (hanchor : (1 - 2 * w) * J w ≤ 4)
    (hcost : interiorCost (v - nleQ) (1 - v) ≤ 4) :
    interiorCost (v - nleQ) (1 - v) <
      residualPsiScalarBound (v - nleQ) (1 - v) nleE := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have hE0 : 0 < nleE := nleE_pos
  have hEle : nleE ≤ 78806 / 100000000000 := nleE_le
  have ha0 : 0 < v - nleQ := by linarith
  have ha2 : v - nleQ ≤ 1 / 2 := by linarith
  have hHb : H (1 - v) = H v := H_complement v
  have hHa : H (v - nleQ) ≤ H v :=
    H_strictMonoOn.monotoneOn ⟨ha0.le, ha2⟩ ⟨hv0.le, hv2.le⟩ (by linarith)
  have hHa0 : 0 ≤ H (v - nleQ) := H_nonneg ha0.le (by linarith)
  have hEcap : nleE ≤ (H (v - nleQ) + H (1 - v)) / 2 := by rw [hHb]; linarith
  obtain ⟨h1, h2⟩ := residualPsi_profile_args_mem hHa0 hE0 hEcap
  have hrp : residualPsiScalarBound (v - nleQ) (1 - v) nleE =
      Scalar.P (H ((v - nleQ + (1 - v)) / 2) - nleE) -
        (Scalar.P ((H (v - nleQ) + H (1 - v)) / 2 - nleE -
            max 0 ((H (v - nleQ) + H (1 - v)) / 2 - nleE - H (v - nleQ))) +
          Scalar.P ((H (v - nleQ) + H (1 - v)) / 2 - nleE +
            max 0 ((H (v - nleQ) + H (1 - v)) / 2 - nleE - H (v - nleQ)))) / 2 := rfl
  rw [hrp]
  -- the parent term
  have hmid : (v - nleQ + (1 - v)) / 2 = (1 - nleQ) / 2 := by ring
  have hPparent : Scalar.P (H ((v - nleQ + (1 - v)) / 2) - nleE) =
      eta (nleE + (1 - H ((1 - nleQ) / 2))) := by
    rw [hmid]
    show eta (1 - (H ((1 - nleQ) / 2) - nleE)) = eta (nleE + (1 - H ((1 - nleQ) / 2)))
    ring_nf
  -- the child terms
  have hPa : Scalar.P ((H (v - nleQ) + H (1 - v)) / 2 - nleE -
      max 0 ((H (v - nleQ) + H (1 - v)) / 2 - nleE - H (v - nleQ))) =
      eta (1 - ((H (v - nleQ) + H (1 - v)) / 2 - nleE -
        max 0 ((H (v - nleQ) + H (1 - v)) / 2 - nleE - H (v - nleQ)))) := rfl
  have hPb : Scalar.P ((H (v - nleQ) + H (1 - v)) / 2 - nleE +
      max 0 ((H (v - nleQ) + H (1 - v)) / 2 - nleE - H (v - nleQ))) =
      eta (1 - ((H (v - nleQ) + H (1 - v)) / 2 - nleE +
        max 0 ((H (v - nleQ) + H (1 - v)) / 2 - nleE - H (v - nleQ)))) := rfl
  rw [hPparent, hPa, hPb]
  -- the ordering of the two child arguments
  have hR0 : 0 ≤ max 0 ((H (v - nleQ) + H (1 - v)) / 2 - nleE - H (v - nleQ)) := le_max_left _ _
  have hmem1 : (1 - ((H (v - nleQ) + H (1 - v)) / 2 - nleE -
      max 0 ((H (v - nleQ) + H (1 - v)) / 2 - nleE - H (v - nleQ)))) ∈ Ioc (0:ℝ) 1 :=
    ⟨by linarith [h1.1, h1.2], by linarith [h1.1]⟩
  have hmem2 : (1 - ((H (v - nleQ) + H (1 - v)) / 2 - nleE +
      max 0 ((H (v - nleQ) + H (1 - v)) / 2 - nleE - H (v - nleQ)))) ∈ Ioc (0:ℝ) 1 :=
    ⟨by linarith [h2.1, h2.2], by linarith [h2.1]⟩
  have hanti := eta_antitoneOn hmem2 hmem1 (by linarith)
  -- the child profile value is at most 4
  have hwmem : H w ∈ Ioc (0:ℝ) 1 := ⟨H_pos hw0 (by linarith), H_le_one _⟩
  have hHwle : H w ≤ 1 - ((H (v - nleQ) + H (1 - v)) / 2 - nleE +
      max 0 ((H (v - nleQ) + H (1 - v)) / 2 - nleE - H (v - nleQ))) := by
    rcases le_total ((H (v - nleQ) + H (1 - v)) / 2 - nleE - H (v - nleQ)) 0 with hc | hc
    · rw [max_eq_left hc, hHb]
      linarith
    · rw [max_eq_right hc, hHb]
      linarith
  have hchild : eta (1 - ((H (v - nleQ) + H (1 - v)) / 2 - nleE +
      max 0 ((H (v - nleQ) + H (1 - v)) / 2 - nleE - H (v - nleQ)))) ≤ 4 := by
    have hetaw : eta (H w) = (1 - 2 * w) * J w := Comparison.eta_H hw0 hw2
    have := eta_antitoneOn hwmem hmem2 hHwle
    rw [hetaw] at this
    linarith
  have hparent := eta_parent_ge
  linarith

#print axioms J_le_pow
#print axioms J_ge_pow
#print axioms nle_parentDefect
#print axioms eta_parent_ge
#print axioms nle_violation


/-! ## 9. The refutations

The witness is `a = v - q`, `b = 1 - v`, `E = H (2⁻²⁵)`, with `v = 1/16` for the
low-entropy regions and `v = 1/8` for the central region.  Every hypothesis of
`ResidualPsiScalarOwner` is verified, including the psi-active one, and the
conclusion fails. -/

theorem nle_witness_H16 : (1 : ℝ) / 100 ≤ H (1 / 16) := by
  have h := H_gt_parabola (p := (1 / 16 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h
  linarith

theorem nle_witness_H8 : (1 : ℝ) / 100 ≤ H (1 / 8) := by
  have h := H_gt_parabola (p := (1 / 8 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h
  linarith

theorem J_sixteenth_le : J (1 / 16 : ℝ) ≤ 4 := by
  have := J_le_pow (u := (1 / 16 : ℝ)) 4 (by norm_num) (by norm_num) (by norm_num)
  simpa using this

theorem J_eighth_le : J (1 / 8 : ℝ) ≤ 3 := by
  have := J_le_pow (u := (1 / 8 : ℝ)) 3 (by norm_num) (by norm_num) (by norm_num)
  simpa using this

theorem J_sixteenth_shift_le : J (1 / 16 - nleQ) ≤ 4 := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have hu : (0:ℝ) < 1 / 16 - nleQ := by linarith
  have hb : (1 - (1 / 16 - nleQ)) / (1 / 16 - nleQ) ≤ 2 ^ (4:ℕ) := by
    rw [div_le_iff₀ hu]
    norm_num
    linarith
  have := J_le_pow (u := (1 / 16 - nleQ)) 4 hu (by linarith) hb
  simpa using this

theorem J_eighth_shift_le : J (1 / 8 - nleQ) ≤ 3 := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have hu : (0:ℝ) < 1 / 8 - nleQ := by linarith
  have hb : (1 - (1 / 8 - nleQ)) / (1 / 8 - nleQ) ≤ 2 ^ (3:ℕ) := by
    rw [div_le_iff₀ hu]
    norm_num
    linarith
  have := J_le_pow (u := (1 / 8 - nleQ)) 3 hu (by linarith) hb
  simpa using this

theorem nle_cost16 : interiorCost (1 / 16 - nleQ) (1 - 1 / 16) ≤ 4 := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have hJb : J (1 - 1 / 16 : ℝ) = - J (1 / 16 : ℝ) := J_complement _
  have hJ16 := J_sixteenth_le
  have hJa := J_sixteenth_shift_le
  unfold interiorCost
  rw [hJb]
  nlinarith [hJa, hJ16, hq0, hqle]

theorem nle_cost8 : interiorCost (1 / 8 - nleQ) (1 - 1 / 8) ≤ 4 := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have hJb : J (1 - 1 / 8 : ℝ) = - J (1 / 8 : ℝ) := J_complement _
  have hJ8 := J_eighth_le
  have hJa := J_eighth_shift_le
  unfold interiorCost
  rw [hJb]
  nlinarith [hJa, hJ8, hq0, hqle]

theorem nle_anchor16 : (1 - 2 * (1 / 8 : ℝ)) * J (1 / 8) ≤ 4 := by
  nlinarith [J_eighth_le, J_nonneg (v := (1/8 : ℝ)) (by norm_num) (by norm_num)]

theorem nle_anchor8 : (1 - 2 * (1 / 16 : ℝ)) * J (1 / 16) ≤ 4 := by
  nlinarith [J_sixteenth_le, J_nonneg (v := (1/16 : ℝ)) (by norm_num) (by norm_num)]

theorem nle_violation16 :
    interiorCost (1 / 16 - nleQ) (1 - 1 / 16) <
      residualPsiScalarBound (1 / 16 - nleQ) (1 - 1 / 16) nleE := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  exact nle_violation (v := 1 / 16) (w := 1 / 8) (by norm_num) (by norm_num)
    (by linarith) nle_witness_H16 (by norm_num) (by norm_num)
    (by linarith [H_eighth_le, H_sixteenth_le]) nle_anchor16 nle_cost16

theorem nle_violation8 :
    interiorCost (1 / 8 - nleQ) (1 - 1 / 8) <
      residualPsiScalarBound (1 / 8 - nleQ) (1 - 1 / 8) nleE := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  exact nle_violation (v := 1 / 8) (w := 1 / 16) (by norm_num) (by norm_num)
    (by linarith) nle_witness_H8 (by norm_num) (by norm_num)
    (by linarith [H_eighth_le, H_sixteenth_le]) nle_anchor8 nle_cost8

/-- Every `ResidualPsiScalarOwner` hypothesis at the `v`-witness. -/
theorem nle_owner_hypotheses {v : ℝ} (hv0 : 0 < v) (hv2 : v < 1 / 2)
    (hHv : 1 / 100 ≤ H v) (hvq : (1:ℝ)/100 < v) :
    0 < v - nleQ ∧ v - nleQ < 1 - v ∧ (1 : ℝ) - v < 1 ∧
      (v - nleQ) + (1 - v) ≤ 1 ∧ 0 < nleE ∧
      nleE ≤ (H (v - nleQ) + H (1 - v)) / 2 ∧
      1 / 16 < (v - nleQ) + (1 - v) ∧
      1 / 100 < H (((v - nleQ) + (1 - v)) / 2) - nleE ∧
      phi (((v - nleQ) + (1 - v)) / 2) nleE < psi (((v - nleQ) + (1 - v)) / 2) nleE := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have hE0 : 0 < nleE := nleE_pos
  have hEle : nleE ≤ 78806 / 100000000000 := nleE_le
  have ha0 : 0 < v - nleQ := by linarith
  have hHb : H (1 - v) = H v := H_complement v
  have hHa0 : 0 ≤ H (v - nleQ) := H_nonneg ha0.le (by linarith)
  have hmid : ((v - nleQ) + (1 - v)) / 2 = (1 - nleQ) / 2 := by ring
  have hq2 : nleQ ^ 2 ≤ 1 / 100 := by nlinarith
  refine ⟨ha0, by linarith, by linarith, by linarith, hE0, ?_, by linarith, ?_, ?_⟩
  · rw [hHb]; linarith
  · rw [hmid]; linarith [nle_parentDefect]
  · exact nle_active hmid

theorem not_residualPsiScalarOwner_normalizedLowEntropy :
    ¬ ResidualPsiScalarOwner normalizedLowEntropyResidualRegion := by
  intro hown
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have hEle : nleE ≤ 78806 / 100000000000 := nleE_le
  have hEge : (78805 : ℝ) / 100000000000 ≤ nleE := nleE_ge
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    nle_owner_hypotheses (v := 1 / 16) (by norm_num) (by norm_num) nle_witness_H16 (by norm_num)
  have hregion : normalizedLowEntropyResidualRegion (1 / 16 - nleQ) (1 - 1 / 16) nleE :=
    ⟨by norm_num, by linarith, by linarith⟩
  have hconc := hown (1 / 16 - nleQ) (1 - 1 / 16) nleE h1 h2 h3 h4 h5 h6 h7 h8 hregion h9
  linarith [nle_violation16]

theorem not_residualPsiScalarOwner_oppositeLowEntropy :
    ¬ ResidualPsiScalarOwner oppositeLowEntropyResidualRegion := by
  intro hown
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have hEle : nleE ≤ 78806 / 100000000000 := nleE_le
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    nle_owner_hypotheses (v := 1 / 16) (by norm_num) (by norm_num) nle_witness_H16 (by norm_num)
  have hregion : oppositeLowEntropyResidualRegion (1 / 16 - nleQ) (1 - 1 / 16) nleE :=
    ⟨by norm_num, by linarith⟩
  have hconc := hown (1 / 16 - nleQ) (1 - 1 / 16) nleE h1 h2 h3 h4 h5 h6 h7 h8 hregion h9
  linarith [nle_violation16]

theorem not_residualPsiScalarOwner_oppositeCentral :
    ¬ ResidualPsiScalarOwner oppositeCentralResidualRegion := by
  intro hown
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    nle_owner_hypotheses (v := 1 / 8) (by norm_num) (by norm_num) nle_witness_H8 (by norm_num)
  have hregion : oppositeCentralResidualRegion (1 / 8 - nleQ) (1 - 1 / 8) nleE :=
    ⟨by norm_num, by linarith⟩
  have hconc := hown (1 / 8 - nleQ) (1 - 1 / 8) nleE h1 h2 h3 h4 h5 h6 h7 h8 hregion h9
  linarith [nle_violation8]

#print axioms nle_cost16
#print axioms nle_violation16
#print axioms nle_violation8
#print axioms not_residualPsiScalarOwner_normalizedLowEntropy
#print axioms not_residualPsiScalarOwner_oppositeLowEntropy
#print axioms not_residualPsiScalarOwner_oppositeCentral


/-! ## 10. The reduction layer and the exact partition

These are the two structural statements branch 4 was asked for.  They are
independent of the refutation above and remain valid. -/

/-- **Reduction layer.**  The three-variable bound written purely in `eta`:
the parent term is `eta` at `E + C q` with `C q = 1 - H m`, and the child term
is `eta` at the average child deficit `E + (1 - (H a + H b)/2)`, displaced by
the forced imbalance `max 0 ((H a + H b)/2 - E - H a)`. -/
theorem residualPsiScalarBound_eq_eta (a b E : ℝ) :
    residualPsiScalarBound a b E =
      eta (E + (1 - H ((a + b) / 2))) -
        (eta (E + (1 - (H a + H b) / 2) + max 0 ((H a + H b) / 2 - E - H a)) +
          eta (E + (1 - (H a + H b) / 2) - max 0 ((H a + H b) / 2 - E - H a))) / 2 := by
  have h1 : (1:ℝ) - (H ((a + b) / 2) - E) = E + (1 - H ((a + b) / 2)) := by ring
  have h2 : (1:ℝ) - ((H a + H b) / 2 - E - max 0 ((H a + H b) / 2 - E - H a)) =
      E + (1 - (H a + H b) / 2) + max 0 ((H a + H b) / 2 - E - H a) := by ring
  have h3 : (1:ℝ) - ((H a + H b) / 2 - E + max 0 ((H a + H b) / 2 - E - H a)) =
      E + (1 - (H a + H b) / 2) - max 0 ((H a + H b) / 2 - E - H a) := by ring
  show eta (1 - (H ((a + b) / 2) - E)) -
      (eta (1 - ((H a + H b) / 2 - E - max 0 ((H a + H b) / 2 - E - H a))) +
        eta (1 - ((H a + H b) / 2 - E + max 0 ((H a + H b) / 2 - E - H a)))) / 2 = _
  rw [h1, h2, h3]

/-- The complementary leaf of branch 4 inside the low-entropy region. -/
def highRatioLowEntropyResidualRegion (a b E : ℝ) : Prop :=
  1 / 2 ≤ b ∧ E ≤ 1 / 1000000 ∧ 8 * E < 1 - a - b

/-- **Exact binary partition coverage.**  The two leaves `q ≤ 8E` and `q > 8E`
cover `oppositeLowEntropyResidualRegion` exactly: their union is the whole
region, not merely a subset of it. -/
theorem oppositeLowEntropy_cover (a b E : ℝ) :
    oppositeLowEntropyResidualRegion a b E ↔
      (normalizedLowEntropyResidualRegion a b E ∨
        highRatioLowEntropyResidualRegion a b E) := by
  constructor
  · rintro ⟨hb, hE⟩
    rcases le_total (1 - a - b) (8 * E) with h | h
    · exact Or.inl ⟨hb, hE, h⟩
    · rcases eq_or_lt_of_le h with h' | h'
      · exact Or.inl ⟨hb, hE, h'.ge⟩
      · exact Or.inr ⟨hb, hE, h'⟩
  · rintro (⟨hb, hE, _⟩ | ⟨hb, hE, _⟩) <;> exact ⟨hb, hE⟩

/-- **The two leaves are disjoint**, and the shared endpoint `1 - a - b = 8E`
belongs to the normalized leaf. -/
theorem lowEntropy_leaves_disjoint (a b E : ℝ) :
    ¬ (normalizedLowEntropyResidualRegion a b E ∧
        highRatioLowEntropyResidualRegion a b E) := by
  rintro ⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩
  linarith

theorem lowEntropy_endpoint_in_normalized {a b E : ℝ}
    (hb : 1 / 2 ≤ b) (hE : E ≤ 1 / 1000000) (heq : 1 - a - b = 8 * E) :
    normalizedLowEntropyResidualRegion a b E := ⟨hb, hE, heq.le⟩

/-- **The complementary leaf is vacuous**, given the retained factor-eight
parent criterion: on `q > 8E` (with `0 < q ≤ 2/5`) the parent is phi-dominated,
contradicting the psi-active hypothesis carried by `ResidualPsiScalarOwner`.
So branch 4 really is the only analytic content in the low-entropy region —
which is exactly why its failure is fatal for the low-entropy owner. -/
theorem highRatio_vacuous (hP : ParentEightDominance) {a b E : ℝ}
    (hE : 0 < E) (hq : 0 < 1 - a - b) (hq25 : 1 - a - b ≤ 2 / 5)
    (hregion : highRatioLowEntropyResidualRegion a b E)
    (hactive : phi ((a + b) / 2) E < psi ((a + b) / 2) E) : False := by
  obtain ⟨_, _, h8⟩ := hregion
  exact absurd (psi_lt_phi_of_parentEight hP hE hq hq25 (by linarith))
    (not_lt.2 hactive.le)

/-- The refuting witness lies in the **normalized** leaf, i.e. strictly inside
branch 4, not in the complementary leaf. -/
theorem nle_witness_in_normalized :
    normalizedLowEntropyResidualRegion (1 / 16 - nleQ) (1 - 1 / 16) nleE ∧
      ¬ highRatioLowEntropyResidualRegion (1 / 16 - nleQ) (1 - 1 / 16) nleE := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have hEge : (78805 : ℝ) / 100000000000 ≤ nleE := nleE_ge
  have hEle : nleE ≤ 78806 / 100000000000 := nleE_le
  refine ⟨⟨by norm_num, by linarith, by linarith⟩, ?_⟩
  rintro ⟨-, -, h⟩
  linarith

#print axioms residualPsiScalarBound_eq_eta
#print axioms oppositeLowEntropy_cover
#print axioms lowEntropy_leaves_disjoint
#print axioms lowEntropy_endpoint_in_normalized
#print axioms highRatio_vacuous
#print axioms nle_witness_in_normalized

#print axioms log_two_lower
#print axioms log_two_upper
#print axioms log_eleven_ninths_lower

end GeneralCK

end


