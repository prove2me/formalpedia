-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailCoupling
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailCoupling
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T20:42:04.664348+00:00
-- url     : https://prove2.me/theorems/8a006f94-3fd3-482b-8665-e48da57d17a7
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailCoupling` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailCoupling` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailCoupling` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailCoupling (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailCoupling.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapSlopeCertificate
import Definitions.Def_CK_GeneralCK_ReflectionDiagonalPositive_v2
import Definitions.Def_CK_GeneralCK_CorrectionHessianNatural

-- ===== source module GeneralCK.PureGapDoubleCapLowTailCoupling =====
section

/-!
# Exact bias coupling on the low double-cap tail

This module isolates the entropy-inverse/contact coupling at the canonical
low entropy floor. It proves no residual or slope sign. The source is a
draft until an independent Lean compile and axiom audit have passed.
-/

namespace GeneralCK
open Certificates.Reflection Reflection

noncomputable def doubleCapLowTailY (m : ℝ) : ℝ :=
  1 - 2 * entropyInverse (H (2 * m) / 2)

noncomputable def doubleCapLowTailC (m : ℝ) : ℝ :=
  regularContact ((1 - 2 * m) / biasE (doubleCapLowTailY m))

theorem doubleCapLowTailY_entropy {m : ℝ}
    (hm : 0 < m) (hmq : m ≤ 1 / 4) :
    biasE (doubleCapLowTailY m) = Real.log 2 * (H (2 * m) / 2) := by
  have hh : 0 < H (2 * m) / 2 :=
    div_pos (H_pos (by linarith) (by linarith)) two_pos
  have hh1 : H (2 * m) / 2 < 1 :=
    (doubleCapLowFloor_lt_entropyCap hm hmq).trans_le (H_le_one m)
  have hv : 0 < entropyInverse (H (2 * m) / 2) :=
    entropyInverse_pos hh hh1.le
  have hv1 : entropyInverse (H (2 * m) / 2) < 1 := by
    linarith [entropyInverse_lt_half hh.le hh1]
  have hspec := (entropyInverse_spec hh.le hh1.le).2.2
  unfold doubleCapLowTailY
  rw [Correction.Natural.biasE_probability hv hv1,
    Certificates.Mixed.hn_eq_H_mul_log, hspec]
  ring

theorem doubleCapLowTailX_entropy {m : ℝ}
    (hm : 0 < m) (hmq : m ≤ 1 / 4) :
    biasE (1 - 4 * m) = 2 * biasE (doubleCapLowTailY m) := by
  have h2m : 0 < 2 * m := by linarith
  have h2m1 : 2 * m < 1 := by linarith
  have hy := doubleCapLowTailY_entropy hm hmq
  calc
    biasE (1 - 4 * m) = biasE (1 - 2 * (2 * m)) := by congr 1; ring
    _ = Certificates.Mixed.hn (2 * m) :=
      Correction.Natural.biasE_probability h2m h2m1
    _ = H (2 * m) * Real.log 2 :=
      Certificates.Mixed.hn_eq_H_mul_log (2 * m)
    _ = 2 * biasE (doubleCapLowTailY m) := by rw [hy]; ring

theorem doubleCapLowTailC_physical {m : ℝ}
    (hm : 0 < m) (hmq : m ≤ 1 / 4) :
    doubleCapLowTailC m =
      regularContact (((1 - 2 * m) / (H (2 * m) / 2)) / Real.log 2) := by
  have hh : 0 < H (2 * m) / 2 :=
    div_pos (H_pos (by linarith) (by linarith)) two_pos
  have hy := doubleCapLowTailY_entropy hm hmq
  unfold doubleCapLowTailC
  rw [hy]
  congr 1
  field_simp [hh.ne', log_two_pos.ne']

theorem doubleCapLowTailC_entropy_equation {m : ℝ}
    (hm : 0 < m) (hmq : m ≤ 1 / 4) :
    biasE (doubleCapLowTailC m) =
      doubleCapLowTailC m * biasE (doubleCapLowTailY m) / (1 - 2 * m) := by
  have hk : 0 < 1 - 2 * m := by linarith
  have hy := doubleCapLowTailY_entropy hm hmq
  have hEy : 0 < biasE (doubleCapLowTailY m) := by
    rw [hy]
    exact mul_pos log_two_pos
      (div_pos (H_pos (by linarith) (by linarith)) two_pos)
  have hc := regularContact_equation
    ((1 - 2 * m) / biasE (doubleCapLowTailY m))
  change doubleCapLowTailC m =
    ((1 - 2 * m) / biasE (doubleCapLowTailY m)) *
      biasE (doubleCapLowTailC m) at hc
  apply (eq_div_iff hk.ne').2
  field_simp [hk.ne', hEy.ne'] at hc ⊢
  nlinarith [hc]

/-- The true contact lies strictly between the mean bias and the inverse-
entropy bias. This ordering by itself is not enough for the slope sign. -/
theorem doubleCapLowTailC_between {m : ℝ}
    (hm : 0 < m) (hmq : m ≤ 1 / 4) :
    1 - 2 * m < doubleCapLowTailC m ∧
      doubleCapLowTailC m < doubleCapLowTailY m := by
  let k : ℝ := 1 - 2 * m
  let y : ℝ := doubleCapLowTailY m
  let c : ℝ := doubleCapLowTailC m
  have hk0 : 0 < k := by dsimp [k]; linarith
  have hk1 : k < 1 := by dsimp [k]; linarith
  have hh : 0 < H (2 * m) / 2 :=
    div_pos (H_pos (by linarith) (by linarith)) two_pos
  have hcap := doubleCapLowFloor_lt_entropyCap hm hmq
  have hh1 : H (2 * m) / 2 < 1 := hcap.trans_le (H_le_one m)
  have hv := entropyInverse_spec hh.le hh1.le
  have hvm : entropyInverse (H (2 * m) / 2) < m := by
    by_contra hn
    have hmv : m ≤ entropyInverse (H (2 * m) / 2) := le_of_not_gt hn
    have hHle : H m ≤ H (entropyInverse (H (2 * m) / 2)) :=
      H_strictMonoOn.monotoneOn
        ⟨hm.le, by linarith⟩ ⟨hv.1, hv.2.1⟩ hmv
    linarith [hv.2.2]
  have hky : k < y := by dsimp [k, y, doubleCapLowTailY]; linarith
  have hy1 : y < 1 := by
    dsimp [y, doubleCapLowTailY]
    linarith [entropyInverse_pos hh hh1.le]
  have hEk := Correction.Natural.biasE_probability hm (by linarith : m < 1)
  rw [Certificates.Mixed.hn_eq_H_mul_log] at hEk
  have hEy0 := doubleCapLowTailY_entropy hm hmq
  have hEy : 0 < biasE y := by
    dsimp [y]
    rw [hEy0]
    exact mul_pos log_two_pos hh
  have hEkpos : 0 < biasE k := by
    dsimp [k]
    rw [hEk]
    exact mul_pos (H_pos hm (by linarith)) log_two_pos
  have hEyEk : biasE y < biasE k := by
    dsimp [k, y]
    rw [hEk, hEy0]
    have h := mul_lt_mul_of_pos_right hcap log_two_pos
    nlinarith [h]
  have hcMem := regularContact_mem (k / biasE y)
  have hcEq : regularRatio c = k / biasE y := by
    dsimp [c, doubleCapLowTailC, k, y]
    exact regularRatio_regularContact _
  have hkRatio : regularRatio k < k / biasE y := by
    unfold regularRatio
    exact (div_lt_div_iff₀ hEkpos hEy).2 (by nlinarith [hEyEk, hk0])
  have hyRatio : k / biasE y < regularRatio y := by
    unfold regularRatio
    exact (div_lt_div_iff₀ hEy hEy).2 (by nlinarith [hky, hEy])
  have hkMem : k ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hk1⟩
  have hyMem : y ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hy1⟩
  have hmono := regularRatio_strictMonoOn.monotoneOn
  have hkc : k < c := by
    by_contra hn
    have hck : c ≤ k := le_of_not_gt hn
    have hle := hmono hcMem hkMem hck
    change regularRatio c ≤ regularRatio k at hle
    rw [hcEq] at hle
    linarith
  have hcy : c < y := by
    by_contra hn
    have hyc : y ≤ c := le_of_not_gt hn
    have hle := hmono hyMem hcMem hyc
    change regularRatio y ≤ regularRatio c at hle
    rw [hcEq] at hle
    linarith
  exact ⟨hkc, hcy⟩

#print axioms doubleCapLowTailY_entropy
#print axioms doubleCapLowTailX_entropy
#print axioms doubleCapLowTailC_physical
#print axioms doubleCapLowTailC_entropy_equation
#print axioms doubleCapLowTailC_between

end GeneralCK

end


