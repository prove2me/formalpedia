-- Prove2me | Definitions.Def_CK_GeneralCK_PsiLowEntropyLeafReplay
-- name    : CK_GeneralCK_PsiLowEntropyLeafReplay
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:55:45.724954+00:00
-- url     : https://prove2.me/theorems/43977a5a-4304-4a88-8406-19c9525ebae1
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiLowEntropyLeafReplay` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiLowEntropyLeafReplay` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiLowEntropyLeafReplay` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiLowEntropyLeafReplay (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiLowEntropyLeafReplay.lean)

import Definitions.Def_CK_GeneralCK_PsiScalarOwnerCore
import Definitions.Def_CK_GeneralCK_EtaMonotone
import Definitions.Def_CK_GeneralCK_Certificates_LogBounds

-- ===== source module GeneralCK.PsiLowEntropyLeafReplay =====
section

/-!
# The five global-low-entropy leaves: exact endpoints, exact coverage, certified margin

This file is the Lean replacement for the archived discovery script
`cluster/active_psi_scalar_plan/source/residual/GLOBAL_LOW_ENTROPY.py`.
The archived Python/JSON records are *not* used as evidence anywhere below:
only the binary path words `0, 10, 110, 1110, 1111` and the root interval
`[2/5, 15/16]` are transcribed, and the rational endpoints are then
reconstructed here by exact bisection (`box`).

What is proved:

* `leaves_eq` — the five archived paths bisect `[2/5, 15/16]` into five
  intervals with *exact* rational endpoints.
* `leaves_endpoints` — the left endpoint of the first leaf is `2/5`, the right
  endpoint of the last leaf is `15/16`, and every pair of adjacent endpoints
  coincides exactly (so the cover has no gap and no overlap of interiors).
* `leaves_cover` — an `Iff`: a real `q` lies in `[2/5, 15/16]` **iff** it lies
  in one of the five leaves.  This is exact coverage, not a per-leaf bound.
* `margin_leaf0 … margin_leaf4` — on each leaf,
  `K(l) + 1/10 ≤ A_h(10⁻⁶)`, where `A` and `K` are the archived parent test
  functions.  Every transcendental quantity (`Real.log`, `H`, `J`, `eta`) is
  bounded by kernel-checked rational enclosures coming from
  `GeneralCK.Certificates.checkLog_sound` (the Taylor series for
  `log ((1+w)/(1-w))` with an exactly summed rational remainder).
* `psi_add_margin_le_lowEntropyA` — assembling monotonicity in `q` and in `E`
  with the five leaf margins: for `q ∈ [2/5, 15/16]` and `0 < E ≤ 10⁻⁶`,
  `psi ((1-q)/2) E + 1/10 ≤ A_q(E)`.
* `not_activePsi_of_parentLowerBound` — the phase-2 consumption shape: given
  the (separately owned) parent lower bound `A_q(E) ≤ phi ((a+b)/2) E`, the
  hypothesis `phi ((a+b)/2) E < psi ((a+b)/2) E` of `ResidualPsiScalarOwner`
  is contradictory on this range.

The certified margin proved here is `1/10`.  The archived discovery figure is
`0.108344815058…`; the rational lower bound actually certified for the worst
leaf is `alo4 - kub4` (see `margin_leaf4`), which is ``169065717022113/1562500000000000`` — this is
smaller than the discovery figure because the archived checker uses the exact
entropy inverse whereas the proof below uses an explicit rational witness
`v = 1/5` for it.

NOT proved here, and deliberately left as an explicit hypothesis:
the parent lower bound `A_q(E) ≤ phi ((a+b)/2) E`, and the small-mean,
normalized-low-entropy and parent-dominance cases that
`GLOBAL_LOW_ENTROPY_PROOF.md` also imports.  This file alone does **not**
establish the low-entropy owner.
-/

namespace GeneralCK
namespace LowEntropyLeaf

open scoped BigOperators

/-! ## §0  The archived parent test, transcribed -/

/-- `A_q(E) = (1 - q - E) · log₂((2 - E)/E)`, the archived parent lower bound. -/
noncomputable def lowEntropyA (qq E : ℝ) : ℝ :=
  (1 - qq - E) * (Real.log ((2 - E) / E) / Real.log 2)

/-- `K(q) = η(1 - H((1-q)/2))`, the archived parent upper bound for `psi`. -/
noncomputable def lowEntropyK (qq : ℝ) : ℝ := eta (1 - H ((1 - qq) / 2))

/-! ## §1  Exact reconstruction of the five leaves from the archived paths -/

/-- One exact bisection step on a closed rational interval. -/
def bisect (r : ℚ × ℚ) (b : Bool) : ℚ × ℚ :=
  if b then ((r.1 + r.2) / 2, r.2) else (r.1, (r.1 + r.2) / 2)

/-- The archived root interval `[2/5, 15/16]`. -/
def root : ℚ × ℚ := (2 / 5, 15 / 16)

/-- The box of a binary path word, reconstructed by exact rational bisection. -/
def box (p : List Bool) : ℚ × ℚ := p.foldl bisect root

/-- The five archived path words `0, 10, 110, 1110, 1111`. -/
def paths : List (List Bool) :=
  [[false], [true, false], [true, true, false],
   [true, true, true, false], [true, true, true, true]]

/-- The five leaves. -/
def leaves : List (ℚ × ℚ) := paths.map box

theorem leaves_eq :
    leaves = [(2 / 5, 107 / 160), (107 / 160, 257 / 320), (257 / 320, 557 / 640),
      (557 / 640, 1157 / 1280), (1157 / 1280, 15 / 16)] := by
  norm_num [leaves, paths, box, bisect, root]

/-- Exact endpoint matching: first endpoint, last endpoint, and every adjacent
pair coincide.  Together with `leaves_cover` this is the complete
binary-partition statement. -/
theorem leaves_endpoints :
    (box [false]).1 = 2 / 5 ∧
    (box [false]).2 = (box [true, false]).1 ∧
    (box [true, false]).2 = (box [true, true, false]).1 ∧
    (box [true, true, false]).2 = (box [true, true, true, false]).1 ∧
    (box [true, true, true, false]).2 = (box [true, true, true, true]).1 ∧
    (box [true, true, true, true]).2 = 15 / 16 := by
  norm_num [box, bisect, root]

/-- Exact coverage of the root interval by the five leaves. -/
theorem leaves_cover (x : ℝ) :
    ((2 / 5 : ℝ) ≤ x ∧ x ≤ 15 / 16) ↔
      ∃ lh ∈ leaves, ((lh.1 : ℚ) : ℝ) ≤ x ∧ x ≤ ((lh.2 : ℚ) : ℝ) := by
  rw [leaves_eq]
  constructor
  · rintro ⟨h1, h2⟩
    rcases le_or_gt x (107 / 160 : ℝ) with ha | ha
    · exact ⟨(2 / 5, 107 / 160), by simp, by norm_num; constructor <;> linarith⟩
    rcases le_or_gt x (257 / 320 : ℝ) with hb | hb
    · exact ⟨(107 / 160, 257 / 320), by simp, by norm_num; constructor <;> linarith⟩
    rcases le_or_gt x (557 / 640 : ℝ) with hc | hc
    · exact ⟨(257 / 320, 557 / 640), by simp, by norm_num; constructor <;> linarith⟩
    rcases le_or_gt x (1157 / 1280 : ℝ) with hd | hd
    · exact ⟨(557 / 640, 1157 / 1280), by simp, by norm_num; constructor <;> linarith⟩
    · exact ⟨(1157 / 1280, 15 / 16), by simp, by norm_num; constructor <;> linarith⟩
  · rintro ⟨lh, hmem, hl, hr⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl <;>
      (norm_num at hl hr; constructor <;> linarith)

/-- The union of the five leaves is *exactly* the archived root interval. -/
theorem leaves_iUnion :
    (⋃ lh ∈ leaves, Set.Icc ((lh.1 : ℚ) : ℝ) ((lh.2 : ℚ) : ℝ))
      = Set.Icc (2 / 5 : ℝ) (15 / 16) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Icc, exists_prop]
  exact (leaves_cover x).symm

/-! ## §2  Generic rational enclosure helpers -/

theorem log_scale (s : ℝ) (k : ℕ) (hs : 0 < s) :
    Real.log ((2 : ℝ) ^ k * s) = (k : ℝ) * Real.log 2 + Real.log s := by
  rw [Real.log_mul (by positivity) (ne_of_gt hs), Real.log_pow]

theorem log_one_div (x : ℝ) : Real.log (1 / x) = -Real.log x := by simp [one_div]

/-- Upper bound for `H p` from upper bounds on `-log p` and `-log (1-p)`. -/
theorem H_le_of (p lp l1p X : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hlp : -Real.log p ≤ lp) (hl1p : -Real.log (1 - p) ≤ l1p)
    (hX : p * lp + (1 - p) * l1p ≤ X * Real.log 2) : H p ≤ X := by
  have h2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have hb : Real.binEntropy p = p * (-Real.log p) + (1 - p) * (-Real.log (1 - p)) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
  have e1 : p * (-Real.log p) ≤ p * lp := mul_le_mul_of_nonneg_left hlp hp0
  have e2 : (1 - p) * (-Real.log (1 - p)) ≤ (1 - p) * l1p :=
    mul_le_mul_of_nonneg_left hl1p (by linarith)
  rw [H, div_le_iff₀ h2, hb]
  linarith

/-- Upper bound for `J v` from an upper bound on `-log (v/(1-v))`. -/
theorem J_le_of (v lj X : ℝ) (_hv : 0 < v) (_hv1 : v < 1)
    (hlj : -Real.log (v / (1 - v)) ≤ lj) (hX : lj ≤ X * Real.log 2) : J v ≤ X := by
  have h2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have he : Real.log ((1 - v) / v) = -Real.log (v / (1 - v)) := by
    rw [← Real.log_inv, inv_div]
  rw [J, div_le_iff₀ h2, he]
  linarith

/-- `eta h ≤ (1 - 2v)·X` from a rational witness `v` with `H v ≤ h` and
`J v ≤ X`.  This is the only place where the entropy inverse is used, and it
is used monotonically, never evaluated. -/
theorem eta_le_of_witness (h v X : ℝ) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hv0 : 0 < v) (hv1 : v ≤ 1 / 2) (hHv : H v ≤ h) (hJ : J v ≤ X) (_hX : 0 ≤ X) :
    eta h ≤ (1 - 2 * v) * X := by
  have hspec := entropyInverse_spec hh0.le hh1
  have hu0 : 0 < entropyInverse h := entropyInverse_pos hh0 hh1
  have hu1 : entropyInverse h ≤ 1 / 2 := hspec.2.1
  have hvu : v ≤ entropyInverse h := by
    have hmono := entropyInverse_mono (H_nonneg hv0.le (by linarith)) hh1 hHv
    rwa [entropyInverse_H_lower hv0.le hv1] at hmono
  have hJu : J (entropyInverse h) ≤ J v := J_antitone hv0 hu1 hvu
  have hJu0 : 0 ≤ J (entropyInverse h) := J_nonneg hu0 hu1
  rw [eta_eq_profile hh0.le hh1]
  calc (1 - 2 * entropyInverse h) * J (entropyInverse h)
      ≤ (1 - 2 * v) * J v := mul_le_mul (by linarith) hJu hJu0 (by linarith)
    _ ≤ (1 - 2 * v) * X := mul_le_mul_of_nonneg_left hJ (by linarith)

/-- A crude but sufficient quantitative lower bound: `H p ≥ 5/32` on
`[1/32, 1/2]`.  Used only to place `E + 1 - H m` inside `Ioc 0 1`. -/
theorem H_ge_five_div_32 {m : ℝ} (hm : 1 / 32 ≤ m) (hm' : m ≤ 1 / 2) :
    (5 : ℝ) / 32 ≤ H m := by
  have h2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have hb : Real.binEntropy (1 / 32 : ℝ)
      = (1 / 32) * (-Real.log (1 / 32)) + (1 - 1 / 32) * (-Real.log (1 - 1 / 32)) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
  have h32 : -Real.log (1 / 32 : ℝ) = 5 * Real.log 2 := by
    rw [one_div, Real.log_inv, neg_neg, show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num,
      Real.log_pow]
    norm_num
  have hc : Real.log (1 - (1 / 32 : ℝ)) ≤ 0 :=
    Real.log_nonpos (by norm_num) (by norm_num)
  have hbase : (5 : ℝ) / 32 ≤ H (1 / 32 : ℝ) := by
    rw [H, le_div_iff₀ h2, hb, h32]
    linarith
  have hmono : H (1 / 32 : ℝ) ≤ H m :=
    H_strictMonoOn.monotoneOn ⟨by norm_num, by norm_num⟩ ⟨by linarith, hm'⟩ hm
  linarith

/-! ## §3  Kernel-checked rational log enclosures -/

theorem log_two_bounds :
    ((13862943611/20000000000 : ℝ)) ≤ Real.log 2 ∧ Real.log 2 ≤ ((8664339757/12500000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := ((1 / 3) : ℚ)) (n := 14)
    (lo := ((13862943611/20000000000) : ℚ)) (hi := ((8664339757/12500000000) : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  exact h

theorem log_big_ge : ((181358215479/12500000000 : ℝ)) ≤ Real.log 1999999 := by
  have h := Certificates.checkLog_sound (w := ((951423/3048575) : ℚ)) (n := 13)
    (lo := ((16142840683/25000000000) : ℚ)) (hi := ((64571362733/100000000000) : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((1999999/1048576) : ℝ) 20 (by norm_num)
  rw [show (2 : ℝ) ^ (20 : ℕ) * (1999999/1048576) = 1999999 by norm_num] at hs
  norm_num at hs
  have htwo := log_two_bounds
  linarith only [h.1, htwo.1, hs]

theorem logb_big_ge :
    ((16352787381/781250000 : ℝ)) ≤ Real.log ((2 - 1 / 1000000) / (1 / 1000000)) / Real.log 2 := by
  have h2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have htwo := log_two_bounds
  rw [show ((2 : ℝ) - 1 / 1000000) / (1 / 1000000) = 1999999 by norm_num,
    le_div_iff₀ h2]
  linarith only [log_big_ge, htwo.2]

theorem nlogM0 :
    ((120397280431/100000000000 : ℝ)) ≤ -Real.log (3/10) ∧ -Real.log (3/10) ≤ ((120397280433/100000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (1/4 : ℚ)) (n := 11)
    (lo := (6385320297/12500000000 : ℚ)) (hi := (51082562377/100000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((5/3) : ℝ) 1 (by norm_num)
  rw [show (2 : ℝ) ^ (1 : ℕ) * (5/3) = 1 / (3/10) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogMc0 :
    ((35667494393/100000000000 : ℝ)) ≤ -Real.log (1 - 3/10) ∧ -Real.log (1 - 3/10) ≤ ((17833747197/50000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (3/17 : ℚ)) (n := 9)
    (lo := (35667494393/100000000000 : ℚ)) (hi := (17833747197/50000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((10/7) : ℝ) 0 (by norm_num)
  rw [show (2 : ℝ) ^ (0 : ℕ) * (10/7) = 1 / (1 - 3/10) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogV0 :
    ((41588830833/10000000000 : ℝ)) ≤ -Real.log (1/64) ∧ -Real.log (1/64) ≤ ((25993019271/6250000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (1/3 : ℚ)) (n := 14)
    (lo := (13862943611/20000000000 : ℚ)) (hi := (8664339757/12500000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((2) : ℝ) 5 (by norm_num)
  rw [show (2 : ℝ) ^ (5 : ℕ) * (2) = 1 / (1/64) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogVc0 :
    ((98427231/6250000000 : ℝ)) ≤ -Real.log (1 - 1/64) ∧ -Real.log (1 - 1/64) ≤ ((1574835697/100000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (1/127 : ℚ)) (n := 3)
    (lo := (98427231/6250000000 : ℚ)) (hi := (1574835697/100000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((64/63) : ℝ) 0 (by norm_num)
  rw [show (2 : ℝ) ^ (0 : ℕ) * (64/63) = 1 / (1 - 1/64) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogJ0 :
    ((207156736317/50000000000 : ℝ)) ≤ -Real.log ((1/64) / (1 - 1/64)) ∧ -Real.log ((1/64) / (1 - 1/64)) ≤ ((647364801/156250000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (31/95 : ℚ)) (n := 14)
    (lo := (67739882359/100000000000 : ℚ)) (hi := (1693497059/2500000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((63/32) : ℝ) 5 (by norm_num)
  rw [show (2 : ℝ) ^ (5 : ℕ) * (63/32) = 1 / ((1/64) / (1 - 1/64)) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogM1 :
    ((89901454111/50000000000 : ℝ)) ≤ -Real.log (53/320) ∧ -Real.log (53/320) ≤ ((7192116329/4000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (27/133 : ℚ)) (n := 10)
    (lo := (2573342007/6250000000 : ℚ)) (hi := (41173472113/100000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((80/53) : ℝ) 2 (by norm_num)
  rw [show (2 : ℝ) ^ (2 : ℕ) * (80/53) = 1 / (53/320) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogMc1 :
    ((18107233739/100000000000 : ℝ)) ≤ -Real.log (1 - 53/320) ∧ -Real.log (1 - 53/320) ≤ ((905361687/5000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (53/587 : ℚ)) (n := 6)
    (lo := (18107233739/100000000000 : ℚ)) (hi := (905361687/5000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((320/267) : ℝ) 0 (by norm_num)
  rw [show (2 : ℝ) ^ (0 : ℕ) * (320/267) = 1 / (1 - 53/320) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogV1 :
    ((13862943611/5000000000 : ℝ)) ≤ -Real.log (1/16) ∧ -Real.log (1/16) ≤ ((8664339757/3125000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (1/3 : ℚ)) (n := 14)
    (lo := (13862943611/20000000000 : ℚ)) (hi := (8664339757/12500000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((2) : ℝ) 3 (by norm_num)
  rw [show (2 : ℝ) ^ (3 : ℕ) * (2) = 1 / (1/16) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogVc1 :
    ((6453852113/100000000000 : ℝ)) ≤ -Real.log (1 - 1/16) ∧ -Real.log (1 - 1/16) ≤ ((3226926057/50000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (1/31 : ℚ)) (n := 4)
    (lo := (6453852113/100000000000 : ℚ)) (hi := (3226926057/50000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((16/15) : ℝ) 0 (by norm_num)
  rw [show (2 : ℝ) ^ (0 : ℕ) * (16/15) = 1 / (1 - 1/16) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogJ1 :
    ((270805020107/100000000000 : ℝ)) ≤ -Real.log ((1/16) / (1 - 1/16)) ∧ -Real.log ((1/16) / (1 - 1/16)) ≤ ((270805020111/100000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (7/23 : ℚ)) (n := 13)
    (lo := (31430432971/50000000000 : ℚ)) (hi := (62860865943/100000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((15/8) : ℝ) 3 (by norm_num)
  rw [show (2 : ℝ) ^ (3 : ℕ) * (15/8) = 1 / ((1/16) / (1 - 1/16)) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogM2 :
    ((231833344993/100000000000 : ℝ)) ≤ -Real.log (63/640) ∧ -Real.log (63/640) ≤ ((231833344997/100000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (17/143 : ℚ)) (n := 7)
    (lo := (5972297707/25000000000 : ℚ)) (hi := (23889190829/100000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((80/63) : ℝ) 3 (by norm_num)
  rw [show (2 : ℝ) ^ (3 : ℕ) * (80/63) = 1 / (63/640) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogMc2 :
    ((1295323873/12500000000 : ℝ)) ≤ -Real.log (1 - 63/640) ∧ -Real.log (1 - 63/640) ≤ ((2072518197/20000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (63/1217 : ℚ)) (n := 5)
    (lo := (1295323873/12500000000 : ℚ)) (hi := (2072518197/20000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((640/577) : ℝ) 0 (by norm_num)
  rw [show (2 : ℝ) ^ (0 : ℕ) * (640/577) = 1 / (1 - 63/640) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogV2 :
    ((212026353617/100000000000 : ℝ)) ≤ -Real.log (3/25) ∧ -Real.log (3/25) ≤ ((212026353621/100000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (1/49 : ℚ)) (n := 4)
    (lo := (1020549863/25000000000 : ℚ)) (hi := (4082199453/100000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((25/24) : ℝ) 3 (by norm_num)
  rw [show (2 : ℝ) ^ (3 : ℕ) * (25/24) = 1 / (3/25) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogVc2 :
    ((255666743/2000000000 : ℝ)) ≤ -Real.log (1 - 3/25) ∧ -Real.log (1 - 3/25) ≤ ((12783337151/100000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (3/47 : ℚ)) (n := 6)
    (lo := (255666743/2000000000 : ℚ)) (hi := (12783337151/100000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((25/22) : ℝ) 0 (by norm_num)
  rw [show (2 : ℝ) ^ (0 : ℕ) * (25/22) = 1 / (1 - 3/25) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogJ2 :
    ((199243016467/100000000000 : ℝ)) ≤ -Real.log ((3/25) / (1 - 3/25)) ∧ -Real.log ((3/25) / (1 - 3/25)) ≤ ((19924301647/10000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (5/17 : ℚ)) (n := 13)
    (lo := (60613580357/100000000000 : ℚ)) (hi := (30306790179/50000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((11/6) : ℝ) 2 (by norm_num)
  rw [show (2 : ℝ) ^ (2 : ℕ) * (11/6) = 1 / ((3/25) / (1 - 3/25)) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogM3 :
    ((68394368727/25000000000 : ℝ)) ≤ -Real.log (83/1280) ∧ -Real.log (83/1280) ≤ ((8549296091/3125000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (77/243 : ℚ)) (n := 13)
    (lo := (65633320743/100000000000 : ℚ)) (hi := (8204165093/12500000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((160/83) : ℝ) 3 (by norm_num)
  rw [show (2 : ℝ) ^ (3 : ℕ) * (160/83) = 1 / (83/1280) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogMc3 :
    ((1340833027/20000000000 : ℝ)) ≤ -Real.log (1 - 83/1280) ∧ -Real.log (1 - 83/1280) ≤ ((419010321/6250000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (83/2477 : ℚ)) (n := 5)
    (lo := (1340833027/20000000000 : ℚ)) (hi := (419010321/6250000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((1280/1197) : ℝ) 0 (by norm_num)
  rw [show (2 : ℝ) ^ (0 : ℕ) * (1280/1197) = 1 / (1 - 83/1280) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogV3 :
    ((4479398673/2500000000 : ℝ)) ≤ -Real.log (1/6) ∧ -Real.log (1/6) ≤ ((179175946923/100000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (1/5 : ℚ)) (n := 10)
    (lo := (4054651081/10000000000 : ℚ)) (hi := (40546510811/100000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((3/2) : ℝ) 2 (by norm_num)
  rw [show (2 : ℝ) ^ (2 : ℕ) * (3/2) = 1 / (1/6) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogVc3 :
    ((18232155679/100000000000 : ℝ)) ≤ -Real.log (1 - 1/6) ∧ -Real.log (1 - 1/6) ≤ ((113950973/625000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (1/11 : ℚ)) (n := 6)
    (lo := (18232155679/100000000000 : ℚ)) (hi := (113950973/625000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((6/5) : ℝ) 0 (by norm_num)
  rw [show (2 : ℝ) ^ (0 : ℕ) * (6/5) = 1 / (1 - 1/6) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogJ3 :
    ((160943791241/100000000000 : ℝ)) ≤ -Real.log ((1/6) / (1 - 1/6)) ∧ -Real.log ((1/6) / (1 - 1/6)) ≤ ((40235947811/25000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (1/9 : ℚ)) (n := 7)
    (lo := (22314355131/100000000000 : ℚ)) (hi := (5578588783/25000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((5/4) : ℝ) 2 (by norm_num)
  rw [show (2 : ℝ) ^ (2 : ℕ) * (5/4) = 1 / ((1/6) / (1 - 1/6)) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogM4 :
    ((151778909103/50000000000 : ℝ)) ≤ -Real.log (123/2560) ∧ -Real.log (123/2560) ≤ ((303557818211/100000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (37/283 : ℚ)) (n := 8)
    (lo := (13149472993/50000000000 : ℚ)) (hi := (26298945987/100000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((160/123) : ℝ) 4 (by norm_num)
  rw [show (2 : ℝ) ^ (4 : ℕ) * (160/123) = 1 / (123/2560) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogMc4 :
    ((153873387/3125000000 : ℝ)) ≤ -Real.log (1 - 123/2560) ∧ -Real.log (1 - 123/2560) ≤ ((984789677/20000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (123/4997 : ℚ)) (n := 4)
    (lo := (153873387/3125000000 : ℚ)) (hi := (984789677/20000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((2560/2437) : ℝ) 0 (by norm_num)
  rw [show (2 : ℝ) ^ (0 : ℕ) * (2560/2437) = 1 / (1 - 123/2560) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogV4 :
    ((160943791241/100000000000 : ℝ)) ≤ -Real.log (1/5) ∧ -Real.log (1/5) ≤ ((40235947811/25000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (1/9 : ℚ)) (n := 7)
    (lo := (22314355131/100000000000 : ℚ)) (hi := (5578588783/25000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((5/4) : ℝ) 2 (by norm_num)
  rw [show (2 : ℝ) ^ (2 : ℕ) * (5/4) = 1 / (1/5) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogVc4 :
    ((22314355131/100000000000 : ℝ)) ≤ -Real.log (1 - 1/5) ∧ -Real.log (1 - 1/5) ≤ ((5578588783/25000000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (1/9 : ℚ)) (n := 7)
    (lo := (22314355131/100000000000 : ℚ)) (hi := (5578588783/25000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((5/4) : ℝ) 0 (by norm_num)
  rw [show (2 : ℝ) ^ (0 : ℕ) * (5/4) = 1 / (1 - 1/5) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem nlogJ4 :
    ((13862943611/10000000000 : ℝ)) ≤ -Real.log ((1/5) / (1 - 1/5)) ∧ -Real.log ((1/5) / (1 - 1/5)) ≤ ((8664339757/6250000000 : ℝ)) := by
  have h := Certificates.checkLog_sound (w := (1/3 : ℚ)) (n := 14)
    (lo := (13862943611/20000000000 : ℚ)) (hi := (8664339757/12500000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h
  have hs := log_scale ((2) : ℝ) 1 (by norm_num)
  rw [show (2 : ℝ) ^ (1 : ℕ) * (2) = 1 / ((1/5) / (1 - 1/5)) by norm_num, log_one_div] at hs
  norm_num at hs
  have htwo := log_two_bounds
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

/-! ## §4  Monotonicity of the archived parent test -/

theorem lowEntropyA_nonneg_logfactor {E : ℝ} (hE : 0 < E) (hE1 : E ≤ 1) :
    0 ≤ Real.log ((2 - E) / E) / Real.log 2 := by
  apply div_nonneg _ log_two_pos.le
  apply Real.log_nonneg
  rw [le_div_iff₀ hE]
  linarith

theorem lowEntropyA_antitone_q {qq r E : ℝ} (hqr : qq ≤ r) (hE : 0 < E) (hE1 : E ≤ 1) :
    lowEntropyA r E ≤ lowEntropyA qq E := by
  unfold lowEntropyA
  exact mul_le_mul_of_nonneg_right (by linarith) (lowEntropyA_nonneg_logfactor hE hE1)

theorem lowEntropyA_antitone_E {qq E : ℝ} (hq : qq ≤ 15 / 16) (hE : 0 < E)
    (hEs : E ≤ 1 / 1000000) :
    lowEntropyA qq (1 / 1000000) ≤ lowEntropyA qq E := by
  have h2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have hratio : ((2 : ℝ) - 1 / 1000000) / (1 / 1000000) ≤ (2 - E) / E := by
    rw [show ((2 : ℝ) - 1 / 1000000) / (1 / 1000000) = 1999999 by norm_num,
      show (2 - E) / E = 2 / E - 1 by field_simp]
    have hinv : (2000000 : ℝ) ≤ 2 / E := by
      rw [le_div_iff₀ hE]; linarith
    linarith
  have hlog : Real.log (((2 : ℝ) - 1 / 1000000) / (1 / 1000000)) ≤ Real.log ((2 - E) / E) :=
    Real.log_le_log (by norm_num) hratio
  have hdiv : Real.log (((2 : ℝ) - 1 / 1000000) / (1 / 1000000)) / Real.log 2
      ≤ Real.log ((2 - E) / E) / Real.log 2 :=
    (div_le_div_iff_of_pos_right h2).2 hlog
  unfold lowEntropyA
  exact mul_le_mul (by linarith) hdiv
    (lowEntropyA_nonneg_logfactor (by norm_num) (by norm_num)) (by linarith)

theorem lowEntropyK_antitone {qq r : ℝ} (hq : 2 / 5 ≤ qq) (hqr : qq ≤ r)
    (hr : r ≤ 15 / 16) : lowEntropyK r ≤ lowEntropyK qq := by
  have hHq0 : (0 : ℝ) ≤ H ((1 - qq) / 2) := H_nonneg (by linarith) (by linarith)
  have hHr0 : (0 : ℝ) ≤ H ((1 - r) / 2) := H_nonneg (by linarith) (by linarith)
  have hHq1 : H ((1 - qq) / 2) < 1 := by
    have h := H_strictMonoOn (a := (1 - qq) / 2) (b := 1 / 2)
      ⟨by linarith, by linarith⟩ ⟨by norm_num, le_rfl⟩ (by linarith)
    rwa [H_half] at h
  have hHr1 : H ((1 - r) / 2) < 1 := by
    have h := H_strictMonoOn (a := (1 - r) / 2) (b := 1 / 2)
      ⟨by linarith, by linarith⟩ ⟨by norm_num, le_rfl⟩ (by linarith)
    rwa [H_half] at h
  have hmono : H ((1 - r) / 2) ≤ H ((1 - qq) / 2) :=
    H_strictMonoOn.monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      (by linarith)
  exact eta_antitoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)

theorem psi_le_lowEntropyK {qq E : ℝ} (hq : 2 / 5 ≤ qq) (hq' : qq ≤ 15 / 16)
    (hE : 0 < E) (hEs : E ≤ 1 / 1000000) :
    psi ((1 - qq) / 2) E ≤ lowEntropyK qq := by
  have hH0 : (0 : ℝ) ≤ H ((1 - qq) / 2) := H_nonneg (by linarith) (by linarith)
  have hH1 : H ((1 - qq) / 2) < 1 := by
    have h := H_strictMonoOn (a := (1 - qq) / 2) (b := 1 / 2)
      ⟨by linarith, by linarith⟩ ⟨by norm_num, le_rfl⟩ (by linarith)
    rwa [H_half] at h
  have hHbig : (5 : ℝ) / 32 ≤ H ((1 - qq) / 2) :=
    H_ge_five_div_32 (by linarith) (by linarith)
  exact eta_antitoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)

theorem lowEntropyA_ge_of (hh C : ℝ) (hnn : 0 ≤ 1 - hh - 1 / 1000000)
    (hC : C ≤ Real.log ((2 - 1 / 1000000) / (1 / 1000000)) / Real.log 2) :
    (1 - hh - 1 / 1000000) * C ≤ lowEntropyA hh (1 / 1000000) := by
  unfold lowEntropyA
  exact mul_le_mul_of_nonneg_left hC hnn

/-! ## §5  Per-leaf certified margins -/

/-- Leaf 0 (archived path `0`): `[2/5, 107/160]`, witness `v = 1/64`. -/
theorem H_m0 : H ((3/10) : ℝ) ≤ ((3525163597/4000000000) : ℝ) := by
  have htwo := log_two_bounds
  refine H_le_of (3/10) (120397280433/100000000000) (17833747197/50000000000) (3525163597/4000000000) (by norm_num) (by norm_num)
    nlogM0.2 nlogMc0.2 ?_
  linarith only [htwo.1]

theorem H_v0 : H ((1/64) : ℝ) ≤ ((11611507531/100000000000) : ℝ) := by
  have htwo := log_two_bounds
  refine H_le_of (1/64) (25993019271/6250000000) (1574835697/100000000000) (11611507531/100000000000) (by norm_num) (by norm_num)
    nlogV0.2 nlogVc0.2 ?_
  linarith only [htwo.1]

theorem J_v0 : J ((1/64) : ℝ) ≤ ((14943199809/2500000000) : ℝ) := by
  have htwo := log_two_bounds
  refine J_le_of (1/64) (647364801/156250000) (14943199809/2500000000) (by norm_num) (by norm_num) nlogJ0.2 ?_
  linarith only [htwo.1]

theorem K_le0 : lowEntropyK ((2/5) : ℝ) ≤ ((463239194079/80000000000) : ℝ) := by
  have hHm := H_m0
  have hHv := H_v0
  have hJ := J_v0
  have hHm0 : (0 : ℝ) ≤ H ((3/10) : ℝ) := H_nonneg (by norm_num) (by norm_num)
  have hbase : eta (1 - H ((3/10) : ℝ)) ≤ (1 - 2 * (1/64)) * (14943199809/2500000000) :=
    eta_le_of_witness (1 - H ((3/10) : ℝ)) (1/64) (14943199809/2500000000)
      (by linarith) (by linarith) (by norm_num) (by norm_num) (by linarith) hJ (by norm_num)
  have hK : lowEntropyK ((2/5) : ℝ) = eta (1 - H ((3/10) : ℝ)) := by
    unfold lowEntropyK
    norm_num
  rw [hK]
  linarith

theorem A_ge0 : ((5416844467168869/781250000000000) : ℝ) ≤ lowEntropyA ((107/160) : ℝ) (1 / 1000000) := by
  have hbase := lowEntropyA_ge_of ((107/160) : ℝ) (16352787381/781250000) (by norm_num) logb_big_ge
  linarith

theorem margin_leaf0 :
    lowEntropyK ((2/5) : ℝ) + 1 / 10 ≤ lowEntropyA ((107/160) : ℝ) (1 / 1000000) := by
  have h1 := K_le0
  have h2 := A_ge0
  linarith

/-- Leaf 1 (archived path `10`): `[107/160, 257/320]`, witness `v = 1/16`. -/
theorem H_m1 : H ((53/320) : ℝ) ≤ ((32379905081/50000000000) : ℝ) := by
  have htwo := log_two_bounds
  refine H_le_of (53/320) (7192116329/4000000000) (905361687/5000000000) (32379905081/50000000000) (by norm_num) (by norm_num)
    nlogM1.2 nlogMc1.2 ?_
  linarith only [htwo.1]

theorem H_v1 : H ((1/16) : ℝ) ≤ ((33729006663/100000000000) : ℝ) := by
  have htwo := log_two_bounds
  refine H_le_of (1/16) (8664339757/3125000000) (3226926057/50000000000) (33729006663/100000000000) (by norm_num) (by norm_num)
    nlogV1.2 nlogVc1.2 ?_
  linarith only [htwo.1]

theorem J_v1 : J ((1/16) : ℝ) ≤ ((24418066223/6250000000) : ℝ) := by
  have htwo := log_two_bounds
  refine J_le_of (1/16) (270805020111/100000000000) (24418066223/6250000000) (by norm_num) (by norm_num) nlogJ1.2 ?_
  linarith only [htwo.1]

theorem K_le1 : lowEntropyK ((107/160) : ℝ) ≤ ((170926463561/50000000000) : ℝ) := by
  have hHm := H_m1
  have hHv := H_v1
  have hJ := J_v1
  have hHm0 : (0 : ℝ) ≤ H ((53/320) : ℝ) := H_nonneg (by norm_num) (by norm_num)
  have hbase : eta (1 - H ((53/320) : ℝ)) ≤ (1 - 2 * (1/16)) * (24418066223/6250000000) :=
    eta_le_of_witness (1 - H ((53/320) : ℝ)) (1/16) (24418066223/6250000000)
      (by linarith) (by linarith) (by norm_num) (by norm_num) (by linarith) hJ (by norm_num)
  have hK : lowEntropyK ((107/160) : ℝ) = eta (1 - H ((53/320) : ℝ)) := by
    unfold lowEntropyK
    norm_num
  rw [hK]
  linarith

theorem A_ge1 : ((1609719331423497/390625000000000) : ℝ) ≤ lowEntropyA ((257/320) : ℝ) (1 / 1000000) := by
  have hbase := lowEntropyA_ge_of ((257/320) : ℝ) (16352787381/781250000) (by norm_num) logb_big_ge
  linarith

theorem margin_leaf1 :
    lowEntropyK ((107/160) : ℝ) + 1 / 10 ≤ lowEntropyA ((257/320) : ℝ) (1 / 1000000) := by
  have h1 := K_le1
  have h2 := A_ge1
  linarith

/-- Leaf 2 (archived path `110`): `[257/320, 557/640]`, witness `v = 3/25`. -/
theorem H_m2 : H ((63/640) : ℝ) ≤ ((46402292667/100000000000) : ℝ) := by
  have htwo := log_two_bounds
  refine H_le_of (63/640) (231833344997/100000000000) (2072518197/20000000000) (46402292667/100000000000) (by norm_num) (by norm_num)
    nlogM2.2 nlogMc2.2 ?_
  linarith only [htwo.1]

theorem H_v2 : H ((3/25) : ℝ) ≤ ((5293608653/10000000000) : ℝ) := by
  have htwo := log_two_bounds
  refine H_le_of (3/25) (212026353621/100000000000) (12783337151/100000000000) (5293608653/10000000000) (by norm_num) (by norm_num)
    nlogV2.2 nlogVc2.2 ?_
  linarith only [htwo.1]

theorem J_v2 : J ((3/25) : ℝ) ≤ ((143723455899/50000000000) : ℝ) := by
  have htwo := log_two_bounds
  refine J_le_of (3/25) (19924301647/10000000000) (143723455899/50000000000) (by norm_num) (by norm_num) nlogJ2.2 ?_
  linarith only [htwo.1]

theorem K_le2 : lowEntropyK ((257/320) : ℝ) ≤ ((2730745662081/1250000000000) : ℝ) := by
  have hHm := H_m2
  have hHv := H_v2
  have hJ := J_v2
  have hHm0 : (0 : ℝ) ≤ H ((63/640) : ℝ) := H_nonneg (by norm_num) (by norm_num)
  have hbase : eta (1 - H ((63/640) : ℝ)) ≤ (1 - 2 * (3/25)) * (143723455899/50000000000) :=
    eta_le_of_witness (1 - H ((63/640) : ℝ)) (3/25) (143723455899/50000000000)
      (by linarith) (by linarith) (by norm_num) (by norm_num) (by linarith) hJ (by norm_num)
  have hK : lowEntropyK ((257/320) : ℝ) = eta (1 - H ((63/640) : ℝ)) := by
    unfold lowEntropyK
    norm_num
  rw [hK]
  linarith

theorem A_ge2 : ((4241471521372113/1562500000000000) : ℝ) ≤ lowEntropyA ((557/640) : ℝ) (1 / 1000000) := by
  have hbase := lowEntropyA_ge_of ((557/640) : ℝ) (16352787381/781250000) (by norm_num) logb_big_ge
  linarith

theorem margin_leaf2 :
    lowEntropyK ((257/320) : ℝ) + 1 / 10 ≤ lowEntropyA ((557/640) : ℝ) (1 / 1000000) := by
  have h1 := K_le2
  have h2 := A_ge2
  linarith

/-- Leaf 3 (archived path `1110`): `[557/640, 1157/1280]`, witness `v = 1/6`. -/
theorem H_m3 : H ((83/1280) : ℝ) ≤ ((34637998957/100000000000) : ℝ) := by
  have htwo := log_two_bounds
  refine H_le_of (83/1280) (8549296091/3125000000) (419010321/6250000000) (34637998957/100000000000) (by norm_num) (by norm_num)
    nlogM3.2 nlogMc3.2 ?_
  linarith only [htwo.1]

theorem H_v3 : H ((1/6) : ℝ) ≤ ((65002242167/100000000000) : ℝ) := by
  have htwo := log_two_bounds
  refine H_le_of (1/6) (179175946923/100000000000) (113950973/625000000) (65002242167/100000000000) (by norm_num) (by norm_num)
    nlogV3.2 nlogVc3.2 ?_
  linarith only [htwo.1]

theorem J_v3 : J ((1/6) : ℝ) ≤ ((232192809493/100000000000) : ℝ) := by
  have htwo := log_two_bounds
  refine J_le_of (1/6) (40235947811/25000000000) (232192809493/100000000000) (by norm_num) (by norm_num) nlogJ3.2 ?_
  linarith only [htwo.1]

theorem K_le3 : lowEntropyK ((557/640) : ℝ) ≤ ((232192809493/150000000000) : ℝ) := by
  have hHm := H_m3
  have hHv := H_v3
  have hJ := J_v3
  have hHm0 : (0 : ℝ) ≤ H ((83/1280) : ℝ) := H_nonneg (by norm_num) (by norm_num)
  have hbase : eta (1 - H ((83/1280) : ℝ)) ≤ (1 - 2 * (1/6)) * (232192809493/100000000000) :=
    eta_le_of_witness (1 - H ((83/1280) : ℝ)) (1/6) (232192809493/100000000000)
      (by linarith) (by linarith) (by norm_num) (by norm_num) (by linarith) hJ (by norm_num)
  have hK : lowEntropyK ((557/640) : ℝ) = eta (1 - H ((83/1280) : ℝ)) := by
    unfold lowEntropyK
    norm_num
  rw [hK]
  linarith

theorem A_ge3 : ((6285537238422351/3125000000000000) : ℝ) ≤ lowEntropyA ((1157/1280) : ℝ) (1 / 1000000) := by
  have hbase := lowEntropyA_ge_of ((1157/1280) : ℝ) (16352787381/781250000) (by norm_num) logb_big_ge
  linarith

theorem margin_leaf3 :
    lowEntropyK ((557/640) : ℝ) + 1 / 10 ≤ lowEntropyA ((1157/1280) : ℝ) (1 / 1000000) := by
  have h1 := K_le3
  have h2 := A_ge3
  linarith

/-- Leaf 4 (archived path `1111`): `[1157/1280, 15/16]`, witness `v = 1/5`. -/
theorem H_m4 : H ((123/2560) : ℝ) ≤ ((3475519547/12500000000) : ℝ) := by
  have htwo := log_two_bounds
  refine H_le_of (123/2560) (303557818211/100000000000) (984789677/20000000000) (3475519547/12500000000) (by norm_num) (by norm_num)
    nlogM4.2 nlogMc4.2 ?_
  linarith only [htwo.1]

theorem H_v4 : H ((1/5) : ℝ) ≤ ((72192809491/100000000000) : ℝ) := by
  have htwo := log_two_bounds
  refine H_le_of (1/5) (40235947811/25000000000) (5578588783/25000000000) (72192809491/100000000000) (by norm_num) (by norm_num)
    nlogV4.2 nlogVc4.2 ?_
  linarith only [htwo.1]

theorem J_v4 : J ((1/5) : ℝ) ≤ ((200000000003/100000000000) : ℝ) := by
  have htwo := log_two_bounds
  refine J_le_of (1/5) (8664339757/6250000000) (200000000003/100000000000) (by norm_num) (by norm_num) nlogJ4.2 ?_
  linarith only [htwo.1]

theorem K_le4 : lowEntropyK ((1157/1280) : ℝ) ≤ ((600000000009/500000000000) : ℝ) := by
  have hHm := H_m4
  have hHv := H_v4
  have hJ := J_v4
  have hHm0 : (0 : ℝ) ≤ H ((123/2560) : ℝ) := H_nonneg (by norm_num) (by norm_num)
  have hbase : eta (1 - H ((123/2560) : ℝ)) ≤ (1 - 2 * (1/5)) * (200000000003/100000000000) :=
    eta_le_of_witness (1 - H ((123/2560) : ℝ)) (1/5) (200000000003/100000000000)
      (by linarith) (by linarith) (by norm_num) (by norm_num) (by linarith) hJ (by norm_num)
  have hK : lowEntropyK ((1157/1280) : ℝ) = eta (1 - H ((123/2560) : ℝ)) := by
    unfold lowEntropyK
    norm_num
  rw [hK]
  linarith

theorem A_ge4 : ((1022032858525119/781250000000000) : ℝ) ≤ lowEntropyA ((15/16) : ℝ) (1 / 1000000) := by
  have hbase := lowEntropyA_ge_of ((15/16) : ℝ) (16352787381/781250000) (by norm_num) logb_big_ge
  linarith

theorem margin_leaf4 :
    lowEntropyK ((1157/1280) : ℝ) + 1 / 10 ≤ lowEntropyA ((15/16) : ℝ) (1 / 1000000) := by
  have h1 := K_le4
  have h2 := A_ge4
  linarith

/-! ## §6  Assembly over the exact partition -/

/-- On every `q` of the archived root interval the parent test has margin at
least `1/10`.  The case split is exactly the five-leaf partition of §1. -/
theorem margin_of_root {qq : ℝ} (hq : 2 / 5 ≤ qq) (hq' : qq ≤ 15 / 16) :
    lowEntropyK qq + 1 / 10 ≤ lowEntropyA qq (1 / 1000000) := by
  rcases le_or_gt qq (107 / 160 : ℝ) with ha | ha
  · have hK := lowEntropyK_antitone (qq := 2 / 5) (r := qq) le_rfl hq hq'
    have hA := lowEntropyA_antitone_q (qq := qq) (r := 107 / 160) (E := 1 / 1000000) ha (by norm_num) (by norm_num)
    linarith [margin_leaf0]
  rcases le_or_gt qq (257 / 320 : ℝ) with hb | hb
  · have hK := lowEntropyK_antitone (qq := 107 / 160) (r := qq) (by norm_num) ha.le hq'
    have hA := lowEntropyA_antitone_q (qq := qq) (r := 257 / 320) (E := 1 / 1000000) hb (by norm_num) (by norm_num)
    linarith [margin_leaf1]
  rcases le_or_gt qq (557 / 640 : ℝ) with hc | hc
  · have hK := lowEntropyK_antitone (qq := 257 / 320) (r := qq) (by norm_num) hb.le hq'
    have hA := lowEntropyA_antitone_q (qq := qq) (r := 557 / 640) (E := 1 / 1000000) hc (by norm_num) (by norm_num)
    linarith [margin_leaf2]
  rcases le_or_gt qq (1157 / 1280 : ℝ) with hd | hd
  · have hK := lowEntropyK_antitone (qq := 557 / 640) (r := qq) (by norm_num) hc.le hq'
    have hA := lowEntropyA_antitone_q (qq := qq) (r := 1157 / 1280) (E := 1 / 1000000) hd (by norm_num)
      (by norm_num)
    linarith [margin_leaf3]
  · have hK := lowEntropyK_antitone (qq := 1157 / 1280) (r := qq) (by norm_num) hd.le hq'
    have hA := lowEntropyA_antitone_q (qq := qq) (r := 15 / 16) (E := 1 / 1000000) hq' (by norm_num) (by norm_num)
    linarith [margin_leaf4]

/-- Main quantitative statement: on `q ∈ [2/5, 15/16]` and `0 < E ≤ 10⁻⁶`,
the archived parent lower bound `A_q(E)` beats `psi` at the parent by `1/10`. -/
theorem psi_add_margin_le_lowEntropyA {qq E : ℝ} (hq : 2 / 5 ≤ qq) (hq' : qq ≤ 15 / 16)
    (hE : 0 < E) (hEs : E ≤ 1 / 1000000) :
    psi ((1 - qq) / 2) E + 1 / 10 ≤ lowEntropyA qq E := by
  have h1 := psi_le_lowEntropyK hq hq' hE hEs
  have h2 := margin_of_root hq hq'
  have h3 := lowEntropyA_antitone_E hq' hE hEs
  linarith

/-- The same statement in the `(a, b)` coordinates of `ResidualPsiScalarOwner`:
`q = 1 - (a+b)`, so `q ∈ [2/5, 15/16]` becomes `a + b ∈ [1/16, 3/5]`. -/
theorem psi_add_margin_le_lowEntropyA_mean {a b E : ℝ}
    (hlo : 1 / 16 ≤ a + b) (hhi : a + b ≤ 3 / 5) (hE : 0 < E) (hEs : E ≤ 1 / 1000000) :
    psi ((a + b) / 2) E + 1 / 10 ≤ lowEntropyA (1 - (a + b)) E := by
  have h := psi_add_margin_le_lowEntropyA (qq := 1 - (a + b)) (by linarith) (by linarith) hE hEs
  rwa [show (1 - (1 - (a + b))) / 2 = (a + b) / 2 by ring] at h

/-- Phase-2 consumption shape.

`hparent` is the archived all-`q` parent test `phi(parent) ≥ A_q(E)`.  It is
**not** proved in this file: it is the separately owned analytic input (task
`analytic-low-entropy`).  Given it, the `hactive` hypothesis of
`ResidualPsiScalarOwner` is contradictory whenever
`a + b ∈ [1/16, 3/5]` and `0 < E ≤ 10⁻⁶`. -/
theorem not_activePsi_of_parentLowerBound {a b E : ℝ}
    (hlo : 1 / 16 ≤ a + b) (hhi : a + b ≤ 3 / 5) (hE : 0 < E) (hEs : E ≤ 1 / 1000000)
    (hparent : lowEntropyA (1 - (a + b)) E ≤ phi ((a + b) / 2) E) :
    ¬ phi ((a + b) / 2) E < psi ((a + b) / 2) E := by
  intro hactive
  have h := psi_add_margin_le_lowEntropyA_mean hlo hhi hE hEs
  linarith

/-- Directly in the shape of `ResidualPsiScalarOwner`.

On `a + b ∈ (1/16, 3/5]` with `0 < E ≤ 10⁻⁶`, the owner's own `hactive`
hypothesis is contradictory once the separately owned parent lower bound
`hparent` is supplied, so the region is vacuous and the scalar bound holds. -/
theorem residualPsiScalarBound_le_of_parentLowerBound {a b E : ℝ}
    (hmean : 1 / 16 < a + b) (hhi : a + b ≤ 3 / 5)
    (hE : 0 < E) (hEs : E ≤ 1 / 1000000)
    (hparent : lowEntropyA (1 - (a + b)) E ≤ phi ((a + b) / 2) E)
    (hactive : phi ((a + b) / 2) E < psi ((a + b) / 2) E) :
    residualPsiScalarBound a b E ≤ interiorCost a b :=
  absurd hactive (not_activePsi_of_parentLowerBound hmean.le hhi hE hEs hparent)

#print axioms lowEntropyA
#print axioms lowEntropyK
#print axioms bisect
#print axioms box
#print axioms leaves
#print axioms log_two_bounds
#print axioms log_big_ge
#print axioms logb_big_ge
#print axioms H_le_of
#print axioms J_le_of
#print axioms eta_le_of_witness
#print axioms H_ge_five_div_32
#print axioms K_le0
#print axioms K_le1
#print axioms K_le2
#print axioms K_le3
#print axioms K_le4
#print axioms A_ge0
#print axioms A_ge1
#print axioms A_ge2
#print axioms A_ge3
#print axioms A_ge4
#print axioms lowEntropyA_antitone_q
#print axioms lowEntropyA_antitone_E
#print axioms lowEntropyK_antitone
#print axioms psi_le_lowEntropyK
#print axioms leaves_iUnion
#print axioms residualPsiScalarBound_le_of_parentLowerBound
#print axioms leaves_eq
#print axioms leaves_endpoints
#print axioms leaves_cover
#print axioms margin_leaf0
#print axioms margin_leaf1
#print axioms margin_leaf2
#print axioms margin_leaf3
#print axioms margin_leaf4
#print axioms margin_of_root
#print axioms psi_add_margin_le_lowEntropyA
#print axioms psi_add_margin_le_lowEntropyA_mean
#print axioms not_activePsi_of_parentLowerBound

end LowEntropyLeaf
end GeneralCK

end


