-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8LargeSShift
-- name    : CK_GeneralCK_Certificates_E8LargeSShift
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:38:40.572582+00:00
-- url     : https://prove2.me/theorems/21efcfe1-6a0a-41d2-a66f-122e8d15df35
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8LargeSShift` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8LargeSShift` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8LargeSShift` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8LargeSShift (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8LargeSShift.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellInverseCoverage
import Definitions.Def_CK_GeneralCK_PureGapE8LargeSConsumer

-- ===== source module GeneralCK.Certificates.E8LargeSShift =====
section

/-!
# The unconditional scalar shift in the E8 large-s structure

Generated primitive and graph data: `scripts/generate_e8_large_s_shift.py`.
Every numerical assertion is checked by kernel reduction.  Coverage of the
target slope follows from the intermediate value theorem, and the derivative
enclosure is for the canonical inverse.  The monotonicity and log-convexity
fields of `E8LargeSStructure` remain separate analytic obligations.
-/

namespace GeneralCK.Certificates.E8LargeSShift
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisReparamInterval E8InverseJet5Bridge

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def precision : ℕ := 64
def fastLogWitness : FastLogBoxWitness := ⟨0, 32, 0, 32⟩
def logTwo : DyadicInterval precision := ⟨12786308645202655642, 12786308645202655715⟩
def wholeAlpha : DyadicInterval precision := ⟨11303980300928476134, 11304164768369213231⟩
theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo fastLogWitness = true := by decide +kernel

def lowerAlpha : DyadicInterval precision := ⟨11303980300928476134, 11303980300928476134⟩
def lowerExp : DyadicInterval precision := ⟨5415731082419764933, 5415731082419766982⟩
def lowerLog : DyadicInterval precision := ⟨4748547319204434972, 4748547319204436629⟩
def lowerY : DyadicInterval precision := ⟨58106710159950564818, 58106710159950598448⟩
def lowerInput : Inputs precision := ⟨lowerAlpha, lowerExp, lowerLog, logTwo⟩
def lowerExpWitness : ExpWitness precision :=
  ⟨5415731082419764933, scale precision, 5415731082419766982, scale precision,
   1, 32, 1, 32,
   ⟨-22607960601856955864, -22607960601856955722⟩, ⟨-22607960601856948888, -22607960601856948744⟩⟩

theorem lower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul lowerAlpha) lowerExp lowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add lowerExp) lowerLog fastLogWitness = true := by decide +kernel

theorem lower_denominators : DenominatorsPositive lowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem lower_y_eq : (yBox lowerInput).d0 = lowerY := by decide +kernel

theorem lower_contains : lowerY.Contains (Y (lower wholeAlpha)) := by
  rw [← lower_y_eq]
  apply checked_yBox_d0_contains lower_primitive_checks.1
    lower_primitive_checks.2 logTwo_checked lower_denominators
  exact point_contains precision 11303980300928476134

def upperAlpha : DyadicInterval precision := ⟨11304164768369213231, 11304164768369213231⟩
def upperExp : DyadicInterval precision := ⟨5415622768881255532, 5415622768881257581⟩
def upperLog : DyadicInterval precision := ⟨4748463587879576622, 4748463587879578277⟩
def upperY : DyadicInterval precision := ⟨58107483756725446857, 58107483756725480475⟩
def upperInput : Inputs precision := ⟨upperAlpha, upperExp, upperLog, logTwo⟩
def upperExpWitness : ExpWitness precision :=
  ⟨5415622768881255532, scale precision, 5415622768881257581, scale precision,
   1, 32, 1, 32,
   ⟨-22608329536738430062, -22608329536738429916⟩, ⟨-22608329536738423082, -22608329536738422936⟩⟩

theorem upper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul upperAlpha) upperExp upperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add upperExp) upperLog fastLogWitness = true := by decide +kernel

theorem upper_denominators : DenominatorsPositive upperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem upper_y_eq : (yBox upperInput).d0 = upperY := by decide +kernel

theorem upper_contains : upperY.Contains (Y (upper wholeAlpha)) := by
  rw [← upper_y_eq]
  apply checked_yBox_d0_contains upper_primitive_checks.1
    upper_primitive_checks.2 logTwo_checked upper_denominators
  exact point_contains precision 11304164768369213231

def wholeExp : DyadicInterval precision := ⟨5415622768881255532, 5415731082419766982⟩
def wholeLog : DyadicInterval precision := ⟨4748463587879576622, 4748547319204436629⟩
def wholeY : DyadicInterval precision := ⟨58105705045544940493, 58108488922124220414⟩
def wholeInput : Inputs precision := ⟨wholeAlpha, wholeExp, wholeLog, logTwo⟩
def wholeExpWitness : ExpWitness precision :=
  ⟨5415622768881255532, scale precision, 5415731082419766982, scale precision,
   1, 32, 1, 32,
   ⟨-22608329536738430062, -22608329536738429916⟩, ⟨-22607960601856948888, -22607960601856948744⟩⟩

theorem whole_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAlpha) wholeExp wholeExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeExp) wholeLog fastLogWitness = true := by decide +kernel

theorem whole_denominators : DenominatorsPositive wholeInput := by
  unfold DenominatorsPositive
  decide +kernel

def derivativeBox : DyadicInterval precision := ⟨3245358456462951644, 3246164656237355226⟩

theorem derivativeBox_eq :
    (eval (xBox wholeInput) (yBox wholeInput)).d1 = derivativeBox := by decide +kernel

theorem whole_y_derivative_positive : 0 < (yBox wholeInput).d1.lo := by decide +kernel

theorem covers : ∃ a : ℝ, wholeAlpha.Contains a ∧ 0 < a ∧ Y a = 63/20 := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    lower_contains upper_contains _ _ (show (63/20 : ℝ) ∈ Icc (63/20) (63/20) from ⟨le_rfl, le_rfl⟩)
  · norm_num [lowerY, scale, precision]
  · norm_num [upperY, scale, precision]

/-- A concrete lower bound with a rational safety margin. -/
theorem derivative_lower : (175/1000 : ℝ) < deriv e8RegularQ (63/20) := by
  obtain ⟨a, ha, hapos, hay⟩ := covers
  have hc := checked_stable_contains_canonical whole_primitive_checks.1
    whole_primitive_checks.2 logTwo_checked whole_denominators
    whole_y_derivative_positive ha hapos
  have hmem : (63/20 : ℝ) ∈ e8SlopeRange := by
    rw [← hay]
    exact E8TAxisStableJet5.Y_mem_e8SlopeRange hapos
  have hd := hc.2.1
  rw [derivativeBox_eq, hay] at hd
  have he : (e8QJet5 e8ThetaCanonicalJet5).d1 (63/20) = deriv e8RegularQ (63/20) := by
    rw [deriv_e8RegularQ_eq (by norm_num), deriv_e8Q hmem]
    rfl
  rw [he] at hd
  have hm : (scale precision : ℝ) * (175/1000) < derivativeBox.lo := by
    norm_num [scale, precision, derivativeBox]
  have hp := hm.trans_le hd.1
  exact (mul_lt_mul_iff_right₀ (scale_cast_pos precision)).mp (by simpa [mul_comm] using hp)

/-- The exact scalar field required by `E8LargeSStructure`, with no premises. -/
theorem shift : 2 * (Real.log 2 / 8) < deriv e8RegularQ (63/20) := by
  have hc : logTwo.Contains (Real.log 2) :=
    logBoxCheck_sound logTwo_checked (by simpa using ofInt_sound precision 2)
  have hb : Real.log 2 < 7/10 := by
    have hm : (logTwo.hi : ℝ) < (scale precision : ℝ) * (7/10) := by
      norm_num [logTwo, scale, precision]
    exact (mul_lt_mul_iff_right₀ (scale_cast_pos precision)).mp
      (by simpa [mul_comm] using hc.2.trans_lt hm)
  linarith [derivative_lower]

#print axioms derivative_lower
#print axioms shift

end GeneralCK.Certificates.E8LargeSShift

end


