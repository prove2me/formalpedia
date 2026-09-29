-- Prove2me | Definitions.Def_CK_CKLaneC_RSEnc_Residual
-- name    : CK_CKLaneC_RSEnc_Residual
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:50:56.217288+00:00
-- url     : https://prove2.me/theorems/2da0085b-7bb6-4bdb-81c9-3e910b6b8311
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSEnc.Residual` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSEnc.Residual` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSEnc.Residual` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSEnc.Residual (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSEnc/Residual.lean)

import Definitions.Def_CK_GeneralCK_RadialDerivatives
import Definitions.Def_CK_GeneralCK_EtaMonotone
import Definitions.Def_CK_GeneralCK_ProfileBasics

-- ===== source module CKLaneC.RSEnc.Residual =====
section

/-!
# Lane C (RA-stat): residual signs ⇒ enclosures of the implicit inverses (R1's δ-coordinates)

Lane R1 represents the implicit inverses in the coordinate `δ = 1 - 2v` with
`h(δ) = H((1 - δ)/2)`:

* contact:  `δ_true = 1 - 2 · radialContact z 1`, residual `z · h(δ) - δ` (decreasing in `δ`);
* entropy:  `δ_true = 1 - 2 · entropyInverse E`,  residual `h(δ) - E`      (decreasing in `δ`).

A nonnegative residual certifies `δ ≤ δ_true`, a nonpositive one `δ_true ≤ δ`.  All four statements
are immediate from the corpus inverse laws (`radialContact_le_iff`, `le_radialContact_iff`,
`entropyInverse_H_lower`, `entropyInverse_mono`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneC.RSEnc

open GeneralCK

/-- R1's entropy coordinate `h(δ) = H((1-δ)/2)`. -/
noncomputable def hdelta (δ : ℝ) : ℝ := H ((1 - δ) / 2)

private theorem H_nonneg_rs {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : 0 ≤ H v := by
  unfold H
  exact div_nonneg (Real.binEntropy_nonneg h0 h1) (Real.log_nonneg (by norm_num))

private theorem H_le_one_rs {v : ℝ} : H v ≤ 1 := by
  unfold H
  rw [div_le_one (Real.log_pos (by norm_num))]
  exact Real.binEntropy_le_log_two

theorem contact_delta_le {z δ : ℝ} (hz : 0 < z) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hres : 0 ≤ z * hdelta δ - δ) : δ ≤ 1 - 2 * radialContact z 1 := by
  have hv0 : 0 ≤ (1 - δ) / 2 := by linarith
  have hv1 : (1 - δ) / 2 ≤ 1 / 2 := by linarith
  have h := (radialContact_le_iff hz (by norm_num : (0 : ℝ) < 1) hv0 hv1).2 (by
    unfold hdelta at hres
    have e : 1 - 2 * ((1 - δ) / 2) = δ := by ring
    rw [e]
    linarith)
  linarith

theorem contact_delta_ge {z δ : ℝ} (hz : 0 < z) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hres : z * hdelta δ - δ ≤ 0) : 1 - 2 * radialContact z 1 ≤ δ := by
  have hv0 : 0 ≤ (1 - δ) / 2 := by linarith
  have hv1 : (1 - δ) / 2 ≤ 1 / 2 := by linarith
  have h := (le_radialContact_iff hz (by norm_num : (0 : ℝ) < 1) hv0 hv1).2 (by
    unfold hdelta at hres
    have e : 1 - 2 * ((1 - δ) / 2) = δ := by ring
    rw [e]
    linarith)
  linarith

theorem entropy_delta_le {E δ : ℝ} (hE0 : 0 ≤ E) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hres : 0 ≤ hdelta δ - E) : δ ≤ 1 - 2 * entropyInverse E := by
  have hv0 : 0 ≤ (1 - δ) / 2 := by linarith
  have hv1 : (1 - δ) / 2 ≤ 1 / 2 := by linarith
  unfold hdelta at hres
  have hmono := entropyInverse_mono hE0 H_le_one_rs (show E ≤ H ((1 - δ) / 2) by linarith)
  rw [entropyInverse_H_lower hv0 hv1] at hmono
  linarith

theorem entropy_delta_ge {E δ : ℝ} (hE1 : E ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hres : hdelta δ - E ≤ 0) : 1 - 2 * entropyInverse E ≤ δ := by
  have hv0 : 0 ≤ (1 - δ) / 2 := by linarith
  have hv1 : (1 - δ) / 2 ≤ 1 / 2 := by linarith
  unfold hdelta at hres
  have hHnn := H_nonneg_rs hv0 (by linarith)
  have hmono := entropyInverse_mono hHnn hE1 (show H ((1 - δ) / 2) ≤ E by linarith)
  rw [entropyInverse_H_lower hv0 hv1] at hmono
  linarith

/-- Two-sided contact enclosure from two residual signs. -/
theorem contact_delta_mem {z δlo δhi : ℝ} (hz : 0 < z) (h0 : 0 ≤ δlo) (hlohi : δlo ≤ δhi)
    (h1 : δhi ≤ 1) (hlo : 0 ≤ z * hdelta δlo - δlo) (hhi : z * hdelta δhi - δhi ≤ 0) :
    δlo ≤ 1 - 2 * radialContact z 1 ∧ 1 - 2 * radialContact z 1 ≤ δhi :=
  ⟨contact_delta_le hz h0 (hlohi.trans h1) hlo,
    contact_delta_ge hz (h0.trans hlohi) h1 hhi⟩

/-- Two-sided entropy-inverse enclosure from two residual signs. -/
theorem entropy_delta_mem {E δlo δhi : ℝ} (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (h0 : 0 ≤ δlo)
    (hlohi : δlo ≤ δhi) (h1 : δhi ≤ 1) (hlo : 0 ≤ hdelta δlo - E) (hhi : hdelta δhi - E ≤ 0) :
    δlo ≤ 1 - 2 * entropyInverse E ∧ 1 - 2 * entropyInverse E ≤ δhi :=
  ⟨entropy_delta_le hE0 h0 (hlohi.trans h1) hlo,
    entropy_delta_ge hE1 (h0.trans hlohi) h1 hhi⟩

end CKLaneC.RSEnc

end


