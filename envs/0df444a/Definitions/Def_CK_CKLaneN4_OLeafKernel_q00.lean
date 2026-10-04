-- Prove2me | Definitions.Def_CK_CKLaneN4_OLeafKernel_q00
-- name    : CK_CKLaneN4_OLeafKernel_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T13:42:45.006703+00:00
-- url     : https://prove2.me/theorems/2b83eff5-178c-499d-a4da-ade5d2a5d40b
-- title:
--   Courtade–Kumar proof module `CKLaneN4.OLeafKernel (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.OLeafKernel (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.OLeafKernel (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.OLeafKernel (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/OLeafKernel (piece 1 of 4).lean)

import Definitions.Def_CK_CKLaneN4_LowEntropy25
import Definitions.Def_CK_CKLaneD_OCompact



/-!
# Lane N4: (O) leaf obligations for the archived labels 4, 7, 8, 9

Per-leaf obligation `CKLaneD.OCompact.OLeafOK (uvtBox p)` (the OP_Compact-region form of BRIEF §7) on
the full archived leaf image `CKLaneD.InUVT (uvtBox p)`.

* Label 4 (`global_eight_ratio`, OUTER_OPPOSITE.py): the archived method checks, on the whole leaf,
  `E.b ≤ 11/200`, `q.b ≤ 2/5`, `d.a ≥ 8 E.b`; the leaf is then owned by the union of the global
  eight-ratio theorem (`q ≤ 8E`) and PARENT8 (`q ≥ 8E`), with the `q = 0` face by parent equality.
  `checkL4 p w = true → OLeafOK (uvtBox p)` (`checkL4_sound`), unconditional: the witness is a rational
  box bound to the archived path by `CKLaneD.imageCheck` plus two log certificates.
* Labels 7, 8, 9 (`global_parent8`, `global_low_entropy_025`, `global_parent16`): every leaf image lies
  in `E ≤ 1/25` (Lane G1 `CKLaneG1.E25All.all_le`), where `OP_LowEntropy25` applies
  (`oLeafOK_of_le25`).
-/

namespace CKLaneN4

open GeneralCK CKLaneD CKLaneD.OCompact

/-- The clipped physical image of a leaf lies in a rational box certified by `imageCheck`
(copied from Lane M12 `CKLaneM12.inBox_of_imageCheck`). -/
theorem inBox_of_imageCheck {U : UVT} {B : Box} (h : imageCheck U B = true) {a b E : ℝ}
    (hin : InUVT U a b E) : InBox B a b E := by
  unfold imageCheck at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨ht0, ht1⟩, hal⟩, hah⟩, hbl⟩, hbh⟩ := h
  unfold InUVT at hin
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hin
  have hal' := pow2LowerOK_sound hal
  have hbl' := pow2UpperOK_sound hbl
  push_cast at hbl'
  refine ⟨hal'.trans h1, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hah with hah | hah
    · exact h2.trans (pow2UpperOK_sound hah)
    · have hq : ((1 / 10 : ℚ) : ℝ) ≤ (B.ahi : ℝ) := Rat.cast_le.mpr hah
      have h10 : ((1 / 10 : ℚ) : ℝ) = 1 / 10 := by norm_num
      rw [h10] at hq
      linarith
  · linarith
  · rcases hbh with hbh | hbh
    · have := pow2LowerOK_sound hbh
      push_cast at this
      linarith
    · have : (1 : ℝ) - (B.alo : ℝ) ≤ (B.bhi : ℝ) := by exact_mod_cast hbh
      linarith [hal'.trans h1]
  · rw [ht0]; exact h7
  · rw [ht1]; exact h8

/-! ## Labels 7, 8, 9: the low-entropy corollary -/

theorem oLeafOK_of_le25 {U : UVT} (h : ∀ a b E : ℝ, InUVT U a b E → E ≤ 1 / 25) : OLeafOK U := by
  intro k μ hab hsum hb ha _ _ _ hin hact
  exact opLowEntropy25 k μ hab hsum hb ha (h _ _ _ hin) hact

/-! ## Label 4: eight-ratio ∪ PARENT8 on the full leaf image -/

/-- Untrusted label-4 witness: rational box and log certificates at `ahi`, `blo`. -/
structure L4Witness where
  box : Box
  pa : PtCert
  pb : PtCert
  deriving Repr, DecidableEq

end CKLaneN4


