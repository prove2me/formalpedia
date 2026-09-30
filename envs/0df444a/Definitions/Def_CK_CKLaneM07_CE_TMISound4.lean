-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_TMISound4
-- name    : CK_CKLaneM07_CE_TMISound4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:54:43.215498+00:00
-- url     : https://prove2.me/theorems/7a9fc09e-d868-4a85-86d8-f1ddc6b31f35
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.TMISound4` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.TMISound4` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.TMISound4` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.TMISound4 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/TMISound4.lean)

import Definitions.Def_CK_CKLaneM07_CE_TMISound3

-- ===== source module CKLaneM07.CE.TMISound4 =====
section

/-!
# Lane M07 / CE-stat: soundness of the fixed-point Taylor-model kernel (part 4: centring, log, reciprocal)
-/

set_option autoImplicit false

namespace CKLaneM07.CE

/-! ## Centring -/

theorem pEval_center (x y : ℝ) (s : TMI) :
    pEval x y s.center.p = pEval x y s.p - (pC00 s.p : ℝ) := by
  rcases s with ⟨p, r⟩
  rcases p with _ | ⟨r0, p⟩
  · simp [TMI.center, pC00, pEval]
  · rcases r0 with _ | ⟨a, r0⟩
    · simp [TMI.center, pC00, pEval, rowEval]
    · simp only [TMI.center, pC00, pEval, rowEval]; push_cast; ring

theorem center_r (s : TMI) : s.center.r = s.r := by
  rcases s with ⟨p, r⟩
  rcases p with _ | ⟨r0, p⟩
  · rfl
  · rcases r0 with _ | ⟨a, r0⟩ <;> rfl

/-- real value of the constant coefficient -/
noncomputable def c0R (s : TMI) : ℝ := (pC00 s.p : ℝ) / SC

theorem EnclAt.center {x y u : ℝ} {s : TMI} (hs : EnclAt x y u s) :
    EnclAt x y (u - c0R s) s.center := by
  unfold EnclAt at *
  rw [pEval_center, center_r]
  unfold c0R
  have hS := SC_pos
  calc |u - (pC00 s.p : ℝ) / SC - (pEval x y s.p - (pC00 s.p : ℝ)) / SC| =
        |u - pEval x y s.p / SC| := by congr 1; field_simp; ring
    _ ≤ _ := hs

theorem abs_le_of_EnclAt {x y u : ℝ} {s : TMI} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hs : EnclAt x y u s) :
    |u| ≤ ((pAbs s.p + s.r : ℕ) : ℝ) / SC := by
  unfold EnclAt at hs
  have hS := SC_pos
  have hp := abs_pEval_le hx hy s.p
  have h1 : |u| ≤ |pEval x y s.p / SC| + (s.r : ℝ) / SC := by
    have := abs_sub_abs_le_abs_sub u (pEval x y s.p / SC)
    linarith
  rw [abs_div, abs_of_pos hS] at h1
  push_cast
  calc |u| ≤ |pEval x y s.p| / SC + (s.r : ℝ) / SC := h1
    _ ≤ (pAbs s.p : ℝ) / SC + (s.r : ℝ) / SC := by gcongr
    _ = _ := by ring

/-! ## The relative deviation `w = (u - u0)/u0` -/

theorem EnclAt.wOf {x y u : ℝ} {s : TMI} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hs : EnclAt x y u s)
    (h0 : 0 < pC00 s.p) : EnclAt x y ((u - c0R s) / c0R s) s.wOf.1 := by
  have hS := SC_pos
  have hc := hs.center
  have hm := EnclAt.mulC hx hy ((ONE * ONE) / pC00 s.p) hc
  have hu0 : (0 : ℝ) < (pC00 s.p : ℝ) := by exact_mod_cast h0
  obtain ⟨hi1, hi2⟩ := ediv_bounds (ONE * ONE) (pC00 s.p) h0
  set inv := (ONE * ONE) / pC00 s.p
  have hdev := abs_le_of_EnclAt hx hy hc
  unfold EnclAt at hm ⊢
  simp only [TMI.wOf]
  set c := s.center
  set m := TMI.mulC inv c
  have hSC : SC = ((ONE : ℤ) : ℝ) := rfl
  -- (u - u0)/u0 = (u - u0) * (SC / u0)
  have e1 : (u - c0R s) / c0R s = (u - c0R s) * (SC / (pC00 s.p : ℝ)) := by
    unfold c0R; field_simp
  have hgap : |SC / (pC00 s.p : ℝ) - (inv : ℝ) / SC| ≤ 1 / SC := by
    push_cast at hi1 hi2
    rw [← hSC] at hi1 hi2
    have e2 : SC / (pC00 s.p : ℝ) - (inv : ℝ) / SC = (SC * SC / (pC00 s.p : ℝ) - (inv : ℝ)) / SC := by
      field_simp
    rw [e2, abs_div, abs_of_pos hS]
    gcongr
    rw [abs_le]; constructor <;> linarith
  have herr : |(u - c0R s) * (SC / (pC00 s.p : ℝ)) - (inv : ℝ) / SC * (u - c0R s)| ≤
      ((pAbs c.p + c.r : ℕ) : ℝ) / SC / SC := by
    have e3 : (u - c0R s) * (SC / (pC00 s.p : ℝ)) - (inv : ℝ) / SC * (u - c0R s) =
        (u - c0R s) * (SC / (pC00 s.p : ℝ) - (inv : ℝ) / SC) := by ring
    rw [e3, abs_mul]
    calc |u - c0R s| * |SC / (pC00 s.p : ℝ) - (inv : ℝ) / SC| ≤
          ((pAbs c.p + c.r : ℕ) : ℝ) / SC * (1 / SC) := by
          gcongr
      _ = _ := by ring
  have hcd := cdiv_ge_SC (pAbs c.p + c.r)
  rw [e1]
  push_cast at hcd ⊢
  calc |(u - c0R s) * (SC / (pC00 s.p : ℝ)) - pEval x y m.p / SC| ≤
        |(u - c0R s) * (SC / (pC00 s.p : ℝ)) - (inv : ℝ) / SC * (u - c0R s)| +
          |(inv : ℝ) / SC * (u - c0R s) - pEval x y m.p / SC| := abs_sub_le _ _ _
    _ ≤ ((pAbs c.p : ℝ) + (c.r : ℝ)) / SC / SC + (m.r : ℝ) / SC := by
        gcongr
        · push_cast at herr; exact herr
    _ ≤ ((m.r : ℝ) + (cdiv (pAbs c.p + c.r) ONEn : ℝ) + 1) / SC := by
        have e4 : ((pAbs c.p : ℝ) + (c.r : ℝ)) / SC / SC + (m.r : ℝ) / SC =
            (((pAbs c.p : ℝ) + (c.r : ℝ)) / SC + (m.r : ℝ)) / SC := by ring
        rw [e4]
        apply div_le_div_of_nonneg_right _ hS.le
        linarith
    _ = _ := by ring

theorem rhoQ_cast (w : TMI) : ((rhoQ w : ℚ) : ℝ) = ((pAbs w.p + w.r : ℕ) : ℝ) / SC := by
  unfold rhoQ; rw [SC_eq_nat]; push_cast; ring

end CKLaneM07.CE

end


