-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_TMISound3
-- name    : CK_CKLaneM07_CE_TMISound3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:52:35.067433+00:00
-- url     : https://prove2.me/theorems/722d319b-696c-4094-a671-400163d3f977
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.TMISound3` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.TMISound3` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.TMISound3` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.TMISound3 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/TMISound3.lean)

import Definitions.Def_CK_CKLaneM07_CE_TMISound2

-- ===== source module CKLaneM07.CE.TMISound3 =====
section

/-!
# Lane M07 / CE-stat: soundness of the fixed-point Taylor-model kernel (part 3: truncated products)
-/

set_option autoImplicit false

namespace CKLaneM07.CE

theorem rowEval_take_drop (y : ℝ) : ∀ (m : ℕ) (s : RowI),
    rowEval y s = rowEval y (s.take m) + y ^ m * rowEval y (s.drop m)
  | 0, s => by simp [rowEval]
  | m + 1, [] => by simp [rowEval]
  | m + 1, b :: s => by
      simp only [List.take_succ_cons, List.drop_succ_cons, rowEval]
      rw [rowEval_take_drop y m s]
      ring

theorem rowEval_scale (y : ℝ) (a : ℤ) : ∀ s : RowI,
    rowEval y (s.map (fun b => a * b)) = (a : ℝ) * rowEval y s
  | [] => by simp [rowEval]
  | b :: s => by
      simp only [List.map_cons, rowEval, rowEval_scale y a s]
      push_cast; ring

theorem abs_pow_le_one {y : ℝ} (hy : |y| ≤ 1) (m : ℕ) : |y ^ m| ≤ 1 := by
  rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hy

/-- truncated row product: error bounded by `rowDropT` -/
theorem rowMulT_err {y : ℝ} (hy : |y| ≤ 1) : ∀ (n : ℕ) (r s : RowI),
    |rowEval y r * rowEval y s - rowEval y (rowMulT n r s)| ≤ (rowDropT n r s : ℝ)
  | 0, r, s => by
      simp only [rowMulT, rowDropT, rowEval, sub_zero]
      push_cast
      rw [abs_mul]
      exact mul_le_mul (abs_rowEval_le hy r) (abs_rowEval_le hy s) (abs_nonneg _) (Nat.cast_nonneg _)
  | n + 1, [], s => by simp [rowMulT, rowDropT, rowEval]
  | n + 1, a :: r, s => by
      have ih := rowMulT_err hy n r s
      simp only [rowMulT, rowDropT, rowEval_rowAdd, rowEval]
      rw [rowEval_scale]
      have hs := rowEval_take_drop y (n + 1) s
      push_cast
      have e : ((a : ℝ) + y * rowEval y r) * rowEval y s -
          ((a : ℝ) * rowEval y (s.take (n + 1)) + (0 + y * rowEval y (rowMulT n r s))) =
          (a : ℝ) * (y ^ (n + 1) * rowEval y (s.drop (n + 1))) +
            y * (rowEval y r * rowEval y s - rowEval y (rowMulT n r s)) := by
        rw [hs]; ring
      rw [e]
      calc _ ≤ |(a : ℝ) * (y ^ (n + 1) * rowEval y (s.drop (n + 1)))| +
            |y * (rowEval y r * rowEval y s - rowEval y (rowMulT n r s))| := abs_add_le _ _
        _ ≤ |(a : ℝ)| * (1 * (rowAbs (s.drop (n + 1)) : ℝ)) + 1 * (rowDropT n r s : ℝ) := by
            rw [abs_mul, abs_mul, abs_mul]
            gcongr
            · exact abs_pow_le_one hy _
            · exact abs_rowEval_le hy _
        _ = _ := by rw [natAbs_cast]; ring

theorem rowsFrom_err {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (K i1 : ℕ) (r : RowI) :
    ∀ (i2 : ℕ) (q : PolI),
      |rowEval y r * pEval x y q - pEval x y (rowsFrom K i1 r i2 q)| ≤ (rowsDrop K i1 r i2 q : ℝ)
  | i2, [] => by simp [rowsFrom, rowsDrop, pEval]
  | i2, s :: q => by
      unfold rowsFrom rowsDrop
      split_ifs with h
      · have ih := rowsFrom_err hx hy K i1 r (i2 + 1) q
        have hm := rowMulT_err hy (K + 1 - (i1 + i2)) r s
        simp only [pEval]
        push_cast
        have e : rowEval y r * (rowEval y s + x * pEval x y q) -
            (rowEval y (rowMulT (K + 1 - (i1 + i2)) r s) + x * pEval x y (rowsFrom K i1 r (i2 + 1) q)) =
            (rowEval y r * rowEval y s - rowEval y (rowMulT (K + 1 - (i1 + i2)) r s)) +
              x * (rowEval y r * pEval x y q - pEval x y (rowsFrom K i1 r (i2 + 1) q)) := by ring
        rw [e]
        calc _ ≤ |rowEval y r * rowEval y s - rowEval y (rowMulT (K + 1 - (i1 + i2)) r s)| +
              |x * (rowEval y r * pEval x y q - pEval x y (rowsFrom K i1 r (i2 + 1) q))| :=
              abs_add_le _ _
          _ ≤ (rowDropT (K + 1 - (i1 + i2)) r s : ℝ) + 1 * (rowsDrop K i1 r (i2 + 1) q : ℝ) := by
              rw [abs_mul]
              gcongr
          _ = _ := by ring
      · simp only [pEval, sub_zero]
        push_cast
        rw [abs_mul]
        exact mul_le_mul (abs_rowEval_le hy r) (abs_pEval_le hx hy (s :: q)) (abs_nonneg _)
          (Nat.cast_nonneg _)

theorem pMulKept_err {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (K : ℕ) (q : PolI) :
    ∀ (i1 : ℕ) (p : PolI),
      |pEval x y p * pEval x y q - pEval x y (pMulKept K q i1 p)| ≤ (pDrop K q i1 p : ℝ)
  | i1, [] => by simp [pMulKept, pDrop, pEval]
  | i1, r :: p => by
      unfold pMulKept pDrop
      split_ifs with h
      · have ih := pMulKept_err hx hy K q (i1 + 1) p
        have hr := rowsFrom_err hx hy K i1 r 0 q
        simp only [pEval, pEval_pAdd, rowEval]
        push_cast
        have e : (rowEval y r + x * pEval x y p) * pEval x y q -
            (pEval x y (rowsFrom K i1 r 0 q) + (0 + x * pEval x y (pMulKept K q (i1 + 1) p))) =
            (rowEval y r * pEval x y q - pEval x y (rowsFrom K i1 r 0 q)) +
              x * (pEval x y p * pEval x y q - pEval x y (pMulKept K q (i1 + 1) p)) := by ring
        rw [e]
        calc _ ≤ |rowEval y r * pEval x y q - pEval x y (rowsFrom K i1 r 0 q)| +
              |x * (pEval x y p * pEval x y q - pEval x y (pMulKept K q (i1 + 1) p))| :=
              abs_add_le _ _
          _ ≤ (rowsDrop K i1 r 0 q : ℝ) + 1 * (pDrop K q (i1 + 1) p : ℝ) := by
              rw [abs_mul]
              gcongr
          _ = _ := by ring
      · simp only [pEval, sub_zero]
        push_cast
        rw [abs_mul]
        exact mul_le_mul (abs_pEval_le hx hy (r :: p)) (abs_pEval_le hx hy q) (abs_nonneg _)
          (Nat.cast_nonneg _)

/-- the fixed-point Taylor-model product is sound -/
theorem EnclAt.mul {x y u v : ℝ} {s t : TMI} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (K : ℕ)
    (hs : EnclAt x y u s) (ht : EnclAt x y v t) : EnclAt x y (u * v) (TMI.mul K s t) := by
  unfold EnclAt at *
  have hS := SC_pos
  simp only [TMI.mul]
  set kept := pMulKept K t.p 0 s.p
  have hkept := pMulKept_err hx hy K t.p 0 s.p
  have hround := pEval_round 1 hx hy kept
  simp only [one_mul] at hround
  set rp := kept.map (List.map (fun a => a / ONE))
  set Ps := pEval x y s.p
  set Pt := pEval x y t.p
  have hPs := abs_pEval_le hx hy s.p
  have hPt := abs_pEval_le hx hy t.p
  have hkr := (show ((1 : ℤ) : ℝ) = 1 by norm_num)
  rw [hkr, one_div] at hround
  -- decomposition
  have e : u * v - pEval x y rp / SC =
      ((u - Ps / SC) * v + Ps / SC * (v - Pt / SC)) + (Ps * Pt - pEval x y kept) / SC / SC +
        (SC⁻¹ * pEval x y kept - pEval x y rp) / SC := by
    field_simp; ring
  rw [e]
  have hv : |v| ≤ (pAbs t.p : ℝ) / SC + (t.r : ℝ) / SC := by
    have := abs_sub_abs_le_abs_sub v (Pt / SC)
    rw [abs_div, abs_of_pos hS] at this
    have h2 : |Pt| / SC ≤ (pAbs t.p : ℝ) / SC := by gcongr
    linarith
  have h1 : |(u - Ps / SC) * v + Ps / SC * (v - Pt / SC)| ≤
      ((s.r : ℝ) * (pAbs t.p : ℝ) + (s.r : ℝ) * (t.r : ℝ) + (pAbs s.p : ℝ) * (t.r : ℝ)) / SC / SC := by
    calc _ ≤ |(u - Ps / SC) * v| + |Ps / SC * (v - Pt / SC)| := abs_add_le _ _
      _ = |u - Ps / SC| * |v| + |Ps| / SC * |v - Pt / SC| := by
          rw [abs_mul, abs_mul, abs_div, abs_of_pos hS]
      _ ≤ (s.r : ℝ) / SC * ((pAbs t.p : ℝ) / SC + (t.r : ℝ) / SC) + (pAbs s.p : ℝ) / SC * ((t.r : ℝ) / SC) := by
          gcongr
      _ = _ := by ring
  have h2 : |(Ps * Pt - pEval x y kept) / SC / SC| ≤ (pDrop K t.p 0 s.p : ℝ) / SC / SC := by
    rw [abs_div, abs_div, abs_of_pos hS]
    gcongr
  have h3 : |(SC⁻¹ * pEval x y kept - pEval x y rp) / SC| ≤ (pCount rp : ℝ) / SC := by
    rw [abs_div, abs_of_pos hS]
    gcongr
  have c1 := cdiv_ge_SC (pDrop K t.p 0 s.p)
  have c2 := cdiv_ge_SC (s.r * pAbs t.p)
  have c3 := cdiv_ge_SC (t.r * pAbs s.p)
  have c4 := cdiv_ge_SC (s.r * t.r)
  push_cast at c2 c3 c4 ⊢
  calc _ ≤ |(u - Ps / SC) * v + Ps / SC * (v - Pt / SC)| + |(Ps * Pt - pEval x y kept) / SC / SC| +
        |(SC⁻¹ * pEval x y kept - pEval x y rp) / SC| := abs_add_three _ _ _
    _ ≤ ((s.r : ℝ) * (pAbs t.p : ℝ) + (s.r : ℝ) * (t.r : ℝ) + (pAbs s.p : ℝ) * (t.r : ℝ)) / SC / SC +
          (pDrop K t.p 0 s.p : ℝ) / SC / SC + (pCount rp : ℝ) / SC := by
        gcongr
    _ ≤ ((cdiv (pDrop K t.p 0 s.p) ONEn : ℝ) + (pCount rp : ℝ) + (cdiv (s.r * pAbs t.p) ONEn : ℝ) +
          (cdiv (t.r * pAbs s.p) ONEn : ℝ) + (cdiv (s.r * t.r) ONEn : ℝ)) / SC := by
        have key : ((s.r : ℝ) * (pAbs t.p : ℝ) + (s.r : ℝ) * (t.r : ℝ) + (pAbs s.p : ℝ) * (t.r : ℝ)) / SC / SC +
            (pDrop K t.p 0 s.p : ℝ) / SC / SC + (pCount rp : ℝ) / SC =
            ((pDrop K t.p 0 s.p : ℝ) / SC + (pCount rp : ℝ) + (s.r : ℝ) * (pAbs t.p : ℝ) / SC +
              (t.r : ℝ) * (pAbs s.p : ℝ) / SC + (s.r : ℝ) * (t.r : ℝ) / SC) / SC := by ring
        rw [key]
        apply div_le_div_of_nonneg_right _ hS.le
        linarith
    _ = _ := by ring

end CKLaneM07.CE

end


