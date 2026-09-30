-- Prove2me | Definitions.Def_CK_CKLaneN23_CPosSplit
-- name    : CK_CKLaneN23_CPosSplit
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T11:25:15.841375+00:00
-- url     : https://prove2.me/theorems/76b91316-b54a-474b-80d9-7a9e8ea8ab61
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CPosSplit` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CPosSplit` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CPosSplit` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CPosSplit (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CPosSplit.lean)

import Definitions.Def_CK_CKLaneN23_CornerFinal_v2

-- ===== source module CKLaneN23.CPosSplit =====
section
set_option maxRecDepth 100000

/-!
# CKLaneN23.CPosSplit — the positivity grid as independent cell checks (Lane N23b)

`grid_of_forall` is the converse of `grid_aux`: a grid check holds if each of its cells does.  It lets
the 8 × 16 positivity grid of the corner checker (`posCheckC`) be kernel-evaluated cell by cell
(`boxCell j k`, modules `CKLaneN23.PosCell.C<j>_<k>`), each cell being exactly the `(j, k)` entry of
`posGrid D_tc_Gam.P D_tc_Gam.r D_tc_Gam.n 8 16`.  No new mathematics: only Boolean bookkeeping.
-/

namespace CKLaneN23.CT

theorem grid_rec_of_forall (lo hi : ℚ) (f : ℚ → ℚ → Bool) (m k : ℕ)
    (h : ∀ j < k, f (lo + (hi - lo) * (j : ℚ) / m) (lo + (hi - lo) * ((j : ℚ) + 1) / m) = true) :
    Nat.rec (motive := fun _ => Bool) true
      (fun j ih => ih && f (lo + (hi - lo) * (j : ℚ) / m) (lo + (hi - lo) * ((j : ℚ) + 1) / m)) k = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (Nat.rec (motive := fun _ => Bool) true
      (fun j ih => ih && f (lo + (hi - lo) * (j : ℚ) / m) (lo + (hi - lo) * ((j : ℚ) + 1) / m)) k &&
        f (lo + (hi - lo) * (k : ℚ) / m) (lo + (hi - lo) * ((k : ℚ) + 1) / m)) = true
    rw [ih (fun j hj => h j (by omega)), h k (by omega)]
    rfl

theorem grid_of_forall (lo hi : ℚ) (f : ℚ → ℚ → Bool) (m : ℕ)
    (h : ∀ j < m, f (lo + (hi - lo) * (j : ℚ) / m) (lo + (hi - lo) * ((j : ℚ) + 1) / m) = true) :
    grid lo hi f m = true :=
  grid_rec_of_forall lo hi f m m h

/-- the `(j, k)` cell (σ-interval `j` of 8, τ-interval `k` of 16) of the corner positivity grid -/
noncomputable def boxCell (j k : ℕ) : Bool :=
  boxChk D_tc_Gam.P D_tc_Gam.r D_tc_Gam.n
    ((-1 / 2) + (1 / 2 - (-1 / 2)) * (j : ℚ) / (8 : ℕ))
    ((-1 / 2) + (1 / 2 - (-1 / 2)) * ((j : ℚ) + 1) / (8 : ℕ))
    ((-1 / 2) + (1 / 2 - (-1 / 2)) * (k : ℚ) / (16 : ℕ))
    ((-1 / 2) + (1 / 2 - (-1 / 2)) * ((k : ℚ) + 1) / (16 : ℕ))

/-- one row of the corner positivity grid (σ-interval number `j` of 8) -/
noncomputable def posRow (j : ℕ) : Bool :=
  grid (-1 / 2) (1 / 2) (fun c d => boxChk D_tc_Gam.P D_tc_Gam.r D_tc_Gam.n
    ((-1 / 2) + (1 / 2 - (-1 / 2)) * (j : ℚ) / (8 : ℕ))
    ((-1 / 2) + (1 / 2 - (-1 / 2)) * ((j : ℚ) + 1) / (8 : ℕ)) c d) 16

theorem posRow_of_cells (j : ℕ) (h : ∀ k < 16, boxCell j k = true) : posRow j = true :=
  grid_of_forall (-1 / 2) (1 / 2) _ 16 (fun k hk => h k hk)

theorem posCheckC_of_rows (h : ∀ j < 8, posRow j = true) : posCheckC = true := by
  have hz : zeroPrefix D_tc_Gam.P 2 = true := by decide +kernel
  have hn : decide (2 ≤ D_tc_Gam.n) = true := by decide +kernel
  have hg : posGrid D_tc_Gam.P D_tc_Gam.r D_tc_Gam.n 8 16 = true :=
    grid_of_forall (-1 / 2) (1 / 2) _ 8 (fun j hj => h j hj)
  unfold posCheckC
  rw [hz, hn, hg]
  rfl

theorem forall_lt_8 {P : ℕ → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5)
    (h6 : P 6) (h7 : P 7) : ∀ j < 8, P j := by
  intro j hj
  interval_cases j <;> assumption

theorem forall_lt_16 {P : ℕ → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5)
    (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) (h12 : P 12) (h13 : P 13)
    (h14 : P 14) (h15 : P 15) : ∀ k < 16, P k := by
  intro k hk
  interval_cases k <;> assumption

end CKLaneN23.CT

end


