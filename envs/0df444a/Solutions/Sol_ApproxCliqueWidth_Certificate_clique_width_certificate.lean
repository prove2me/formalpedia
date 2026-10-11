-- Prove2me | solution 1 for ApproxCliqueWidth.Certificate.clique_width_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T15:48:37.610309+00:00
-- url     : https://prove2.me/submissions/0cb41cd9-550d-4d57-81f2-e990a4821d81
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_KExpr
import Definitions.Def_ApproxCliqueWidth_Certificate_CutRank
import Definitions.Def_ApproxCliqueWidth_Certificate_BranchDecomp
import Definitions.Def_ApproxCliqueWidth_Certificate_Interpolation
import Theorems.Thm_ApproxCliqueWidth_Certificate_bw_ge_of_wellLinked
import Theorems.Thm_ApproxCliqueWidth_Certificate_cutrk_symmetric_interpolation
import Theorems.Thm_ApproxCliqueWidth_Certificate_bw_le_of_no_wellLinked
import Theorems.Thm_ApproxCliqueWidth_Certificate_rwd_le_cwd_le

set_option autoImplicit false

open ApproxCliqueWidth.Certificate in
theorem cutrk_empty_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : cutrk G ∅ = 0 := by
  unfold cutrk cutrkStar
  have h := Matrix.rank_le_card_height
    ((G.adjMatrix (ZMod 2)).submatrix (fun x : (∅ : Finset V) => (x : V))
      (fun y : (((∅ : Finset V))ᶜ : Finset V) => (y : V)))
  have h1 : Fintype.card (∅ : Finset V) = 0 := by simp
  rw [h1] at h
  have : (Matrix.rank ((G.adjMatrix (ZMod 2)).submatrix (fun x : (∅ : Finset V) => (x : V))
      (fun y : (((∅ : Finset V))ᶜ : Finset V) => (y : V)))) = 0 := Nat.le_zero.mp h
  exact_mod_cast this

open ApproxCliqueWidth.Certificate in
theorem cutrk_singleton_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : cutrk G {v} ≤ 1 := by
  unfold cutrk cutrkStar
  have h := Matrix.rank_le_card_height
    ((G.adjMatrix (ZMod 2)).submatrix (fun x : ({v} : Finset V) => (x : V))
      (fun y : (({v} : Finset V)ᶜ : Finset V) => (y : V)))
  have h1 : Fintype.card ({v} : Finset V) = 1 := by simp
  have : (Matrix.rank ((G.adjMatrix (ZMod 2)).submatrix (fun x : ({v} : Finset V) => (x : V))
      (fun y : (({v} : Finset V)ᶜ : Finset V) => (y : V)))) ≤ 1 := by
    rw [← h1]; exact h
  exact_mod_cast this

open ApproxCliqueWidth.Certificate in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k) :
    ((∃ W : Finset V, W.card = 3 * k + 1 ∧ IsWellLinked (cutrk G) W) → ¬ HasKExpr G k) ∧
    ((¬ ∃ W : Finset V, W.card = 3 * k + 1 ∧ IsWellLinked (cutrk G) W) →
        HasKExpr G (2 ^ (3 * k + 2) - 1)) := by
  obtain ⟨hsym, hsub, -, -⟩ := cutrk_symmetric_interpolation G
  have h0 := cutrk_empty_eq_zero G
  have h1 := cutrk_singleton_le_one G
  refine ⟨?_, ?_⟩
  · rintro ⟨W, hWc, hW⟩ hK
    have hcard : 3 * k + 1 ≤ Fintype.card V := by
      rw [← hWc]; exact Finset.card_le_univ W
    rcases (rwd_le_cwd_le G).1 k hK with ⟨hle, _⟩ | ⟨D, hD⟩
    · omega
    · obtain ⟨u, w, hadj, hlt⟩ :=
        bw_ge_of_wellLinked (by omega) (cutrk G) hsym hsub h0 (3 * k + 1) (by omega) W hWc hW D
      have := hD u w hadj
      push_cast at hlt
      linarith
  · intro hno
    have hbw : BwLE (cutrk G) ((3 * k + 1 : ℕ) : ℤ) :=
      bw_le_of_no_wellLinked (cutrk G) hsym hsub h1 h0 (3 * k + 1) hno
    have := (rwd_le_cwd_le G).2 ‹Nonempty V› (3 * k + 1) (by exact_mod_cast hbw)
    have e : 3 * k + 1 + 1 = 3 * k + 2 := by omega
    rw [e] at this
    exact this
