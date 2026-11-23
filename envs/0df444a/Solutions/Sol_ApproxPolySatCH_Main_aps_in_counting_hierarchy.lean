-- Prove2me | solution 1 for ApproxPolySatCH.Main.aps_in_counting_hierarchy
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:24:01.71237+00:00
-- url     : https://prove2.me/submissions/d951bd62-61b5-4eff-9be4-fc20341c8c0b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages
import Theorems.Thm_ApproxPolySatCH_Main_aps_to_mrv
import Theorems.Thm_ApproxPolySatCH_Main_mrv_in_ch
import Theorems.Thm_ApproxPolySatCH_Main_circuit_dense_reduction
import Theorems.Thm_ApproxPolySatCH_Main_randomized_turing_in_ch
import Theorems.Thm_ApproxPolySatCH_Main_manyOne_in_ch
import Theorems.Thm_ApproxPolySatCH_Main_dense_sparse_reductions
import Theorems.Thm_ApproxPolySatCH_Main_inCH_three_tagged_union

set_option autoImplicit false

open ApproxPolySatCH.Main

theorem solution : ∀ k : CoefficientField, InCH (APSLanguage k) := by
  intro k
  have hs : InCH (SparseLanguage k) := by
    rcases aps_to_mrv with ⟨hrat, hfin⟩
    rcases mrv_in_ch with ⟨hratCH, hfinCH⟩
    cases k with
    | rational =>
        exact randomized_turing_in_ch hratCH hrat
    | finite p hp mu hmon hpos hirr =>
        obtain ⟨M, c, d, a, b, e, h, hdec, hquery⟩ :=
          hfin (.finite p hp mu hmon hpos hirr) (by simp)
        exact randomized_turing_in_ch hfinCH ⟨M, c, d, a, b, hdec⟩
  rcases dense_sparse_reductions k with ⟨hds, hsd⟩
  have hd : InCH (DenseLanguage k) := manyOne_in_ch hds hs
  have hc : InCH (CircuitLanguage k) :=
    manyOne_in_ch (circuit_dense_reduction k) hd
  simpa [APSLanguage] using
    (inCH_three_tagged_union (SparseLanguage k) (DenseLanguage k) (CircuitLanguage k)
      hs hd hc)
