-- Prove2me | solution 1 for APFPaper1.Foundation.novelty_positive_gap_ledger
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-10-11T23:36:26.736058+00:00
-- url     : https://prove2.me/submissions/1129e07d-79b8-41a2-8a51-0a322bef25dd

import Definitions.Def_APFPaper1_SupportNovel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
set_option autoImplicit false
open Classical
open APFPaper1.Foundation

theorem solution {D P Record : Type*} [DecidableEq D] (L : Ledger D P Record)
    (S : Finset D) (d : D) (hf : Feasible L (insert d S))
    (hn : SupportNovel L S d) : cost L S < cost L (insert d S) := by
  obtain ⟨η, hη, hn⟩ := hn
  obtain ⟨p, hp⟩ := hf
  have hbound : cost L S + η ≤ cost L (insert d S) := by
    apply le_csInf (show (costs L (insert d S)).Nonempty from ⟨L.price p, p, hp, rfl⟩)
    rintro c ⟨q, hq, rfl⟩
    by_contra! hlt
    exact hn q (L.serves_mono q S (insert d S) (Finset.subset_insert _ _) hq)
      (le_of_lt hlt) (L.carries_of_serves q (insert d S) d hq (Finset.mem_insert_self _ _))
  linarith
