-- Prove2me | solution 1 for ApproxPolySatCH.Main.annihilator_presentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:42:27.026272+00:00
-- url     : https://prove2.me/submissions/b8345d4a-2db0-42ac-bb63-d8299db13e90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ApproxPolySatCH_Main_principal_irreducible_annihilator
import Theorems.Thm_ApproxPolySatCH_Main_annihilator_base_change
import Theorems.Thm_ApproxPolySatCH_Main_annihilator_generator_degree
import Theorems.Thm_ApproxPolySatCH_Main_aps_iff_annihilator_eval_zero

set_option autoImplicit false

open ApproxPolySatCH.Main

theorem solution {k : Type} [Field k] {n : ℕ}
    (hn : 1 ≤ n) (f : Fin (n + 1) → Poly k n)
    (hf : MinimallyDependent f) :
    ∃ H : Poly k (n + 1), AnnihilatorPresentation f H ∧
      H.totalDegree ≤ maxDegree f ^ (n + 1) ∧
      (APS f ↔ MvPolynomial.eval (0 : Fin (n + 1) → k) H = 0) := by
  obtain ⟨H, hirr, hker⟩ := principal_irreducible_annihilator hn f hf
  have hext : annihilator (extendedSystem f) =
      Ideal.span {MvPolynomial.map (algebraMap k (Constants k)) H} :=
    annihilator_base_change f H hker
  exact ⟨H, ⟨hirr, hker, hext⟩,
    annihilator_generator_degree hn f hf H hker,
    aps_iff_annihilator_eval_zero f H hext⟩
