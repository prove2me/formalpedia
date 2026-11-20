-- Prove2me | Definitions.Def_VWZClique_Count
-- name    : VWZClique_Count
-- status  : Definition
-- author  : @orz
-- created : 2026-11-20T00:58:13.91526+00:00
-- url     : https://prove2.me/theorems/e6ea04a2-102e-4412-b689-d6bf0b1ae37c
-- title:
--   Word-RAM specification for exact clique counting
-- statement:
--   An accepting program must return the number of unordered cliques in the first output word. The word width grows logarithmically with graph order.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good (2026), Theorem 1.1 and Appendix A. https://zamir.prof/kclq.pdf

import Mathlib
import Definitions.Def_MonDepMW_RunsWithin

namespace VWZClique
open Classical in
noncomputable def count {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : ℕ :=
  ((Finset.univ.powersetCard k).filter fun s : Finset (Fin n) =>
    ∀ u ∈ s, ∀ v ∈ s, u ≠ v → G.Adj u v).card

def countsWithin (k : ℕ) (e : ℝ) : Prop :=
  ∃ (P : List TrulySubcubicAPSP.Instr) (b : ℕ) (C : ℝ), 0 < b ∧ 0 < C ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 2 ≤ n →
      ∃ t : ℕ, (t : ℝ) ≤ C * (n : ℝ) ^ e ∧
        MonDepMW.RunsWithin P (b * (n.log2 + 1)) t (MonDepMW.graphInput G)
          (fun out => out 0 = (count G k : ℤ))
end VWZClique


