-- Prove2me | Definitions.Def_CombOpt_ChvatalRank_chvatalClosure
-- name    : CombOpt_ChvatalRank_chvatalClosure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:39.183875+00:00
-- url     : https://prove2.me/theorems/92ad1634-e5f8-489a-b9b0-72e602771ab2
-- title:
--   The closure $P'$
-- statement:
--   For $P\subseteq\mathbb R^n$, the **closure** $P'$ is the set of all vectors in $P$ that satisfy every Gomory–Chvátal cut for $P$.
--
--   The closure is the first "wave" of cuts towards $P_I$. Although infinitely many cuts are involved, Theorem 6.34 shows that for a rational polyhedron finitely many suffice.
--
--   **Formalization Note** The definition uses the set $P$ and all cuts, not a defining system and not the finite subfamily (6.22). The intersection with $P$ is explicit, which also gives $\emptyset'=\emptyset$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.7, p. 233 (PDF 241)

import Mathlib
import Definitions.Def_CombOpt_ChvatalRank_IsGomoryChvatalCut

open Matrix

namespace CombOpt.ChvatalRank

/-- **The closure `P′`.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.7, p. 233 (PDF 241): "let P′ denote the set of all vectors in P
that satisfy every Gomory-Chvátal cut for P."

**Formalization Note.** Defined from the set `P` by the valid-inequality form of a cut, with all
(infinitely many) cuts, not from a defining system or from the finite subsystem (6.22) of the proof
of Theorem 6.34. `∅′ = ∅`. -/
def chvatalClosure {n : ℕ} (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | x ∈ P ∧ ∀ (c : Fin n → ℝ) (t : ℝ), IsGomoryChvatalCut P c t → c ⬝ᵥ x ≤ t}

end CombOpt.ChvatalRank


