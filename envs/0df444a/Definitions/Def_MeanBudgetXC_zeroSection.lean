-- Prove2me | Definitions.Def_MeanBudgetXC_zeroSection
-- name    : MeanBudgetXC_zeroSection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:35.570008+00:00
-- url     : https://prove2.me/theorems/233f7b99-e865-44c3-9fbe-e1eee2e35621
-- title:
--   The zero section $Z_Q$
-- statement:
--   The **zero section** of a graph $Q$ at context size $d$ is the set
--   $$Z_Q=\{x\ge0:c_S\cdot x\le1\ (|S|=d)\}\subseteq\mathbb{R}^E.$$
--   Lemma 4.1 identifies it with the face of the pair body on which the nonedge coordinates vanish.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.1, p.17, display (11)

import Mathlib
import Definitions.Def_MeanBudgetXC_coverVec

namespace MeanBudgetXC

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **zero section** `Z_Q = {x ≥ 0 : c_S · x ≤ 1 (|S| = d)}` of (11) (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 4.1, p.17). -/
def zeroSection (Q : SimpleGraph V) [DecidableRel Q.Adj] (d : ℕ) : Set (Q.edgeSet → ℝ) :=
  {x | 0 ≤ x ∧ ∀ S : Finset V, S.card = d → coverVec Q S ⬝ᵥ x ≤ 1}

end MeanBudgetXC


