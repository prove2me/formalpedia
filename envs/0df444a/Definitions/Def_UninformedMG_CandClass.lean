-- Prove2me | Definitions.Def_UninformedMG_CandClass
-- name    : UninformedMG_CandClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:08.399252+00:00
-- url     : https://prove2.me/theorems/edb4e687-2555-47be-a5db-e47318dfbfff
-- title:
--   Finite class of candidate value tables
-- statement:
--   A **candidate class** is a finite nonempty set $\mathcal V$ of candidates. Each candidate $v$ carries a value table $v_h(s)$ on every layer $h=1,\dots,H+1$ and state $s\in S_h$.
--
--   The algorithm runs on the grid of Eq. (19). Lemma B.5 is stated for a general class whose tables satisfy $v_1=v_{H+1}=0$ and $0\le v_h(s)\le1$.
--
--   **Formalization Note** A candidate is an index $v$ with table `val v`, so that two distinct candidates may have the same table. The grid's indices are its numerator tables, which are in bijection with its values.
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Section 1.4, p.5 (PDF p.7), and Lemma B.5, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_UninformedMG_Game

namespace UninformedMG

variable {H : ℕ}

/-- **Candidate class** of value tables (Section 1.4, p.5; Lemma B.5, p.22): a finite nonempty
index set `V` of candidates, each candidate `v` carrying a table `v_h(s)` on every layer,
including the terminal one.

**Formalization Note.** The paper identifies a candidate with its table; here a candidate is an
index `v : C` and its table is `val v`. The algorithm runs on the grid of Eq. (19) (`grid`);
the generic class is used by Lemma B.5, which assumes only `v_1 = v_{H+1} = 0` and
`0 ≤ v_h(s) ≤ 1`, stated there as hypotheses. -/
structure CandClass (G : Game H) where
  /-- The candidates. -/
  C : Type
  [cFintype : Fintype C]
  [cDecEq : DecidableEq C]
  [cNonempty : Nonempty C]
  /-- The value table `v_h(s)` of candidate `v` (Lean layer `h` = paper step `h + 1`). -/
  val : C → (h : Fin (H + 1)) → G.St h → ℝ

attribute [instance] CandClass.cFintype CandClass.cDecEq CandClass.cNonempty

end UninformedMG


