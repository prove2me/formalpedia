-- Prove2me | Definitions.Def_SecretaryWD_Weighted_Assignment
-- name    : SecretaryWD_Weighted_Assignment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:48:57.6249+00:00
-- url     : https://prove2.me/theorems/2fa9ed0e-3641-4dba-a3a4-89b8748d3eaa
-- title:
--   Weighted assignments and the sorted offline benchmark
-- statement:
--   An assignment maps each of $K$ goods to an agent or leaves it unassigned. It is valid when no agent receives more than one good. If agent $e$ has value $v(e)$ and good $k$ has weight $w(k)$, its value is
--
--   $$\sum_{k=1}^{K}v(s(k))w(k),\qquad v(\bot)=0.$$
--
--   The offline benchmark $\mathrm{OPT}$ gives the heaviest good to the highest-value agent, the next good to the next agent, and so on; goods beyond the number of agents stay unassigned. Equal values are ordered by increasing agent index. These definitions state the weighted secretary objective and its offline comparator.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), pp. 3–4, Section 2, Weighted Secretary Problems and OPT

import Mathlib

namespace SecretaryWD.Weighted

/-- A weighted one-to-one assignment has at most one good per agent. -/
def ValidAssignment {n K : ℕ} (s : Fin K → Option (Fin n)) : Prop :=
  ∀ k l e, s k = some e → s l = some e → k = l

/-- The value of an assignment, with unassigned goods contributing zero. -/
def assignmentValue {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ)
    (s : Fin K → Option (Fin n)) : ℝ :=
  ∑ k : Fin K, (s k).elim 0 v * w k

/-- Larger value wins; an equal value is resolved in favor of the smaller agent index. -/
def better {n : ℕ} (v : Fin n → ℝ) (e f : Fin n) : Prop :=
  v f < v e ∨ (v e = v f ∧ e.val < f.val)

/-- The zero-based position of an agent in decreasing value order. -/
noncomputable def valueRank {n : ℕ} (v : Fin n → ℝ) (e : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun f => better v f e)).card

/-- Give good `k` to the agent of rank `k`, if one exists. -/
noncomputable def optimalAssignment {n K : ℕ} (v : Fin n → ℝ) :
    Fin K → Option (Fin n) := by
  classical
  intro k
  exact if h : ∃ e : Fin n, valueRank v e = k.val then some (Classical.choose h) else none

/-- Offline benchmark: the heaviest good goes to the highest-value agent. -/
noncomputable def OPT {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ) : ℝ :=
  assignmentValue v w (optimalAssignment v)

end SecretaryWD.Weighted


