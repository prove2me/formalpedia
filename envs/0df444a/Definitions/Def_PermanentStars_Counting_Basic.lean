-- Prove2me | Definitions.Def_PermanentStars_Counting_Basic
-- name    : PermanentStars_Counting_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:15.404632+00:00
-- url     : https://prove2.me/theorems/7c2b3a75-2091-44df-a00e-de42643d89fd
-- title:
--   The basic star construction graph
-- statement:
--   States record covered leaves $S$ and either a closed marker or an open star size $k$ and center image $j$. Begin uses the least uncovered leaf $i$ and label $A_{ij}$; Grow adds any uncovered leaf $v$ and label $-A_{vj}$; Close resets the marker with label one. The endpoints are $(\varnothing;\mathrm{closed})$ and $([n];\mathrm{closed})$.
--
--   The graph is defined by these transition rules, independently of the permanent. Sizes are bounded by $n$; impossible open states are isolated. This finite carrier convention does not delete reachable states or change path sums. An optional open marker avoids confusing the closed sentinel with a valid zero-based vertex.
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), §3, equations (7)–(9), p.6

import Definitions.Def_PermanentStars_Counting_Graphs

namespace PermanentStars.Counting

abbrev BasicState (n : ℕ) := Finset (Fin n) × Option (Fin (n + 1) × Fin n)

def leastUncovered {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : Prop :=
  i ∉ S ∧ ∀ v : Fin n, v ∉ S → i ≤ v

def basicValid {n : ℕ} (s : BasicState n) : Prop :=
  ∀ k j, s.2 = some (k, j) → 0 < k.val ∧ k.val ≤ s.1.card

/-- Equations (7)--(9), p.6. Impossible open states are isolated. -/
def basicRule {n : ℕ} (s t : BasicState n) (l : Label n) : Prop :=
  basicValid s ∧ basicValid t ∧
  ((∃ i j k, s.2 = none ∧ leastUncovered s.1 i ∧ t.1 = insert i s.1 ∧
      t.2 = some (k, j) ∧ k.val = 1 ∧ l = .var i j) ∨
   (∃ k j i k', s.2 = some (k, j) ∧ i ∉ s.1 ∧ t.1 = insert i s.1 ∧
      k'.val = k.val + 1 ∧ t.2 = some (k', j) ∧ l = .negVar i j) ∨
   (∃ k j, s.2 = some (k, j) ∧ t = (s.1, none) ∧ l = .one))

noncomputable def basicABP (n : ℕ) : Graph (BasicState n) (Label n) :=
  ruleGraph _ _ (∅, none) (Finset.univ, none) 1 (fun s t l _ => basicRule s t l)

end PermanentStars.Counting


