-- Prove2me | Definitions.Def_GoldsteinMCSP_Hardness_Conflict
-- name    : GoldsteinMCSP_Hardness_Conflict
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T17:12:10.065191+00:00
-- url     : https://prove2.me/theorems/b6ffc16a-4afc-4f1b-83d3-f498ea45b968
-- title:
--   Specific duos, compatible occurrence matches and the conflict graph
-- statement:
--   A specific duo records its component index and starting position, and consists of two adjacent letters within that component. A match pairs specific duos with equal ordered letter pairs. Two distinct matches conflict exactly when their partial position bijections disagree: for some pair of offsets in {0,1}, the source positions coincide and the target positions do not, or conversely. This is the symmetric form of the three cases on page 4, and retains occurrence identities and component boundaries.
--
--   The conflict graph is the finite simple undirected graph on these matches. Its maximum independent-set cardinality is computed by enumerating all sublists of the duplicate-free match list, keeping pairwise compatible sublists, and taking the maximum of their lengths. The empty independent set is included, so this maximum is attained even for empty words. Applying the definition to singleton families yields the paper's ordinary string conflict graph.
-- source:
--   Goldstein, Kolman and Zheng (2005), Minimum Common String Partition Problem: Hardness and Approximations, EJC 12, R50, DOI 10.37236/1947, Section 1.1, printed/PDF pp. 4–5

import Definitions.Def_GoldsteinMCSP_Hardness_Strings

namespace GoldsteinMCSP.Hardness

/-- Specific duos retain both the component and start position. -/
def duoStarts (a : Family) : List (ℕ × ℕ) :=
  (List.range a.length).flatMap fun c =>
    (List.range ((a.getD c []).length - 1)).map (c, ·)

def duoAt (a : Family) (p : ℕ × ℕ) : ℕ × ℕ :=
  ((a.getD p.1 []).getD p.2 0, (a.getD p.1 []).getD (p.2 + 1) 0)

abbrev Match := (ℕ × ℕ) × (ℕ × ℕ)

def duoMatches (a b : Family) : List Match :=
  (duoStarts a).flatMap fun i =>
    ((duoStarts b).filter fun j => duoAt a i == duoAt b j).map (i, ·)

/-- Two occurrences overlap iff component and position both agree. -/
def samePosition (p : ℕ × ℕ) (d : ℕ) (q : ℕ × ℕ) (e : ℕ) : Bool :=
  p.1 == q.1 && p.2 + d == q.2 + e

/-- The two two-letter partial bijections cannot coexist. This includes reverse-order conflicts. -/
def conflicts (m n : Match) : Bool :=
  m != n && ([0,1].any fun d => [0,1].any fun e =>
    samePosition m.1 d n.1 e != samePosition m.2 d n.2 e)

/-- The concrete conflict graph, with vertices the actual match occurrences. -/
def conflictGraph (a b : Family) : SimpleGraph {m : Match // m ∈ duoMatches a b} where
  Adj m n := m ≠ n ∧ (conflicts m.val n.val = true ∨ conflicts n.val m.val = true)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- An attained finite maximum, with the empty independent set included. -/
def conflictMIS (a b : Family) : ℕ :=
  (((duoMatches a b).sublists.filter fun s =>
    s.all fun m => s.all fun n => !conflicts m n).map List.length).foldl max 0

end GoldsteinMCSP.Hardness


