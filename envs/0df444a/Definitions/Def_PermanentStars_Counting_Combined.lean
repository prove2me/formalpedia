-- Prove2me | Definitions.Def_PermanentStars_Counting_Combined
-- name    : PermanentStars_Counting_Combined
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:54:10.252874+00:00
-- url     : https://prove2.me/theorems/dfd273b6-7f9f-4f98-b89a-2fc41911efa8
-- title:
--   Cutoff ABPs and the disjoint combined graph
-- statement:
--   For each retained closed terminal nursery, the cutoff graph attaches its star-formation component to a common sink. It retains the main-state source. The combined graph takes disjoint copies for the cutoffs and introduces a fresh source and sink joined by unit transitions.
--
--   Both graphs are specified by actual finite vertex carriers and transition relations. Ambient carriers retain unreachable states. In particular, the effective size of a cutoff graph counts reachable vertices, not all vertices in its carrier. The main theorem separately requires an actually emitted elementary-label graph with bounded total size and construction cost.
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), §4.3, equation (18) and Corollary 4.5, p.10

import Definitions.Def_PermanentStars_Counting_Gadgets

namespace PermanentStars.Counting

/-- Main states, one fresh gadget interior per nursery, and the common cutoff sink. -/
abbrev CutoffVertex (P : Cutoffs) (n : ℕ) :=
  MainState n ⊕ ((Nursery n × ClusterState P n) ⊕ Unit)

def liftGadget {n : ℕ} {P : Cutoffs} (d : Nursery n) : GadgetVertex P n → CutoffVertex P n
  | .inl _ => .inl (terminal d)
  | .inr (.inl a) => .inr (.inl (d, a))
  | .inr (.inr _) => .inr (.inr ())

def cutoffRule {n : ℕ} (P : Cutoffs) (r : ℕ)
    (s t : CutoffVertex P n) (l : Label n) (slot : Fin (n + 1)) : Prop :=
  (slot.val = 0 ∧ ∃ a b, s = .inl a ∧ t = .inl b ∧ mainRule P r a b l) ∨
  (∃ d a b, nurseryMass d ≤ n ∧ (nurserySupport d : ℚ) ≤ P.alpha r * n ∧
    s = liftGadget d a ∧ t = liftGadget d b ∧ gadgetRule P r d a b l slot)

noncomputable def cutoffABP (P : Cutoffs) (r n : ℕ) : Graph (CutoffVertex P n) (Label n) :=
  ruleGraph _ _ (.inl ((∅, none), zeroNursery n)) (.inr (.inr ()))
    (n + 1) (cutoffRule P r)

abbrev CombinedVertex (P : Cutoffs) (n : ℕ) := Unit ⊕ ((P.R × CutoffVertex P n) ⊕ Unit)

def combinedRule {n : ℕ} (P : Cutoffs) (s t : CombinedVertex P n)
    (l : Label n) (slot : Fin (n + 1)) : Prop :=
  (slot.val = 0 ∧ l = .one ∧
    ((∃ r : P.R, s = .inl () ∧ t = .inr (.inl (r, (cutoffABP P r.val n).source))) ∨
     (∃ r : P.R, s = .inr (.inl (r, (cutoffABP P r.val n).sink)) ∧ t = .inr (.inr ())))) ∨
  (∃ (r : P.R) (a b : CutoffVertex P n), s = .inr (.inl (r, a)) ∧ t = .inr (.inl (r, b)) ∧
    cutoffRule P r.val a b l slot)

noncomputable def combinedABP (P : Cutoffs) (n : ℕ) : Graph (CombinedVertex P n) (Label n) :=
  ruleGraph _ _ (.inl ()) (.inr (.inr ())) (n + 1) (combinedRule P)

end PermanentStars.Counting


