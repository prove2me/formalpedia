-- Prove2me | Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_Candidates
-- name    : FiniteGroupTesting_LinearQuery_Supplement_Candidates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:17:29.304077+00:00
-- url     : https://prove2.me/theorems/305abc7b-cf7b-4d21-ad6c-e3a210f41240
-- title:
--   Finite group representatives and all marked candidates
-- statement:
--   A labelled candidate is an actual group table on $n$ labels. Isomorphic tables are identified, and one representative is chosen from each isomorphism class. Every marking $(\rho,a_1,\ldots,a_k)$ of every representative is enumerated. Thus the number of candidates is
--   $$M=g(n)n^{k+1},$$
--   where $g(n)$ counts isomorphism classes, rather than labelled multiplication tables. Candidate walks, the equality-pattern test, the conductance filter, and locator interpretation use only the candidate and recorded visible data. Enumeration is finite offline processing and has no oracle argument. The candidate group structure is constructed from that candidate table's group axioms; it supplies no promise on the unknown input.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), pp. 26, 29–30, Sections 4.3 and 5.1–5.2

import Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_Dictionary

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev LabelledGroup (n : ℕ) := {op : Table n // IsGroupLaw op}

/-- Group structure is obtained from the axioms of the candidate table, never from the oracle. -/
@[instance_reducible]
def candidateGroup {n : ℕ} (l : LabelledGroup n) : Group (Fin n) := by
  let e := Classical.choose l.property
  have h := Classical.choose_spec l.property
  exact {
    mul := l.val
    one := e
    inv := fun x => Classical.choose (h.2.2.2 x)
    div := fun x y => l.val x (Classical.choose (h.2.2.2 y))
    div_eq_mul_inv := fun _ _ => rfl
    mul_assoc := h.1
    one_mul := h.2.1
    mul_one := h.2.2.1
    inv_mul_cancel := fun x => (Classical.choose_spec (h.2.2.2 x)).2 }

/-- Isomorphism of candidate tables. -/
def candidateIso {n : ℕ} (l r : LabelledGroup n) : Prop :=
  ∃ e : Fin n ≃ Fin n, ∀ x y, e (l.val x y) = r.val (e x) (e y)

def candidateSetoid (n : ℕ) : Setoid (LabelledGroup n) where
  r := candidateIso
  iseqv := {
    refl := fun l => ⟨Equiv.refl _, fun _ _ => rfl⟩
    symm := by
      rintro l r ⟨e, h⟩
      refine ⟨e.symm, ?_⟩
      intro x y
      apply e.injective
      simpa using (h (e.symm x) (e.symm y)).symm
    trans := by
      rintro l r s ⟨e, he⟩ ⟨f, hf⟩
      exact ⟨e.trans f, fun x y => (congrArg f (he x y)).trans (hf (e x) (e y))⟩ }

/-- Exactly one actual table from each isomorphism class; the selection is offline. -/
def groupRepresentatives (n : ℕ) : Finset (LabelledGroup n) := by
  letI := candidateSetoid n
  letI : Fintype (Quotient (candidateSetoid n)) := Fintype.ofFinite _
  exact Finset.univ.image (fun q : Quotient (candidateSetoid n) => q.out)

/-- The group-counting function, not the number of labelled multiplication tables. -/
def groupCount (n : ℕ) : ℕ := (groupRepresentatives n).card

abbrev MarkedCandidate (n k : ℕ) := LabelledGroup n × Fin n × (Fin k → Fin n)

def markedCandidates (n k : ℕ) : Finset (MarkedCandidate n k) :=
  (groupRepresentatives n).biUnion fun l => Finset.univ.image fun ra : Fin n × (Fin k → Fin n) =>
    (l, ra.1, ra.2)

def candidateWalk {n k : ℕ} (c : MarkedCandidate n k) (word : List (Signed k)) : List (Fin n) :=
  letI := candidateGroup c.1
  walk (· * ·) (signedMark c.2.2) c.2.1 word

def candidateConductance {n k : ℕ} (c : MarkedCandidate n k) : Prop :=
  letI := candidateGroup c.1
  ConductanceAtLeast c.2.2 ((1 - spectralAccuracy) / 4)

def candidateLocator {n k : ℕ} (c : MarkedCandidate n k) (ds : List (Fin n))
    (ξ : List (Signed k)) (hit : Option (Fin n × List (Signed k))) : Option (Fin n) :=
  letI := candidateGroup c.1
  interpretHit ds (candidateWalk c ξ) c.2.2 hit

end
end FiniteGroupTesting.LinearQuery.Supplement


