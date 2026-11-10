-- Prove2me | Definitions.Def_CoarseMatching_LowerBound_SubsetLaws
-- name    : CoarseMatching_LowerBound_SubsetLaws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:34:23.628622+00:00
-- url     : https://prove2.me/theorems/b6eb1ba9-3776-4bdc-a8d5-3495a0a79ad1
-- title:
--   Uniform subsets and conditional neighbor sampling
-- statement:
--   For a finite set $A$ and $k\le|A|$, the subset law is uniform on its $k$-element subsets. Given a core $C$, total degree $d$, and outside count $z\le d$, draw independently a uniform $(d-z)$-subset inside $C$ and a uniform $z$-subset outside it, then take their union:
--
--   $$B=I\cup O,\qquad I\subseteq C,\ |I|=d-z,\qquad O\subseteq U\setminus C,\ |O|=z.$$
--
--   The module proves structurally that the conditional neighbor family is nonempty whenever $d\le|C|$ and $d\le|U\setminus C|$. Finite independent sampling is defined by repeated probability bind. Outside the legal cardinality region only, a subset law is totalized by a point mass at the empty set; no theorem uses that branch on admissible parameters.
--
--   The laws are normalized probability mass functions. This finite-subset sampling interface is reusable independently of graph or communication hardness.
-- source:
--   Gillat Kol, Even Coarse Matching Estimates Require Nearly Linear Streaming Space, STOC 2027 submission #1135 (October 2026), §4.1–§4.2, printed pp.11–12 (PDF pp.12–13). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1135.pdf

import Mathlib

namespace CoarseMatching.LowerBound
noncomputable section

/-- Uniform k-subset. Invalid sizes have a stated totalization (the empty set);
all uses in the mission have k ≤ card s. No empty-family zero measure. -/
def subsetLaw {U : Type} [DecidableEq U] (s : Finset U) (k : ℕ) : PMF (Finset U) :=
  if hk : k ≤ s.card then PMF.uniformOfFinset (s.powersetCard k)
    (Finset.powersetCard_nonempty.mpr hk) else PMF.pure ∅

/-- Finite independent samples, not a finite-randomness assumption on algorithms. -/
def iid {A : Type} (q : PMF A) : ℕ → PMF (List A)
  | 0 => PMF.pure []
  | k+1 => q.bind (fun x => (iid q k).map (fun xs => x :: xs))

/-- Uniform inside and outside subsets are independent. Their disjoint union is
uniform conditional on its outside cardinality. -/
def neighborLaw {U : Type} [Fintype U] [DecidableEq U] (C : Finset U) (d z : ℕ) :
    PMF (Finset U) :=
  (subsetLaw C (d-z)).bind fun I =>
    (subsetLaw (Finset.univ \ C) z).map (fun O => I ∪ O)

/-- Structural nonemptiness of every conditional sample family used in Hidden-Core.
This is combinatorics of the sampling API, not a hardness lemma. -/
theorem neighborFamily_nonempty {U : Type} [Fintype U] [DecidableEq U]
    (C : Finset U) (d z : ℕ) (hd : d ≤ C.card)
    (ho : d ≤ (Finset.univ \ C).card) (hz : z ≤ d) :
    ∃ B : Finset U, B.card = d ∧ (B \ C).card = z := by
  obtain ⟨I,hI⟩ := Finset.powersetCard_nonempty.mpr (show d-z ≤ C.card by omega)
  obtain ⟨O,hO⟩ := Finset.powersetCard_nonempty.mpr (show z ≤ (Finset.univ \ C).card by omega)
  rcases Finset.mem_powersetCard.mp hI with ⟨hIC,hIc⟩
  rcases Finset.mem_powersetCard.mp hO with ⟨hOC,hOc⟩
  have dis : Disjoint I O := by
    apply Finset.disjoint_left.mpr
    intro x hx hxo
    exact (Finset.mem_sdiff.mp (hOC hxo)).2 (hIC hx)
  have eq : (I ∪ O) \ C = O := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx,hxc⟩
      exact hx.resolve_left (fun hi => hxc (hIC hi))
    · intro hx
      exact ⟨Or.inr hx, (Finset.mem_sdiff.mp (hOC hx)).2⟩
  exact ⟨I ∪ O, by rw [Finset.card_union_of_disjoint dis,hIc,hOc]; omega, by rw [eq,hOc]⟩

end
end CoarseMatching.LowerBound


