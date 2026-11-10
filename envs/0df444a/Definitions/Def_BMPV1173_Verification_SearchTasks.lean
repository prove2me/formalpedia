-- Prove2me | Definitions.Def_BMPV1173_Verification_SearchTasks
-- name    : BMPV1173_Verification_SearchTasks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:05:32.334596+00:00
-- url     : https://prove2.me/theorems/4ecb703b-1c63-4971-9b6c-ca374f76499d
-- title:
--   Changing-predicate cursor traces and Johnson walk data operations
-- statement:
--   The cursor trace repeatedly finds the next marked coordinate using the predicate for the current history, advances past it, and stops at the mark limit or the end. Johnson states are r-element subsets; neighbors replace one element. The uniform setup state includes the data computed for each subset, and the marking guarantee requires a distinguished element whose containing subsets are all marked whenever a marked state exists.
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, §2.2, Lemma 2.6 and Theorem 2.10, printed pp.15–16 = PDF pp.15–16.

import Definitions.Def_BMPV1173_Verification_Resources

namespace BMPV1173.Verification

noncomputable section
open scoped BigOperators

/-- The procedure's actual cursor trace. The predicate is reevaluated after each
new mark; positions at or before the cursor never need to be visited again. -/
def successiveTrace {M : ℕ} (f : List (Fin M) → Fin M → Bool) : ℕ → List (Fin M) → List (Fin M)
  | 0, hist => hist
  | K+1, hist =>
    match (List.finRange M).find? (fun j =>
      (hist.getLast?.elim 0 (fun i => i.val+1) < j.val+1) && f hist j) with
    | none => hist
    | some j => successiveTrace f K (hist++[j])

def rSubsets (n r : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun I => I.card = r

def johnsonAdjacent {n : ℕ} (r : ℕ) (I J : Finset (Fin n)) : Prop :=
  I.card = r ∧ J.card = r ∧ (I \ J).card = 1 ∧ (J \ I).card = 1

abbrev WalkRegister (n : ℕ) (δ : Type) := Finset (Fin n) × Finset (Fin n) × δ

def walkSetup {ι δ : Type} [Fintype δ] [DecidableEq δ] (n r : ℕ)
    (data : (ι → Bool) → Finset (Fin n) → δ) (x : ι → Bool) :
    EuclideanSpace ℂ (WalkRegister n δ) :=
  ((Real.sqrt ((rSubsets n r).card : ℝ))⁻¹ : ℂ) •
    ∑ I ∈ rSubsets n r, QAlgorithms.ket (I,I,data x I)

def MarkingGuarantee {ι : Type} {n : ℕ} (r : ℕ)
    (D : Set (ι → Bool)) (marked : (ι → Bool) → Finset (Fin n) → Prop) : Prop :=
  ∀ x ∈ D, (∃ I ∈ rSubsets n r, marked x I) →
    ∃ v : Fin n, ∀ I ∈ rSubsets n r, v ∈ I → marked x I

end
end BMPV1173.Verification


