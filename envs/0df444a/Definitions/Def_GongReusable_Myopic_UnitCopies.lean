-- Prove2me | Definitions.Def_GongReusable_Myopic_UnitCopies
-- name    : GongReusable_Myopic_UnitCopies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:26:15.855212+00:00
-- url     : https://prove2.me/theorems/69a78348-5af4-4546-8764-54446ba317fe
-- title:
--   Labeled unit copies and corresponding lifted myopic execution
-- statement:
--   Replace product j by labeled products (j,k), with k ranging over its capacity, each of capacity one and carrying the same usage law and rental-fee function. Project a clone offer to the set of physical products it contains. The clone offer is feasible exactly when that projection is feasible. The least-index offered clone of each product receives its original choice mass; all other clones receive zero. No-purchase probability is unchanged.
--
--   Project a clone history by forgetting clone labels. Lift an original offer rule by applying it to this projected history and offering the least available clone of each requested physical product. This lift uses only the current original choice law and its own projected history. The lifted myopic value is the expected revenue of this operationally constructed clone run with the original maximizing tie rule. The two executions are not assigned equal values by definition. Labels start at zero rather than one; all finite capacities, including zero, are represented.
-- source:
--   Gong, Goyal, Iyengar, Simchi-Levi, Udwani and Wang, Online Assortment Optimization with Reusable Resources, https://doi.org/10.1287/mnsc.2021.4134, supplied manuscript (SSRN 3334789 footers; journal pagination and revision year unverified), printed pp. 9–10 / PDF pp. 9–10

import Definitions.Def_GongReusable_Myopic_Process

open MeasureTheory
open scoped ENNReal
noncomputable section

namespace GongReusable.Myopic

abbrev Clone {P Z : Type} [Fintype P] (M : Model P Z) := Σ j, Fin (M.capacity j)

def projectOffer {P Z : Type} [Fintype P] (M : Model P Z)
    (S : Finset (Clone M)) : Finset P := by
  classical
  exact S.image Sigma.fst

def unitModel {P Z : Type} [Fintype P] (M : Model P Z) : Model (Clone M) Z where
  capacity := fun _ => 1
  feasible := by
    classical
    exact Finset.univ.filter fun S => projectOffer M S ∈ M.feasible
  choice := fun z S j => match j with
    | none => M.choice z (projectOffer M S) none
    | some c => by
      classical
      exact if c ∈ S ∧ ∀ d ∈ S, d.1 = c.1 → c.2.val ≤ d.2.val
        then M.choice z (projectOffer M S) (some c.1) else 0
  duration := fun c => M.duration c.1
  rentalRevenue := fun c => M.rentalRevenue c.1

def projectHistory {P Z : Type} [Fintype P] (M : Model P Z)
    (h : History (Clone M)) : History P := fun t =>
  ((h t).1, projectOffer M (h t).2.1, (h t).2.2.1.map Sigma.fst, (h t).2.2.2)

/-- Offer exactly the least available labeled unit of each proposed physical product. -/
def liftOffer {P Z : Type} [Fintype P] (M : Model P Z) (A : OfferRule P)
    (xq : ℕ → ChoiceProb P) : OfferRule (Clone M) := fun t a _ h u => by
  classical
  let S := A t a (xq t) (projectHistory M h) u
  let I := available (unitModel M) t a h
  exact I.filter fun c => c.1 ∈ S ∧ ∀ d ∈ I, d.1 = c.1 → c.2.val ≤ d.2.val

/-- The current original choice model, with the unused tail set to rejection. -/
def arrivalChoice {P Z : Type} [Fintype P] {T : ℕ}
    (M : Model P Z) (x : Arrivals Z T) (t : ℕ) : ChoiceProb P :=
  if ht : t < T then M.choice (x.type ⟨t, ht⟩)
  else fun _ j => if j.isNone then 1 else 0

def liftedMyopicValue {P Z : Type} [Fintype P] {T : ℕ}
    (M : Model P Z) (x : Arrivals Z T) (tie : Policy P) : ℝ :=
  valueFor (unitModel M) x (liftOffer M (myopicOffer M tie) (arrivalChoice M x))

end GongReusable.Myopic


