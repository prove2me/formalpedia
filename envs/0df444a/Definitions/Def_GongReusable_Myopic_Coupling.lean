-- Prove2me | Definitions.Def_GongReusable_Myopic_Coupling
-- name    : GongReusable_Myopic_Coupling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:26:31.132067+00:00
-- url     : https://prove2.me/theorems/fa678122-ffd2-4c4c-b7c3-3b1fb5b711a1
-- title:
--   Operational FIFO coupling and its fresh-law assertion
-- statement:
--   Run the myopic policy and an arbitrary nonanticipating competitor jointly, each choosing offers from its own preceding history with its own independent action and customer-choice seeds. Maintain a separate initially empty FIFO queue of durations for each product. A myopic rental uses a fresh duration sample and appends it to that product's queue. A competitor rental takes and removes the oldest queued sample, or uses its own independent fresh sample if the queue is empty. Myopic insertion precedes competitor extraction at a shared arrival. Neither policy observes the queues or the other history.
--
--   The joint driving law is the product of two independent tapes of uniforms and product-specific duration samples. Recursion constructs both histories and all queues. The fresh-law predicate says that, for each arrival, product, measurable event E in the competitor's own preceding history and current offer, and measurable duration set B, the probability of E, selecting that product, and using a duration in B equals the probability of E and selecting that product times its usage law evaluated at B. This is the stopped-sequence conditional i.i.d. interpretation; it is not independence from the joint history, and it is not assumed in the process definition.
--
--   The unavailable-product revenue uses the competitor's actual full offer choice probabilities, restricted to products unavailable to the myopic policy just before the offer. The myopic comparison revenue sums its actual conditional assortment revenues. Both are bounded measurable functions under the concrete joint law.
-- source:
--   Gong, Goyal, Iyengar, Simchi-Levi, Udwani and Wang, Online Assortment Optimization with Reusable Resources, https://doi.org/10.1287/mnsc.2021.4134, supplied manuscript (SSRN 3334789 footers; journal pagination and revision year unverified), printed pp. 11–13 / PDF pp. 11–13

import Definitions.Def_GongReusable_Myopic_Process
import Definitions.Def_GongReusable_Myopic_FIFO

open MeasureTheory
open scoped ENNReal
noncomputable section

namespace GongReusable.Myopic

abbrev CoupledState (P : Type) := History P × History P × (P → List ℝ≥0∞)
abbrev JointTape (P : Type) (T : ℕ) := Tape P T × Tape P T

def jointLaw {P Z : Type} [Fintype P] (M : Model P Z) (T : ℕ) : Measure (JointTape P T) :=
  (tapeLaw M T).prod (tapeLaw M T)

/-- ALG inserts before OPT extracts, and neither policy sees the queues or the other's history. -/
def coupledStep {P Z : Type} [Fintype P] (M : Model P Z) (tie π : Policy P)
    (t : ℕ) (a : NNReal) (q : ChoiceProb P) (state : CoupledState P)
    (wA wO : Noise P) : CoupledState P := by
  classical
  let SA := myopicOffer M tie t a q state.1 wA.1.1
  let SO := offer M π t a q state.2.1 wO.1.1
  let jA := choose (q SA) wA.1.2
  let jO := choose (q SO) wO.1.2
  let dA := jA.elim 0 wA.2
  let queues := jA.elim state.2.2 (fun j =>
    Function.update state.2.2 j (fifoPush (state.2.2 j) dA))
  let dO := jO.elim 0 (fun j => (fifoTake (queues j) (wO.2 j)).1)
  let queues' := jO.elim queues (fun j =>
    Function.update queues j (fifoTake (queues j) (wO.2 j)).2)
  exact (Function.update state.1 t (a, SA, jA, dA),
    Function.update state.2.1 t (a, SO, jO, dO), queues')

def coupledRun {P Z : Type} [Fintype P] {T : ℕ} (M : Model P Z)
    (x : Arrivals Z T) (tie π : Policy P) (w : JointTape P T) : ℕ → CoupledState P
  | 0 => (initialHistory, initialHistory, fun _ => [])
  | t + 1 => if ht : t < T then
      coupledStep M tie π t (x.epoch ⟨t, ht⟩) (M.choice (x.type ⟨t, ht⟩))
        (coupledRun M x tie π w t) (w.1 ⟨t, ht⟩) (w.2 ⟨t, ht⟩)
    else coupledRun M x tie π w t

/-- OPT's pre-rental information, including its own current offer. -/
def optBefore {P Z : Type} [Fintype P] {T : ℕ} (M : Model P Z)
    (x : Arrivals Z T) (tie π : Policy P) (t : Fin T) (w : JointTape P T) :
    History P × Finset P :=
  ((coupledRun M x tie π w t).2.1, (coupledRun M x tie π w (t.val + 1)).2.1 t |>.2.1)

def optRental {P Z : Type} [Fintype P] {T : ℕ} (M : Model P Z)
    (x : Arrivals Z T) (tie π : Policy P) (t : Fin T) (w : JointTape P T) : Rental P :=
  (coupledRun M x tie π w (t.val + 1)).2.1 t

/-- The stopped sequence's fresh-law assertion relative to OPT's own observations. -/
def FreshOptDurations {P Z : Type} [Fintype P] {T : ℕ} (M : Model P Z)
    (x : Arrivals Z T) (tie π : Policy P) : Prop :=
  ∀ (t : Fin T) (j : P) (E : Set (History P × Finset P)), MeasurableSet E →
    ∀ B : Set ℝ≥0∞, MeasurableSet B →
      jointLaw M T {w | optBefore M x tie π t w ∈ E ∧
        (optRental M x tie π t w).2.2.1 = some j ∧
        (optRental M x tie π t w).2.2.2 ∈ B} =
      jointLaw M T {w | optBefore M x tie π t w ∈ E ∧
        (optRental M x tie π t w).2.2.1 = some j} * M.duration j B

def unavailableRevenue {P Z : Type} [Fintype P] {T : ℕ} (M : Model P Z)
    (x : Arrivals Z T) (tie π : Policy P) (w : JointTape P T) : ℝ := by
  classical
  exact ∑ t : Fin T,
    let state := coupledRun M x tie π w t
    let SO := (optRental M x tie π t w).2.1
    ∑ j ∈ SO \ available M t (x.epoch t) state.1,
      meanRevenue M j * M.choice (x.type t) SO (some j)

def coupledMyopicRevenue {P Z : Type} [Fintype P] {T : ℕ} (M : Model P Z)
    (x : Arrivals Z T) (tie π : Policy P) (w : JointTape P T) : ℝ :=
  pathRevenue M x (coupledRun M x tie π w T).1

end GongReusable.Myopic


