-- Prove2me | Definitions.Def_GongReusable_Myopic_Process
-- name    : GongReusable_Myopic_Process
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:24:51.105622+00:00
-- url     : https://prove2.me/theorems/02da9d7a-4170-47f2-b7fc-fda74c859068
-- title:
--   Sequential rental law, expected revenue and clairvoyant value
-- statement:
--   At each of the finitely many ordered arrivals, independent uniform variables randomize the policy's action and the customer's choice. Independent samples with product-specific laws are supplied for each product; only the selected product's duration is used. All these coordinates have their finite product probability measure. The run recursively constructs the current offer from the preceding history, samples the selected product, and adds that rental to the history. No purchase records duration zero and earns nothing. Presampling unused coordinates does not reveal them to a policy.
--
--   The objective J is the genuine integral, under this product measure, of the sum of conditional assortment revenues R(S,z). The module separately defines the sum of actual rental fees using the complete sampled duration, with no horizon truncation. Integrability of each fee and fresh independent duration sampling give equality between these two expected revenues. The assortment objective is measurable and bounded because only finitely many arrival types and finite offers occur.
--
--   The clairvoyant value is the supremum of J over all measurable randomized history policies, chosen with knowledge of the full fixed input but without access to future draws. Rejection belongs to the class. Its values lie between zero and T times the largest mean fee (zero when there are no products), so the real supremum is neither empty nor unbounded. The myopic value uses the concrete maximizing rule with any measurable tie proposal.
-- source:
--   Gong, Goyal, Iyengar, Simchi-Levi, Udwani and Wang, Online Assortment Optimization with Reusable Resources, https://doi.org/10.1287/mnsc.2021.4134, supplied manuscript (SSRN 3334789 footers; journal pagination and revision year unverified), printed pp. 5–6, 9, 11 / PDF pp. 5–6, 9, 11

import Definitions.Def_GongReusable_Myopic_Model

open MeasureTheory
open scoped ENNReal
noncomputable section

namespace GongReusable.Myopic

abbrev OfferRule (P : Type) := ℕ → NNReal → ChoiceProb P → History P → ℝ → Finset P
abbrev Noise (P : Type) := (ℝ × ℝ) × (P → ℝ≥0∞)
abbrev Tape (P : Type) (T : ℕ) := Fin T → Noise P

def noiseLaw {P Z : Type} [Fintype P] (M : Model P Z) : Measure (Noise P) :=
  (uniform.prod uniform).prod (Measure.pi M.duration)

def tapeLaw {P Z : Type} [Fintype P] (M : Model P Z) (T : ℕ) : Measure (Tape P T) :=
  Measure.pi (fun _ => noiseLaw M)

/-- One physical rental, after the offer and customer choice have been made. -/
def step {P : Type} (A : OfferRule P) (t : ℕ) (a : NNReal)
    (q : ChoiceProb P) (h : History P) (w : Noise P) [Fintype P] : History P := by
  classical
  let S := A t a q h w.1.1
  let j := choose (q S) w.1.2
  let d := j.elim 0 w.2
  exact Function.update h t (a, S, j, d)

/-- Sequential simulation. Only coordinates before t enter the policy's history. -/
def run {P Z : Type} [Fintype P] {T : ℕ} (M : Model P Z) (x : Arrivals Z T)
    (A : OfferRule P) (w : Tape P T) : ℕ → History P
  | 0 => initialHistory
  | t + 1 => if ht : t < T then
      step A t (x.epoch ⟨t, ht⟩) (M.choice (x.type ⟨t, ht⟩)) (run M x A w t) (w ⟨t, ht⟩)
    else run M x A w t

def pathRevenue {P Z : Type} [Fintype P] {T : ℕ} (M : Model P Z)
    (x : Arrivals Z T) (h : History P) : ℝ :=
  ∑ t : Fin T, revenue M (M.choice (x.type t)) (h t).2.1

def actualFees {P Z : Type} [Fintype P] (M : Model P Z)
    (T : ℕ) (h : History P) : ℝ :=
  ∑ t ∈ Finset.range T, (h t).2.2.1.elim 0 (fun j => M.rentalRevenue j (h t).2.2.2)

def valueFor {P Z : Type} [Fintype P] {T : ℕ} (M : Model P Z)
    (x : Arrivals Z T) (A : OfferRule P) : ℝ :=
  ∫ w, pathRevenue M x (run M x A w T) ∂tapeLaw M T

def policyValue {P Z : Type} [Fintype P] {T : ℕ} (M : Model P Z)
    (x : Arrivals Z T) (π : Policy P) : ℝ := valueFor M x (offer M π)

def myopicValue {P Z : Type} [Fintype P] {T : ℕ} (M : Model P Z)
    (x : Arrivals Z T) (tie : Policy P) : ℝ := valueFor M x (myopicOffer M tie)

/-- The entire nonanticipating class, selected with full knowledge of fixed inputs. -/
def optimalValue {P Z : Type} [Fintype P] {T : ℕ} (M : Model P Z)
    (x : Arrivals Z T) : ℝ := sSup (Set.range (policyValue M x))

end GongReusable.Myopic


