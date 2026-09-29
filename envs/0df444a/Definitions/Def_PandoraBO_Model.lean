-- Prove2me | Definitions.Def_PandoraBO_Model
-- name    : PandoraBO_Model
-- status  : Definition
-- author  : @QianJaneXie
-- created : 2026-09-29T02:12:05.857402+00:00
-- url     : https://prove2.me/theorems/48e3c6b1-c2ee-46e3-8179-2cb5bcb88164
-- title:
--   Finite independent Pandora model with positive and zero multiplier index rules
-- statement:
--   There are $n+1$ independent integrable real box rewards with positive deterministic opening costs. Measurable randomized policies use ordered histories and an independent uniform seed, must open a first box, never reopen a box, and stop irreversibly. Reward is the maximum observed reward without an outside option. The module defines expected reward and cost, penalized and budget optimality, real value suprema and the nonnegative dual minimum. Positive index policies use finite expected-improvement roots. The new zero index is the infimum of all almost-sure extended-real upper bounds of a box reward, that is, its essential supremum; it can be positive infinity. A generalized policy is either a positive-multiplier Gittins policy or a zero-multiplier essential-supremum policy. Complementary slackness means $\lambda(B-C(\pi))=0$ and does not itself include feasibility. The existing strict-gap predicate remains only for a positivity corollary. No optimality, multiplier existence, or budget matching is built into the definitions.
-- source:
--   Xie, Astudillo, Frazier, Scully and Terenin, Cost-aware Bayesian Optimization via the Pandora's Box Gittins Index, NeurIPS 2024; arXiv:2406.20062v3 (16 January 2025), https://arxiv.org/pdf/2406.20062v3. Sections 3.1–3.2 and Appendix B.5, with explicitly proposed zero-multiplier extensions and complementary slackness for the corrected Theorem 2.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Data.EReal.Basic

/-!
# A finite, independent Pandora's-box model

There are `n + 1` boxes. Rewards have arbitrary integrable probability laws on
the real line and costs are deterministic and strictly positive. A policy
observes an ordered history, uses an independent uniform seed for randomization,
opens at least one box, and never opens a box twice. Stopping is irrevocable.

The definitions impose no optimality, budget activity, or reservation-index
existence assumptions on an instance or on a policy.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace PandoraBO

abbrev Box (n : ℕ) := Fin (n + 1)

/-- An ordered history, padded with inactive slots. The Boolean marks whether
the slot is occupied; the other coordinates are the box and its observed reward.
Padding retains the ordinary finite-product Borel measurable structure. -/
abbrev History (n : ℕ) := Fin (n + 1) → Bool × Box n × ℝ

abbrev Decision (n : ℕ) := Option (Box n)

instance decisionMeasurableSpace (n : ℕ) : MeasurableSpace (Decision n) := ⊤

/-- The full, finite independent-box model. -/
structure Instance (n : ℕ) where
  law : Box n → Measure ℝ
  law_probability : ∀ i, IsProbabilityMeasure (law i)
  reward_integrable : ∀ i, Integrable (fun x : ℝ => x) (law i)
  cost : Box n → ℝ
  cost_positive : ∀ i, 0 < cost i

/-- A single uniform seed suffices for arbitrary randomized policies with a
finite horizon and standard Borel observations. It is independent of all boxes. -/
def seedLaw : Measure ℝ := volume.restrict (Set.Icc 0 1)

abbrev Outcome (n : ℕ) := (Box n → ℝ) × ℝ

/-- Independent rewards and an independent uniform randomization seed. -/
def jointLaw {n : ℕ} (M : Instance n) : Measure (Outcome n) :=
  letI : ∀ i, IsProbabilityMeasure (M.law i) := M.law_probability
  (Measure.pi M.law).prod seedLaw

def occupied {n : ℕ} (h : History n) (k : Fin (n + 1)) : Prop :=
  (h k).1 = true

def observedBox {n : ℕ} (h : History n) (k : Fin (n + 1)) : Box n :=
  (h k).2.1

def observedReward {n : ℕ} (h : History n) (k : Fin (n + 1)) : ℝ :=
  (h k).2.2

def wasOpened {n : ℕ} (h : History n) (i : Box n) : Prop :=
  ∃ k, occupied h k ∧ observedBox h k = i

/-- Histories are nonempty occupied prefixes and contain no repeated box. -/
def validHistory {n : ℕ} (h : History n) : Prop :=
  occupied h 0 ∧
  (∀ k l, k ≤ l → occupied h l → occupied h k) ∧
  (∀ k l, occupied h k → occupied h l →
    observedBox h k = observedBox h l → k = l)

/-- Policies choose using only their uniform seed and past observations.
`none` means stop. The first opening is mandatory. -/
structure Policy (n : ℕ) where
  first : ℝ → Box n
  first_measurable : Measurable first
  next : History n × ℝ → Decision n
  next_measurable : Measurable next
  next_unopened : ∀ h u i, next (h, u) = some i → ¬ wasOpened h i

/-- Initial history after the mandatory first opening. -/
def initialHistory {n : ℕ} (π : Policy n) (ω : Outcome n) : History n :=
  fun k => if k = 0 then (true, π.first ω.2, ω.1 (π.first ω.2))
    else (false, 0, 0)

/-- The fuel is the number of further opportunities. Stopping immediately
returns the current history, so a stopped policy can never resume. -/
def rolloutAux {n : ℕ} (π : Policy n) (ω : Outcome n) :
    ℕ → ℕ → History n → History n
  | 0, _, h => h
  | fuel + 1, step, h =>
    match π.next (h, ω.2) with
    | none => h
    | some i =>
      if hs : step < n + 1 then
        rolloutAux π ω fuel (step + 1)
          (Function.update h ⟨step, hs⟩ (true, i, ω.1 i))
      else h

/-- One mandatory opening followed by at most `n` further openings. -/
def terminalHistory {n : ℕ} (π : Policy n) (ω : Outcome n) : History n :=
  rolloutAux π ω n 1 (initialHistory π ω)

/-- Maximum observed reward. The first occupied slot supplies the initial
maximum, so there is no outside option and negative rewards remain negative. -/
def historyReward {n : ℕ} (h : History n) : ℝ := by
  classical
  exact (List.finRange (n + 1)).foldl
    (fun incumbent k => if occupied h k then max incumbent (observedReward h k)
      else incumbent)
    (observedReward h 0)

def historyCost {n : ℕ} (M : Instance n) (h : History n) : ℝ := by
  classical
  exact ∑ k : Fin (n + 1), if occupied h k then M.cost (observedBox h k) else 0

def terminalReward {n : ℕ} (π : Policy n) (ω : Outcome n) : ℝ :=
  historyReward (terminalHistory π ω)

def terminalCost {n : ℕ} (M : Instance n) (π : Policy n) (ω : Outcome n) : ℝ :=
  historyCost M (terminalHistory π ω)

def expectedReward {n : ℕ} (M : Instance n) (π : Policy n) : ℝ :=
  ∫ ω, terminalReward π ω ∂jointLaw M

def expectedCost {n : ℕ} (M : Instance n) (π : Policy n) : ℝ :=
  ∫ ω, terminalCost M π ω ∂jointLaw M

/-- Expected terminal maximum minus a multiplier times expected opening cost. -/
def value {n : ℕ} (M : Instance n) (multiplier : ℝ) (π : Policy n) : ℝ :=
  expectedReward M π - multiplier * expectedCost M π

def optimal {n : ℕ} (M : Instance n) (multiplier : ℝ) (π : Policy n) : Prop :=
  ∀ ρ : Policy n, value M multiplier ρ ≤ value M multiplier π

def optimalValue {n : ℕ} (M : Instance n) (multiplier : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ π : Policy n, r = value M multiplier π}

def dualValue {n : ℕ} (M : Instance n) (B multiplier : ℝ) : ℝ :=
  optimalValue M multiplier + multiplier * B

def dualMinimizer {n : ℕ} (M : Instance n) (B multiplier : ℝ) : Prop :=
  0 ≤ multiplier ∧ ∀ t : ℝ, 0 ≤ t → dualValue M B multiplier ≤ dualValue M B t

def budgetFeasible {n : ℕ} (M : Instance n) (B : ℝ) (π : Policy n) : Prop :=
  expectedCost M π ≤ B

def budgetOptimal {n : ℕ} (M : Instance n) (B : ℝ) (π : Policy n) : Prop :=
  budgetFeasible M B π ∧
  ∀ ρ : Policy n, budgetFeasible M B ρ → expectedReward M ρ ≤ expectedReward M π

def fullInformationPayoff {n : ℕ} (r : Box n → ℝ) : ℝ :=
  (List.finRange (n + 1)).foldl (fun incumbent i => max incumbent (r i)) (r 0)

def fullInformationReward {n : ℕ} (M : Instance n) : ℝ :=
  ∫ ω, fullInformationPayoff ω.1 ∂jointLaw M

def zeroCostOptimal {n : ℕ} (M : Instance n) (π : Policy n) : Prop :=
  optimal M 0 π

def budgetValue {n : ℕ} (M : Instance n) (B : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ π : Policy n, budgetFeasible M B π ∧ r = expectedReward M π}

/-- A feasible budget with a strict reward gap below full information.
Used only for the positive-multiplier corollary, not the main theorem. -/
def genuinelyActiveBudget {n : ℕ} (M : Instance n) (B : ℝ) : Prop :=
  (∃ π : Policy n, budgetFeasible M B π) ∧
  budgetValue M B < fullInformationReward M

/-- A useful alternative activity condition, stated without assuming an
optimal multiplier exists. Its equivalence to a strict value gap needs proof. -/
def belowEveryFullInformationPolicy {n : ℕ} (M : Instance n) (B : ℝ) : Prop :=
  ∀ π : Policy n, expectedReward M π = fullInformationReward M → B < expectedCost M π

def expectedImprovement {n : ℕ} (M : Instance n) (i : Box n) (z : ℝ) : ℝ :=
  ∫ y, max (y - z) 0 ∂M.law i

def reservationRoot {n : ℕ} (M : Instance n) (i : Box n) (c z : ℝ) : Prop :=
  expectedImprovement M i z = c

def reservationIndices {n : ℕ} (M : Instance n) (multiplier : ℝ) (z : Box n → ℝ) : Prop :=
  ∀ i, reservationRoot M i (multiplier * M.cost i) (z i)

/-- At a positive cost multiplier, a Pandora/Gittins policy opens a maximum
index first. It subsequently opens only a remaining maximum-index box whose
index is at least the incumbent; it stops only when every remaining index is
at most the incumbent. At equality either stopping or opening is permitted,
and all index ties may be randomized through the seed. -/
def isGittinsPolicy {n : ℕ} (M : Instance n) (multiplier : ℝ) (π : Policy n) : Prop :=
  ∃ z : Box n → ℝ, reservationIndices M multiplier z ∧
    (∀ u i, z i ≤ z (π.first u)) ∧
    (∀ h u, validHistory h →
      match π.next (h, u) with
      | none => ∀ i, ¬ wasOpened h i → z i ≤ historyReward h
      | some i => historyReward h ≤ z i ∧
        ∀ j, ¬ wasOpened h j → z j ≤ z i)

/-- The essential supremum of a box reward, expressed as the infimum of
its almost-sure extended-real upper bounds. The value may be positive infinity;
the probability-law assumptions rule out negative infinity. -/
def zeroReservationIndex {n : ℕ} (M : Instance n) (i : Box n) : EReal :=
  sInf {z : EReal | ∀ᵐ (y : ℝ) ∂M.law i, (y : EReal) ≤ z}

/-- The zero-multiplier index rule uses essential suprema rather than finite
solutions of a zero-level expected-improvement equation. Equality permits
stopping or continuing, and index ties can be randomized. A particular choice
of ties need not satisfy a given budget. -/
def isZeroGittinsPolicy {n : ℕ} (M : Instance n) (π : Policy n) : Prop :=
  (∀ u i, zeroReservationIndex M i ≤ zeroReservationIndex M (π.first u)) ∧
  (∀ h u, validHistory h →
    match π.next (h, u) with
    | none => ∀ i, ¬ wasOpened h i →
        zeroReservationIndex M i ≤ (historyReward h : EReal)
    | some i => (historyReward h : EReal) ≤ zeroReservationIndex M i ∧
        ∀ j, ¬ wasOpened h j → zeroReservationIndex M j ≤ zeroReservationIndex M i)

/-- The extended rule includes exactly the positive finite-index branch and
the zero essential-supremum branch. Negative multipliers satisfy neither. -/
def isGeneralizedGittinsPolicy {n : ℕ} (M : Instance n)
    (multiplier : ℝ) (π : Policy n) : Prop :=
  (0 < multiplier ∧ isGittinsPolicy M multiplier π) ∨
  (multiplier = 0 ∧ isZeroGittinsPolicy M π)

/-- Complementary slackness permits unused expected budget when the
multiplier is zero; feasibility is a separate condition. -/
def complementarySlackness {n : ℕ} (M : Instance n)
    (B multiplier : ℝ) (π : Policy n) : Prop :=
  multiplier * (B - expectedCost M π) = 0

end PandoraBO


