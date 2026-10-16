-- Prove2me | Definitions.Def_InfFisher_Linear_Market
-- name    : InfFisher_Linear_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:11.673827+00:00
-- url     : https://prove2.me/theorems/0ca4e077-cd12-42b9-af22-b0722f4eca79
-- title:
--   §2–§3 — continuum Fisher market, allocations, demand, equilibrium, and feasible utilities
-- statement:
--   The continuum Fisher market has an item measure $\mu$ and finitely many buyers. A bundle is a nonnegative essentially bounded function; an allocation assigns such a bundle $x_i$ to each buyer with $\sum_i x_i\le 1$ almost everywhere. Prices are nonnegative integrable functions. The value of a bundle is the integral pairing
--
--   $$\langle f,g\rangle=\int f(\theta)g(\theta)\,d\mu(\theta).$$
--
--   A buyer demands a utility maximizing affordable bundle. A market equilibrium consists of feasible allocations, demanded bundles, and a price whose integral against unused supply is zero. The file also defines the primal and dual Eisenberg–Gale objectives and their optimality predicates, the maximum scaled valuation, pure allocations, and the feasible utility set $U$ of (1).
--
--   These are the shared objects used by the paper's equilibrium and fair division results.
--
--   **Formalization Note** Functions are compared almost everywhere where appropriate. Positive utility and positive dual scale are required in optimality predicates because the paper treats $\log0$ as an infinite objective value. Zero budgets remain allowed in the equilibrium predicate for Lemma 6.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, §2, pp. 5–7; (PEG), p. 7; (DEG) and (1), p. 8

import Mathlib

namespace InfFisher.Linear

open MeasureTheory
variable {α : Type*} [MeasurableSpace α]

/-- The integral pairing on the item space. -/
noncomputable def pair (μ : Measure α) (f g : α → ℝ) : ℝ :=
  ∫ θ, f θ * g θ ∂μ

/-- A nonnegative essentially bounded bundle. -/
def IsBundle (μ : Measure α) (y : α → ℝ) : Prop :=
  MemLp y ⊤ μ ∧ 0 ≤ᵐ[μ] y

/-- A feasible allocation of unit supply among finitely many buyers. -/
def IsAllocation (μ : Measure α) {n : ℕ} (x : Fin n → α → ℝ) : Prop :=
  (∀ i, IsBundle μ (x i)) ∧ ∀ᵐ θ ∂μ, ∑ i, x i θ ≤ 1

/-- An allocation by almost everywhere disjoint measurable subsets. -/
def IsPure (μ : Measure α) (Θ : Set α) {n : ℕ} (x : Fin n → α → ℝ) : Prop :=
  ∃ S : Fin n → Set α,
    (∀ i, MeasurableSet (S i) ∧ S i ⊆ Θ) ∧
    (∀ i j, i ≠ j → μ (S i ∩ S j) = 0) ∧
    ∀ i, x i =ᵐ[μ] (S i).indicator (fun _ => (1 : ℝ))

/-- An integrable nonnegative price. -/
def IsPrice (μ : Measure α) (p : α → ℝ) : Prop :=
  Integrable p μ ∧ 0 ≤ᵐ[μ] p

/-- Buyer `i`'s demand correspondence at prices `p`. -/
def InDemand (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (B : Fin n → ℝ) (p : α → ℝ) (i : Fin n) (y : α → ℝ) : Prop :=
  IsBundle μ y ∧ pair μ p y ≤ B i ∧
  ∀ y', IsBundle μ y' → pair μ p y' ≤ B i →
    pair μ (v i) y' ≤ pair μ (v i) y

/-- A market equilibrium, allowing zero budgets as in Lemma 6. -/
def IsME (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (B : Fin n → ℝ) (x : Fin n → α → ℝ) (p : α → ℝ) : Prop :=
  IsPrice μ p ∧ IsAllocation μ x ∧
  (∀ i, InDemand μ v B p i (x i)) ∧
  pair μ p (fun θ => 1 - ∑ i, x i θ) = 0

/-- Objective of the Eisenberg–Gale primal program. -/
noncomputable def pegObj (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (B : Fin n → ℝ) (x : Fin n → α → ℝ) : ℝ :=
  ∑ i, B i * Real.log (pair μ (v i) (x i))

/-- Optimality with the paper's convention that zero utility has log value `-∞`. -/
def IsPEGOptimal (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (B : Fin n → ℝ) (x : Fin n → α → ℝ) : Prop :=
  IsAllocation μ x ∧ (∀ i, 0 < pair μ (v i) (x i)) ∧
  ∀ x', IsAllocation μ x' → (∀ i, 0 < pair μ (v i) (x' i)) →
    pegObj μ v B x' ≤ pegObj μ v B x

/-- Feasibility for the Eisenberg–Gale dual program. -/
def IsDEGFeasible (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (p : α → ℝ) (β : Fin n → ℝ) : Prop :=
  IsPrice μ p ∧ (∀ i, 0 ≤ β i) ∧
    ∀ i, (fun θ => β i * v i θ) ≤ᵐ[μ] p

/-- Objective of the Eisenberg–Gale dual program. -/
noncomputable def degObj (μ : Measure α) {n : ℕ} (B : Fin n → ℝ)
    (p : α → ℝ) (β : Fin n → ℝ) : ℝ :=
  (∫ θ, p θ ∂μ) - ∑ i, B i * Real.log (β i)

/-- Dual optimality with the paper's convention at `β i = 0`. -/
def IsDEGOptimal (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (B : Fin n → ℝ) (p : α → ℝ) (β : Fin n → ℝ) : Prop :=
  IsDEGFeasible μ v p β ∧ (∀ i, 0 < β i) ∧
  ∀ p' β', IsDEGFeasible μ v p' β' → (∀ i, 0 < β' i) →
    degObj μ B p β ≤ degObj μ B p' β'

/-- The pointwise maximum of scaled buyer valuations. -/
noncomputable def maxScaled {n : ℕ} (v : Fin n → α → ℝ)
    (β : Fin n → ℝ) : α → ℝ :=
  fun θ => ⨆ i, β i * v i θ

/-- The feasible utility set `U(v,Θ)` of (1). -/
def feasUtil (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ) : Set (Fin n → ℝ) :=
  {u | ∃ x, IsAllocation μ x ∧ ∀ i, u i = pair μ (v i) (x i)}

end InfFisher.Linear


