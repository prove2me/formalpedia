-- Prove2me | Definitions.Def_ReusableAssort_Hybrid_Supplement_AdvBookingCounterexample
-- name    : ReusableAssort_Hybrid_Supplement_AdvBookingCounterexample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:18:00.328838+00:00
-- url     : https://prove2.me/theorems/f1dadd5e-16ee-4ab4-9031-edf04c6b6376
-- title:
--   ec26–ec27 — one-period advanced-booking LP, Algorithm 5 as printed, and a counterexample instance
-- statement:
--   Restrict the advanced-booking model to one time period, one deterministic type, and immediate check-in. No unit has yet been rented. For two products the LP has offer variables $x_S$ and unconditional allocation variables $y_{S,i}$, satisfying $x,y\ge0$, $\sum_S x_S\le1$, $y_{S,i}\le\phi(S,i)x_S$, and $\sum_S y_{S,i}\le c_i$. Its objective is $\sum_{S,i}r_i y_{S,i}$. Optimality compares every feasible assignment.
--
--   `expRevAlg5One` implements the printed Algorithm 5 in this corner: sample $\hat S$ with probability $x_{\hat S}$, discard each product independently with probability $\gamma$, call Procedure 1 with target $y_{\hat S,i}$, and integrate the consumer's revenue. Positive inventories make both availability tests automatic. These definitions serve a refutation of the general theorem, so a restriction of the algorithm suffices; no general booking guarantee is asserted.
--
--   The fixed instance has two inventory-100 products, fee 1, duration 1, and all assortments feasible. The type always chooses product 0 if present and chooses nothing otherwise. The assignment splits offer probability equally between $\{0\}$ and $\{0,1\}$; each has unconditional allocation probability $1/2$ to product 0. All other allocation variables are zero.
--
--   **Formalization Note** All time/check-in indices are 1, so the printed LP's inconsistent general indices do not affect this restriction. The target in Algorithm 5 line 9 is used exactly as printed, without division by $x_{\hat S}$. Finite sums integrate its randomness. Only the refutation theorem uses this one-period definition.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, pp. ec26–ec27 (PDF 52–53), Expected-LP-AdvBooking and Algorithm 5

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_SubAssort

namespace ReusableAssort.Hybrid.Supplement

/-- The one-period, immediate-check-in restriction of Expected-LP-AdvBooking (ec26).
All time, check-in and type indices equal 1. No unit can already be out. -/
def advOneFeasible (I : Instance 2 1 (Fin 1))
    (x : Finset (Fin 2) → ℝ) (y : Finset (Fin 2) → Fin 2 → ℝ) : Prop :=
  (∀ S ∈ I.feas, 0 ≤ x S) ∧ (∑ S ∈ I.feas, x S ≤ 1) ∧
  (∀ S ∈ I.feas, ∀ i, 0 ≤ y S i ∧ y S i ≤ I.phi 0 S i * x S) ∧
  (∀ i, ∑ S ∈ I.feas, y S i ≤ (I.c i : ℝ))

/-- The objective of the one-period advanced-booking LP. -/
noncomputable def advOneObj (I : Instance 2 1 (Fin 1))
    (y : Finset (Fin 2) → Fin 2 → ℝ) : ℝ :=
  ∑ S ∈ I.feas, ∑ i, I.r 0 i * y S i

/-- Optimality in the one-period advanced-booking LP. -/
def advOneOptimal (I : Instance 2 1 (Fin 1))
    (x : Finset (Fin 2) → ℝ) (y : Finset (Fin 2) → Fin 2 → ℝ) : Prop :=
  advOneFeasible I x y ∧ ∀ x' y', advOneFeasible I x' y' → advOneObj I y' ≤ advOneObj I y

/-- Algorithm 5, ec27, on a one-period instance with positive inventories and immediate
check-in: sample Shat with law x, independently discard with probability γ, and call Procedure 1
with the *printed* unconditional targets y Shat i (not y Shat i / x Shat).
The last sum integrates the consumer's choice. Every unit is available throughout this step. -/
noncomputable def expRevAlg5One (I : Instance 2 1 (Fin 1))
    (x : Finset (Fin 2) → ℝ) (y : Finset (Fin 2) → Fin 2 → ℝ) (γ : ℝ) : ℝ :=
  ∑ Shat ∈ I.feas, x Shat *
    ∑ Sbar ∈ Shat.powerset,
      ((∏ _i ∈ Sbar, (1 - γ)) * ∏ _i ∈ Shat \ Sbar, γ) *
        ∑ Stil ∈ Sbar.powerset,
          subAssort (I.phi 0) Sbar (y Shat) Stil *
            ∑ i ∈ Stil, I.phi 0 Stil i * I.r 0 i

/-- A source counterexample in the unambiguous corner t = s_t = T = 1:
two products of inventory 100, all assortments feasible, fee 1, duration 1,
and a single type that chooses product 0 exactly when it is offered. -/
noncomputable def advCounterI : Instance 2 1 (Fin 1) where
  c := fun _ => 100
  feas := Finset.univ
  phi := fun _ S i => if i = 0 ∧ (0 : Fin 2) ∈ S then 1 else 0
  r := fun _ _ => 1
  g := fun _ _ d => if d = 1 then 1 else 0
  F := fun _ _ => 1

/-- Split the offer probability equally between {0} and {0,1}. -/
noncomputable def advCounterX (S : Finset (Fin 2)) : ℝ :=
  if (0 : Fin 2) ∈ S then 1 / 2 else 0

/-- On each of those offers the unconditional allocation probability is 1/2. -/
noncomputable def advCounterY (S : Finset (Fin 2)) (i : Fin 2) : ℝ :=
  if i = 0 ∧ (0 : Fin 2) ∈ S then 1 / 2 else 0

end ReusableAssort.Hybrid.Supplement


