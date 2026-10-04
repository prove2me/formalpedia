-- Prove2me | Definitions.Def_SeatInventory_Nested_Model
-- name    : SeatInventory_Nested_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:26:23.750429+00:00
-- url     : https://prove2.me/theorems/7f9d4553-74d5-485b-9bea-52a3b2e6632b
-- title:
--   Two nested fare classes: realised and expected revenue, $\bar P(S)$, EMSR and the EMSR protection level
-- statement:
--   **The two-class nested seat inventory model** (Belobaba, Sects. 5.1–5.2).
--
--   A single flight leg has capacity $C \in \mathbb N$ seats, sold in two fare classes with average fares $f_1$ (class 1, the high fare) and $f_2$ (class 2, the low fare). Requests for the two classes are random variables $r_1, r_2 : \Omega \to \mathbb N$ on a probability space $(\Omega, \mu)$. A **protection level** $S \in \mathbb N$ is the number of seats protected for class 1; the class-2 **booking limit** is $BL_2 = C - S$, and the class-1 booking limit is the whole cabin $C$.
--
--   1. **Nested revenue.** All class-2 requests arrive before any class-1 request. Class 2 then books $\min(r_2, C-S)$ seats and class 1 may book any seat that is still unsold, so the realised revenue is
--   $$R^{\mathrm{nest}}_S(r_1, r_2) = f_2 \min(r_2, C - S) + f_1 \min\bigl(r_1,\, C - \min(r_2, C - S)\bigr).$$
--   2. **Distinct revenue.** In two separate (non-nested) inventories class 1 receives exactly $S$ seats and class 2 receives $C - S$, so $R^{\mathrm{dist}}_S(r_1, r_2) = f_2 \min(r_2, C-S) + f_1 \min(r_1, S)$.
--   3. **Expected revenues** $\bar R^{\mathrm{nest}}(S) = \mathbb E[R^{\mathrm{nest}}_S(r_1, r_2)]$ and $\bar R^{\mathrm{dist}}(S) = \mathbb E[R^{\mathrm{dist}}_S(r_1, r_2)]$.
--   4. **Tail probability** $\bar P(S) = P[r \ge S]$, the probability of receiving $S$ or more requests (Eq. (6.2)).
--   5. **Expected class revenue** of $S$ seats in a class with fare $f$: $\bar R(S) = f \cdot \bar b(S)$ with expected bookings $\bar b(S) = \mathbb E[\min(r, S)]$ (Eqs. (5.9), (5.14)).
--   6. **Expected marginal seat revenue** of the $S$-th seat: $\mathrm{EMSR}(S) = f \cdot \bar P(S)$ (Eqs. (5.11), (6.1)).
--   7. **The EMSR protection level** (Eq. (5.15)): the largest integer $S \in \{0, \dots, C\}$ with
--   $$\mathrm{EMSR}_1(S) = f_1 \cdot P[r_1 \ge S] \ge f_2,$$
--   and $0$ if there is none (when $f_2 \le f_1$, $S = 0$ always qualifies because $P[r_1 \ge 0] = 1$).
--
--   These are the objects of the thesis's two-class nested model; every theorem of the mission is stated in terms of them.
--
--   **Formalization Note** The thesis writes the model with continuous densities but requires integer seat counts; here demands are $\mathbb N$-valued and $\bar P(S)$ is $P[r \ge S]$ as in Eq. (6.2) and the prose of Eq. (5.11), not $P[r > S]$ as in Eq. (5.2). Probabilities are `μ.real` of the event, expectations are Bochner integrals (the revenues are bounded, so they are integrable once the demands are measurable). Truncated subtraction $C - S$ is used only for $S \le C$ in the theorems. The protection level is the threshold of (5.15), not an argmax of expected revenue.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 105, Eqs. (5.8)-(5.11); p. 108 (nested booking limits, booking order); p. 109, Eqs. (5.14)-(5.15); p. 112 (booking order); p. 142, Eqs. (6.1)-(6.2)

import Mathlib

namespace SeatInventory.Nested

open MeasureTheory

/-! ### Two nested fare classes on a single flight leg (Belobaba 1987, Sects. 5.1–5.2)

Demands are `ℕ`-valued random variables `r₁ r₂ : Ω → ℕ` on a probability space `(Ω, μ)`.
Fares are `f₁` (class 1, high) and `f₂` (class 2, low), capacity is `C`, and `S` is the number of
seats protected for class 1 (the class-2 booking limit is `C - S`). -/

/-- Realised revenue of a two-class **nested** inventory with protection level `S` when all class-2
requests arrive before any class-1 request (Belobaba p. 108, p. 112): class 2 books
`min r₂ (C - S)` seats, and class 1 may then book any seat still unsold,
`min r₁ (C - min r₂ (C - S))`. -/
def nestedRevenue (f₁ f₂ : ℝ) (C S r₁ r₂ : ℕ) : ℝ :=
  f₂ * (min r₂ (C - S) : ℕ) + f₁ * (min r₁ (C - min r₂ (C - S)) : ℕ)

/-- Realised revenue of two **distinct** (non-nested) inventories with `S` seats allotted to class 1
and `C - S` seats to class 2 (Belobaba Eqs. (5.8)–(5.10)). -/
def distinctRevenue (f₁ f₂ : ℝ) (C S r₁ r₂ : ℕ) : ℝ :=
  f₂ * (min r₂ (C - S) : ℕ) + f₁ * (min r₁ S : ℕ)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Expected revenue of the nested inventory with protection level `S`: the expectation of
`nestedRevenue` under `μ`. -/
noncomputable def expectedNestedRevenue (μ : Measure Ω) (r₁ r₂ : Ω → ℕ) (f₁ f₂ : ℝ)
    (C S : ℕ) : ℝ :=
  ∫ ω, nestedRevenue f₁ f₂ C S (r₁ ω) (r₂ ω) ∂μ

/-- Expected revenue of the distinct inventories with `S` seats allotted to class 1. -/
noncomputable def expectedDistinctRevenue (μ : Measure Ω) (r₁ r₂ : Ω → ℕ) (f₁ f₂ : ℝ)
    (C S : ℕ) : ℝ :=
  ∫ ω, distinctRevenue f₁ f₂ C S (r₁ ω) (r₂ ω) ∂μ

/-- `P̄(S) = P[r ≥ S]`, the probability of receiving `S` or more requests (Belobaba Eq. (6.2)). -/
noncomputable def tailProb (μ : Measure Ω) (r : Ω → ℕ) (S : ℕ) : ℝ :=
  μ.real {ω | S ≤ r ω}

/-- Expected revenue of a fare class with fare `f` from `S` seats, `R̄(S) = f · b̄(S)` with expected
bookings `b̄(S) = E[min r S]` (Belobaba Eqs. (5.9), (5.14)). -/
noncomputable def classRevenue (μ : Measure Ω) (r : Ω → ℕ) (f : ℝ) (S : ℕ) : ℝ :=
  f * ∫ ω, ((min (r ω) S : ℕ) : ℝ) ∂μ

/-- Expected marginal seat revenue of the `S`-th seat, `EMSR(S) = f · P̄(S)`
(Belobaba Eqs. (5.11), (6.1)). -/
noncomputable def emsr (μ : Measure Ω) (r : Ω → ℕ) (f : ℝ) (S : ℕ) : ℝ :=
  f * tailProb μ r S

open Classical in
/-- The EMSR protection level for class 1 against class 2 (Belobaba Eq. (5.15)): the largest
integer `S ∈ {0, …, C}` with `EMSR₁(S) = f₁ · P[r₁ ≥ S] ≥ f₂`, and `0` if no such `S` exists. -/
noncomputable def emsrProtectionLevel (μ : Measure Ω) (r₁ : Ω → ℕ) (f₁ f₂ : ℝ) (C : ℕ) : ℕ :=
  ((Finset.range (C + 1)).filter (fun S => f₂ ≤ emsr μ r₁ f₁ S)).sup id

end SeatInventory.Nested


