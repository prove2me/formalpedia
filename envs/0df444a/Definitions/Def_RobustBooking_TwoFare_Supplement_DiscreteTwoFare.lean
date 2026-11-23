-- Prove2me | Definitions.Def_RobustBooking_TwoFare_Supplement_DiscreteTwoFare
-- name    : RobustBooking_TwoFare_Supplement_DiscreteTwoFare
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:43:51.689068+00:00
-- url     : https://prove2.me/theorems/2a98381a-f9e7-432a-86a1-3ca47dc27ce6
-- title:
--   The discrete two-fare booking problem: unit orders, all-or-none policies, competitive ratios, nested policy, c and θ_D (Eqs. (3)–(4))
-- statement:
--   These definitions set up the **discrete two-fare booking problem** of Ball and Queyranne (2009). There are $n\ge 1$ units of capacity, $n$ an integer, and two fares $f_1>f_2>0$ with discount ratio $r=f_2/f_1$. An instance $I$ is a finite sequence, of any length and in any order, of **unit orders**, each of fare class *high* (fare $f_1$) or *low* (fare $f_2$). Each order must be accepted whole or rejected, irrevocably, at its arrival, and at most $n$ orders can be accepted.
--
--   1. A **deterministic discrete policy** $A$ decides to accept or reject the current order from the classes of the earlier orders, its own earlier decisions and the class of the current order. When $n$ orders have already been accepted the order is rejected. Its revenue $R(A,I)$ is the total fare of the accepted orders.
--   2. The **offline optimum** $R^*(I)$ is the largest total fare of at most $n$ orders of $I$.
--   3. The **competitive ratio** of $A$ is
--   $$\inf\Big\{\frac{R(A,I)}{R^*(I)} : R^*(I)>0\Big\}.$$
--   A **randomized discrete policy** is a random choice $A(\omega)$ of a deterministic discrete policy, $\omega$ drawn from a probability measure $\mu$; its competitive ratio is the infimum of $\mathbb E_\mu[R(A(\omega),I)]/R^*(I)$ over the same instances.
--   4. The **discrete nested policy** with integer protection level $\theta\in\{0,\dots,n\}$ accepts every high-fare order while capacity remains and accepts a low-fare order iff capacity remains and fewer than $n-\theta$ low-fare orders have been accepted. The number $n-\theta$ is the **booking limit** of the low class.
--   5. Eq. (3): $c(x)=\min\{(n-(1-r)x)/n,\;x/n\}$. Eq. (4), the **optimum rounding**:
--   $$\theta_D(r,n)=\begin{cases} n-\lfloor b(r)n\rfloor & \text{if } c(\lfloor b(r)n\rfloor)\ge c(\lceil b(r)n\rceil),\\ n-\lceil b(r)n\rceil & \text{otherwise,}\end{cases}$$
--   where $b(r)=1/(2-r)$.
--
--   These objects are what Theorems 2 and 3 and Proposition 4 of the paper are about: the discrete counterpart of the continuous model of the published mission, where orders cannot be split.
--
--   **Formalization Note** `FareClass`, `fare` and `b` are reused from the published `RobustBooking.TwoFare.Booking`; its continuous `optRevenue`, policies and ratios are not used. An instance is a `List FareClass`: the integer demands of p. 952 are read as numbers of unit orders (p. 956), not as indivisible orders of several units. A policy is any function `List (FareClass × Bool) → FareClass → Bool` of the history and the current class; the run applies the capacity test. The offline optimum is `sSup` of a finite nonempty set of reals, so it is attained. The ratios are `sInf` of sets that are bounded below by `0`, and nonempty when `n ≥ 1` (one high order). Revenue on a fixed instance takes finitely many values, so the integral in the randomized ratio is that of a bounded function once it is measurable, which the theorems assume. In `thetaD` the floor and ceiling are `Nat.floor`/`Nat.ceil` of the nonnegative real `b(r)n`; for `0 < r < 1` both lie in `[0, n]`, so the natural subtraction is exact; ties go to the floor as in Eq. (4).
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 952 (discrete problem), pp. 950–951 (competitive ratio), p. 951 (nested protection levels), p. 954 (randomized policies; Eqs. (3)–(4)), p. 956 (unit orders, x_i ∈ {0,1})

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking

namespace RobustBooking.TwoFare.Supplement

open MeasureTheory

/-- The history seen by a discrete two-fare policy: the earlier unit orders, in arrival order, each
with its fare class and whether it was accepted (Ball–Queyranne 2009, p. 952 and p. 956: in the
discrete problem every order is one unit and is accepted whole or rejected). -/
abbrev DHist : Type := List (FareClass × Bool)

/-- A deterministic online policy for the discrete two-fare problem: from the history and the fare
class of the current unit order it decides to accept (`true`) or reject (`false`). It never sees
future orders or the length of the sequence. -/
abbrev DDetPolicy : Type := DHist → FareClass → Bool

/-- Running a discrete policy with integer capacity `n` on the remaining orders, given the history
and the number `used` of orders accepted so far. An order is accepted iff fewer than `n` orders
have been accepted and the policy accepts it; the result lists the decisions in arrival order. -/
def runFrom (n : ℕ) (A : DDetPolicy) : DHist → ℕ → List FareClass → List Bool
  | _, _, [] => []
  | hist, used, c :: rest =>
      let a : Bool := decide (used < n) && A hist c
      a :: runFrom n A (hist ++ [(c, a)]) (if a then used + 1 else used) rest

/-- The accept/reject decisions of policy `A` on instance `I`, in arrival order. -/
def accepted (n : ℕ) (A : DDetPolicy) (I : List FareClass) : List Bool :=
  runFrom n A [] 0 I

/-- The online revenue `R(A, I)` of a discrete policy: the sum of the fares of the accepted
orders. -/
noncomputable def revenue (f₁ f₂ : ℝ) (n : ℕ) (A : DDetPolicy) (I : List FareClass) : ℝ :=
  (List.zipWith (fun c a => if a then fare f₁ f₂ c else 0) I (accepted n A I)).sum

/-- The optimal offline revenue `R*(I)` of the discrete problem: the largest total fare of a set of
at most `n` orders of `I`. The set of values is finite and contains `0` (the empty set), so the
supremum is attained. -/
noncomputable def optRevenue (f₁ f₂ : ℝ) (n : ℕ) (I : List FareClass) : ℝ :=
  sSup {v : ℝ | ∃ S : Finset (Fin I.length), S.card ≤ n ∧
    v = ∑ i ∈ S, fare f₁ f₂ (I.get i)}

/-- The competitive ratio of a deterministic discrete policy (p. 950): the infimum of
`R(A, I) / R*(I)` over all discrete instances with positive optimal offline revenue. -/
noncomputable def competitiveRatio (f₁ f₂ : ℝ) (n : ℕ) (A : DDetPolicy) : ℝ :=
  sInf {c : ℝ | ∃ I : List FareClass, 0 < optRevenue f₁ f₂ n I ∧
    c = revenue f₁ f₂ n A I / optRevenue f₁ f₂ n I}

/-- The competitive ratio of a randomized discrete policy (p. 951, p. 954): a random choice `A ω`
of a deterministic discrete policy, `ω ∼ μ`; the infimum of `E[R(A, I)] / R*(I)` over all
discrete instances with positive optimal offline revenue. -/
noncomputable def randCompetitiveRatio (f₁ f₂ : ℝ) (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Ω → DDetPolicy) : ℝ :=
  sInf {c : ℝ | ∃ I : List FareClass, 0 < optRevenue f₁ f₂ n I ∧
    c = (∫ ω, revenue f₁ f₂ n (A ω) I ∂μ) / optRevenue f₁ f₂ n I}

/-- The number of low-fare orders accepted so far, read off the history. -/
def lowAccepted (hist : DHist) : ℕ :=
  (hist.filter (fun p => decide (p.1 = FareClass.low) && p.2)).length

/-- The discrete nested policy with integer protection level `θ` (pp. 951, 952, 956): a high-fare
order is accepted while capacity remains; a low-fare order is accepted iff capacity remains and
fewer than `n - θ` low-fare orders have been accepted (booking limit `n - θ`). The capacity test
is made by the run. Used with `θ ≤ n`. -/
def nestedD (n θ : ℕ) : DDetPolicy := fun hist c =>
  match c with
  | .high => true
  | .low => decide (lowAccepted hist < n - θ)

/-- Eq. (3), p. 954: `c(x) = min {(n - (1 - r) x) / n, x / n}`. -/
noncomputable def cfun (r : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  min (((n : ℝ) - (1 - r) * x) / n) (x / n)

/-- Eq. (4), p. 954, the optimum rounding: `θ_D(r, n) = n - ⌊b(r) n⌋` if
`c(⌊b(r) n⌋) ≥ c(⌈b(r) n⌉)`, and `n - ⌈b(r) n⌉` otherwise. For `0 < r < 1` one has
`n / 2 < b(r) n < n`, so both subtractions are exact. -/
noncomputable def thetaD (r : ℝ) (n : ℕ) : ℕ :=
  if cfun r n (⌈b r * n⌉₊ : ℝ) ≤ cfun r n (⌊b r * n⌋₊ : ℝ) then n - ⌊b r * n⌋₊
  else n - ⌈b r * n⌉₊

end RobustBooking.TwoFare.Supplement


