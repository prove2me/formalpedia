-- Prove2me | Definitions.Def_SubquadCutReach_Faster_Averaging
-- name    : SubquadCutReach_Faster_Averaging
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T16:58:20.203328+00:00
-- url     : https://prove2.me/theorems/ce66c98f-76a7-4dd1-ac9e-607ce3b216c9
-- title:
--   Signed truncation and the specified optimistic averaging updates
-- statement:
--   The box projection clips every coordinate to $[-1,1]$. With $\eta=1/8$, the optimistic state, trial and regret follow the two updates in the source. Signed truncation retains $B$ binary fractional digits of the magnitude. For averaging, $B=6+5(\lfloor\log_2 n\rfloor+1)$ ensures coefficient error at most $1/(64n^5)$ when $n\ge1$.
--
--   $$v_t^+=P(v_t-\eta\widehat\ell_t),\quad v_{t+1}=P(v_t-\eta\ell_t),\quad \bar z=T^{-1}\sum_{t=1}^T z_t^+.$$
--
--   The compressed state stores every potential pair value and one potential per vertex. Loss evaluations use truncated weighted imbalances, with the repeated vertex-coordinate loss divided by $n$. The average uses trial states. Rational bit size bounds numerator and denominator separately. These are actual recurrences, with no hypotheses asserting their desired convergence.
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), §A.1–A.2, Theorem A.2, Lemmas A.1 and A.3, equations (6)–(9), pp.20–22 (PDF pp.22–24)

import Mathlib
import Definitions.Def_SubquadCutReach_Faster_Protocol

set_option autoImplicit false
open scoped BigOperators

namespace SubquadCutReach.Faster

noncomputable def clip (r : ℝ) : ℝ := max (-1) (min 1 r)

noncomputable def omdState {d : ℕ} (loss hint : ℕ → Fin d → ℝ) : ℕ → Fin d → ℝ
  | 0 => fun _ => 0
  | t+1 => fun i => clip (omdState loss hint t i - (1/8:ℝ) * loss t i)

noncomputable def omdTrial {d : ℕ} (loss hint : ℕ → Fin d → ℝ) (t : ℕ) : Fin d → ℝ :=
  fun i => clip (omdState loss hint t i - (1/8:ℝ) * hint t i)

noncomputable def regret {d : ℕ} (loss hint : ℕ → Fin d → ℝ) (T : ℕ) (u : Fin d → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, ∑ i, loss t i * (omdTrial loss hint t i - u i)

/-- Signed binary truncation. Endpoints ±1 are retained; B fractional digits. -/
noncomputable def trunc (B : ℕ) (a : ℝ) : ℝ :=
  (if a < 0 then -1 else 1) * (⌊|a| * (2:ℝ)^B⌋ : ℤ) / (2:ℝ)^B

noncomputable def precision (n : ℕ) : ℕ := 6 + 5*(Nat.log 2 n+1)

noncomputable def weighted {n : ℕ} (H : SimpleGraph (Fin n)) (v : Fin n)
    (X : Finset (Fin n)) (a : Fin n → ℝ) : ℝ := by
  classical
  exact ∑ w ∈ X, if H.Adj v w then a w else 0

noncomputable def approxImbalance {n : ℕ} (H : SimpleGraph (Fin n))
    (z : Fractional n) : Fin n → ℝ :=
  fractionalImbalance H (fun u v => trunc (precision n) (z u v))

abbrev AvgState (n : ℕ) := Fractional n × (Fin n → ℝ)

/-- Exactly equations (7),(8): both the trial and actual updates start at the persistent state.
The n repeated coordinates have been compressed to one vertex potential. -/
noncomputable def avgUpdate {n : ℕ} (H : SimpleGraph (Fin n)) (b : Fin n → ℤ)
    (base sample : AvgState n) : AvgState n :=
  ((fun u v => clip (base.1 u v - (1/8:ℝ)*(sample.2 u-sample.2 v))),
   fun v => clip (base.2 v - (1/8:ℝ)*((b v : ℝ)-approxImbalance H sample.1 v)/(n:ℝ)))

noncomputable def avgState {n : ℕ} (H : SimpleGraph (Fin n)) (b : Fin n → ℤ) : ℕ → AvgState n
  | 0 => (fun _ _ => 0, fun _ => 0)
  | t+1 => let v := avgState H b t; avgUpdate H b v (avgUpdate H b v v)

noncomputable def avgTrial {n : ℕ} (H : SimpleGraph (Fin n)) (b : Fin n → ℤ)
    (t : ℕ) : AvgState n := let v := avgState H b t; avgUpdate H b v v

noncomputable def average {n : ℕ} (H : SimpleGraph (Fin n)) (b : Fin n → ℤ)
    (T : ℕ) : Fractional n := fun u v => (∑ t ∈ Finset.range T, (avgTrial H b t).1 u v)/(T:ℝ)

/-- Numerator and denominator each have at most B binary digits (zero is permitted). -/
def RationalBits (B : ℕ) (x : ℝ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ a < 2^B ∧ d < 2^B ∧ x = (a:ℝ)/d

/-- Known weights row layout: X row, followed by weights. -/
noncomputable def weightInput {n : ℕ} (v : Fin n) (X : Finset (Fin n))
    (a : Fin n → ℝ) (B : ℕ) : Memory := by
  classical
  exact input n v.val B fun i =>
    if h : i < n then if (⟨i,h⟩ : Fin n) ∈ X then 1 else 0
    else if h : i-n < n then a ⟨i-n,h⟩ else 0

noncomputable def weightDigits (n : ℕ) (c : ℝ) : ℕ :=
  (Nat.ceil c+2)*(Nat.log 2 (n+2)+1)

noncomputable def weightMatrixInput {n : ℕ} (X : Fin n → Finset (Fin n))
    (a : Fin n → Fin n → ℝ) (B : ℕ) : Memory := by
  classical
  exact input n B 0 fun i =>
    if hi : i < n*n then
      if hu : i/n < n then if hv : i%n < n then
        if (⟨i%n,hv⟩ : Fin n) ∈ X ⟨i/n,hu⟩ then 1 else 0 else 0 else 0
    else
      let j := i-n*n
      if hu : j/n < n then if hv : j%n < n then a ⟨j/n,hu⟩ ⟨j%n,hv⟩ else 0 else 0

end SubquadCutReach.Faster


