-- Prove2me | Definitions.Def_RobustBooking_BidPrice_Model
-- name    : RobustBooking_BidPrice_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T00:19:02.056297+00:00
-- url     : https://prove2.me/theorems/f0b79f05-754f-4f2b-af5e-4324f7cd35cd
-- title:
--   Continuous bid-price booking: sized requests with real fares, fare-interval admissibility, r, ρ and the offline optimum
-- statement:
--   **The continuous bid-price booking model.** A seller holds capacity $n > 0$, a real number (in the continuous problem demands and accepted quantities are nonnegative reals and orders may be partially accepted). A **request** carries a real **fare** $O$ and a positive real **quantity** $d > 0$. An **instance** $I$ is a finite list of requests. For a set of fares $F$, an instance is **admissible for $F$** when every request's fare lies in $F$; in the bid-price problem $F = [f_{\min}, f_{\max}]$, the fares between the minimum fare $f_{\min}$ and the maximum ("regular") fare $f_{\max}$, below which no request is even considered.
--
--   The **maximum discount ratio** is $r = f_{\min}/f_{\max}$, and
--   $$\rho(r) = \frac{1}{1 - \ln r},$$
--   with $\ln$ the natural logarithm.
--
--   An offline acceptance vector $x$ for $I$ is **feasible** for capacity $n$ when $0 \le x_i \le d_i$ for every request and $\sum_i x_i \le n$. The **optimal offline revenue** is
--   $$v^*(I) = \sup\Big\{\sum_i O_i\, x_i \;:\; x \text{ feasible}\Big\},$$
--   the revenue of a clairvoyant seller who knows the whole instance in advance.
--
--   **Formalization Note.** Requests are sized (`qty_pos : 0 < qty`); the paper's unit orders with fractional acceptance $0 \le x_i \le 1$ are the case `qty = 1`. The offline optimum is a real `sSup`; for $n \ge 0$ its set is nonempty ($x = 0$) and bounded above ($0 \le x_i \le d_i$), so it is the true, attained maximum. $r$ and $\rho$ are plain real expressions; theorems assume $0 < f_{\min} < f_{\max}$, under which $\ln r < 0$ and $0 < \rho < 1$.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 950 (offline optimum), p. 952 (continuous problem), p. 956 (§2, fares in [fmin, fmax]), p. 959 (r and ρ)

import Mathlib

namespace RobustBooking.BidPrice

/-- A booking request (order) of the continuous bid-price control problem (Ball–Queyranne 2009,
§2, p. 956): each request specifies a fare, which can be any real number, and a quantity, which
may be any positive real number (the continuous problem of p. 952; the unit orders of p. 956 with
fractional acceptance `0 ≤ x ≤ 1` are the case `qty = 1`). -/
structure Request where
  /-- The fare `O` offered by the request. -/
  fare : ℝ
  /-- The quantity requested. -/
  qty : ℝ
  /-- Quantities are positive real numbers. -/
  qty_pos : 0 < qty

/-- An instance is admissible for the fare set `F` if every request's fare lies in `F`. For the
bid-price problem `F = [f_min, f_max]` (p. 956: fares lie between the maximum fare `f_max` and the
minimum fare `f_min`, "below which no request will even be considered"). -/
def FaresIn (F : Set ℝ) (I : List Request) : Prop :=
  ∀ q ∈ I, q.fare ∈ F

/-- The maximum discount ratio `r = f_min / f_max` (p. 959). -/
noncomputable def discountRatio (fmin fmax : ℝ) : ℝ := fmin / fmax

/-- `ρ = 1 / (1 - ln r)` (p. 959), with `ln` the natural logarithm `Real.log`. -/
noncomputable def rho (r : ℝ) : ℝ := 1 / (1 - Real.log r)

/-- A feasible offline acceptance vector for the instance `I` (a finite list of requests) and
capacity `n`: `x i` is the quantity accepted from the `i`-th request, with `0 ≤ x i ≤ qty i`
(partial orders may be accepted) and total accepted quantity at most `n`. -/
def IsFeasibleOffline (n : ℝ) (I : List Request) (x : Fin I.length → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ (I.get i).qty) ∧ ∑ i, x i ≤ n

/-- The optimal offline (clairvoyant) revenue `v*(I)` (p. 950): the supremum of the revenue
`∑ fare · x` over all feasible offline acceptance vectors. For `0 ≤ n` the set contains the value
of `x = 0`, and `x` lies in the box `0 ≤ x ≤ qty`, so the set of revenues is nonempty and bounded
above and the supremum is the true (attained) maximum. -/
noncomputable def offlineOpt (n : ℝ) (I : List Request) : ℝ :=
  sSup {v : ℝ | ∃ x : Fin I.length → ℝ, IsFeasibleOffline n I x ∧
    v = ∑ i, (I.get i).fare * x i}

end RobustBooking.BidPrice


