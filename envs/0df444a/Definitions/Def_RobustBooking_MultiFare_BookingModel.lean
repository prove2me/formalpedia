-- Prove2me | Definitions.Def_RobustBooking_MultiFare_BookingModel
-- name    : RobustBooking_MultiFare_BookingModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T23:24:21.603243+00:00
-- url     : https://prove2.me/theorems/274420eb-b83e-4ef5-8066-7aa064d508a4
-- title:
--   Continuous m-fare online booking model: requests, online policies, revenue, offline optimum, competitive ratio
-- statement:
--   **The continuous $m$-fare booking problem.** A seller holds $n > 0$ units of capacity (seats) and faces a sequence of booking requests. There are $m$ fare classes, numbered $1, \dots, m$; class $i$ pays the fare $f_i$ per unit. A **request** $r$ names a class $\mathrm{cls}(r)$ and a quantity $\mathrm{qty}(r)$. An **instance** is a finite list $I = (r_1, \dots, r_s)$ of requests with $1 \le \mathrm{cls}(r_k) \le m$ and $\mathrm{qty}(r_k) > 0$ for every $k$. Demands are real numbers and requests may be partially accepted (the *continuous problem*).
--
--   A **deterministic online policy** $A$ is any rule that, when request $r_{k+1}$ arrives, sees the earlier requests $r_1, \dots, r_k$ together with the quantities $x_1, \dots, x_k$ it accepted from them, and the current request, and proposes a quantity $a$. The accepted quantity is the proposal clipped to the feasible range,
--   $$x_{k+1} = \max\Bigl(0,\ \min\bigl(a,\ \mathrm{qty}(r_{k+1}),\ n - \textstyle\sum_{l \le k} x_l\bigr)\Bigr),$$
--   so every rule is a feasible, non-anticipative policy. Its **revenue** on $I$ is $R(A, I) = \sum_k f_{\mathrm{cls}(r_k)}\, x_k$.
--
--   The **offline optimum** is
--   $$v^*(I) = \sup\Bigl\{ \textstyle\sum_k f_{\mathrm{cls}(r_k)}\, x_k \;:\; 0 \le x_k \le \mathrm{qty}(r_k),\ \sum_k x_k \le n \Bigr\}.$$
--
--   The **competitive ratio** of a deterministic policy is
--   $$c(A) = \inf\Bigl\{ \frac{R(A, I)}{v^*(I)} \;:\; I \text{ an instance with } v^*(I) > 0 \Bigr\}.$$
--   A **randomized policy** is a random choice $A(\omega)$ of a deterministic policy, with $\omega$ drawn from a probability measure $\mu$ on an arbitrary measurable space $\Omega$; its competitive ratio is
--   $$c(\mu, A) = \inf\Bigl\{ \frac{\mathbb{E}_{\omega \sim \mu}[R(A(\omega), I)]}{v^*(I)} \;:\; I \text{ an instance with } v^*(I) > 0 \Bigr\}.$$
--   These are the performance measures of Ball and Queyranne (pp. 950–951) on the continuous problem (p. 952) with the $m$ fare classes of §2.1.
--
--   **Formalization Note.** Fares are a function `f : ℕ → ℝ` read 1-based on `1..m`; the fare ordering $f_1 > \dots > f_m > 0$ is not part of the model but a hypothesis of each theorem. Requests carry a real quantity; the paper's unit orders with fractional acceptance $0 \le x_i \le 1$ (p. 956) are the case $\mathrm{qty} = 1$, and "$n$ requests for fare class $i$" can be one request of quantity $n$. A policy sees its own past accepted quantities; since those are determined by the past requests, this is the same class of policies as history-of-requests rules. $v^*$ is a real `sSup` of a nonempty set (take $x = 0$) that is bounded above; the competitive ratios are real `sInf`s over a set that is nonempty (a single class-1 request has $v^* > 0$) and, when fares are positive, bounded below by $0$. The expected revenue is a Bochner integral; for a fixed instance the revenue is bounded in $\omega$, so measurability in $\omega$ (a hypothesis of the theorems) makes it integrable.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, pp. 950–952 (competitive ratio, randomized competitive ratio, continuous problem), p. 956 (online policies), p. 957 §2.1 (m fare classes)

import Mathlib

namespace RobustBooking.MultiFare

open MeasureTheory

/-- A booking request of the continuous `m`-fare problem: the fare class `cls`
(classes are numbered `1, …, m`, class `i` paying the fare `f i`) and the requested
quantity `qty`. -/
structure Request where
  cls : ℕ
  qty : ℝ

/-- An instance (demand sequence) of the `m`-fare problem: every request is for one of the
classes `1, …, m` and asks for a positive quantity. -/
def IsInstance (m : ℕ) (I : List Request) : Prop :=
  ∀ r ∈ I, 1 ≤ r.cls ∧ r.cls ≤ m ∧ 0 < r.qty

/-- A deterministic online booking policy. Given the past requests together with the
quantities it accepted from them (oldest first) and the current request, it proposes a
quantity to accept. It never sees future requests. -/
def DetPolicy : Type := List (Request × ℝ) → Request → ℝ

/-- The proposal `a` for request `r`, clipped to the feasible range
`[0, min r.qty (n - used)]`, where `used` is the capacity already sold. -/
noncomputable def clip (n used : ℝ) (r : Request) (a : ℝ) : ℝ :=
  max 0 (min a (min r.qty (n - used)))

/-- Run a policy on the remaining requests, starting from the booking record `past`. -/
noncomputable def runFrom (n : ℝ) (A : DetPolicy) :
    List (Request × ℝ) → List Request → List (Request × ℝ)
  | past, [] => past
  | past, r :: rs =>
      runFrom n A (past ++ [(r, clip n (past.map Prod.snd).sum r (A past r))]) rs

/-- The booking record (each request with the quantity accepted from it) produced by the
policy `A` on instance `I` with capacity `n`. -/
noncomputable def run (n : ℝ) (A : DetPolicy) (I : List Request) : List (Request × ℝ) :=
  runFrom n A [] I

/-- Revenue of policy `A` on instance `I`: the sum of fare times accepted quantity. -/
noncomputable def revenue (f : ℕ → ℝ) (n : ℝ) (A : DetPolicy) (I : List Request) : ℝ :=
  ((run n A I).map fun p => f p.1.cls * p.2).sum

/-- Offline optimal revenue `v*(I)`: the supremum of `∑ f_{cls k} x_k` over all
`x` with `0 ≤ x_k ≤ qty_k` and `∑ x_k ≤ n` (partial acceptance allowed). -/
noncomputable def offlineOpt (f : ℕ → ℝ) (n : ℝ) (I : List Request) : ℝ :=
  sSup {v : ℝ | ∃ x : Fin I.length → ℝ,
    (∀ k, 0 ≤ x k ∧ x k ≤ (I.get k).qty) ∧ ∑ k, x k ≤ n ∧
    v = ∑ k, f (I.get k).cls * x k}

/-- Competitive ratio of a deterministic policy: the infimum, over all instances with
positive offline optimum, of revenue divided by offline optimum. -/
noncomputable def competitiveRatio (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (A : DetPolicy) : ℝ :=
  sInf {c : ℝ | ∃ I : List Request, IsInstance m I ∧ 0 < offlineOpt f n I ∧
    c = revenue f n A I / offlineOpt f n I}

/-- Competitive ratio of a randomized policy, i.e. a random choice `A ω` of a deterministic
policy with `ω` drawn from the probability measure `μ`: the infimum, over all instances
with positive offline optimum, of expected revenue divided by offline optimum. -/
noncomputable def randCompetitiveRatio (m : ℕ) (f : ℕ → ℝ) (n : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (A : Ω → DetPolicy) : ℝ :=
  sInf {c : ℝ | ∃ I : List Request, IsInstance m I ∧ 0 < offlineOpt f n I ∧
    c = (∫ ω, revenue f n (A ω) I ∂μ) / offlineOpt f n I}

end RobustBooking.MultiFare


