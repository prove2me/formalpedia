-- Prove2me | Definitions.Def_AirlineYieldMgmt_BookingLimits_Model
-- name    : AirlineYieldMgmt_BookingLimits_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T11:00:52.410977+00:00
-- url     : https://prove2.me/theorems/6209d474-70e2-4ba6-87b1-2a838e7c5ad3
-- title:
--   Model 1 of Subramanian–Stidham–Lautenbacher: data, standing assumptions, the value functions Uₙ of recursion (2)–(3), and the booking limit b_in of Eq. (7)
-- statement:
--   **Model 1 (single-leg seat allocation with cancellations and no-shows).** There are $m$ fare classes and $N$ decision periods, or **stages**, numbered in reverse chronological order $n = N, N-1, \dots, 1, 0$: stage $N$ opens the flight for reservations and stage $0$ is departure. The **state** $x \in \{0, 1, 2, \dots\}$ is the number of seats currently reserved. At each stage $n \ge 1$ exactly one event occurs: a request for a seat in fare class $i$ (probability $p_{in} \ge 0$), a cancellation by a customer holding a reservation (probability $q_n(x)$), or a null event, whose probability is fixed by Eq. (1),
--   $$p_{0n}(x) \;=\; 1 - \sum_{i=1}^m p_{in} - q_n(x).$$
--   Accepting a class-$i$ request at stage $n$ earns $r_{in} \ge 0$. At departure each reservation holder is independently a no-show with probability $\beta$, so the number $Y(x)$ of passengers who show up is binomial-$(x, 1-\beta)$; if $Y(x) = y$ an overbooking penalty $\pi(y)$ is incurred. $C$ is the capacity of the airplane.
--
--   For a function $f$ and $0 \le \gamma \le 1$ write
--   $$\mathrm{E}\,f(\mathrm{Bin}(x,\gamma)) \;=\; \sum_{k=0}^{x} \binom{x}{k} \gamma^k (1-\gamma)^{x-k} f(k).$$
--   The **value functions** $U_n$ are defined by the recursion (2)–(3):
--   $$U_0(x) = \mathrm{E}\big[-\pi(Y(x))\big],\quad Y(x)\sim\mathrm{Bin}(x,1-\beta),$$
--   $$U_n(x) = \sum_{i=1}^m p_{in}\max\{r_{in} + U_{n-1}(x+1),\ U_{n-1}(x)\} + q_n(x)\,U_{n-1}(x-1) + p_{0n}(x)\,U_{n-1}(x),\qquad n \ge 1.$$
--   The states reachable at stage $n$ are $0 \le x \le N - n$.
--
--   The **standing assumptions** of the model are: $p_{in} \ge 0$ and $r_{in} \ge 0$; $q_n(\cdot)$ is non-negative, nondecreasing and concave in $x$, with $q_n(0) = 0$; the null-event probability $p_{0n}(x)$ is non-negative for $1 \le n \le N$ and $0 \le x \le N - n$; $0 \le \beta \le 1$; $\pi(y)$ is non-negative, convex and nondecreasing in $y \ge 0$, with $\pi(y) = 0$ for $y \le C$.
--
--   The **booking limit** of fare class $i$ at stage $n \ge 1$ is Eq. (7):
--   $$b_{in} \;=\; \min\{x : U_{n-1}(x) - U_{n-1}(x+1) > r_{in}\},$$
--   with $b_{in} = \infty$ when no such $x$ exists.
--
--   **Formalization Note.** Fare class `i : Fin m` is the paper's class $i$ = `i.val + 1`; stages and states are natural numbers; probabilities, fares, $\beta$ and values are real. `Model.U` is defined by structural recursion on $n$ for every $x \in \mathbb N$; the paper uses it only on $0 \le x \le N - n$, and every theorem restricts to that range. The null-event probability `Model.p0` is *defined* by Eq. (1), and its non-negativity is assumed only on the reachable states (in the paper's linear case $q_n(x) = q_n x$, Remark 1, the sum $\sum_i p_{in} + q_n(x)$ exceeds $1$ for large $x$). The term $x - 1$ is natural-number subtraction, so at $x = 0$ it reads $U_{n-1}(0)$; the assumption $q_n(0) = 0$ (a cancellation requires a reservation; the page leaves it implicit, since otherwise (2) would evaluate $U_{n-1}(-1)$) makes that term vanish. "Nondecreasing and concave in $x$" for $q_n$ is discrete: `Monotone (q n)` and $q_n(x+2) - q_n(x+1) \le q_n(x+1) - q_n(x)$ for all $x \in \mathbb N$. The penalty $\pi$ is a function on $\mathbb R$ whose convexity, monotonicity and non-negativity are assumed on $y \ge 0$ as on the page; only its values at integers enter $U_0$. The binomial expectation is the finite sum above (`binomExp`). In `Model.bookingLimit` the minimum in (7) is taken over the reachable states $0 \le x \le N - n$ (the "for all $x$" of (7) is read on this range), as a `Finset.min` in `WithTop ℕ`; the minimum of the empty set is `⊤`, which encodes $b_{in} = \infty$.
-- source:
--   Subramanian, Stidham, Lautenbacher, Airline Yield Management with Overbooking, Cancellations, and No-Shows, Transp. Sci. 33(2), 1999, pp. 149–151, §1: model (pp. 149–150), Eq. (1) (p. 150), Eqs. (2)–(3) (p. 150), Eq. (7) (p. 151)

import Mathlib

namespace AirlineYieldMgmt.BookingLimits

open Finset

/-- The data of Model 1 of Subramanian–Stidham–Lautenbacher (1999), §1, pp. 149–150, with `m`
fare classes. Fare class `i : Fin m` is the paper's class `i.val + 1`. Stages `n` count the
periods remaining (stage `N` opens reservations, stage `0` is departure); states `x` are the
number of reserved seats.

* `N` — the number of decision periods (stages `N, N-1, …, 1, 0`);
* `C` — the capacity of the airplane;
* `p n i` — `p_{in}`, the probability of a request in fare class `i` at stage `n`;
* `q n x` — `q_n(x)`, the probability of a cancellation at stage `n` when `x` seats are reserved;
* `r n i` — `r_{in}`, the revenue earned by accepting a class-`i` request at stage `n`;
* `β` — the probability that a customer holding a reservation is a no-show;
* `π` — the overbooking penalty `π(y)` incurred when `y` customers show up. -/
structure Model (m : ℕ) where
  N : ℕ
  C : ℕ
  p : ℕ → Fin m → ℝ
  q : ℕ → ℕ → ℝ
  r : ℕ → Fin m → ℝ
  β : ℝ
  π : ℝ → ℝ

variable {m : ℕ}

/-- The null-event probability `p_{0n}(x)`, determined by Eq. (1), p. 150:
`∑_{i=1}^m p_{in} + q_n(x) + p_{0n}(x) = 1`. -/
noncomputable def Model.p0 (M : Model m) (n x : ℕ) : ℝ :=
  1 - (∑ i, M.p n i) - M.q n x

/-- `E[f(Y(x))]` for `Y(x) ∼ Bin(x, γ)`, written as the finite sum
`∑_{k=0}^{x} C(x,k) γ^k (1-γ)^{x-k} f(k)`. -/
noncomputable def binomExp (x : ℕ) (γ : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ k ∈ range (x + 1), (x.choose k : ℝ) * γ ^ k * (1 - γ) ^ (x - k) * f k

/-- The optimal value functions `U_n(x)` of Model 1, defined by the recursion (2)–(3), p. 150:

`U_0(x) = E[-π(Y(x))]` with `Y(x) ∼ Bin(x, 1 - β)`, and for `n ≥ 1`
`U_n(x) = ∑_i p_{in} max{r_{in} + U_{n-1}(x+1), U_{n-1}(x)} + q_n(x) U_{n-1}(x-1)
          + p_{0n}(x) U_{n-1}(x)`.

It is defined on every `x : ℕ`; the paper uses it on `0 ≤ x ≤ N - n`. The term `x - 1` is
natural-number subtraction, so at `x = 0` it reads `U_{n-1}(0)`; under `q_n(0) = 0`
(`Model.Standing.q_zero`) that term vanishes, as in the paper. -/
noncomputable def Model.U (M : Model m) : ℕ → ℕ → ℝ
  | 0, x => binomExp x (1 - M.β) (fun y => -M.π y)
  | n + 1, x =>
      (∑ i, M.p (n + 1) i * max (M.r (n + 1) i + M.U n (x + 1)) (M.U n x))
        + M.q (n + 1) x * M.U n (x - 1) + M.p0 (n + 1) x * M.U n x

/-- The standing assumptions of Model 1 (§1, pp. 149–150):
request probabilities and fares are non-negative; `q_n(·)` is non-negative, nondecreasing and
concave (in the discrete sense) with `q_n(0) = 0` (a cancellation needs a reservation); the
null-event probability `p_{0n}(x)` of Eq. (1) is non-negative for `1 ≤ n ≤ N` on the reachable
states `0 ≤ x ≤ N - n`; `0 ≤ β ≤ 1`; and `π` is non-negative, convex and nondecreasing on
`y ≥ 0`, with `π(y) = 0` for `y ≤ C`. -/
structure Model.Standing (M : Model m) : Prop where
  p_nonneg : ∀ n i, 0 ≤ M.p n i
  r_nonneg : ∀ n i, 0 ≤ M.r n i
  q_nonneg : ∀ n x, 0 ≤ M.q n x
  q_mono : ∀ n, Monotone (M.q n)
  q_concave : ∀ n x, M.q n (x + 2) - M.q n (x + 1) ≤ M.q n (x + 1) - M.q n x
  q_zero : ∀ n, M.q n 0 = 0
  p0_nonneg : ∀ n, 1 ≤ n → n ≤ M.N → ∀ x, x ≤ M.N - n → 0 ≤ M.p0 n x
  β_nonneg : 0 ≤ M.β
  β_le_one : M.β ≤ 1
  π_nonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ M.π y
  π_convex : ConvexOn ℝ (Set.Ici 0) M.π
  π_mono : MonotoneOn M.π (Set.Ici 0)
  π_zero : ∀ y : ℝ, y ≤ M.C → M.π y = 0

/-- The booking limit `b_{in}` of Eq. (7), p. 151:
`b_{in} := min{x : U_{n-1}(x) - U_{n-1}(x+1) > r_{in}}`, and `b_{in} = ∞` when there is no such
`x`. The minimum ranges over the states reachable at stage `n`, `0 ≤ x ≤ N - n`; the value lives
in `WithTop ℕ`, where `⊤` is `∞` (the minimum of the empty set). -/
noncomputable def Model.bookingLimit (M : Model m) (n : ℕ) (i : Fin m) : WithTop ℕ :=
  ((range (M.N - n + 1)).filter
    (fun x => M.r n i < M.U (n - 1) x - M.U (n - 1) (x + 1))).min

end AirlineYieldMgmt.BookingLimits


