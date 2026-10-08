-- Prove2me | Definitions.Def_KellyReversibility_Symmetric_SymmetricQueue
-- name    : KellyReversibility_Symmetric_SymmetricQueue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:36:44.861423+00:00
-- url     : https://prove2.me/theorems/fc1d69b6-c5c0-4021-a0a0-686a765fea3f
-- title:
--   Symmetric queue with gamma-mixture service: data, Markov state space and transition rates
-- statement:
--   A **symmetric queue** (Kelly, §3.3, pp. 72–73) holds customers in positions $1, 2, \dots, n$, where $n$ is the number present. A total service effort is supplied at rate $\phi(n)$, with $\phi(n) > 0$ for $n > 0$; a proportion $\gamma(l, n)$ of it goes to the customer in position $l$, where $\sum_{l=1}^n \gamma(l, n) = 1$. When that customer leaves, the customers in positions $l+1, \dots, n$ move down to $l, \dots, n-1$. An arriving customer moves into position $l \in \{1, \dots, n+1\}$ with probability $\gamma(l, n+1)$, and the customers in positions $l, \dots, n$ move up by one. The use of the *same* function $\gamma$ for service and for arrivals is the symmetry condition $\gamma \equiv \delta$.
--
--   **Gamma-mixture service** (pp. 74–76). Customers of class $c$ (from a countable set $\mathcal C$) arrive in a Poisson stream of rate $\nu(c) \ge 0$, with $\sum_c \nu(c) < \infty$. On arrival a class-$c$ customer receives the refined class $(c, z)$, $z$ in a countable set $\mathcal Z$, with probability $p(c, z) \ge 0$, $\sum_z p(c, z) = 1$. A class-$(c, z)$ customer requires $w(c, z) \ge 1$ independent stages of service, each exponentially distributed with mean $d(c, z) > 0$; so his service requirement is gamma distributed with mean $w(c,z)d(c,z)$ and variance $w(c,z)d(c,z)^2$.
--
--   **The Markov process.** The record of the customer in position $l$ is $\mathbf c(l) = (c(l), z(l), u(l))$, where $u(l) \in \{1, \dots, w(c(l), z(l))\}$ is the stage in progress, and the state is $\mathbf c = (\mathbf c(1), \dots, \mathbf c(n))$. The state space consists of all finite sequences of records with $\nu(c(l))p(c(l), z(l)) > 0$ and $1 \le u(l) \le w(c(l), z(l))$. The transition rates $q(\mathbf c, \mathbf c')$ are the sums of the rates of the following events:
--
--   1. *arrival*: a class-$(c,z)$ customer enters position $l \in \{1, \dots, n+1\}$ at stage $1$, at rate $\nu(c)p(c,z)\gamma(l, n+1)$;
--   2. *stage completion*: the customer in position $l$, at stage $u < w(c(l), z(l))$, moves to stage $u + 1$, at rate $\phi(n)\gamma(l, n)/d(c(l), z(l))$;
--   3. *departure*: the customer in position $l$, at stage $u = w(c(l), z(l))$, leaves, at the same rate $\phi(n)\gamma(l, n)/d(c(l), z(l))$.
--
--   Every event changes the state, so $q(\mathbf c, \mathbf c) = 0$. The file also defines the weight of (3.18),
--   $$\prod_{l=1}^n \frac{\nu(c(l))\,p(c(l), z(l))\,d(c(l), z(l))}{\phi(l)},$$
--   the mean service requirement $a(c) = \sum_z p(c, z) w(c, z) d(c, z)$ of a class-$c$ customer, the arrival rate of work $a = \sum_c \nu(c) a(c)$, the terms $a^n / \prod_{l=1}^n \phi(l)$ of the series (3.15), and the numbers of customers of each class and of each refined class in a state.
--
--   This is the model of every result of §3.3 that is stated for gamma-mixture service.
--
--   **Formalization Note** Positions are list indices shifted by one: list index $i$ is position $l = i + 1$, and `γ l n`, `φ n` keep the book's $1$-based indexing. The parameters sit in a structure, and the standing assumptions are the separate predicate `IsValid`. Records whose refined class arrives at rate zero are excluded from the state space: such states cannot be reached and the book's distribution vanishes on them. The finiteness of $\sum_c \nu(c)$ is the book's standing assumption (§1.1) that the process leaves every state at a finite rate. `meanReq` and `load` are `tsum`s; theorems that use them assume the series converge.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 72–76 (PDF pp. 75–79), §3.3: definition of a symmetric queue (i)–(iv), p. 72; Markov description, pp. 74 and 76

import Mathlib

namespace KellyReversibility.Symmetric

/-- The data of a symmetric queue (Kelly 1979, §3.3, pp. 72–76) whose customers of class `c`
arrive in a Poisson stream of rate `ν c`, are given the refined class `(c, z)` with probability
`p c z`, and then require `w c z` independent exponential stages of service, each of mean
`d c z`.  The queue supplies total service effort at rate `φ n` when it holds `n` customers, and
directs the proportion `γ l n` of it to the customer in position `l` (`1 ≤ l ≤ n`).  An arriving
customer moves into position `l` with probability `γ l (n + 1)`, the same function `γ`: this is
the symmetry condition `γ ≡ δ` of p. 73.  Positions are numbered from `1`, as in the book. -/
structure SymmetricQueue (C Z : Type*) where
  /-- arrival rate `ν(c)` of class-`c` customers -/
  ν : C → ℝ
  /-- probability `p(c, z)` that a class-`c` arrival gets the refined class `(c, z)` -/
  p : C → Z → ℝ
  /-- number of exponential stages `w(c, z)` of a class-`(c, z)` customer -/
  w : C → Z → ℕ
  /-- mean `d(c, z)` of each stage -/
  d : C → Z → ℝ
  /-- total service effort `φ(n)` when `n` customers are present -/
  φ : ℕ → ℝ
  /-- `γ l n`: proportion of effort to position `l` when `n` are present; also the probability
  that an arrival finding `n - 1` customers moves into position `l` -/
  γ : ℕ → ℕ → ℝ

namespace SymmetricQueue

variable {C Z : Type*}

/-- The standing assumptions on the data (pp. 72–76): rates and probabilities are nonnegative,
`∑_z p(c, z) = 1`, the total arrival rate `∑_c ν(c)` is finite (so that the process leaves each
state at a finite rate, §1.1), every refined class has at least one stage of positive mean,
`φ(n) > 0` for `n > 0`, and `∑_{l=1}^n γ(l, n) = 1` for `n ≥ 1`. -/
structure IsValid (Q : SymmetricQueue C Z) : Prop where
  ν_nonneg : ∀ c, 0 ≤ Q.ν c
  ν_summable : Summable Q.ν
  p_nonneg : ∀ c z, 0 ≤ Q.p c z
  p_hasSum : ∀ c, HasSum (Q.p c) 1
  w_pos : ∀ c z, 1 ≤ Q.w c z
  d_pos : ∀ c z, 0 < Q.d c z
  φ_pos : ∀ n, 0 < n → 0 < Q.φ n
  γ_nonneg : ∀ l n, 0 ≤ Q.γ l n
  γ_sum : ∀ n, 0 < n → ∑ l ∈ Finset.Icc 1 n, Q.γ l n = 1

end SymmetricQueue

/-- The record `c(l) = (c(l), z(l), u(l))` of the customer in a position: class, refined class,
and the stage `u(l)` of service in progress. -/
structure Customer (C Z : Type*) where
  cls : C
  ref : Z
  stage : ℕ

namespace SymmetricQueue

variable {C Z : Type*} (Q : SymmetricQueue C Z)

/-- A customer record that can occur: its refined class arrives at positive rate
`ν(c) p(c, z) > 0`, and its stage satisfies `1 ≤ u ≤ w(c, z)`. -/
def ValidCustomer (e : Customer C Z) : Prop :=
  0 < Q.ν e.cls * Q.p e.cls e.ref ∧ 1 ≤ e.stage ∧ e.stage ≤ Q.w e.cls e.ref

/-- The state space of the Markov process `c = (c(1), …, c(n))`: finite lists of valid
customer records, list index `i` holding the customer in position `l = i + 1`. -/
def State : Type _ := {x : List (Customer C Z) // ∀ e ∈ x, Q.ValidCustomer e}

open Classical in
/-- Arrival transitions.  A class-`(c, z)` customer arrives at rate `ν(c) p(c, z)` and moves
into position `l = i + 1` (`0 ≤ i ≤ n`) with probability `γ(i + 1, n + 1)`, starting at stage
`1`; customers in positions `l, …, n` move up by one.  `arrivalRate x y` is the total rate of
the arrival events that turn `x` into `y`. -/
noncomputable def arrivalRate (x y : List (Customer C Z)) : ℝ :=
  ∑ i ∈ Finset.range (x.length + 1),
    match y[i]? with
    | some e =>
        if e.stage = 1 ∧ x.insertIdx i e = y then
          Q.ν e.cls * Q.p e.cls e.ref * Q.γ (i + 1) (x.length + 1)
        else 0
    | none => 0

open Classical in
/-- Service transitions.  The customer in position `l = i + 1` of a state with `n` customers
receives effort `φ(n) γ(l, n)`, so completes its current stage at rate `φ(n) γ(l, n) / d(c, z)`.
If the stage was not its last (`u < w(c, z)`) its stage becomes `u + 1`; if it was the last
(`u = w(c, z)`) the customer leaves and positions `l + 1, …, n` move down by one.
`serviceRate x y` is the total rate of the service events that turn `x` into `y`. -/
noncomputable def serviceRate (x y : List (Customer C Z)) : ℝ :=
  ∑ i ∈ Finset.range x.length,
    match x[i]? with
    | some e =>
        if (e.stage < Q.w e.cls e.ref ∧
              x.set i { cls := e.cls, ref := e.ref, stage := e.stage + 1 } = y) ∨
            (e.stage = Q.w e.cls e.ref ∧ x.eraseIdx i = y) then
          Q.φ x.length * Q.γ (i + 1) x.length / Q.d e.cls e.ref
        else 0
    | none => 0

/-- The transition rates `q(c, c')` of the Markov process `c` on its state space.  Every
transition changes the state, so `q(c, c) = 0`. -/
noncomputable def rate (x y : Q.State) : ℝ :=
  Q.arrivalRate x.1 y.1 + Q.serviceRate x.1 y.1

/-- The unnormalized weight of (3.18):
`∏_{l=1}^n ν(c(l)) p(c(l), z(l)) d(c(l), z(l)) / φ(l)`. -/
noncomputable def eqWeight (x : List (Customer C Z)) : ℝ :=
  ∏ i : Fin x.length,
    Q.ν (x.get i).cls * Q.p (x.get i).cls (x.get i).ref * Q.d (x.get i).cls (x.get i).ref /
      Q.φ ((i : ℕ) + 1)

/-- The mean service requirement of a class-`c` customer,
`a(c) = ∑_z p(c, z) w(c, z) d(c, z)` (p. 76). -/
noncomputable def meanReq (c : C) : ℝ :=
  ∑' z, Q.p c z * (Q.w c z : ℝ) * Q.d c z

/-- The average amount of service requirement arriving per unit time,
`a = ∑_c ν(c) a(c)` (p. 76). -/
noncomputable def load : ℝ :=
  ∑' c, Q.ν c * Q.meanReq c

/-- The `n`-th term `a^n / ∏_{l=1}^n φ(l)` of the series (3.15) for `b⁻¹`. -/
noncomputable def normTerm (a : ℝ) (n : ℕ) : ℝ :=
  a ^ n / ∏ l ∈ Finset.Icc 1 n, Q.φ l

end SymmetricQueue

open Classical in
/-- The number of customers of class `c` in a list of customer records. -/
noncomputable def classCount {C Z : Type*} (x : List (Customer C Z)) (c : C) : ℕ :=
  x.countP (fun e => decide (e.cls = c))

open Classical in
/-- The number of customers of refined class `(c, z)` in a list of customer records. -/
noncomputable def refinedCount {C Z : Type*} (x : List (Customer C Z)) (k : C × Z) : ℕ :=
  x.countP (fun e => decide (e.cls = k.1 ∧ e.ref = k.2))

end KellyReversibility.Symmetric


