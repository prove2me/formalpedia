-- Prove2me | Definitions.Def_JacksonJobshop_Equilibrium_System
-- name    : JacksonJobshop_Equilibrium_System
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:12:45.322038+00:00
-- url     : https://prove2.me/theorems/e0e62af3-6d7d-4110-a56b-ac6893021d0f
-- title:
--   Jobshop-like queueing system (N, L, M, R): Assumptions (2.1)–(2.4), balance equations (3.1), equilibrium, notations (4.1)–(4.4), (4.6), (6.1)–(6.2)
-- statement:
--   This file sets up J. R. Jackson's **jobshop-like queueing system** $(N, L, M, R)$ and the objects in which its equilibrium theorem is stated.
--
--   **The system.** There are $N \ge 1$ service centers, Center $1, \dots, N$. A **state vector** is $\bar k = (k_1, \dots, k_N)$ with non-negative integer components, $k_n$ being the queue length at Center $n$, and $S(\bar k) = k_1 + \dots + k_N$ is the total number of customers. The system is given by
--
--   1. arrival rates $L = \{\lambda(K) \mid K = 0, 1, 2, \dots\}$: in state $\bar k$ a customer arrives in a short time $h$ with probability $h\lambda(S(\bar k)) + o(h)$;
--   2. service rates $M = \{\mu(n, k) \mid n \in [1, N],\ k = 0, 1, \dots\}$: with $k_n$ customers at Center $n$, a service there completes with probability $h\mu(n, k_n) + o(h)$;
--   3. routing probabilities $R = \{r(m, n) \mid m \in [0, N],\ n \in [1, N+1]\}$: $r(0, n)$ is the probability that Center $n$ is first on a customer's routing, $r(m, n)$ that Center $n$ follows Center $m$, $r(m, N+1)$ that the routing ends after Center $m$, and $r(0, N+1)$ that the routing is empty;
--   4. numbers $e(1), \dots, e(N)$ solving the traffic equations (2.5).
--
--   The standing assumptions are:
--
--   - **(2.1)** either all $\lambda(K) > 0$, or for some $K_0 \ge 0$, $\lambda(K) > 0$ for $K \le K_0$ and $\lambda(K) = 0$ for $K > K_0$;
--   - **(2.2)** $\mu(n, 0) = 0$ and $\mu(n, k) > 0$ for $k \ge 1$;
--   - **(2.3)** for each $m \in [0, N]$, $\{r(m, n) \mid n \in [1, N+1]\}$ is a probability distribution;
--   - **(2.4)** the system
--   $$e(n) = r(0, n) + \sum_{m=1}^N e(m)\, r(m, n), \qquad n \in [1, N], \tag{2.5}$$
--   has a unique solution $\{e(n)\}$, and all $e(n) \ge 0$.
--
--   **Balance equations.** For a function $q$ on state vectors, the stationary form of the balance equations (3.1) at $\bar k$ is
--   $$0 = -\Big[\lambda(S(\bar k))\sum_{n=1}^N r(0, n) + \sum_{n} \mu(n, k_n)\big(1 - r(n, n)\big)\Big] q(\bar k) + \sum_n \lambda(S(\bar k) - 1)\, r(0, n)\, q(\bar h(n)) + \sum_n \mu(n, k_n + 1)\, r(n, N+1)\, q(\bar l(n)) + \sum_m \sum_n \mu(n, k_n + 1)\, r(n, m)\, q(\bar j(m, n)),$$
--   where all sums run over $[1, N]$, pairs $m = n$ are omitted from the double sum, and terms are omitted whose state argument would have a negative component; $\bar h(n)$ is $\bar k$ with $k_n$ replaced by $k_n - 1$, $\bar l(n)$ is $\bar k$ with $k_n$ replaced by $k_n + 1$, and $\bar j(m, n)$ is $\bar k$ with $k_m$ replaced by $k_m - 1$ and $k_n$ by $k_n + 1$.
--
--   The paper prints $\lambda(S(\bar k))$ as the arrival-outflow coefficient in (3.1); this is inconsistent with its own transition probabilities on p. 134 whenever $r(0, N+1) > 0$, and we use $\lambda(S(\bar k)) \sum_n r(0, n)$, which is the equation those transition probabilities give. (An arrival with an empty routing leaves the state unchanged.)
--
--   An **equilibrium state probability distribution** is a probability distribution $\{q(\bar k)\}$ over state vectors ($q \ge 0$, $\sum_{\bar k} q(\bar k) = 1$) such that $P(\bar k, t) \equiv q(\bar k)$ is a constant solution of (3.1), i.e. the stationary equation above holds at every $\bar k$.
--
--   **Notations of §4** (empty products equal $1$):
--   $$W(K) = \prod_{i=0}^{K-1} \lambda(i), \qquad w(\bar k) = \prod_{n=1}^N \prod_{i=1}^{k_n} \frac{e(n)}{\mu(n, i)}, \qquad T(K) = \sum_{S(\bar k) = K} w(\bar k),$$
--   $$\pi = \Big\{\sum_{K=0}^\infty W(K)\, T(K)\Big\}^{-1} \text{ if the sum converges}, \qquad \pi = 0 \text{ otherwise},$$
--   and the candidate distribution (4.6) is $p(\bar k) = \pi\, w(\bar k)\, W(S(\bar k))$.
--
--   **Notations of §6** for the constant-arrival-rate case with no service deletions ($k_n^* = +\infty$):
--   $$w_n(k) = \prod_{i=1}^k \frac{\lambda(0)\, e(n)}{\mu(n, i)}, \qquad p_n(k) = \frac{w_n(k)}{\sum_{i=0}^\infty w_n(i)} \text{ if the sum converges}, \quad p_n(k) = 0 \text{ otherwise}.$$
--
--   These objects carry every result of the mission: Theorem (4.5) states that $p$ is the equilibrium distribution when $\pi > 0$.
--
--   **Formalization Note** Centers are `Fin N` (the paper's Center $n$ is index $n-1$) and $N > 0$ is a field of the structure. The routing is one function `r : Option (Fin N) → Option (Fin N) → ℝ`: in the first argument `none` is the paper's index $0$, in the second argument `none` is the paper's index $N+1$, so $\sum_{n}$ over `Option (Fin N)` is exactly the sum over $[1, N+1]$ in (2.3). The numbers $e(n)$ are a field of the structure together with the three clauses of (2.4) (they solve (2.5), every solution of (2.5) equals them, they are non-negative); they are not computed by a formula. Guarded terms of (3.1) are written with `if 0 < k n` (resp. `m ≠ n ∧ 0 < k m`), so natural-number subtraction is never evaluated at a zero component. A probability distribution is `HasSum q 1` with `q ≥ 0`. The "= 0 otherwise" clauses of $\pi$ and $p_n$ are written as explicit `if Summable … then … else 0`. $T(K)$ sums over `Finset.Nat.antidiagonalTuple N K`, the finite set of state vectors with $S(\bar k) = K$.
-- source:
--   Jackson, Jobshop-Like Queueing Systems, Management Science 10(1) (1963), pp. 133-136 and 140: §2 states and Assumptions (2.1)-(2.4) with (2.5); §3 transition probabilities (p. 134) and equations (3.1) (p. 135); §4 definition of equilibrium (p. 135) and notations (4.1)-(4.4), (4.6) (p. 136); §6 notations (6.1)-(6.2) (p. 140)

import Mathlib

namespace JacksonJobshop.Equilibrium

/-- Jackson's jobshop-like queueing system `(N, L, M, R)` (Management Science 10(1), 1963,
§§2–3, pp. 133–135), with its standing Assumptions (2.1)–(2.4).

* Centers are `Fin N`; the paper's Center `n` is `⟨n - 1, _⟩`.
* `lam K` is `λ(K)`, the arrival rate when `K` customers are present.
* `mu n k` is `μ(n, k)`, the service-completion rate at Center `n` holding `k` customers.
* `r : Option (Fin N) → Option (Fin N) → ℝ` encodes `R = {r(m, n) | m ∈ [0, N], n ∈ [1, N + 1]}`:
  in the first argument `none` is the paper's index `0` (start of a routing); in the second
  argument `none` is the paper's index `N + 1` (end of a routing). So `r none (some n) = r(0, n)`,
  `r (some m) none = r(m, N + 1)`, `r none none = r(0, N + 1)`, `r (some m) (some n) = r(m, n)`.
* `e n` is the solution `e(n)` of the traffic equations (2.5), assumed unique and
  non-negative by (2.4). -/
structure JobshopSystem (N : ℕ) where
  /-- arrival rates `λ(K)`, `K ∈ [0, ∞)` -/
  lam : ℕ → ℝ
  /-- service rates `μ(n, k)`, `n ∈ [1, N]`, `k ∈ [0, ∞)` -/
  mu : Fin N → ℕ → ℝ
  /-- routing probabilities `r(m, n)`, `m ∈ [0, N]`, `n ∈ [1, N + 1]` -/
  r : Option (Fin N) → Option (Fin N) → ℝ
  /-- the solution `e(n)` of equations (2.5) -/
  e : Fin N → ℝ
  /-- `N` is a positive integer (p. 133). -/
  N_pos : 0 < N
  /-- Assumption (2.1): either all `λ(K) > 0`, or for some `K₀ ≥ 0`, `λ(K) > 0` for `K ≤ K₀`
  and `λ(K) = 0` for `K > K₀`. -/
  lam_assumption :
    (∀ K, 0 < lam K) ∨ ∃ K₀ : ℕ, (∀ K, K ≤ K₀ → 0 < lam K) ∧ ∀ K, K₀ < K → lam K = 0
  /-- Assumption (2.2), first part: each `μ(n, 0) = 0`. -/
  mu_zero : ∀ n, mu n 0 = 0
  /-- Assumption (2.2), second part: all other `μ(n, k)` are positive. -/
  mu_pos : ∀ n k, 0 < k → 0 < mu n k
  /-- Assumption (2.3), non-negativity: each `{r(m, n) | n ∈ [1, N + 1]}` has non-negative
  entries. -/
  r_nonneg : ∀ m n, 0 ≤ r m n
  /-- Assumption (2.3), normalisation: for each `m ∈ [0, N]`, `Σ_{n ∈ [1, N+1]} r(m, n) = 1`. -/
  r_sum : ∀ m, ∑ n, r m n = 1
  /-- Assumption (2.4): `e` solves (2.5), `e(n) = r(0, n) + Σ_{m=1}^N e(m) r(m, n)`. -/
  e_traffic : ∀ n, e n = r none (some n) + ∑ m, e m * r (some m) (some n)
  /-- Assumption (2.4): the solution of (2.5) is unique. -/
  e_unique : ∀ e' : Fin N → ℝ,
    (∀ n, e' n = r none (some n) + ∑ m, e' m * r (some m) (some n)) → e' = e
  /-- Assumption (2.4): the `e(n)` are all non-negative. -/
  e_nonneg : ∀ n, 0 ≤ e n

variable {N : ℕ}

/-- `S(k) = k₁ + ⋯ + k_N`, the total number of customers in state `k` (p. 133). -/
def S (k : Fin N → ℕ) : ℕ := ∑ n, k n

/-- The stationary form (`dP/dt = 0`) of the balance equation (3.1) (p. 135) at the state `k`,
for a function `q` on state vectors, **with the arrival-outflow coefficient
`λ(S(k)) Σ_{n=1}^N r(0, n)`** given by the transition probabilities on p. 134 (the paper prints
`λ(S(k))` there, which disagrees with those transition probabilities when `r(0, N+1) > 0`).

Terms whose shifted state would have a negative component are omitted (they are guarded by
`0 < k n`, resp. `0 < k m`), and the double sum runs over ordered pairs `m ≠ n`.
* `h(n) = k` except its `n`th component is `k n - 1`;
* `l(n) = k` except its `n`th component is `k n + 1`;
* `j(m, n) = k` except its `m`th component is `k m - 1` and its `n`th is `k n + 1`. -/
def Balance (sys : JobshopSystem N) (q : (Fin N → ℕ) → ℝ) (k : Fin N → ℕ) : Prop :=
  0 = -((sys.lam (S k) * ∑ n, sys.r none (some n)) +
          ∑ n, sys.mu n (k n) * (1 - sys.r (some n) (some n))) * q k
    + ∑ n, (if 0 < k n then
        sys.lam (S k - 1) * sys.r none (some n) * q (Function.update k n (k n - 1)) else 0)
    + ∑ n, sys.mu n (k n + 1) * sys.r (some n) none * q (Function.update k n (k n + 1))
    + ∑ m, ∑ n, (if m ≠ n ∧ 0 < k m then
        sys.mu n (k n + 1) * sys.r (some n) (some m) *
          q (Function.update (Function.update k m (k m - 1)) n (k n + 1)) else 0)

/-- An equilibrium state probability distribution (p. 135): a probability distribution
`{q(k)}` over state vectors such that `P(k, t) ≡ q(k)` is a constant solution of (3.1). -/
def IsEquilibrium (sys : JobshopSystem N) (q : (Fin N → ℕ) → ℝ) : Prop :=
  (∀ k, 0 ≤ q k) ∧ HasSum q 1 ∧ ∀ k, Balance sys q k

/-- (4.1) `W(K) = Π_{i=0}^{K-1} λ(i)` (empty product `1`). -/
def W (sys : JobshopSystem N) (K : ℕ) : ℝ := ∏ i ∈ Finset.range K, sys.lam i

/-- (4.2) `w(k) = Π_{n=1}^N Π_{i=1}^{k_n} [e(n)/μ(n, i)]` (empty products `1`). -/
noncomputable def w (sys : JobshopSystem N) (k : Fin N → ℕ) : ℝ :=
  ∏ n, ∏ i ∈ Finset.Icc 1 (k n), sys.e n / sys.mu n i

/-- (4.3) `T(K) = Σ_{S(k) = K} w(k)`, a finite sum over state vectors with total `K`. -/
noncomputable def T (sys : JobshopSystem N) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Nat.antidiagonalTuple N K, w sys k

open scoped Classical in
/-- (4.4) `π = {Σ_{K=0}^∞ W(K) T(K)}⁻¹` if the sum converges, `= 0` otherwise. -/
noncomputable def piConst (sys : JobshopSystem N) : ℝ :=
  if Summable (fun K => W sys K * T sys K) then (∑' K, W sys K * T sys K)⁻¹ else 0

/-- (4.6) `p(k) = π w(k) W(S(k))`. -/
noncomputable def productForm (sys : JobshopSystem N) (k : Fin N → ℕ) : ℝ :=
  piConst sys * w sys k * W sys (S k)

/-- (6.1) in the case `k_n* = +∞`: `w_n(k) = Π_{i=1}^k [λ(0) e(n)/μ(n, i)]`. -/
noncomputable def wn (sys : JobshopSystem N) (n : Fin N) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 k, sys.lam 0 * sys.e n / sys.mu n i

open scoped Classical in
/-- (6.2) `p_n(k) = w_n(k) / Σ_{i=0}^∞ w_n(i)` if the sum converges, `= 0` otherwise. -/
noncomputable def pn (sys : JobshopSystem N) (n : Fin N) (k : ℕ) : ℝ :=
  if Summable (fun i => wn sys n i) then wn sys n k / ∑' i, wn sys n i else 0

end JacksonJobshop.Equilibrium


