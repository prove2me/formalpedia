-- Prove2me | Definitions.Def_BertsekasShreve_FiniteHorizon_Model
-- name    : BertsekasShreve_FiniteHorizon_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:51:08.351033+00:00
-- url     : https://prove2.me/theorems/095b613a-c5f1-4c5c-9e7f-7b1e24bcacec
-- title:
--   The abstract monotone model of Section 2.1: constraint sets U(x), the mapping H, T_μ, T, policies
-- statement:
--   This file fixes the abstract model of Part I of Bertsekas and Shreve (Section 2.1).
--
--   **Data.** A model consists of
--
--   1. two sets $S$ (the **state space**) and $C$ (the **control space**);
--   2. for each $x\in S$ a nonempty **control constraint set** $U(x)\subseteq C$;
--   3. a mapping $H : S\times C\times F\to R^*$, where $R^*=[-\infty,\infty]$ and $F$ is the set of all functions $J:S\to R^*$, ordered pointwise ($J\le J'$ iff $J(x)\le J'(x)$ for all $x$);
--   4. the **Monotonicity Assumption**: for every $x\in S$, $u\in U(x)$ and $J,J'\in F$,
--   $$J\le J'\ \Longrightarrow\ H(x,u,J)\le H(x,u,J').$$
--
--   **Policies.** $M$ is the set of functions $\mu:S\to C$ with $\mu(x)\in U(x)$ for every $x$, and $\Pi$ is the set of sequences $\pi=(\mu_0,\mu_1,\dots)$ with every $\mu_k\in M$. A policy $(\mu,\mu,\dots)$ is **stationary**; the tail $(\mu_i,\mu_{i+1},\dots)$ of $\pi$ is again a policy.
--
--   **Operators.** For $\mu\in M$ and $J\in F$,
--   $$T_\mu(J)(x)=H\bigl[x,\mu(x),J\bigr],\qquad T(J)(x)=\inf_{u\in U(x)}H(x,u,J)\qquad(x\in S).$$
--   $T^k$ is the $k$-fold composition of $T$, with $T^0(J)=J$, and for $\pi=(\mu_0,\mu_1,\dots)$ the composition $(T_{\mu_0}T_{\mu_1}\cdots T_{\mu_{N-1}})(J)$ applies $T_{\mu_{N-1}}$ to $J$ first and $T_{\mu_0}$ last (it is $J$ when $N=0$).
--
--   Every statement of the mission is phrased in this model; the finite-horizon problem built on it is in the companion definition file.
--
--   **Formalization Note** $F$ is `S → EReal`. The infimum in $T$ is `⨅ u ∈ U x`, so $\inf\emptyset=+\infty$ as in the book; since $U(x)$ is nonempty this case does not occur. No nonemptiness of $S$ or $C$ is assumed (the book assumes none). The composition is defined by recursion, `comp π (N+1) J = comp π N (T_{μ_N} J)`.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, pp. 26–27, Section 2.1, items (1)–(5), eqs. (1)–(3) of Chapter 2 (Monotonicity Assumption)

import Mathlib

namespace BertsekasShreve.FiniteHorizon

/-- The abstract monotone model of Bertsekas & Shreve, *Stochastic Optimal Control: The
Discrete-Time Case*, Section 2.1, items (1)–(4) and the Monotonicity Assumption (pp. 26–27).

* `S`, `C` are the state space and the control space (item (1)); no nonemptiness is assumed.
* `U x ⊆ C` is the nonempty control constraint set at `x` (item (2)).
* `F = S → EReal` is the set of extended-real-valued functions on `S` (item (4)), ordered
  pointwise (item (5)).
* `H : S × C × F → R*` is the basic mapping (p. 27), curried.
* `mono` is the Monotonicity Assumption, eq. (3) of Chapter 2: for every `x ∈ S`, `u ∈ U(x)`,
  `J ≤ J'` implies `H(x, u, J) ≤ H(x, u, J')`. -/
structure Model (S C : Type*) where
  U : S → Set C
  U_nonempty : ∀ x, (U x).Nonempty
  H : S → C → (S → EReal) → EReal
  mono : ∀ x, ∀ u ∈ U x, ∀ J J' : S → EReal, J ≤ J' → H x u J ≤ H x u J'

namespace Model

variable {S C : Type*} (m : Model S C)

/-- The set `M` of all functions `μ : S → C` with `μ(x) ∈ U(x)` for all `x ∈ S` (item (3)). -/
def Selector : Type _ := {μ : S → C // ∀ x, μ x ∈ m.U x}

/-- The set `Π` of policies: sequences `π = (μ₀, μ₁, …)` with every `μ_k ∈ M` (item (3)). -/
def Policy : Type _ := ℕ → m.Selector

/-- The stationary policy `(μ, μ, …)` (item (3)). -/
def stationary (μ : m.Selector) : m.Policy := fun _ => μ

/-- The tail policy `(μ_i, μ_{i+1}, …)` of `π = (μ₀, μ₁, …)`. -/
def Policy.shift {m : Model S C} (π : m.Policy) (i : ℕ) : m.Policy := fun k => π (i + k)

/-- `T_μ(J)(x) = H[x, μ(x), J]`, eq. (1) of Chapter 2. -/
def Tmu (μ : m.Selector) (J : S → EReal) : S → EReal := fun x => m.H x (μ.1 x) J

/-- `T(J)(x) = inf_{u ∈ U(x)} H(x, u, J)`, eq. (2) of Chapter 2. Its `k`-fold composition
`T^k` is `m.T^[k]`, with `T^0(J) = J`. -/
noncomputable def T (J : S → EReal) : S → EReal := fun x => ⨅ u ∈ m.U x, m.H x u J

/-- The composition `(T_{μ₀} T_{μ₁} ⋯ T_{μ_{N−1}})(J)` for `π = (μ₀, μ₁, …)`: the mapping
`T_{μ_{N−1}}` is applied to `J` first and `T_{μ₀}` last; for `N = 0` it is `J`. -/
def comp (π : m.Policy) : ℕ → (S → EReal) → (S → EReal)
  | 0, J => J
  | N + 1, J => comp π N (m.Tmu (π N) J)

end Model

end BertsekasShreve.FiniteHorizon


