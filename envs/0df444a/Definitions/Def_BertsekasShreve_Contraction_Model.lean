-- Prove2me | Definitions.Def_BertsekasShreve_Contraction_Model
-- name    : BertsekasShreve_Contraction_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:49:14.790891+00:00
-- url     : https://prove2.me/theorems/1bf303c1-a993-45f6-aba3-16c2fc9f8fc4
-- title:
--   The abstract monotone DP model of Sections 2.1–2.2: $T_\mu$, $T$, $J_\pi$, $J^*$, $J^*_N$, and the space $B$
-- statement:
--   This file fixes the abstract sequential optimization model of Part I of Bertsekas and Shreve and the cost functions built from it.
--
--   **The model.** A model consists of
--
--   1. a **state space** $S$ and a **control space** $C$ (arbitrary sets);
--   2. for each $x\in S$ a nonempty **control constraint set** $U(x)\subseteq C$;
--   3. a mapping $H: S\times C\times F\to R^*$, where $R^*=[-\infty,\infty]$ and $F$ is the set of all functions $J:S\to R^*$, ordered pointwise;
--   4. a function $J_0\in F$ with $J_0(x)>-\infty$ for every $x\in S$.
--
--   The **monotonicity assumption**, in force throughout Part I, is part of the model: for every $x\in S$, $u\in U(x)$ and $J,J'\in F$,
--
--   $$J\le J'\ \Longrightarrow\ H(x,u,J)\le H(x,u,J').$$
--
--   **Policies.** $M$ is the set of functions $\mu:S\to C$ with $\mu(x)\in U(x)$ for all $x$, and $\Pi$ is the set of sequences $\pi=(\mu_0,\mu_1,\dots)$ with every $\mu_k\in M$. The policy $(\mu,\mu,\dots)$ is called **stationary**.
--
--   **Operators.** For $\mu\in M$ and $J\in F$,
--
--   $$T_\mu(J)(x)=H\bigl(x,\mu(x),J\bigr),\qquad T(J)(x)=\inf_{u\in U(x)}H(x,u,J)\qquad(x\in S).$$
--
--   $T^k$ is the $k$-fold composition of $T$, with $T^0(J)=J$. For $\pi\in\Pi$, $(T_{\mu_0}T_{\mu_1}\cdots T_{\mu_{N-1}})(J)$ is the composition in which $T_{\mu_{N-1}}$ is applied to $J$ first and $T_{\mu_0}$ last.
--
--   **Cost functions.**
--
--   $$J_\pi(x)=\lim_{N\to\infty}(T_{\mu_0}\cdots T_{\mu_{N-1}})(J_0)(x),\qquad J^*(x)=\inf_{\pi\in\Pi}J_\pi(x),\qquad J^*_N(x)=\inf_{\pi\in\Pi}(T_{\mu_0}\cdots T_{\mu_{N-1}})(J_0)(x),$$
--
--   and $J_\mu=J_\pi$ for the stationary policy $\pi=(\mu,\mu,\dots)$. A policy is **optimal** if $J_\pi=J^*$, and optimal at $x$ if $J_\pi(x)=J^*(x)$.
--
--   **The space $B$.** $B$ is the Banach space of all bounded real-valued functions on $S$ with the supremum norm $\|J\|=\sup_{x\in S}|J(x)|$. An element of $B$ is regarded as an element of $F$. For $J,J'\in F$ and a real $c$, "$\|J-J'\|\le c$" means that $J(x)$ and $J'(x)$ are real for every $x$ and $|J(x)-J'(x)|\le c$ for every $x$.
--
--   This is the common vocabulary of every statement in the mission.
--
--   **Formalization Note** $F$ is `S → EReal`; $B$ is Mathlib's `lp (fun _ : S => ℝ) ⊤`, whose norm is the supremum norm, and `toF` embeds it in $F$. The limit defining $J_\pi$ is `limUnder atTop`, the true limit whenever it exists (under Assumption C it exists and is real). The book adopts $\infty-\infty=\infty$, while Mathlib's `EReal` has $\bot+\top=\bot$; no statement of this mission adds infinities of opposite sign. The predicate `SupDistLe J J' c` is "$\|J-J'\|\le c$" read with the book's arithmetic, under which an infinite value at any point makes the difference infinite there.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, pp. 26–29, Section 2.1 items (1)–(7), Eqs. (1)–(3) of Chapter 2 and the Monotonicity Assumption; Section 2.2, Eqs. (4)–(8) of Chapter 2

import Mathlib

namespace BertsekasShreve.Contraction

open Filter Topology

/-- The abstract monotone dynamic programming model of Bertsekas & Shreve, Sections 2.1–2.2
(pp. 26–28).

* `S`, `C` are the state and control spaces (item (1), p. 26).
* `U x ⊆ C` is the nonempty control constraint set at `x` (item (2)).
* `H : S → C → (S → EReal) → EReal` is the basic mapping `H : SCF → R*` (p. 27), where
  `F = S → EReal` is the set of extended-real-valued functions on `S` (item (4)).
* `mono` is the Monotonicity Assumption (3), p. 27, in effect throughout Part I.
* `J0` is the given function `J₀ ∈ F` with `J₀(x) > −∞` for all `x` (eq. (4), p. 28). -/
structure Model (S C : Type*) where
  U : S → Set C
  U_nonempty : ∀ x, (U x).Nonempty
  H : S → C → (S → EReal) → EReal
  mono : ∀ x, ∀ u ∈ U x, ∀ J J' : S → EReal, J ≤ J' → H x u J ≤ H x u J'
  J0 : S → EReal
  J0_ne_bot : ∀ x, J0 x ≠ ⊥

namespace Model

variable {S C : Type*} (P : Model S C)

/-- The set `M` of functions `μ : S → C` with `μ(x) ∈ U(x)` for all `x` (item (3), p. 26). -/
def Selector : Type _ := {μ : S → C // ∀ x, μ x ∈ P.U x}

/-- The set `Π` of policies `π = (μ₀, μ₁, …)` with every `μ_k ∈ M` (item (3), p. 26). -/
def Policy : Type _ := ℕ → P.Selector

/-- The stationary policy `(μ, μ, …)`. -/
def stationary (μ : P.Selector) : P.Policy := fun _ => μ

/-- `T_μ(J)(x) = H[x, μ(x), J]`, eq. (1) of Chapter 2. -/
def Tmu (μ : P.Selector) (J : S → EReal) : S → EReal := fun x => P.H x (μ.1 x) J

/-- `T(J)(x) = inf_{u ∈ U(x)} H(x, u, J)`, eq. (2) of Chapter 2. `T^k` is `P.T^[k]`, `T^0 = id`. -/
noncomputable def T (J : S → EReal) : S → EReal := fun x => ⨅ u ∈ P.U x, P.H x u J

/-- The composition `(T_{μ₀} T_{μ₁} ⋯ T_{μ_{N−1}})(J)`: `T_{μ_{N−1}}` is applied to `J` first and
`T_{μ₀}` last; `comp π 0 J = J`. -/
def comp (π : P.Policy) : ℕ → (S → EReal) → (S → EReal)
  | 0, J => J
  | N + 1, J => comp π N (P.Tmu (π N) J)

/-- The cost function of a policy, eq. (6) of Chapter 2:
`J_π(x) = lim_{N → ∞} (T_{μ₀} ⋯ T_{μ_{N−1}})(J₀)(x)`, taken as `limUnder`; it is the true limit
whenever the limit exists (under Assumption C it exists and is real). -/
noncomputable def Jpi (π : P.Policy) : S → EReal :=
  fun x => limUnder atTop (fun N => P.comp π N P.J0 x)

/-- `J_μ = J_π` for the stationary policy `π = (μ, μ, …)` (p. 29). -/
noncomputable def Jmu (μ : P.Selector) : S → EReal := P.Jpi (P.stationary μ)

/-- The optimal cost function, eq. (8) of Chapter 2: `J*(x) = inf_{π ∈ Π} J_π(x)`. -/
noncomputable def Jstar : S → EReal := fun x => ⨅ π : P.Policy, P.Jpi π x

/-- The `N`-stage optimal cost function, eq. (7) of Chapter 2:
`J*_N(x) = inf_{π ∈ Π} (T_{μ₀} ⋯ T_{μ_{N−1}})(J₀)(x)`. -/
noncomputable def JNstar (N : ℕ) : S → EReal := fun x => ⨅ π : P.Policy, P.comp π N P.J0 x

end Model

/-- The Banach space `B` of bounded real-valued functions on `S` with the supremum norm
`‖J‖ = sup_{x ∈ S} |J(x)|` (item (4), p. 26), as Mathlib's `ℓ^∞(S, ℝ)`. -/
abbrev BFun (S : Type*) := lp (fun _ : S => ℝ) ⊤

/-- A bounded real function viewed as an element of `F = S → EReal`. -/
def toF {S : Type*} (J : BFun S) : S → EReal := fun x => ((J x : ℝ) : EReal)

/-- `‖J − J'‖ ≤ c` for extended-real-valued functions, read with the book's arithmetic
(`∞ − ∞ = −∞ + ∞ = ∞`, p. 26): `J(x)` and `J'(x)` are real at every `x` and
`|J(x) − J'(x)| ≤ c`. Under the book's conventions any infinite value makes the difference
`±∞` at that point, so the sup-norm bound forces finiteness. -/
def SupDistLe {S : Type*} (J J' : S → EReal) (c : ℝ) : Prop :=
  ∀ x, ∃ a b : ℝ, J x = (a : EReal) ∧ J' x = (b : EReal) ∧ |a - b| ≤ c

end BertsekasShreve.Contraction


