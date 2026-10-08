-- Prove2me | Definitions.Def_BertsekasShreve_Generalized_Model
-- name    : BertsekasShreve_Generalized_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:19:26.952559+00:00
-- url     : https://prove2.me/theorems/312ec5dd-e768-4632-968e-ef335276b764
-- title:
--   The generalized abstract DP model of Section 6.1: restricted classes $F^*\subset\tilde F\subset F$ and $\tilde M\subset M$
-- statement:
--   This file fixes the generalized abstract dynamic programming model of Bertsekas and Shreve, Chapter 6, Section 6.1, built on the notation of Section 2.1.
--
--   **The model.** A model consists of
--
--   1. a **state space** $S$ and a **control space** $C$;
--   2. for each $x\in S$ a nonempty **control constraint set** $U(x)\subseteq C$;
--   3. two sets of extended-real-valued functions $F^*\subset\tilde F\subset F$, where $F$ is the set of all functions $J:S\to R^*=[-\infty,\infty]$, ordered pointwise;
--   4. a set $\tilde M$ of functions $\mu:S\to C$ with $\mu(x)\in U(x)$ for all $x\in S$ (a subset of the set $M$ of all such selectors);
--   5. a mapping $H:S\times C\times\tilde F\to R^*$ satisfying the **monotonicity assumption**: for all $x\in S$, $u\in U(x)$ and $J,J'\in\tilde F$,
--   $$J\le J'\ \Longrightarrow\ H(x,u,J)\le H(x,u,J');$$
--   6. a function $J_0\in F^*$ with $J_0(x)>-\infty$ for every $x\in S$.
--
--   The sets $F^*$, $\tilde F$ and $\tilde M$ are arbitrary; the conditions A.1–A.5 of the chapter, which constrain them, are stated in a separate definition. The special case $F^*=\tilde F=F$, $\tilde M=M$ is the model of Chapters 2–5.
--
--   **Policies and operators.** $\tilde\Pi$ is the set of policies $\pi=(\mu_0,\mu_1,\dots)$ with every $\mu_k\in\tilde M$; $(\mu,\mu,\dots)$ is a **stationary** policy. For $\mu\in\tilde M$ and $J\in\tilde F$,
--   $$T_\mu(J)(x)=H[x,\mu(x),J],\qquad T(J)(x)=\inf_{u\in U(x)}H(x,u,J)\qquad(x\in S),$$
--   $T^k$ is the $k$-fold composition of $T$ with $T^0(J)=J$, and $(T_{\mu_0}\cdots T_{\mu_{N-1}})(J)$ applies $T_{\mu_{N-1}}$ first.
--
--   **Cost functions.** For $\pi\in\tilde\Pi$ and a positive integer $N$,
--   $$J_{N,\pi}=(T_{\mu_0}\cdots T_{\mu_{N-1}})(J_0),\qquad J_\pi(x)=\lim_{N\to\infty}(T_{\mu_0}\cdots T_{\mu_{N-1}})(J_0)(x),$$
--   $J_\mu=J_{(\mu,\mu,\dots)}$, and the optimal costs are infima over $\tilde\Pi$ only:
--   $$J^*_N(x)=\inf_{\pi\in\tilde\Pi}J_{N,\pi}(x),\qquad J^*(x)=\inf_{\pi\in\tilde\Pi}J_\pi(x).$$
--
--   **The space $B$.** $B$ is the Banach space of bounded real functions on $S$ with $\|J\|=\sup_{x\in S}|J(x)|$; an element of $B$ is regarded as an element of $F$. For a set $\bar B\subseteq B$ and $G\subseteq F$, "$J\in\bar B\cap G$" means that $J$ is a bounded real function in $\bar B$ that belongs to $G$. For $G,G'\in F$ the bound "$\|G-G'\|\le c$" is read with the book's arithmetic, in which $\infty-\infty=\infty$: both functions are real at every point and $|G(x)-G'(x)|\le c$ for all $x$.
--
--   This is the common substrate of every statement in the mission.
--
--   **Formalization Note** $F$ is `S → EReal`. Lean's $H$ is a total function on `S → C → (S → EReal) → EReal`, but monotonicity is required only for $u\in U(x)$ and $J,J'\in\tilde F$, and every statement of the mission evaluates $H$ only at functions in $\tilde F$, so values outside $\tilde F$ play no role. $J_\pi$ is `limUnder atTop`, the true limit whenever it exists; Assumption C̃ guarantees existence where it is used. $B$ is Mathlib's $\ell^\infty(S,\mathbb R)$. No sum of values of opposite infinite sign occurs in any statement of the mission, so Mathlib's `EReal` addition agrees with the book's convention $\infty-\infty=\infty$ wherever it is used.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, pp. 26–29, Section 2.1 items (1)–(6), eqs. (1)–(2), (5)–(8) of Chapter 2; pp. 92–93, Section 6.1, eqs. (1)–(2) of Chapter 6

import Mathlib
import Definitions.Def_BertsekasShreve_Contraction_Model

namespace BertsekasShreve.Generalized

open Filter Topology

/-- The generalized abstract dynamic programming model of Bertsekas & Shreve, Section 6.1
(pp. 92–93), built on the notation of Section 2.1 (pp. 26–27).

* `S`, `C` are the state and control spaces (item (1), p. 26).
* `U x ⊆ C` is the nonempty control constraint set at `x` (item (2), p. 26).
* `Fstar` and `Ftil` are the two given subsets `F* ⊂ F̃ ⊂ F` of the set `F = S → EReal` of
  extended-real-valued functions on `S` (p. 92). They are arbitrary sets; only the conditions
  A.1–A.5 (stated separately) constrain them.
* `Mtil` is the given subset `M̃` of the set `M` of functions `μ : S → C` with `μ(x) ∈ U(x)` for
  all `x` (p. 92).
* `H : S → C → (S → EReal) → EReal` is the mapping `H : S C F̃ → R*` of p. 92. Lean's `H` is total,
  but the book defines it on `S × C × F̃` only: `mono`, the monotonicity assumption of p. 92, is
  required only for `u ∈ U(x)` and `J, J' ∈ F̃`, and every statement of the mission evaluates `H`
  only at functions that lie in `F̃`.
* `J0` is the given function `J₀ ∈ F*` with `J₀(x) > −∞` for all `x` (p. 92). -/
structure Model (S C : Type*) where
  U : S → Set C
  U_nonempty : ∀ x, (U x).Nonempty
  Fstar : Set (S → EReal)
  Ftil : Set (S → EReal)
  Fstar_subset : Fstar ⊆ Ftil
  Mtil : Set (S → C)
  Mtil_subset : ∀ μ ∈ Mtil, ∀ x, μ x ∈ U x
  H : S → C → (S → EReal) → EReal
  mono : ∀ x, ∀ u ∈ U x, ∀ J ∈ Ftil, ∀ J' ∈ Ftil, J ≤ J' → H x u J ≤ H x u J'
  J0 : S → EReal
  J0_mem : J0 ∈ Fstar
  J0_ne_bot : ∀ x, J0 x ≠ ⊥

namespace Model

variable {S C : Type*} (P : Model S C)

/-- An element of `M̃`. -/
def Sel : Type _ := {μ : S → C // μ ∈ P.Mtil}

/-- The set `Π̃ = {(μ₀, μ₁, …) ∈ Π | μ_k ∈ M̃, k = 0, 1, …}` of policies built from `M̃` (p. 92). -/
def Policy : Type _ := ℕ → P.Sel

/-- The stationary policy `(μ, μ, …) ∈ Π̃`. -/
def stationary (μ : P.Sel) : P.Policy := fun _ => μ

/-- The tail `(μ_i, μ_{i+1}, …)` of a policy `π = (μ₀, μ₁, …)`. -/
def shift (π : P.Policy) (i : ℕ) : P.Policy := fun k => π (i + k)

/-- `T_μ(J)(x) = H[x, μ(x), J]` (p. 92). -/
def Tmu (μ : S → C) (J : S → EReal) : S → EReal := fun x => P.H x (μ x) J

/-- `T(J)(x) = inf_{u ∈ U(x)} H(x, u, J)` (p. 92). `T^k` is `P.T^[k]`, with `T^0 = id`. -/
noncomputable def T (J : S → EReal) : S → EReal := fun x => ⨅ u ∈ P.U x, P.H x u J

/-- The composition `(T_{μ₀} T_{μ₁} ⋯ T_{μ_{N−1}})(J)`: `T_{μ_{N−1}}` is applied to `J` first and
`T_{μ₀}` last; `comp π 0 J = J` (p. 27). -/
def comp (π : P.Policy) : ℕ → (S → EReal) → (S → EReal)
  | 0, J => J
  | N + 1, J => comp π N (P.Tmu (π N).1 J)

/-- The `N`-stage cost function `J_{N,π}(x) = (T_{μ₀} ⋯ T_{μ_{N−1}})(J₀)(x)`, eq. (1) of Chapter 6. -/
def JN (N : ℕ) (π : P.Policy) : S → EReal := P.comp π N P.J0

/-- The cost function `J_π(x) = lim_{N → ∞} (T_{μ₀} ⋯ T_{μ_{N−1}})(J₀)(x)`, eq. (2) of Chapter 6,
taken as `limUnder`; it is the true limit whenever the limit exists in `[−∞, ∞]` (under
Assumption C̃ it exists and is real). -/
noncomputable def Jpi (π : P.Policy) : S → EReal :=
  fun x => limUnder atTop (fun N => P.comp π N P.J0 x)

/-- `J_μ = J_π` for the stationary policy `π = (μ, μ, …)` (p. 29). -/
noncomputable def Jmu (μ : P.Sel) : S → EReal := P.Jpi (P.stationary μ)

/-- `J*_N(x) = inf_{π ∈ Π̃} J_{N,π}(x)` (p. 93). The infimum is over `Π̃` only. -/
noncomputable def JNstar (N : ℕ) : S → EReal := fun x => ⨅ π : P.Policy, P.JN N π x

/-- `J*(x) = inf_{π ∈ Π̃} J_π(x)` (p. 93). The infimum is over `Π̃` only. -/
noncomputable def Jstar : S → EReal := fun x => ⨅ π : P.Policy, P.Jpi π x

end Model

/-- `J ∈ B̄ ∩ G` for a set `B̄ ⊆ B` and a set `G ⊆ F` (used with `G = F*` and `G = F̃`): `J` is a
bounded real function lying in `B̄`, viewed as an element of `F`, and it belongs to `G`. -/
def MemBbarInter {S : Type*} (Bbar : Set (BertsekasShreve.Contraction.BFun S)) (G : Set (S → EReal)) (J : S → EReal) : Prop :=
  ∃ J' ∈ Bbar, J = BertsekasShreve.Contraction.toF J' ∧ J ∈ G

/-- The function `J + r`, `(J + r)(x) = J(x) + r`, for a real scalar `r` (item (5), p. 26). -/
noncomputable def addConst {S : Type*} (J : S → EReal) (r : ℝ) : S → EReal :=
  fun x => J x + (r : EReal)

end BertsekasShreve.Generalized


