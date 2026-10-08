-- Prove2me | Definitions.Def_BertsekasShreve_Generalized_Assumptions
-- name    : BertsekasShreve_Generalized_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:38:52.736335+00:00
-- url     : https://prove2.me/theorems/386943c0-4829-40c1-b798-4f91bb817269
-- title:
--   Conditions A.1–A.5, Assumptions $\tilde F.2$, $\tilde F.3$, the exact selection assumption and Assumption $\tilde C$
-- statement:
--   The hypotheses of Chapter 6 on the generalized abstract model (state space $S$, constraint sets $U(x)$, classes $F^*\subset\tilde F\subset F$ and $\tilde M$, mapping $H$, initial function $J_0$). For a real $r$, $J+r$ is the function $x\mapsto J(x)+r$.
--
--   1. **A.1** For each $x\in S$ and $u\in U(x)$ there is a $\mu\in\tilde M$ with $\mu(x)=u$.
--   2. **A.2** For all $J\in F^*$ and $r\in\mathbb R$: $T(J)\in F^*$ and $J+r\in F^*$.
--   3. **A.3** For all $J\in\tilde F$, $\mu\in\tilde M$ and $r\in\mathbb R$: $T_\mu(J)\in\tilde F$ and $J+r\in\tilde F$.
--   4. **A.4** For each $J\in F^*$ and $\varepsilon>0$ there is a $\mu_\varepsilon\in\tilde M$ such that for all $x\in S$
--   $$T_{\mu_\varepsilon}(J)(x)\le\begin{cases}T(J)(x)+\varepsilon&\text{if }T(J)(x)>-\infty,\\-1/\varepsilon&\text{if }T(J)(x)=-\infty.\end{cases}$$
--   5. **A.5** If $\{J_k\}\subset\tilde F$ converges pointwise (in $[-\infty,\infty]$), then $\lim_k J_k\in\tilde F$; if moreover $\{J_k\}\subset F^*$, then $\lim_k J_k\in F^*$.
--   6. **Assumption $\tilde F.2$** There is $\alpha\in(0,\infty)$ such that for all $r\in(0,\infty)$ and $J\in\tilde F$,
--   $$H(x,u,J)\le H(x,u,J+r)\le H(x,u,J)+\alpha r\qquad\forall x\in S,\ u\in U(x).$$
--   7. **Assumption $\tilde F.3$** There is $\beta\in(0,\infty)$ such that whenever $J\in F^*$, $\{J_n\}\subset\tilde F$ and real $\{\varepsilon_n\}$ satisfy $\sum_{n\ge1}\varepsilon_n<\infty$, $\varepsilon_n>0$; $J=\lim_n J_n$ pointwise and $J\le J_n$; $J_n(x)\le J(x)+\varepsilon_n$ for $n\ge1$ and $x$ with $J(x)>-\infty$, and $J_n(x)\le J_{n-1}(x)+\varepsilon_n$ for $n\ge2$ and $x$ with $J(x)=-\infty$; and $H(x,u,J_1)<\infty$ for all $x\in S$, $u\in U(x)$ — then there is $\{\mu_n\}\subset\tilde M$ with $\lim_n T_{\mu_n}(J_n)=T(J)$ pointwise,
--   $$T_{\mu_n}(J_n)(x)\le\begin{cases}T(J)(x)+\beta\varepsilon_n,& n\ge1,\ T(J)(x)>-\infty,\\ T_{\mu_{n-1}}(J_{n-1})(x)+\beta\varepsilon_n,& n\ge2,\ T(J)(x)=-\infty.\end{cases}$$
--   8. **Exact selection assumption** For every $J\in F^*$, if the infimum in $T(J)(x)=\inf_{u\in U(x)}H(x,u,J)$ is attained for every $x\in S$, then there is a $\mu^*\in\tilde M$ with $T_{\mu^*}(J)=T(J)$.
--   9. **Assumption $\tilde C$** (for a given set $\bar B$, positive integer $m$ and scalars $\rho$, $\alpha$) $\bar B$ is a closed subset of $B$ and
--      (a) $J_0\in\bar B\cap F^*$; (b) $T(J)\in\bar B\cap F^*$ for all $J\in\bar B\cap F^*$; (c) $T_\mu(J)\in\bar B\cap\tilde F$ for all $J\in\bar B\cap\tilde F$, $\mu\in\tilde M$; for every $\pi\in\tilde\Pi$ the limit $\lim_N(T_{\mu_0}\cdots T_{\mu_{N-1}})(J_0)(x)$ exists and is real for each $x$; $0<\rho<1$, $0<\alpha$; and
--   $$\|T_\mu(J)-T_\mu(J')\|\le\alpha\|J-J'\|\quad\forall\mu\in\tilde M,\ J,J'\in B\cap\tilde F,$$
--   $$\|(T_{\mu_0}\cdots T_{\mu_{m-1}})(J)-(T_{\mu_0}\cdots T_{\mu_{m-1}})(J')\|\le\rho\|J-J'\|\quad\forall\mu_0,\dots,\mu_{m-1}\in\tilde M,\ J,J'\in\bar B\cap\tilde F.$$
--
--   A.1–A.4 are assumed in every result of the chapter and A.5 in Section 6.3. The examples of the book (Borel spaces with universally or analytically measurable policies, semicontinuous models) show why $F^*$, $\tilde F$ and $\tilde M$ need to be different from $F$ and $M$.
--
--   **Formalization Note** The book's index $n=1,2,\dots$ in $\tilde F.3$ is Lean's index $k=n-1$. In Assumption $\tilde C$ the set $\bar B$ and the scalars $m,\rho,\alpha$ are explicit parameters, closedness is in the sup-norm topology of $\ell^\infty(S,\mathbb R)$, and the tuple $\mu_0,\dots,\mu_{m-1}$ is the first $m$ entries of a policy in $\tilde\Pi$. A norm bound $\|G-G'\|\le c$ between extended-real functions means both are real everywhere with $|G(x)-G'(x)|\le c$ (the book's $\infty-\infty=\infty$ makes any infinite value violate the bound); in particular the first Lipschitz bound forces $T_\mu(J)$ to be real-valued for $J\in B\cap\tilde F$, as the book's statement does.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 93, A.1–A.5; p. 94, Assumption F̃.2; p. 95, Assumption F̃.3 and the Exact Selection Assumption; p. 40, Assumptions F.2 and F.3; p. 96, Assumption C̃

import Mathlib
import Definitions.Def_BertsekasShreve_Generalized_Model

namespace BertsekasShreve.Generalized

open Filter Topology

namespace Model

variable {S C : Type*} (P : Model S C)

/-- Condition A.1 (p. 93): for each `x ∈ S` and `u ∈ U(x)` there is a `μ ∈ M̃` with `μ(x) = u`. -/
def A1 : Prop := ∀ x, ∀ u ∈ P.U x, ∃ μ ∈ P.Mtil, μ x = u

/-- Condition A.2 (p. 93): for all `J ∈ F*` and `r ∈ R`, `T(J) ∈ F*` and `J + r ∈ F*`. -/
def A2 : Prop := ∀ J ∈ P.Fstar, P.T J ∈ P.Fstar ∧ ∀ r : ℝ, addConst J r ∈ P.Fstar

/-- Condition A.3 (p. 93): for all `J ∈ F̃`, `μ ∈ M̃` and `r ∈ R`, `T_μ(J) ∈ F̃` and `J + r ∈ F̃`. -/
def A3 : Prop :=
  ∀ J ∈ P.Ftil, (∀ μ ∈ P.Mtil, P.Tmu μ J ∈ P.Ftil) ∧ ∀ r : ℝ, addConst J r ∈ P.Ftil

/-- Condition A.4 (p. 93): for each `J ∈ F*` and `ε > 0` there is a `μ_ε ∈ M̃` such that for all
`x ∈ S`, `T_{μ_ε}(J)(x) ≤ T(J)(x) + ε` if `T(J)(x) > −∞` and `T_{μ_ε}(J)(x) ≤ −1/ε` if
`T(J)(x) = −∞`. -/
def A4 : Prop :=
  ∀ J ∈ P.Fstar, ∀ ε : ℝ, 0 < ε → ∃ μ ∈ P.Mtil, ∀ x,
    (⊥ < P.T J x → P.Tmu μ J x ≤ P.T J x + (ε : EReal)) ∧
    (P.T J x = ⊥ → P.Tmu μ J x ≤ ((-1 / ε : ℝ) : EReal))

/-- Condition A.5 (p. 93): the pointwise limit (in `[−∞, ∞]`) of every pointwise convergent
sequence in `F̃` lies in `F̃`; if moreover the sequence lies in `F*`, the limit lies in `F*`. -/
def A5 : Prop :=
  ∀ (Js : ℕ → S → EReal) (J : S → EReal), (∀ k, Js k ∈ P.Ftil) →
    (∀ x, Tendsto (fun k => Js k x) atTop (𝓝 (J x))) →
    J ∈ P.Ftil ∧ ((∀ k, Js k ∈ P.Fstar) → J ∈ P.Fstar)

/-- Assumption F̃.2 (p. 94) = Assumption F.2 (p. 40) with `F` replaced by `F̃`: there is a scalar
`α ∈ (0, ∞)` such that for all `r ∈ (0, ∞)` and `J ∈ F̃`,
`H(x, u, J) ≤ H(x, u, J + r) ≤ H(x, u, J) + α r` for all `x ∈ S`, `u ∈ U(x)`. -/
def Ftilde2 : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ r : ℝ, 0 < r → ∀ J ∈ P.Ftil, ∀ x, ∀ u ∈ P.U x,
    P.H x u J ≤ P.H x u (addConst J r) ∧
    P.H x u (addConst J r) ≤ P.H x u J + ((α * r : ℝ) : EReal)

/-- Assumption F̃.3 (p. 95) = Assumption F.3 (p. 40) with `J ∈ F*`, `{J_n} ⊂ F̃`, `{μ_n} ⊂ M̃`.
The book's index `n = 1, 2, …` is Lean's `k = n − 1 = 0, 1, …`: `Js k = J_{k+1}`,
`ε k = ε_{k+1}`, `μs k = μ_{k+1}`.

There is a scalar `β ∈ (0, ∞)` such that if `J ∈ F*`, `{J_n} ⊂ F̃` and real `{ε_n}` satisfy
`Σ ε_n < ∞`, `ε_n > 0`; `J = lim J_n` (pointwise), `J ≤ J_n`;
`J_n(x) ≤ J(x) + ε_n` (`n ≥ 1`, `J(x) > −∞`), `J_n(x) ≤ J_{n−1}(x) + ε_n` (`n ≥ 2`, `J(x) = −∞`);
`H(x, u, J_1) < ∞` for all `x ∈ S`, `u ∈ U(x)`; then there is `{μ_n} ⊂ M̃` with
`lim T_{μ_n}(J_n) = T(J)`, `T_{μ_n}(J_n)(x) ≤ T(J)(x) + β ε_n` (`n ≥ 1`, `T(J)(x) > −∞`) and
`T_{μ_n}(J_n)(x) ≤ T_{μ_{n−1}}(J_{n−1})(x) + β ε_n` (`n ≥ 2`, `T(J)(x) = −∞`). -/
def Ftilde3 : Prop :=
  ∃ β : ℝ, 0 < β ∧ ∀ J ∈ P.Fstar, ∀ (Js : ℕ → S → EReal) (ε : ℕ → ℝ),
    (∀ k, Js k ∈ P.Ftil) →
    Summable ε → (∀ k, 0 < ε k) →
    (∀ x, Tendsto (fun k => Js k x) atTop (𝓝 (J x))) →
    (∀ k, J ≤ Js k) →
    (∀ k x, ⊥ < J x → Js k x ≤ J x + (ε k : EReal)) →
    (∀ k x, J x = ⊥ → Js (k + 1) x ≤ Js k x + (ε (k + 1) : EReal)) →
    (∀ x, ∀ u ∈ P.U x, P.H x u (Js 0) < ⊤) →
    ∃ μs : ℕ → S → C, (∀ k, μs k ∈ P.Mtil) ∧
      (∀ x, Tendsto (fun k => P.Tmu (μs k) (Js k) x) atTop (𝓝 (P.T J x))) ∧
      (∀ k x, ⊥ < P.T J x → P.Tmu (μs k) (Js k) x ≤ P.T J x + ((β * ε k : ℝ) : EReal)) ∧
      (∀ k x, P.T J x = ⊥ →
        P.Tmu (μs (k + 1)) (Js (k + 1)) x ≤
          P.Tmu (μs k) (Js k) x + ((β * ε (k + 1) : ℝ) : EReal))

/-- The Exact Selection Assumption (p. 95): for every `J ∈ F*`, if the infimum in
`T(J)(x) = inf_{u ∈ U(x)} H(x, u, J)` is attained for every `x ∈ S`, then there is a `μ* ∈ M̃`
with `T_{μ*}(J) = T(J)`. -/
def ExactSelection : Prop :=
  ∀ J ∈ P.Fstar, (∀ x, ∃ u ∈ P.U x, P.H x u J = P.T J x) →
    ∃ μ ∈ P.Mtil, P.Tmu μ J = P.T J

/-- Assumption C̃ (p. 96), with the closed set `B̄` and the scalars `m`, `ρ`, `α` it introduces
made explicit parameters. Membership in `B̄ ∩ F*` and `B̄ ∩ F̃` is `MemBbarInter`.

* `Bbar` is a closed subset of `B` (sup-norm topology of `ℓ^∞(S, ℝ)`);
* (a) `J₀ ∈ B̄ ∩ F*`;
* (b) for all `J ∈ B̄ ∩ F*`, `T(J) ∈ B̄ ∩ F*`;
* (c) for all `J ∈ B̄ ∩ F̃` and `μ ∈ M̃`, `T_μ(J) ∈ B̄ ∩ F̃`;
* for every `π ∈ Π̃` the limit `lim_{N → ∞} (T_{μ₀} ⋯ T_{μ_{N−1}})(J₀)(x)` exists and is a real
  number for each `x ∈ S`;
* `m` is a positive integer, `0 < ρ < 1`, `0 < α`;
* `‖T_μ(J) − T_μ(J')‖ ≤ α ‖J − J'‖` for all `μ ∈ M̃` and `J, J' ∈ B ∩ F̃` (not only `B̄ ∩ F̃`);
* `‖(T_{μ₀} ⋯ T_{μ_{m−1}})(J) − (T_{μ₀} ⋯ T_{μ_{m−1}})(J')‖ ≤ ρ ‖J − J'‖` for all
  `μ₀, …, μ_{m−1} ∈ M̃` and `J, J' ∈ B̄ ∩ F̃`; the tuple is the first `m` entries of a `π ∈ Π̃`. -/
structure AssumptionCtilde (Bbar : Set (BertsekasShreve.Contraction.BFun S)) (m : ℕ) (ρ α : ℝ) : Prop where
  isClosed : IsClosed Bbar
  J0_mem : MemBbarInter Bbar P.Fstar P.J0
  T_mem : ∀ J, MemBbarInter Bbar P.Fstar J → MemBbarInter Bbar P.Fstar (P.T J)
  Tmu_mem : ∀ μ ∈ P.Mtil, ∀ J, MemBbarInter Bbar P.Ftil J → MemBbarInter Bbar P.Ftil (P.Tmu μ J)
  limit_real : ∀ (π : P.Policy) (x : S), ∃ r : ℝ,
    Tendsto (fun N => P.comp π N P.J0 x) atTop (𝓝 (r : EReal))
  m_pos : 0 < m
  ρ_pos : 0 < ρ
  ρ_lt_one : ρ < 1
  α_pos : 0 < α
  lipschitz : ∀ μ ∈ P.Mtil, ∀ J J' : BertsekasShreve.Contraction.BFun S, BertsekasShreve.Contraction.toF J ∈ P.Ftil → BertsekasShreve.Contraction.toF J' ∈ P.Ftil →
    BertsekasShreve.Contraction.SupDistLe (P.Tmu μ (BertsekasShreve.Contraction.toF J)) (P.Tmu μ (BertsekasShreve.Contraction.toF J')) (α * ‖J - J'‖)
  contraction : ∀ (π : P.Policy), ∀ J ∈ Bbar, ∀ J' ∈ Bbar, BertsekasShreve.Contraction.toF J ∈ P.Ftil → BertsekasShreve.Contraction.toF J' ∈ P.Ftil →
    BertsekasShreve.Contraction.SupDistLe (P.comp π m (BertsekasShreve.Contraction.toF J)) (P.comp π m (BertsekasShreve.Contraction.toF J')) (ρ * ‖J - J'‖)

end Model

end BertsekasShreve.Generalized


