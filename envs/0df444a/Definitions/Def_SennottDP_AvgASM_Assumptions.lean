-- Prove2me | Definitions.Def_SennottDP_AvgASM_Assumptions
-- name    : SennottDP_AvgASM_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T09:29:25.518598+00:00
-- url     : https://prove2.me/theorems/c37a72a1-5d5b-4d29-8a3d-76fb55dd7f00
-- title:
--   The (AC) and (WAC) assumptions (Sennott §8.1, §8.7)
-- statement:
--   Let $(\Delta_N)_{N\ge N_0}$ be an AS for the MDC $\Delta$, and let $J(i)$ be the minimum average cost of $\Delta$.
--
--   The **(AC) assumptions** are:
--   1. (AC1) There exist finite constants $J^N$ and finite functions $r^N$ on $S_N$ with
--   $$J^N+r^N(i)=\min_a\Big\{C(i,a)+\sum_{j\in S_N}P_{ij}(a;N)\,r^N(j)\Big\},\qquad i\in S_N,\ N\ge N_0. \tag{8.1}$$
--   2. (AC2) $\limsup_{N\to\infty}r^N(i)<\infty$ for $i\in S$.
--   3. (AC3) There is a finite constant $Q\ge0$ with $-Q\le\liminf_{N\to\infty}r^N(i)$ for $i\in S$.
--   4. (AC4) $J^*:=\limsup_{N\to\infty}J^N<\infty$ and $J^*\le J(i)$ for $i\in S$.
--
--   The **(WAC) assumptions** keep (AC1), (AC2), (AC4) and replace (AC3) by: (WAC3$_1$) there is a finite function $Q\ge0$ on $S$ with $-Q(i)\le\liminf_N r^N(i)=:u(i)$; and (WAC3$_2$) for every stationary policy $e$ of $\Delta$ and initial state $X_0=i$: (i) $\lim_N\sum_{j\in S_N}P_{ij}(e;N)Q(j)=\sum_jP_{ij}(e)Q(j)<\infty$; (ii) $-\infty<E_e[u(X_n)]$ for $n\ge1$; (iii) $\liminf_{n\to\infty}E_e[u(X_n)]/n\ge0$.
--
--   Finally, "**the VIA and (AC) hold for the base point $x$**" means: in each $\Delta_N$ the limits $J^N=\lim_n(v^N_{n+1}(x)-v^N_n(x))$ and $r^N(i)=\lim_n(v^N_n(i)-v^N_n(x))$ exist, and (AC) holds for these $J^N,r^N$.
--
--   **Formalization Note** $\limsup$ and $\liminf$ over $N$ are taken in `EReal`, so an unbounded sequence has value $\pm\infty$ rather than a junk real. $E_e[u(X_n)]$ is the `EReal` difference of the expectations of $u^+$ and $u^-$; it exceeds $-\infty$ exactly when the negative part has finite expectation. Finite horizon values of the finite model $\Delta_N$ are finite, so they are converted to reals with `toReal`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 169 (AC1)–(AC4) and (8.1); pp. 193–194 (WAC); p. 171 and p. 117 Proposition 6.6.3 (VIA)

import Mathlib
import Definitions.Def_SennottDP_AvgASM_ApproxSeq

namespace SennottDP.AvgASM

open scoped ENNReal NNReal Topology
open Filter

variable {S : Type*} {Act : Type*} [Countable S]

namespace ApproxSeq

variable {M : MDC S Act} (AS : ApproxSeq M)

/-- The right-hand side of (8.1) for the action `a` at `i ∈ S_N`:
`C(i, a) + ∑_{j ∈ S_N} P_ij(a; N) r^N(j)`. (`P_ij(a; N) ≤ 1` is finite, so `toReal` is exact.) -/
noncomputable def acoeTerm (rN : ℕ → S → ℝ) (N : ℕ) (i : S) (a : Act) : ℝ :=
  (M.C i a : ℝ) + ∑ j ∈ AS.SN N, (AS.PN N i a j).toReal * rN N j

/-- (AC1), p. 169: the (finite) constants `J^N` and (finite) functions `r^N` on `S_N` satisfy
`J^N + r^N(i) = min_a {C(i, a) + ∑_{j ∈ S_N} P_ij(a; N) r^N(j)}` for `i ∈ S_N`, `N ≥ N₀` (8.1).
(The values `r^N(i)` for `i ∉ S_N` are not constrained.) -/
def AC1 (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) : Prop :=
  ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N,
    JN N + rN N i = (M.A i).inf' (M.A_nonempty i) (fun a => AS.acoeTerm rN N i a)

/-- (AC2), p. 169: `limsup_{N→∞} r^N(i) < ∞` for `i ∈ S` (computed in `EReal`; `r^N(i)` is
defined for all sufficiently large `N`). -/
def AC2 {M : MDC S Act} (_AS : ApproxSeq M) (rN : ℕ → S → ℝ) : Prop :=
  ∀ i, limsup (fun N => (rN N i : EReal)) atTop < ⊤

/-- (AC3), p. 169: there exists a nonnegative (finite) constant `Q` such that
`−Q ≤ liminf_{N→∞} r^N(i)` for `i ∈ S`. -/
def AC3 {M : MDC S Act} (_AS : ApproxSeq M) (rN : ℕ → S → ℝ) : Prop :=
  ∃ Q : ℝ, 0 ≤ Q ∧ ∀ i, ((-Q : ℝ) : EReal) ≤ liminf (fun N => (rN N i : EReal)) atTop

/-- (AC4), p. 169: `limsup_{N→∞} J^N =: J* < ∞` and `J* ≤ J(i)` for `i ∈ S`, where `J(i)` is the
minimum average cost of `Δ` (in `[0, ∞]`); the comparison is made in `EReal`. -/
def AC4 {M : MDC S Act} (_AS : ApproxSeq M) (JN : ℕ → ℝ) : Prop :=
  limsup (fun N => (JN N : EReal)) atTop < ⊤ ∧
    ∀ i, limsup (fun N => (JN N : EReal)) atTop ≤ ((avgValue M i : ℝ≥0∞) : EReal)

/-- The (AC) assumptions, p. 169, for the witnesses `J^N`, `r^N` of (AC1). -/
def AC (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) : Prop :=
  AS.AC1 JN rN ∧ AS.AC2 rN ∧ AS.AC3 rN ∧ AS.AC4 JN

/-- `u(i) = liminf_{N→∞} r^N(i)`, in `EReal` ((WAC3₁), p. 193). -/
noncomputable def liminfR {M : MDC S Act} (_AS : ApproxSeq M) (rN : ℕ → S → ℝ) (i : S) : EReal :=
  liminf (fun N => (rN N i : EReal)) atTop

/-- `E_e[w(X_n) | X_0 = i]` for the Markov chain induced by the stationary policy `e` of `Δ` and
an extended-real function `w`, as the difference of the expectations of its positive and
negative parts, `∑_j P^{(n)}_{ij}(e) w⁺(j) − ∑_j P^{(n)}_{ij}(e) w⁻(j)`, computed in `EReal`.
It is `> −∞` exactly when the negative part has finite expectation (when both parts are
infinite the `EReal` difference is `−∞`). -/
noncomputable def expectEReal {M : MDC S Act} (_AS : ApproxSeq M) (e : StationaryPolicy M) (w : S → EReal) (n : ℕ) (i : S) : EReal :=
  ((∑' j, nStep e.chain n i j * (w j).toENNReal : ℝ≥0∞) : EReal) -
    ((∑' j, nStep e.chain n i j * (-(w j)).toENNReal : ℝ≥0∞) : EReal)

/-- (WAC3₁), p. 193: there exists a nonnegative (finite) function `Q` on `S` such that
`−Q(i) ≤ liminf_{N→∞} r^N(i) =: u(i)` for `i ∈ S`; and (WAC3₂), pp. 193–194, for that `Q`: for
every stationary policy `e` for `Δ` and initial state `X_0 = i`,
(i) `lim_{N→∞} ∑_{j ∈ S_N} P_ij(e; N) Q(j) = ∑_j P_ij(e) Q(j) < ∞`,
(ii) `−∞ < E_e[u(X_n)]` for `n ≥ 1`,
(iii) `liminf_{n→∞} E_e[u(X_n)]/n ≥ 0`. -/
def WAC3 (rN : ℕ → S → ℝ) : Prop :=
  ∃ Q : S → ℝ≥0,
    (∀ i, ((-(Q i : ℝ) : ℝ) : EReal) ≤ AS.liminfR rN i) ∧
    ∀ e : StationaryPolicy M, ∀ i,
      (Tendsto (fun N => ∑ j ∈ AS.SN N, AS.PN N i (e.f i) j * (Q j : ℝ≥0∞)) atTop
          (𝓝 (∑' j, M.P i (e.f i) j * (Q j : ℝ≥0∞))) ∧
        ∑' j, M.P i (e.f i) j * (Q j : ℝ≥0∞) < ⊤) ∧
      (∀ n, 1 ≤ n → (⊥ : EReal) < AS.expectEReal e (AS.liminfR rN) n i) ∧
      0 ≤ liminf (fun n : ℕ => AS.expectEReal e (AS.liminfR rN) n i / (n : EReal)) atTop

/-- The (WAC) assumptions, pp. 193–194: (WAC1), (WAC2), (WAC4) are (AC1), (AC2), (AC4), and
(WAC3) = (WAC3₁) + (WAC3₂). -/
def WAC (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) : Prop :=
  AS.AC1 JN rN ∧ AS.AC2 rN ∧ AS.WAC3 rN ∧ AS.AC4 JN

/-- The conclusion of Proposition 8.2.1 (pp. 171–172) for the base point `x`: the value iteration
algorithm is justified in each `Δ_N` — the limits `J^N = lim_{n→∞} (v^N_{n+1}(x) − v^N_n(x))` and
`r^N(i) = lim_{n→∞} (v^N_n(i) − v^N_n(x))` (`i ∈ S_N`) exist (the conclusions of Proposition
6.6.3 in `Δ_N`) — and the (AC) assumptions hold for these `J^N` and `r^N`. The finite horizon
values of the finite model `Δ_N` are finite, so `toReal` is exact. -/
def VIAAndAC (x : S) : Prop :=
  ∃ (JN : ℕ → ℝ) (rN : ℕ → S → ℝ),
    (∀ N, AS.N₀ ≤ N → Tendsto (fun n => (AS.valueN (n + 1) N x).toReal - (AS.valueN n N x).toReal)
        atTop (𝓝 (JN N))) ∧
    (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N,
      Tendsto (fun n => (AS.valueN n N i).toReal - (AS.valueN n N x).toReal) atTop
        (𝓝 (rN N i))) ∧
    AS.AC JN rN

end ApproxSeq

end SennottDP.AvgASM


