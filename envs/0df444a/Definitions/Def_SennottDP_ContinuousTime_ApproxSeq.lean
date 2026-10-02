-- Prove2me | Definitions.Def_SennottDP_ContinuousTime_ApproxSeq
-- name    : SennottDP_ContinuousTime_ApproxSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T10:46:38.292841+00:00
-- url     : https://prove2.me/theorems/c9881cca-38d7-46f2-bce6-ef715732b3a6
-- title:
--   Approximating sequence, the (AC) assumptions and limit points of stationary policies
-- statement:
--   Let $\Delta$ be an MDC with state space $S$. An **approximating sequence** (AS) $(\Delta_N)_{N\ge N_0}$ for $\Delta$ consists of finite nonempty sets $S_{N_0}\subseteq S_{N_0+1}\subseteq\cdots$ with $\bigcup_N S_N=S$ and, for $N\ge N_0$, $i\in S_N$, $a\in A_i$, probability distributions $(P_{ij}(a;N))_{j\in S_N}$ with $\lim_{N\to\infty}P_{ij}(a;N)=P_{ij}(a)$ for all $i,j\in S$, $a\in A_i$. The MDC $\Delta_N$ has state space $S_N$ and the action sets and costs of $\Delta$.
--
--   The **(AC) assumptions** for real constants $J^N$ and real functions $r^N$ on $S_N$ are:
--
--   1. (AC1) for $N\ge N_0$ and $i\in S_N$,
--   $$J^N+r^N(i)=\min_{a\in A_i}\Big\{C(i,a)+\sum_{j\in S_N}P_{ij}(a;N)\,r^N(j)\Big\};$$
--   2. (AC2) $\limsup_{N\to\infty}r^N(i)<\infty$ for $i\in S$;
--   3. (AC3) there is a finite constant $Q\ge0$ with $-Q\le\liminf_{N\to\infty}r^N(i)$ for $i\in S$;
--   4. (AC4) $J^*:=\limsup_{N\to\infty}J^N<\infty$ and $J^*\le J(i)$ for $i\in S$, where $J$ is the minimum average cost of $\Delta$.
--
--   A sequence $e^N$ of stationary policies **realizes the minimum** in (AC1) if $e^N(i)\in A_i$ attains the minimum for all $N\ge N_0$, $i\in S_N$. A stationary policy $e$ of $\Delta$ is a **limit point** of $(e^N)$ if there is a subsequence $N_r$ such that, for each $i\in S$, $e^{N_r}(i)=e(i)$ for all sufficiently large $r$.
--
--   These objects are the input of the computational method of Chapter 8, which this mission applies to the auxiliary MDC of a continuous time chain.
--
--   **Formalization Note** The limits superior and inferior are taken in the extended reals `EReal`, so that the book's $\pm\infty$ values are represented. Values of $r^N(i)$ for $i\notin S_N$ and of $J^N$ for $N<N_0$ carry no meaning and do not affect these limits, since each $i$ lies in $S_N$ for all large $N$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 28, Definition 2.5.1; p. 169, (AC1)–(AC4) and (8.1); p. 290, Definition B.4

import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_MDC

open scoped ENNReal NNReal
open Classical Filter Topology

namespace SennottDP.ContinuousTime

variable {S Act : Type}

/-- An approximating sequence (AS) `(Δ_N)_{N ≥ N₀}` for the MDC `M` (Definition 2.5.1, p. 28):
an increasing sequence `(S_N)_{N ≥ N₀}` of finite nonempty subsets of `S` with union `S`, and for
each `N ≥ N₀`, `i ∈ S_N`, `a ∈ A i` a probability distribution `P_{i·}(a; N)` on `S_N` with
`lim_{N→∞} P_{ij}(a; N) = P_{ij}(a)` for every `j ∈ S` (2.17). The action sets and costs of
`Δ_N` are those of `M`. The fields `SN N`, `PN N` for `N < N₀`, and `PN N i a j` for `i ∉ S_N`
or `j ∉ S_N`, carry no meaning and enter no statement except through limits in `N`. -/
structure ApproxSeq (M : MDC S Act) where
  N0 : ℕ
  SN : ℕ → Finset S
  SN_nonempty : ∀ N, N0 ≤ N → (SN N).Nonempty
  SN_mono : ∀ N N', N0 ≤ N → N ≤ N' → SN N ⊆ SN N'
  SN_cover : ∀ i, ∃ N, N0 ≤ N ∧ i ∈ SN N
  PN : ℕ → S → Act → S → ℝ≥0∞
  PN_sum : ∀ N, N0 ≤ N → ∀ i ∈ SN N, ∀ a ∈ M.A i, ∑ j ∈ SN N, PN N i a j = 1
  PN_lim : ∀ i, ∀ a ∈ M.A i, ∀ j, Tendsto (fun N => PN N i a j) atTop (𝓝 (M.P i a j))

namespace ApproxSeq

variable {M : MDC S Act} (Δs : ApproxSeq M)

/-- The bracket of the optimality equation (8.1) of `Δ_N` at the action `a`:
`C(i,a) + Σ_{j ∈ S_N} P_{ij}(a; N) r(j)`. -/
noncomputable def bracket (N : ℕ) (r : S → ℝ) (i : S) (a : Act) : ℝ :=
  M.C i a + ∑ j ∈ Δs.SN N, (Δs.PN N i a j).toReal * r j

/-- The (AC) assumptions (p. 169) for the AS `(Δ_N)` with the constants `J^N` (`JN N`) and the
functions `r^N` (`rN N`, meaningful on `S_N`):

* (AC1) for `N ≥ N₀` and `i ∈ S_N`,
  `J^N + r^N(i) = min_{a ∈ A_i} { C(i,a) + Σ_{j ∈ S_N} P_{ij}(a;N) r^N(j) }` (8.1);
* (AC2) `limsup_{N→∞} r^N(i) < ∞` for `i ∈ S`;
* (AC3) there is a finite constant `Q ≥ 0` with `-Q ≤ liminf_{N→∞} r^N(i)` for `i ∈ S`;
* (AC4) `J* := limsup_{N→∞} J^N < ∞` and `J* ≤ J(i)` for `i ∈ S`, `J` the minimum average cost
  of `M`.

The limits superior and inferior are taken in `EReal`, so that `±∞` are the book's values; for
a fixed `i`, `i ∈ S_N` for all large `N`, so the values of `r^N(i)` at `i ∉ S_N` do not matter. -/
def AC (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) : Prop :=
  (∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, ∃ hA : (M.A i).Nonempty,
      JN N + rN N i = (M.A i).inf' hA (fun a => Δs.bracket N (rN N) i a)) ∧
    (∀ i, limsup (fun N => ((rN N i : ℝ) : EReal)) atTop < ⊤) ∧
    (∃ Q : ℝ, 0 ≤ Q ∧ ∀ i, ((-Q : ℝ) : EReal) ≤ liminf (fun N => ((rN N i : ℝ) : EReal)) atTop) ∧
    limsup (fun N => ((JN N : ℝ) : EReal)) atTop < ⊤ ∧
    ∀ i, limsup (fun N => ((JN N : ℝ) : EReal)) atTop ≤ ((M.avgValue i : ℝ≥0∞) : EReal)

/-- `eN` is a sequence of stationary policies realizing the minimum in (8.1): for `N ≥ N₀` and
`i ∈ S_N`, `e^N(i) ∈ A_i` attains the minimum of the bracket. -/
def RealizesMin (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (eN : ℕ → S → Act) : Prop :=
  ∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N,
    eN N i ∈ M.A i ∧ JN N + rN N i = Δs.bracket N (rN N) i (eN N i)

/-- Definition B.4 (p. 290): the stationary policy `e` of `M` is a limit point of the sequence
`(e^N)_{N ≥ N₀}` of stationary policies of the `Δ_N` if there is a subsequence `N_r ≥ N₀` such
that for each `i ∈ S`, `e^{N_r}(i) = e(i)` for all large `r`. -/
def IsLimitPoint (eN : ℕ → S → Act) (e : S → Act) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ r, Δs.N0 ≤ φ r) ∧ ∀ i, ∀ᶠ r in atTop, eN (φ r) i = e i

end ApproxSeq

end SennottDP.ContinuousTime


