-- Prove2me | Definitions.Def_SennottDP_AvgASM_ApproxSeq
-- name    : SennottDP_AvgASM_ApproxSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T09:21:11.360444+00:00
-- url     : https://prove2.me/theorems/5b7e4d8f-9db8-4653-92bd-92dad389e58c
-- title:
--   Approximating sequences, ATAS, limit points and conformity (Sennott Def. 2.5.1, 2.5.3, B.4, C.4.8, C.4.10)
-- statement:
--   Let $\Delta$ be an MDC on a countable state space $S$. An **approximating sequence** (AS) $(\Delta_N)_{N\ge N_0}$ consists of finite nonempty sets $S_N\subseteq S$, increasing in $N$ with $\bigcup_N S_N=S$, and MDCs $\Delta_N$ on $S_N$ with the same actions and costs as $\Delta$ and transition probabilities $P_{ij}(a;N)$, a probability distribution on $S_N$ for $i\in S_N$, $a\in A_i$, such that
--   $$\lim_{N\to\infty}P_{ij}(a;N)=P_{ij}(a),\qquad i,j\in S.$$
--   Write $v^N_n$ and $V^N_\alpha$ for the $n$-horizon and $\alpha$-discounted value functions of $\Delta_N$.
--
--   1. The AS is an **augmentation type approximating sequence** (ATAS) with augmentation distributions $q_j(i,a,r,N)$ (a distribution over $j\in S_N$ for each $r\notin S_N$) if $P_{ij}(a;N)=P_{ij}(a)+\sum_{r\notin S_N}P_{ir}(a)q_j(i,a,r,N)$; it **sends excess probability to** $G$ if every $q(i,a,r,N)$ is concentrated on $G$.
--   2. A stationary policy $f$ of $\Delta$ is a **limit point** of stationary policies $e^N$ of $\Delta_N$ if along a subsequence $N_r$, $e^{N_r}(i)=f(i)$ for all large $r$, for each $i$.
--   3. A stationary policy $d$ of $\Delta$ induces the policy $d|N$ of $\Delta_N$, whose Markov chain has $P_{ij}(d|N)=P_{ij}(d(i);N)$. For $d$ a $z$ standard policy, the AS is **conforming at $d$** if for large $N$ the chain of $d|N$ is unichain with $z$ in its positive recurrent class, and $m_{iz}(N)\to m_{iz}$, $c_{iz}(N)\to c_{iz}$ for all $i$.
--   4. If the chain of $d$ has a positive recurrent class $R$ with finite average cost $J_R$, the AS is **conforming on $R$** if $\pi_i(N)\to\pi_i$ and $J(i)(N)\to J_R$ for $i\in R$.
--
--   These definitions carry the chapter's hypotheses on how the finite models approximate $\Delta$.
--
--   **Formalization Note** Transition probabilities and quantities of $\Delta_N$ are extended by junk values (`0`) when $N<N_0$ or a state lies outside $S_N$; for each fixed state this affects only finitely many $N$ and hence no limit. $J_R$ is taken as the average cost of the chain of $d$ at $i\in R$, which is constant on $R$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 28 Definition 2.5.1, p. 29 Definition 2.5.3, p. 171, p. 290 Definition B.4, pp. 307–308 Definitions C.4.8, C.4.10

import Mathlib
import Definitions.Def_SennottDP_AvgASM_Criteria
import Definitions.Def_SennottDP_AvgASM_MarkovChain

namespace SennottDP.AvgASM

open scoped ENNReal NNReal Topology
open Filter
open Classical

variable {S : Type*} {Act : Type*} [Countable S]

/-- An approximating sequence (AS) `(Δ_N)_{N ≥ N₀}` for `Δ` (Definition 2.5.1, p. 28). The state
spaces `S_N` (`N ≥ N₀`) are finite nonempty subsets of `S`, increasing in `N`, with
`⋃_N S_N = S`. `Δ_N` has state space `S_N`, the same action sets `A_i` and costs `C(i, a)` as `Δ`
for `i ∈ S_N`, and transition probabilities `P_ij(a; N)`: for `i ∈ S_N` and `a ∈ A_i` a probability
distribution on `S_N`, with `lim_{N → ∞} P_ij(a; N) = P_ij(a)` for `i, j ∈ S` (2.17).
The values `PN N i a j` with `N < N₀`, `i ∉ S_N` or `j ∉ S_N` are not part of the model; for fixed
`i, j` they occur for only finitely many `N`, so they do not affect the limit (2.17). -/
structure ApproxSeq (M : MDC S Act) where
  /-- the first index `N₀` -/
  N₀ : ℕ
  /-- the state space `S_N` of `Δ_N` -/
  SN : ℕ → Finset S
  /-- `S_N` is nonempty for `N ≥ N₀` -/
  SN_nonempty : ∀ N, N₀ ≤ N → (SN N).Nonempty
  /-- `S_N ⊆ S_{N'}` for `N₀ ≤ N ≤ N'` -/
  SN_mono : ∀ N N', N₀ ≤ N → N ≤ N' → SN N ⊆ SN N'
  /-- `⋃_{N ≥ N₀} S_N = S` -/
  SN_cover : ∀ i, ∃ N, N₀ ≤ N ∧ i ∈ SN N
  /-- the transition probabilities `P_ij(a; N)` of `Δ_N` -/
  PN : ℕ → S → Act → S → ℝ≥0∞
  /-- `P_·(a; N)` is a probability distribution on `S_N` for `i ∈ S_N`, `a ∈ A_i` -/
  PN_sum : ∀ N, N₀ ≤ N → ∀ i ∈ SN N, ∀ a ∈ M.A i, ∑ j ∈ SN N, PN N i a j = 1
  /-- (2.17): `P_ij(a; N) → P_ij(a)` as `N → ∞` -/
  PN_tendsto : ∀ i, ∀ a ∈ M.A i, ∀ j, Tendsto (fun N => PN N i a j) atTop (𝓝 (M.P i a j))

namespace ApproxSeq

variable {M : MDC S Act} (AS : ApproxSeq M)

/-- The MDC `Δ_N` (`N ≥ N₀`) on the finite state space `S_N` (Definition 2.5.1). -/
noncomputable def toMDC (N : ℕ) (hN : AS.N₀ ≤ N) : MDC (AS.SN N) Act where
  A i := M.A i.1
  A_nonempty i := M.A_nonempty i.1
  C i a := M.C i.1 a
  P i a j := AS.PN N i.1 a j.1
  P_sum i a ha := by
    rw [Finset.tsum_subtype (AS.SN N) (fun j => AS.PN N i.1 a j)]
    exact AS.PN_sum N hN i.1 i.2 a ha

/-- The `n`-horizon value function `v^N_n(i)` of `Δ_N` (terminal cost `0`, `α = 1`) at `i ∈ S_N`,
`N ≥ N₀`. Convention: for `N < N₀` or `i ∉ S_N`, where `v^N_n(i)` is undefined, the value is `0`;
for each fixed `i` this happens for only finitely many `N`. -/
noncomputable def valueN (n N : ℕ) (i : S) : ℝ≥0∞ :=
  if h : AS.N₀ ≤ N ∧ i ∈ AS.SN N then horizonValue (AS.toMDC N h.1) n ⟨i, h.2⟩ else 0

/-- The `α`-discounted value function `V^N_α(i)` of `Δ_N` at `i ∈ S_N`, `N ≥ N₀` (`0` otherwise,
as for `valueN`). -/
noncomputable def discValueN (α : ℝ) (N : ℕ) (i : S) : ℝ≥0∞ :=
  if h : AS.N₀ ≤ N ∧ i ∈ AS.SN N then discValue (AS.toMDC N h.1) α ⟨i, h.2⟩ else 0

/-- `e N` is a stationary policy for `Δ_N` for every `N ≥ N₀`: `e N i ∈ A_i` for `i ∈ S_N`
(only these values of `e N` are part of the policy). -/
def IsStationarySeq (e : ℕ → S → Act) : Prop :=
  ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, e N i ∈ M.A i

/-- Definition B.4, p. 290: the stationary policy `f` for `Δ` is a limit point of the sequence
`(e^N)` of stationary policies for `(Δ_N)` if there is a subsequence `N_r` such that, given
`i ∈ S`, `e^{N_r}(i) = f(i)` for sufficiently large `r`. -/
def IsLimitPoint (_AS : ApproxSeq M) (e : ℕ → S → Act) (f : StationaryPolicy M) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∀ᶠ r in atTop, e (φ r) i = f.f i

/-- The AS is an augmentation type approximating sequence (ATAS) with augmentation distributions
`q` (Definition 2.5.3, p. 29): for `N ≥ N₀`, `i ∈ S_N`, `a ∈ A_i` and `r ∉ S_N`,
`(q N i a r j)_{j ∈ S_N}` is a probability distribution on `S_N`, and
`P_ij(a; N) = P_ij(a) + ∑_{r ∉ S_N} P_ir(a) q_j(i, a, r, N)` for `j ∈ S_N` (2.19). -/
def IsATASWith (q : ℕ → S → Act → S → S → ℝ≥0∞) : Prop :=
  (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ a ∈ M.A i, ∀ r, r ∉ AS.SN N →
    ∑ j ∈ AS.SN N, q N i a r j = 1) ∧
  ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ a ∈ M.A i, ∀ j ∈ AS.SN N,
    AS.PN N i a j = M.P i a j + ∑' r : {r : S // r ∉ AS.SN N}, M.P i a r.1 * q N i a r.1 j

/-- The ATAS with augmentation distributions `q` sends excess probability to the set `G`
(pp. 29–30): `∑_{j ∈ G ∩ S_N} q_j(i, a, r, N) = 1` always. -/
def SendsExcessTo (q : ℕ → S → Act → S → S → ℝ≥0∞) (G : Set S) : Prop :=
  ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ a ∈ M.A i, ∀ r, r ∉ AS.SN N →
    ∑ j ∈ (AS.SN N).filter (· ∈ G), q N i a r j = 1

/-- The transition matrix on `S_N` of the Markov chain induced in `Δ_N` by the restriction `d|N`
of a stationary policy `d` of `Δ`: `P_ij(d|N) = P_ij(d(i); N)` for `i, j ∈ S_N` (p. 171). The
sequence `(Γ_N)` of these chains is the approximating sequence of the chain induced by `d`
(Definition C.4.1). -/
def restrictChain (d : StationaryPolicy M) (N : ℕ) : AS.SN N → AS.SN N → ℝ≥0∞ :=
  fun i j => AS.PN N i.1 (d.f i.1) j.1

/-- The cost function of the chain induced by `d|N` on `S_N`. -/
def restrictCost (d : StationaryPolicy M) (N : ℕ) : AS.SN N → ℝ≥0∞ :=
  fun i => (M.C i.1 (d.f i.1) : ℝ≥0∞)

/-- `m_{iz}(N)`, the expected first passage time from `i` to `z` in the chain induced by `d|N`
(for `i, z ∈ S_N`; `0` otherwise, which happens for only finitely many `N`). -/
noncomputable def meanPassageN (d : StationaryPolicy M) (z : S) (N : ℕ) (i : S) : ℝ≥0∞ :=
  if h : i ∈ AS.SN N ∧ z ∈ AS.SN N then
    meanPassage (AS.restrictChain d N) {⟨z, h.2⟩} ⟨i, h.1⟩ else 0

/-- `c_{iz}(N)`, the expected first passage cost from `i` to `z` in the chain induced by `d|N`
(for `i, z ∈ S_N`; `0` otherwise). -/
noncomputable def passageCostN (d : StationaryPolicy M) (z : S) (N : ℕ) (i : S) : ℝ≥0∞ :=
  if h : i ∈ AS.SN N ∧ z ∈ AS.SN N then
    passageCost (AS.restrictChain d N) (AS.restrictCost d N) {⟨z, h.2⟩} ⟨i, h.1⟩ else 0

/-- `π_i(N)`, the steady state probability of `i` in the chain induced by `d|N` (for `i ∈ S_N`;
`0` otherwise). -/
noncomputable def steadyStateN (d : StationaryPolicy M) (N : ℕ) (i : S) : ℝ≥0∞ :=
  if h : i ∈ AS.SN N then steadyState (AS.restrictChain d N) ⟨i, h⟩ else 0

/-- `J(i)(N)`, the average cost from `i` of the chain induced by `d|N` (for `i ∈ S_N`; `0`
otherwise). -/
noncomputable def chainAvgCostN (d : StationaryPolicy M) (N : ℕ) (i : S) : ℝ≥0∞ :=
  if h : i ∈ AS.SN N then chainAvgCost (AS.restrictChain d N) (AS.restrictCost d N) ⟨i, h⟩
  else 0

/-- Definition C.4.8, p. 307, for the chain induced by a `z` standard policy `d` (p. 171): the AS
is **conforming at `d`** if (i) there exists `N*` such that for `N ≥ N*` (and `N ≥ N₀`) the chain induced by
`d|N` is unichain with `z` an element of its positive recurrent class, and (ii)
`m_{iz}(N) → m_{iz}` and `c_{iz}(N) → c_{iz}` for all `i`. -/
def IsConformingAt (d : StationaryPolicy M) (z : S) : Prop :=
  (∃ Nstar, ∀ N, Nstar ≤ N → AS.N₀ ≤ N → ∃ hz : z ∈ AS.SN N, IsUnichainWith (AS.restrictChain d N) ⟨z, hz⟩) ∧
  ∀ i, Tendsto (fun N => AS.meanPassageN d z N i) atTop (𝓝 (meanPassage d.chain {z} i)) ∧
    Tendsto (fun N => AS.passageCostN d z N i) atTop (𝓝 (passageCost d.chain d.cost {z} i))

/-- Definition C.4.10, p. 308, for the chain induced by a stationary policy `d` (p. 171): `R` is a
positive recurrent class of the chain induced by `d`, with finite average cost `J_R`, and the AS
is **conforming on `R`**: for `i ∈ R`, `π_i(N) → π_i` and `J(i)(N) → J_R`. (`J_R` is the value at
`i` of the average cost of the chain induced by `d`, which is constant on `R`, Proposition
C.2.1(i).) -/
def IsConformingOn (d : StationaryPolicy M) (R : Set S) : Prop :=
  IsPosRecClass d.chain R ∧ (∀ i ∈ R, chainAvgCost d.chain d.cost i < ⊤) ∧
  ∀ i ∈ R, Tendsto (fun N => AS.steadyStateN d N i) atTop (𝓝 (steadyState d.chain i)) ∧
    Tendsto (fun N => AS.chainAvgCostN d N i) atTop (𝓝 (chainAvgCost d.chain d.cost i))

end ApproxSeq

end SennottDP.AvgASM


