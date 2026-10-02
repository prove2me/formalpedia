-- Prove2me | Definitions.Def_SennottDP_ChainASM_ApproxSeq
-- name    : SennottDP_ChainASM_ApproxSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T14:27:13.131839+00:00
-- url     : https://prove2.me/theorems/0198c1f1-ac15-46f7-8897-feab78b19003
-- title:
--   Approximating sequences of finite Markov chains, conformity, and augmentation type approximating sequences
-- statement:
--   Let $\Gamma$ be a Markov chain with costs on $S$. An **approximating sequence (AS)** $(\Gamma_N)_{N\ge N_0}$ for $\Gamma$ consists of an increasing sequence $(S_N)_{N\ge N_0}$ of nonempty finite subsets of $S$ with $\bigcup_N S_N=S$, and for each $N$ a Markov chain with costs $\Gamma_N$ on $S_N$: the cost at $i\in S_N$ is $C(i)$, and $(P_{ij}(N))_{j\in S_N}$ is a probability distribution on $S_N$ for each $i\in S_N$, with
--   $$\lim_{N\to\infty}P_{ij}(N)=P_{ij},\qquad i,j\in S.$$
--   Quantities of $\Gamma_N$ are written with $(N)$: ${}_GP^{(t)}_{ik}(N)$, ${}_Gu_{ik}(N)$, $m_{iG}(N)$, $c_{iG}(N)$, $\pi_i(N)$, $J(i)(N)$; a set $G\subseteq S$ is read in $\Gamma_N$ as $G\cap S_N$.
--
--   Assume $\Gamma$ is $z$ standard. The AS is **conforming** if (i) there is $N^*$ such that for $N\ge N^*$ the chain $\Gamma_N$ is unichain with $z$ an element of its positive recurrent class, and (ii) $m_{iz}(N)\to m_{iz}$ and $c_{iz}(N)\to c_{iz}$ for all $i$.
--
--   If $\Gamma$ has a positive recurrent class $R$ with finite average cost $J_R$, the AS is **conforming on $R$** if $\pi_i(N)\to\pi_i$ and $J(i)(N)\to J_R$ for $i\in R$.
--
--   The AS is an **augmentation type approximating sequence (ATAS)** if for $i\in S_N$ and each $r\notin S_N$ there is a probability distribution $(q_j(i,r,N))_{j\in S_N}$ (the augmentation distribution) with
--   $$P_{ij}(N)=P_{ij}+\sum_{r\in S-S_N}P_{ir}\,q_j(i,r,N),\qquad j\in S_N.$$
--   It **sends excess probability to $G$** if $\sum_{j\in G}q_j(i,r,N)=1$ always.
--
--   These are Definitions C.4.1, C.4.8, C.4.10 and C.5.1 of the book; conformity is the property under which the finite chains' first passage moments, steady state probabilities and average costs converge to those of $\Gamma$.
--
--   **Formalization Note** The quantities of $\Gamma_N$ are lifted to functions of $N$ and of states of $S$, with value $0$ when $N<N_0$ or a state argument lies outside $S_N$ (the book sets $\pi_i(N)=0$ for $i\notin S_N$); for fixed states this affects only finitely many $N$. Convergence is in $[0,\infty]$. The conformity predicate includes the standing assumption that $\Gamma$ is $z$ standard, and conformity on $R$ includes that $R$ is a positive recurrent class with $J_R<\infty$. The transition values $P_{ij}(N)$ for $j\notin S_N$ are not part of the model.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 302, Definition C.4.1; p. 307, Definition C.4.8; p. 308, Definition C.4.10 and Definition C.5.1, (C.27)

import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.ChainASM

variable {S : Type*}

/-- Definition C.4.1, p. 302: an approximating sequence (AS) `(Γ_N)_{N ≥ N₀}` for the Markov
chain with costs `Γ`. The state spaces `S_N` (`N ≥ N₀`) are nonempty finite subsets of `S`,
increasing in `N`, with `⋃_N S_N = S`. `Γ_N` is a Markov chain with costs on `S_N`: the cost at
`i ∈ S_N` is `C(i)`, and for `i ∈ S_N` the transition probabilities `(P_{ij}(N))_{j ∈ S_N}` form a
probability distribution on `S_N`, with `lim_{N→∞} P_{ij}(N) = P_{ij}` for `i, j ∈ S`.
The values `PN N i j` with `N < N₀`, `i ∉ S_N` or `j ∉ S_N` are not part of the model; for fixed
`i, j` they occur for only finitely many `N` and do not affect the limit. -/
structure ApproxSeq (Γ : MC S) where
  /-- the first index `N₀` -/
  N₀ : ℕ
  /-- the state space `S_N` of `Γ_N` -/
  SN : ℕ → Finset S
  /-- `S_N` is nonempty for `N ≥ N₀` -/
  SN_nonempty : ∀ N, N₀ ≤ N → (SN N).Nonempty
  /-- `S_N ⊆ S_{N'}` for `N₀ ≤ N ≤ N'` -/
  SN_mono : ∀ N N', N₀ ≤ N → N ≤ N' → SN N ⊆ SN N'
  /-- `⋃_{N ≥ N₀} S_N = S` -/
  SN_cover : ∀ i, ∃ N, N₀ ≤ N ∧ i ∈ SN N
  /-- the transition probabilities `P_{ij}(N)` of `Γ_N` -/
  PN : ℕ → S → S → ℝ≥0∞
  /-- `(P_{ij}(N))_{j ∈ S_N}` is a probability distribution on `S_N` for `i ∈ S_N` -/
  PN_sum : ∀ N, N₀ ≤ N → ∀ i ∈ SN N, ∑ j ∈ SN N, PN N i j = 1
  /-- `P_{ij}(N) → P_{ij}` as `N → ∞`, for `i, j ∈ S` -/
  PN_tendsto : ∀ i j, Tendsto (fun N => PN N i j) atTop (𝓝 (Γ.P i j))

namespace ApproxSeq

open Classical

variable {Γ : MC S} (AS : ApproxSeq Γ)

/-- The Markov chain with costs `Γ_N` (`N ≥ N₀`) on the finite state space `S_N`: transition
probabilities `P_{ij}(N)` and costs `C(i)`, `i, j ∈ S_N` (Definition C.4.1). -/
noncomputable def chain (N : ℕ) (hN : AS.N₀ ≤ N) : MC (AS.SN N) where
  P i j := AS.PN N i.1 j.1
  P_sum i := by
    rw [Finset.tsum_subtype (AS.SN N) (fun j => AS.PN N i.1 j)]
    exact AS.PN_sum N hN i.1 i.2
  C i := Γ.C i.1

/-! Quantities of `Γ_N`, written `m_{iG}(N)`, `π_i(N)`, `J(i)(N)`, … (p. 302), as functions of
`N` and of states of `S`. Convention: when `N < N₀` or a state argument is not in `S_N`, where
the quantity of `Γ_N` is undefined, the value is `0` (as the book does for `π_i(N)`, p. 303); for
fixed states this happens for only finitely many `N`, so no limit statement depends on it. A set
`G ⊆ S` is read in `Γ_N` as `G ∩ S_N`. -/

/-- `_G P^{(t)}_{ik}(N)`, the taboo probability in `Γ_N`. -/
noncomputable def tabooProbN (G : Set S) (t N : ℕ) (i k : S) : ℝ≥0∞ :=
  if h : AS.N₀ ≤ N ∧ i ∈ AS.SN N ∧ k ∈ AS.SN N then
    (AS.chain N h.1).tabooProb (Subtype.val ⁻¹' G) t ⟨i, h.2.1⟩ ⟨k, h.2.2⟩ else 0

/-- `_G u_{ik}(N)`, the expected number of visits to `k` during a first passage from `i` to `G`
in `Γ_N`. -/
noncomputable def visitsN (G : Set S) (N : ℕ) (i k : S) : ℝ≥0∞ :=
  if h : AS.N₀ ≤ N ∧ i ∈ AS.SN N ∧ k ∈ AS.SN N then
    (AS.chain N h.1).visits (Subtype.val ⁻¹' G) ⟨i, h.2.1⟩ ⟨k, h.2.2⟩ else 0

/-- `m_{iG}(N)`, the expected first passage time from `i` to `G` in `Γ_N`. -/
noncomputable def meanPassageN (G : Set S) (N : ℕ) (i : S) : ℝ≥0∞ :=
  if h : AS.N₀ ≤ N ∧ i ∈ AS.SN N then
    (AS.chain N h.1).meanPassage (Subtype.val ⁻¹' G) ⟨i, h.2⟩ else 0

/-- `c_{iG}(N)`, the expected cost of a first passage from `i` to `G` in `Γ_N`. -/
noncomputable def passageCostN (G : Set S) (N : ℕ) (i : S) : ℝ≥0∞ :=
  if h : AS.N₀ ≤ N ∧ i ∈ AS.SN N then
    (AS.chain N h.1).passageCost (Subtype.val ⁻¹' G) ⟨i, h.2⟩ else 0

/-- `π_i(N)`, the steady state probability of `i` in `Γ_N` (`0` for `i ∉ S_N`, p. 303). -/
noncomputable def steadyStateN (N : ℕ) (i : S) : ℝ≥0∞ :=
  if h : AS.N₀ ≤ N ∧ i ∈ AS.SN N then (AS.chain N h.1).steadyState ⟨i, h.2⟩ else 0

/-- `J(i)(N)`, the average cost from `i` in `Γ_N`. -/
noncomputable def avgCostN (N : ℕ) (i : S) : ℝ≥0∞ :=
  if h : AS.N₀ ≤ N ∧ i ∈ AS.SN N then (AS.chain N h.1).avgCost ⟨i, h.2⟩ else 0

/-- Definition C.4.8, p. 307. `Γ` is `z` standard, and the AS is **conforming**: (i) there exists
`N*` such that for `N ≥ N*` the chain `Γ_N` is unichain with `z` an element of its positive
recurrent class (in particular `N ≥ N₀` and `z ∈ S_N`); (ii) `m_{iz}(N) → m_{iz}` and
`c_{iz}(N) → c_{iz}` for all `i`, in `[0, ∞]`. -/
def IsConforming (z : S) : Prop :=
  Γ.IsZStandard z ∧
  (∃ Nstar, ∀ N, Nstar ≤ N →
    ∃ h : AS.N₀ ≤ N ∧ z ∈ AS.SN N, (AS.chain N h.1).IsUnichainWith ⟨z, h.2⟩) ∧
  ∀ i, Tendsto (fun N => AS.meanPassageN {z} N i) atTop (𝓝 (Γ.meanPassage {z} i)) ∧
    Tendsto (fun N => AS.passageCostN {z} N i) atTop (𝓝 (Γ.passageCost {z} i))

/-- Definition C.4.10, p. 308. `R` is a positive recurrent class of `Γ` with finite average cost
`J_R`, and the AS is **conforming on `R`**: for `i ∈ R`, `π_i(N) → π_i` and `J(i)(N) → J_R`. -/
def IsConformingOn (R : Set S) : Prop :=
  Γ.IsPosRecClass R ∧ Γ.classAvgCost R < ⊤ ∧
  ∀ i ∈ R, Tendsto (fun N => AS.steadyStateN N i) atTop (𝓝 (Γ.steadyState i)) ∧
    Tendsto (fun N => AS.avgCostN N i) atTop (𝓝 (Γ.classAvgCost R))

/-- Definition C.5.1, p. 308: the AS is an augmentation type approximating sequence (ATAS) with
augmentation distributions `q`: for `N ≥ N₀`, `i ∈ S_N` and each `r ∉ S_N`,
`(q N i r j)_{j ∈ S_N}` (the book's `q_j(i, r, N)`) is a probability distribution on `S_N`, and
`P_{ij}(N) = P_{ij} + ∑_{r ∈ S − S_N} P_{ir} q_j(i, r, N)` for `j ∈ S_N` ((C.27)). -/
def IsATASWith (q : ℕ → S → S → S → ℝ≥0∞) : Prop :=
  (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ r, r ∉ AS.SN N → ∑ j ∈ AS.SN N, q N i r j = 1) ∧
  ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ j ∈ AS.SN N,
    AS.PN N i j = Γ.P i j + ∑' r : {r : S // r ∉ AS.SN N}, Γ.P i r.1 * q N i r.1 j

/-- The ATAS with augmentation distributions `q` sends excess probability to the set `G`
(p. 308): `∑_{j ∈ G} q_j(i, r, N) = 1` for `N ≥ N₀`, `i ∈ S_N`, `r ∉ S_N` (the sum is over
`G ∩ S_N`, where `q_·(i, r, N)` lives). -/
def SendsExcessTo (q : ℕ → S → S → S → ℝ≥0∞) (G : Set S) : Prop :=
  ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ r, r ∉ AS.SN N →
    ∑ j ∈ (AS.SN N).filter (· ∈ G), q N i r j = 1

end ApproxSeq

end SennottDP.ChainASM


