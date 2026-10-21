-- Prove2me | Definitions.Def_BlottoLP_Flow_Model
-- name    : BlottoLP_Flow_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:07.464969+00:00
-- url     : https://prove2.me/theorems/25ac62c6-6974-46ca-abf9-82d9509e78fb
-- title:
--   §2–§4, pp. 4–10 — discrete Colonel Blotto: allocations, mixed strategies, Nash equilibria, marginals 𝒫_A, layered-graph flows, LP1 rows
-- statement:
--   **The game.** An instance of Colonel Blotto has $K$ battlefields, $A$ troops for player A, $B$ troops for player B, and per-battlefield payoffs: $U_k(i,l)\in\mathbb R$ is player A's payoff on battlefield $k$ when A puts $i$ troops and B puts $l$ troops there; B's payoff there is $-U_k(i,l)$ (zero-sum). A **pure strategy** of a player with $N$ troops is an allocation $x=(x_1,\dots,x_K)$ of non-negative integers with $x_1+\dots+x_K=N$. Player A's payoff under pure strategies $x,y$ is $U(x,y)=\sum_{k}U_k(x_k,y_k)$. Mixed strategies, expected payoffs and Nash equilibria are those of this finite zero-sum game; $R_A$ is the set of A's mixed strategies occurring in a Nash equilibrium.
--
--   **Marginals.** For a mixed strategy $\sigma$ of a player with $N$ troops, $\hat x=G(\sigma)$ is the vector with entries $\hat x_{k,j}=\Pr_\sigma[x_k=j]$, $1\le k\le K$, $0\le j\le N$. The set of **Nash-equilibrium marginals** of A is
--   $$
--   \mathcal P_A=\{\hat x \mid \exists\, \sigma\in R_A,\ G_A(\sigma)=\hat x\}\subseteq\mathbb R^{K\times(A+1)}.
--   $$
--
--   **Layered graph and canonical paths (Definitions 4.1–4.2).** The layered graph of a player with $N$ troops has vertices $v_{i,j}$, $0\le i\le K$, $0\le j\le N$, and an edge from $v_{i-1,j}$ to $v_{i,l}$ whenever $1\le i\le K$ and $j\le l$. A **canonical path** is a directed path from $v_{0,0}$ to $v_{K,N}$, recorded as its vertex sequence $s_0=0\le s_1\le\dots\le s_K=N$. The **prefix path** of a pure strategy $x$ visits $v_{k,s_k}$ with $s_k=x_1+\dots+x_k$.
--
--   **Flows.** For edge values $F\ge 0$ on the layered graph, $F$ is a **unit flow** when it satisfies the constraints (a) of Linear Program 1: inflow equals outflow at every vertex of the layers $1,\dots,K-1$; nothing leaves $v_{0,l}$ for $l>0$; one unit leaves $v_{0,0}$; one unit enters $v_{K,N}$. The **flow of a mixed strategy** $\sigma$ puts on the edge $v_{k-1,i}\to v_{k,j}$ the probability $\Pr_\sigma[s_{k-1}=i,\ s_k=j]$. The **marginal of a flow** is eq. (3): $P_{k,j}=\sum_{i=0}^{N-j}F_{k,i,i+j}$, the total flow on the layer-$k$ edges that rise by $j$.
--
--   **Payoff rows of LP1.** For marginals $\hat x$ of A, eq. (4) gives B's expected payoff on battlefield $k$ with $i$ troops,
--   $$
--   W^B_{k,i}=\sum_{l=0}^{A}\hat x_{k,l}\,U^B_k(i,l),\qquad U^B_k(i,l)=-U_k(l,i).
--   $$
--   For edge weights $W$ on the layered graph of a player with $N$ troops, $D=(D_{k,i})$ is a **dynamic-programming bound** when
--   $$
--   D_{0,0}=0,\qquad D_{k,i}\ge D_{k-1,j}+W_{k,i-j}\quad (1\le k\le K,\ 0\le j\le i\le N).
--   $$
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note** Battlefields are 0-based in Lean (`Fin K`); the paper's battlefield $k$ is Lean's $k-1$, and the paper's flow variable $F_{k,i,j}$ lives on the Lean edge $(k-1,i,j)$ from layer $k-1$ to layer $k$. Pure strategies are maps `Fin K → Fin (N+1)` summing to $N$; mixed strategies are real weight functions; the marginal space is indexed by `Fin K × Fin (A+1)`. Edges with $i>j$ do not exist (the edge type excludes them). `U k i l` is A's payoff with A's troops first, so $W^B_{k,i}=\sum_l \hat x_{k,l}\,(-U_k(l,i))$. The payoff on battlefield $k$ depends only on the troops placed there, as eq. (4) uses. **Correction of LP1-(b):** the printed row "$D^B_{0,i}=0$ for all $0\le i\le B$" is replaced by $D_{0,0}=0$ alone ($D_{0,i}$, $i>0$, free). With the printed row the dynamic programme admits paths starting at $v_{0,i}$, i.e. allocations of only $B-i$ troops, and LP1 can miss the game value (example: $K=2$, $A=B=1$, rows indexing A's troops and columns B's, $U_1=\begin{pmatrix}0&-20\\0&5\end{pmatrix}$, $U_2=\begin{pmatrix}0&5\\10&-10\end{pmatrix}$, value $5$, printed LP1 optimum $2$). The DP row is also written with $W_{k,i-j}$ (the printed $W^B_{k-1,i-j}$ is an index slip) and $\mathcal P_A$ is defined from the Nash equilibria, never as the projection of the LP.
-- source:
--   Behnezhad, Dehghani, Derakhshan, Hajiaghayi, Seddighin, Faster and Simpler Algorithm for Optimal Strategies of Blotto Game, arXiv preprint (arXiv:1612.04029, PDF of 2016-12-28), pp. 4–10: §2 (G_A, R_A, 𝒫_A), §3 p. 5 (pure strategies), Definition 4.1 and Definition 4.2 p. 7, proof of Lemma 4.3 p. 7 (prefix sums), Corollary 4.4 p. 8, eqs. (3)–(4) p. 9, Linear Program 1 p. 10

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum

namespace BlottoLP.Flow

open Finset

/-- An instance of the discrete Colonel Blotto game: `K` battlefields, `A` troops of player A,
`B` troops of player B, and the per-battlefield payoffs: `U k i l` is player A's payoff on
battlefield `k` when A puts `i` troops and B puts `l` troops there. The game is zero-sum, so B's
payoff on battlefield `k` is `- U k i l`. Battlefields are 0-based (`Fin K`). -/
structure Instance where
  K : ℕ
  A : ℕ
  B : ℕ
  U : Fin K → ℕ → ℕ → ℝ

/-- Pure strategies of a player with `N` troops on `K` battlefields: allocations
`x : Fin K → {0, …, N}` of exactly `N` troops. -/
abbrev Pure (K N : ℕ) := {x : Fin K → Fin (N + 1) // ∑ k, (x k : ℕ) = N}

/-- Player A's total payoff for the pure profile `(x, y)`: the sum over battlefields of the
per-battlefield payoffs. -/
def payoff (I : Instance) (x : Pure I.K I.A) (y : Pure I.K I.B) : ℝ :=
  ∑ k, I.U k (x.1 k) (y.1 k)

/-- Player A's expected payoff when A uses the weights `σ` on its pure strategies and B uses `τ`
(B's expected payoff is its negative). -/
def expPayoff (I : Instance) (σ : Pure I.K I.A → ℝ) (τ : Pure I.K I.B → ℝ) : ℝ :=
  expPay (payoff I) σ τ

/-- `R_A`: the mixed strategies of player A that occur in a Nash equilibrium of the instance. -/
def RA (I : Instance) : Set (Pure I.K I.A → ℝ) := nashRow (payoff I)

/-- The map `G`: `marginal σ (k, j)` is the probability that the mixed strategy `σ` puts `j`
troops on battlefield `k`. -/
def marginal {K N : ℕ} (σ : Pure K N → ℝ) : Fin K × Fin (N + 1) → ℝ :=
  fun kj => ∑ x ∈ univ.filter (fun x : Pure K N => x.1 kj.1 = kj.2), σ x

/-- `𝒫_A = G_A(R_A)`: the marginals of the Nash-equilibrium strategies of player A. -/
def PA (I : Instance) : Set (Fin I.K × Fin (I.A + 1) → ℝ) := marginal '' RA I

/-- Edges of the layered graph `L` of a player with `N` troops (Definition 4.1): the edge
`⟨(k, i, j), _⟩` goes from `v_{k,i}` to `v_{k+1,j}` (`k : Fin K`, `0 ≤ i ≤ j ≤ N`). The paper's
battlefield `k` (1-based) is Lean's `k - 1`; its flow variable `F_{k,i,j}` lives on Lean's edge
`(k - 1, i, j)`. -/
abbrev Edge (K N : ℕ) := {e : Fin K × Fin (N + 1) × Fin (N + 1) // e.2.1 ≤ e.2.2}

/-- Canonical paths (Definition 4.2), given by their vertex sequence: `s k` is the vertex of
layer `k` visited by the path. The path starts at `v_{0,0}`, ends at `v_{K,N}`, and each step
`v_{k,s k} → v_{k+1,s (k+1)}` is an edge of the layered graph. -/
abbrev CanonicalPath (K N : ℕ) :=
  {s : Fin (K + 1) → Fin (N + 1) //
    s 0 = 0 ∧ s (Fin.last K) = Fin.last N ∧ ∀ k : Fin K, s k.castSucc ≤ s k.succ}

/-- Troops on the first `k` battlefields (Lean battlefields `0, …, k - 1`) under `x`. -/
def prefixSum {K N : ℕ} (x : Pure K N) (k : Fin (K + 1)) : ℕ :=
  ∑ k' ∈ univ.filter (fun k' : Fin K => (k' : ℕ) < (k : ℕ)), (x.1 k' : ℕ)

theorem prefixSum_le {K N : ℕ} (x : Pure K N) (k : Fin (K + 1)) : prefixSum x k ≤ N :=
  (Finset.sum_le_sum_of_subset (filter_subset _ _)).trans_eq x.2

/-- The canonical path of a pure strategy (proof of Lemma 4.3): layer `k` is visited at the
vertex `s_k`, the number of troops on the first `k` battlefields. -/
def prefixPath {K N : ℕ} (x : Pure K N) : CanonicalPath K N :=
  ⟨fun k => ⟨prefixSum x k, Nat.lt_succ_of_le (prefixSum_le x k)⟩, by
    refine ⟨?_, ?_, ?_⟩
    · ext; simp [prefixSum]
    · ext
      simp only [Fin.val_last]
      refine Eq.trans ?_ x.2
      unfold prefixSum
      congr 1
      ext k'
      simp
    · intro k
      show prefixSum x k.castSucc ≤ prefixSum x k.succ
      apply Finset.sum_le_sum_of_subset
      intro a ha
      simp only [mem_filter, mem_univ, true_and, Fin.val_castSucc, Fin.val_succ] at ha ⊢
      omega⟩

/-- Flow of the layer-`k` edges into the vertex `v_{k+1,l}`. -/
def inflow {K N : ℕ} (F : Edge K N → ℝ) (k : Fin K) (l : Fin (N + 1)) : ℝ :=
  ∑ e ∈ univ.filter (fun e : Edge K N => e.1.1 = k ∧ e.1.2.2 = l), F e

/-- Flow of the layer-`k` edges out of the vertex `v_{k,l}`. -/
def outflow {K N : ℕ} (F : Edge K N → ℝ) (k : Fin K) (l : Fin (N + 1)) : ℝ :=
  ∑ e ∈ univ.filter (fun e : Edge K N => e.1.1 = k ∧ e.1.2.1 = l), F e

/-- The membership constraints (a) of Linear Program 1, 0-based: `F` is a flow of size `1` from
`v_{0,0}` to `v_{K,N}` in the layered graph. Flows are non-negative; at every vertex of the
layers `1, …, K - 1` the inflow equals the outflow; nothing leaves `v_{0,l}` for `l > 0`; one
unit leaves `v_{0,0}`; one unit enters `v_{K,N}`. -/
def IsUnitFlow {K N : ℕ} (F : Edge K N → ℝ) : Prop :=
  (∀ e, 0 ≤ F e) ∧
  (∀ (k k' : Fin K), (k' : ℕ) = k + 1 → ∀ l, inflow F k l = outflow F k' l) ∧
  (∀ k : Fin K, (k : ℕ) = 0 → ∀ l : Fin (N + 1), 0 < l → outflow F k l = 0) ∧
  (∀ k : Fin K, (k : ℕ) = 0 → outflow F k 0 = 1) ∧
  (∀ k : Fin K, (k : ℕ) + 1 = K → inflow F k (Fin.last N) = 1)

/-- The flow of a mixed strategy (Corollary 4.4): every pure strategy sends its probability along
its canonical path, so the edge `v_{k,i} → v_{k+1,j}` carries the probability that the first `k`
battlefields hold `i` troops and the first `k + 1` hold `j`. -/
def flowOf {K N : ℕ} (σ : Pure K N → ℝ) : Edge K N → ℝ :=
  fun e => ∑ x ∈ univ.filter (fun x : Pure K N =>
    (prefixPath x).1 e.1.1.castSucc = e.1.2.1 ∧ (prefixPath x).1 e.1.1.succ = e.1.2.2), σ x

/-- Eq. (3): the probability `P_{k,j}` of putting `j` troops on battlefield `k`, read off a flow:
the total flow on the layer-`k` edges `v_{k,i} → v_{k+1,i+j}`. -/
def flowMarginal {K N : ℕ} (F : Edge K N → ℝ) : Fin K × Fin (N + 1) → ℝ :=
  fun kj => ∑ e ∈ univ.filter (fun e : Edge K N =>
    e.1.1 = kj.1 ∧ (e.1.2.2 : ℕ) = e.1.2.1 + kj.2), F e

/-- Eq. (4): `W^B_{k,i}`, player B's expected payoff on battlefield `k` when B puts `i` troops
there and player A's marginals are `x̂`: `Σ_l x̂(k,l) · U^B_k(i,l)` with `U^B_k(i,l) = - U k l i`. -/
def weightB (I : Instance) (xhat : Fin I.K × Fin (I.A + 1) → ℝ) :
    Fin I.K → Fin (I.B + 1) → ℝ :=
  fun k i => ∑ l : Fin (I.A + 1), xhat (k, l) * (- I.U k l i)

/-- The dynamic-programming rows of Linear Program 1-(b), in corrected form: `D_{0,0} = 0`
(the values `D_{0,i}`, `i > 0`, are free) and `D_{k+1,i} ≥ D_{k,j} + W_{k,i-j}` for all
`j ≤ i`, on the layered graph of a player with `N` troops with edge weights `W`. -/
def IsDPBound {K N : ℕ} (W : Fin K → Fin (N + 1) → ℝ) (D : Fin (K + 1) → Fin (N + 1) → ℝ) :
    Prop :=
  D 0 0 = 0 ∧
  ∀ (k : Fin K) (i j t : Fin (N + 1)), (j : ℕ) + t = i →
    D k.castSucc j + W k t ≤ D k.succ i

end BlottoLP.Flow


