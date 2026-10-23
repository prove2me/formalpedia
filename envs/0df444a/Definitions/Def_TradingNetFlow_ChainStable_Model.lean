-- Prove2me | Definitions.Def_TradingNetFlow_ChainStable_Model
-- name    : TradingNetFlow_ChainStable_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:46.594034+00:00
-- url     : https://prove2.me/theorems/ac1bc97a-6f08-46df-ab01-63e3e3c79b2d
-- title:
--   §2, §3.2, §5, PDF 5–16 — trading network, M♮-concave valuations, competitive equilibrium, efficiency, chain stability, contraction
-- statement:
--   This file sets up the trading-network model of Candogan, Epitropou and Vohra and the solution concepts their equivalence theorem is about.
--
--   **Trading network.** A trading network is a directed multigraph $G=(N,E)$: the vertices $N$ are agents and each arc $e\in E$ is a trade that can take place between its two endpoints, the source $e^+$ being the seller and the sink $e^-$ the buyer. Both $N$ and $E$ are finite. For an agent $i$, $\delta^+(i)$ is the set of trades in which $i$ sells, $\delta^-(i)$ the set in which $i$ buys, and $\delta(i)=\delta^+(i)\cup\delta^-(i)$. An *outcome* is a set of trades $X\subseteq E$, and a *price vector* is $p\in\mathbb R^E$.
--
--   **Utility and demand.** Agent $i$ has a valuation $w_i:2^{\delta(i)}\to\mathbb R$ and utility
--   $$u_i(S,p)=w_i(S)+\sum_{e\in S\cap\delta^+(i)}p_e-\sum_{e\in S\cap\delta^-(i)}p_e,\qquad S\subseteq\delta(i).$$
--   For a set of trades $T\subseteq E$, the demand of $i$ *restricted to* $T$ is
--   $$D_i(p^T)=\operatorname{arg\,max}\{u_i(Y,p):Y\subseteq T\cap\delta(i)\};$$
--   for $T=E$ this is the ordinary demand $D_i(p)$.
--
--   **Competitive equilibrium and efficiency (Definitions 2.1, 2.2).** $(X,p)$ is a competitive equilibrium if $X\cap\delta(i)\in D_i(p)$ for every agent $i$. The welfare of $S\subseteq E$ is $\sum_{i\in N}w_i(S\cap\delta(i))$, and $X$ is efficient if it maximizes welfare over all $S\subseteq E$.
--
--   **Standing assumptions (§3.2).** Represent a set $S\subseteq\delta(i)$ by its signed characteristic vector $y\in\mathbb Z^{\delta(i)}$ with $y_e=1$ for $e\in S\cap\delta^+(i)$, $y_e=-1$ for $e\in S\cap\delta^-(i)$ and $y_e=0$ otherwise, and extend $w_i$ to $\mathbb Z^{\delta(i)}$ by $w_i(x)=-\infty$ off the box $\{0,-1\}^{\delta^-(i)}\times\{0,1\}^{\delta^+(i)}$. The model assumes that every $w_i$ is M$^\natural$-concave in this representation, which is equivalent to full substitutability. It also assumes that the seller and the buyer of each trade are different agents.
--
--   **Chain stability (§5, Definition 5.3).** An outcome $X$ with prices $p^X$ (only the coordinates on $X$ matter) is *individually rational* if $X\cap\delta(i)\in D_i(p^X)$ for every $i$, where the demand is restricted to $X$. A *chain* is a nonempty set of distinct trades $e_1,\dots,e_m$ with $e_k^-=e_{k+1}^+$ for $k=1,\dots,m-1$; it may close into a cycle. A chain $Z$ with prices $p^Z$ is a *blocking chain* of $(X,p^X)$ if $Z\cap X=\emptyset$ and, for every agent $i$ involved in $Z$ (that is, $Z\cap\delta(i)\neq\emptyset$), every $Y^i\in D_i(p^{Z\cup X})$ contains $Z\cap\delta(i)$. Here $p^{Z\cup X}$ uses $p^X$ on $X$ and $p^Z$ on $Z$, and the demand is restricted to $Z\cup X$. $(X,p^X)$ is *chain stable* if it is individually rational and has no blocking chain.
--
--   **Contraction (eq. (6)).** Given $(X,p^X)$, the contraction $G^X=(N,E\setminus X)$ keeps the sellers and buyers of the remaining trades and gives agent $i$ the valuation
--   $$\hat w_i(S)=\max_{Y\subseteq X\cap\delta(i)}\Big[w_i(S\cup Y)+\sum_{e\in Y\cap\delta^+(i)}p^X_e-\sum_{e\in Y\cap\delta^-(i)}p^X_e\Big],\qquad S\subseteq\delta(i)\setminus X.$$
--
--   These definitions are shared by every statement of the mission: Theorems 4.1 and 4.3, Lemma 5.5, Corollary 5.6, two steps of the proof of Theorem 5.8, and Theorem 5.8 itself.
--
--   **Formalization Note.** Agents and trades are finite types `N`, `E` with decidable equality. A valuation is a function `w i : Finset E → ℝ`. It is only ever evaluated on subsets of $\delta(i)$, and its values on other sets are never read. Prices are total functions `E → ℝ`. In a blocking chain only the coordinates of $p^X$ on $X$ and of $p^Z$ off $X$ are read. M$^\natural$-concavity is the platform definition `DiscreteConvex.EconomicEquilibrium.MNaturalConcave` (Murota's exchange axiom with values in $\mathbb R\cup\{-\infty\}$), applied to the signed representation `wSigned`, which reads the set off the support of the vector. The paper's word "feasible" in Definition 5.3 has no content here because valuations are real valued on every subset, so it is dropped. Chains are encoded as a duplicate-free nonempty list of trades in which the buyer of each trade is the seller of the next. The contraction's trades are the subtype `{e // e ∉ X}`, and the maximum in (6) is a `Finset.sup'` over the subsets of $X\cap\delta(i)$. The assumption that seller and buyer differ is a reading of §2's "a trade that can take place between the incident pair of vertices", and it is needed for the signed representation to be well defined.
-- source:
--   Candogan, Epitropou & Vohra, Competitive Equilibrium and Trading Networks: A Network Flow Approach, IHS Economics Series Working Paper 323 (Aug. 2016), PDF pp. 5–16, Definitions 2.1, 2.2, 5.3, §2, §3.1–3.2, §5, eq. (6)

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_MNaturalConcave

namespace TradingNetFlow.ChainStable

open Finset

/-- A trading network (Candogan–Epitropou–Vohra, §2, PDF p. 5–6): a directed multigraph with agents
`N` as vertices and trades `E` as arcs; `seller e` is the source `e⁺`, `buyer e` the sink `e⁻`, and
`w i` is agent `i`'s valuation (only ever evaluated on subsets of `δ(i)`). -/
structure Economy (N E : Type*) where
  seller : E → N
  buyer : E → N
  w : N → Finset E → ℝ

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

/-- `δ⁺(i)`: the trades in which `i` is the seller. -/
def Economy.deltaOut (G : Economy N E) (i : N) : Finset E := univ.filter (fun e => G.seller e = i)

/-- `δ⁻(i)`: the trades in which `i` is the buyer. -/
def Economy.deltaIn (G : Economy N E) (i : N) : Finset E := univ.filter (fun e => G.buyer e = i)

/-- `δ(i) = δ⁺(i) ∪ δ⁻(i)`. -/
def Economy.delta (G : Economy N E) (i : N) : Finset E := G.deltaOut i ∪ G.deltaIn i

/-- `u_i(S, p) = w_i(S) + ∑_{e ∈ S ∩ δ⁺(i)} p_e − ∑_{e ∈ S ∩ δ⁻(i)} p_e`. -/
def Economy.utility (G : Economy N E) (i : N) (S : Finset E) (p : E → ℝ) : ℝ :=
  G.w i S + ∑ e ∈ S ∩ G.deltaOut i, p e - ∑ e ∈ S ∩ G.deltaIn i, p e

/-- `D_i(p^T)`: agent `i`'s demand when restricted to the trades in `T`, i.e. the maximizers of
`u_i(·, p)` over `Y ⊆ T ∩ δ(i)`. With `T = univ` this is the unrestricted demand `D_i(p)`. -/
def Economy.demandOn (G : Economy N E) (i : N) (T : Finset E) (p : E → ℝ) : Set (Finset E) :=
  {Y | Y ⊆ T ∩ G.delta i ∧ ∀ Y' ⊆ T ∩ G.delta i, G.utility i Y' p ≤ G.utility i Y p}

/-- Definition 2.1: `(X, p)` is a competitive equilibrium if `X ∩ δ(i) ∈ D_i(p)` for all `i`. -/
def Economy.IsCompetitiveEquilibrium (G : Economy N E) (X : Finset E) (p : E → ℝ) : Prop :=
  ∀ i, X ∩ G.delta i ∈ G.demandOn i univ p

/-- Total welfare `∑_{i ∈ N} w_i(S ∩ δ(i))`. -/
def Economy.welfare (G : Economy N E) (S : Finset E) : ℝ := ∑ i, G.w i (S ∩ G.delta i)

/-- Definition 2.2: `X` is efficient if it maximizes total welfare over all `S ⊆ E`. -/
def Economy.IsEfficient (G : Economy N E) (X : Finset E) : Prop := ∀ S, G.welfare S ≤ G.welfare X

/-- The sign of trade `e` for agent `i` in the signed representation of §3.2–§4 (PDF p. 8):
`+1` if `i` sells `e`, `−1` otherwise (for `e ∈ δ(i)`: if `i` buys `e`). -/
def Economy.sign (G : Economy N E) (i : N) (e : E) : ℤ := if G.seller e = i then 1 else -1

/-- `w_i` as a function on `ℤ^{δ(i)}` (§3.2, PDF p. 8): on the box
`{0,−1}^{δ⁻(i)} × {0,1}^{δ⁺(i)}` it is `w_i` of the set of trades with nonzero coordinate, and
`−∞` (`⊥`) elsewhere. -/
def Economy.wSigned (G : Economy N E) (i : N) : ({e // e ∈ G.delta i} → ℤ) → WithBot ℝ :=
  fun x =>
    if ∀ e, x e = 0 ∨ x e = G.sign i e.1 then
      ((G.w i ((univ.filter (fun e => x e ≠ 0)).map (Function.Embedding.subtype _)) : ℝ) :
        WithBot ℝ)
    else ⊥

/-- Standing assumptions: every trade is between two distinct agents (model reading of §2), and every
valuation, in the signed representation, is M♮-concave (§3.2, PDF p. 8). -/
def Economy.Standing (G : Economy N E) : Prop :=
  (∀ e, G.seller e ≠ G.buyer e) ∧
    ∀ i, DiscreteConvex.EconomicEquilibrium.MNaturalConcave (G.wSigned i)

/-- Individual rationality (§5, PDF p. 12): each agent demands `X ∩ δ(i)` when restricted to `X`
at prices `p^X`. -/
def Economy.IsIndividuallyRational (G : Economy N E) (X : Finset E) (pX : E → ℝ) : Prop :=
  ∀ i, X ∩ G.delta i ∈ G.demandOn i X pX

/-- A chain (§5, PDF p. 13): a nonempty set of distinct trades `e₁, …, e_m` with
`e_k⁻ = e_{k+1}⁺` for `k = 1, …, m − 1`. -/
def Economy.IsChain (G : Economy N E) (Z : Finset E) : Prop :=
  ∃ l : List E, l ≠ [] ∧ l.Nodup ∧ l.toFinset = Z ∧
    l.IsChain (fun e f => G.buyer e = G.seller f)

/-- The combined price vector `p^{Z ∪ X}`: `p^X` on `X`, `p^Z` elsewhere. -/
def joinPrices (X : Finset E) (pX pZ : E → ℝ) : E → ℝ := fun e => if e ∈ X then pX e else pZ e

/-- `(Z, p^Z)` is a blocking chain of `(X, p^X)` (Definition 5.3, PDF p. 13): `Z` is a nonempty
chain disjoint from `X`, and every agent involved in `Z`, restricted to the trades in `Z ∪ X` at
prices `p^{Z ∪ X}`, includes `Z ∩ δ(i)` in every demanded set. -/
def Economy.IsBlockingChain (G : Economy N E) (X : Finset E) (pX : E → ℝ) (Z : Finset E)
    (pZ : E → ℝ) : Prop :=
  Z.Nonempty ∧ G.IsChain Z ∧ Disjoint Z X ∧
    ∀ i, (Z ∩ G.delta i).Nonempty →
      ∀ Y ∈ G.demandOn i (Z ∪ X) (joinPrices X pX pZ), Z ∩ G.delta i ⊆ Y

/-- Definition 5.3: `(X, p^X)` is chain stable if it is individually rational and no blocking chain
exists. -/
def Economy.IsChainStable (G : Economy N E) (X : Finset E) (pX : E → ℝ) : Prop :=
  G.IsIndividuallyRational X pX ∧ ¬ ∃ Z pZ, G.IsBlockingChain X pX Z pZ

/-- The contraction `G^X` of the economy with respect to `(X, p^X)` (eq. (6), PDF p. 16): trades
`E ∖ X`, same sellers and buyers, and valuations
`ŵ_i(S) = max_{Y ⊆ X ∩ δ(i)} [w_i(S ∪ Y) + ∑_{e ∈ Y ∩ δ⁺(i)} p^X_e − ∑_{e ∈ Y ∩ δ⁻(i)} p^X_e]`. -/
def Economy.contraction (G : Economy N E) (X : Finset E) (pX : E → ℝ) :
    Economy N {e : E // e ∉ X} where
  seller e := G.seller e.1
  buyer e := G.buyer e.1
  w i S := ((X ∩ G.delta i).powerset).sup' ⟨∅, Finset.empty_mem_powerset _⟩ (fun Y =>
    G.w i (S.map (Function.Embedding.subtype _) ∪ Y)
      + ∑ e ∈ Y ∩ G.deltaOut i, pX e - ∑ e ∈ Y ∩ G.deltaIn i, pX e)

end TradingNetFlow.ChainStable


