-- Prove2me | Definitions.Def_SepCostShare_MatroidGame
-- name    : SepCostShare_MatroidGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:24:08.740425+00:00
-- url     : https://prove2.me/theorems/c6e061d8-330d-4c4b-9082-8ce4700ce154
-- title:
--   Matroid games with set-function costs: profiles, $N_e(B)$, total cost $C(B)$, ranks $\mathrm{rk}_i$, $\mathrm{rk}(\mathcal B)$
-- statement:
--   A **matroid game** consists of a finite set $N$ of players, a finite set $E$ of resources, and for every player $i$ a matroid $\mathcal M_i=(E_i,\mathcal B_i)$ with ground set $E_i\subseteq E$ and base family $\mathcal B_i$, such that $E=\bigcup_{i\in N}E_i$. Every resource $e$ carries a shareable cost function $c_e:2^N\to\mathbb R_+$, and every player $i$ has a non-shareable cost $d_{i,e}\ge0$ on every resource $e$.
--
--   1. **Subadditive costs.** $c_e$ is *subadditive* if (1) $c_e(S)\le c_e(T)$ for all $S\subseteq T\subseteq N$, and (2) $c_e(S+\{i\})\le c_e(S)+c_e(\{i\})$ for all $S\subsetneq N$, $i\in N$. A game has subadditive costs if every $c_e$ is subadditive.
--   2. **Profiles.** A strategy profile is $B=(B_1,\dots,B_n)$ with $B_i\in\mathcal B_i$ for every $i$. $N_e(B)=\{i\in N: e\in B_i\}$ is the set of players using $e$, and $c_e(B):=c_e(N_e(B))$.
--   3. **Exchange.** $(B_i+f-e,B_{-i})$ is the profile in which player $i$ replaces $e$ by $f$, with $B_i+f-e=(B_i\setminus\{e\})\cup\{f\}$.
--   4. **Total cost.** $$C(B)=\sum_{e\in\bigcup_{i\in N}B_i}c_e(N_e(B))+\sum_{i\in N}\sum_{e\in B_i}d_{i,e},$$ so only resources used by some player are charged.
--   5. **Ranks.** All bases of $\mathcal M_i$ have the same cardinality $\mathrm{rk}_i$, and $\mathrm{rk}(\mathcal B)=\max_{i\in N}\mathrm{rk}_i$.
--
--   These are the objects of every statement of the mission; uncapacitated facility location games are the special case of uniform rank-one matroids.
--
--   **Formalization Note** Players and resources are finite types; a matroid is Mathlib's `Matroid E`, its ground set is $E_i$, and a profile is a map $N\to$ `Finset E` whose values are bases. $\mathrm{rk}_i$ is the natural-number value of Mathlib's `eRank`, which is finite since $E$ is finite. $c_e$ is defined on all subsets of $N$, including $\emptyset$, and $c_e(\emptyset)>0$ is allowed.
-- source:
--   Harks, Hoefer, Huber & Surek, Efficient Black-Box Reductions for Separable Cost Sharing, arXiv:1802.10351v1, §2, p.5 (players, resources, delays, total cost C(S)); §3, p.6 (matroid game, E = ⋃ Eᵢ, rkᵢ, subadditive costs, cₑ(B) := cₑ(Nₑ(B))); Theorem 5, p.7 (rk(𝓑))

import Mathlib

namespace SepCostShare

/-- **Matroid game with set-function costs**, Harks, Hoefer, Huber & Surek, *Efficient Black-Box
Reductions for Separable Cost Sharing*, arXiv:1802.10351v1, §2, p.5 (players, resources, delays)
and §3, p.6 ("The tupel 𝓜 = (N, E, 𝓑, (cₑ)_{e∈E}, (dᵢ,ₑ)_{e∈E,i∈N}) is called a matroid game if
E = ⋃_{i∈N} Eᵢ, and each set system 𝓑ᵢ ⊆ 2^{Eᵢ} forms the base set of some matroid
𝓜ᵢ = (Eᵢ, 𝓑ᵢ)"; "we allow for general subadditive cost functions cₑ : 2^N → ℝ₊").

* `M i` is the matroid `𝓜ᵢ` of player `i`; its ground set `(M i).E` is `Eᵢ` and its bases are `𝓑ᵢ`.
* `c e S` is the cost `cₑ(S) ≥ 0` of resource `e` when exactly the players of `S` use it.
* `d i e` is the non-shareable player-specific cost `dᵢ,ₑ ≥ 0`.
* `cover` is `E = ⋃_{i∈N} Eᵢ`.

**Formalization Note.** Players and resources are finite types `N`, `E`; `n = |N|`, `m = |E|`.
Subadditivity of `c` is the separate predicate `MatroidGame.Subadditive`. -/
structure MatroidGame (N E : Type*) [Fintype N] [Fintype E] where
  /-- the matroid `𝓜ᵢ = (Eᵢ, 𝓑ᵢ)` of player `i` -/
  M : N → Matroid E
  /-- the shareable cost `cₑ : 2^N → ℝ₊` of resource `e` -/
  c : E → Finset N → ℝ
  /-- the player-specific cost `dᵢ,ₑ` -/
  d : N → E → ℝ
  /-- `E = ⋃_{i∈N} Eᵢ` -/
  cover : ∀ e : E, ∃ i : N, e ∈ (M i).E
  c_nonneg : ∀ (e : E) (S : Finset N), 0 ≤ c e S
  d_nonneg : ∀ (i : N) (e : E), 0 ≤ d i e

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

/-- **Subadditive costs**, arXiv:1802.10351v1, §3, p.6: "cₑ is called subadditive, if it satisfies
(1) cₑ(S) ≤ cₑ(T) for all S ⊆ T ⊆ N, and (2) cₑ(S + {i}) ≤ cₑ(S) + cₑ({i}) for all S ⊂ N, i ∈ N."
Every resource cost function of the game is required to be subadditive. -/
def MatroidGame.Subadditive (G : MatroidGame N E) : Prop :=
  (∀ (e : E) (S T : Finset N), S ⊆ T → G.c e S ≤ G.c e T) ∧
  (∀ (e : E) (S : Finset N), S ⊂ Finset.univ → ∀ i : N, G.c e (insert i S) ≤ G.c e S + G.c e {i})

/-- A **strategy profile** of a matroid game (§3, p.6: "we will write 𝓑ᵢ instead of 𝓢ᵢ"): every
player `i` picks a base `Bᵢ` of its matroid `𝓜ᵢ`. Profiles are maps `N → Finset E`. -/
def MatroidGame.IsProfile (G : MatroidGame N E) (B : N → Finset E) : Prop :=
  ∀ i : N, (G.M i).IsBase (↑(B i) : Set E)

/-- `Nₑ(B) = {i ∈ N : e ∈ Bᵢ}`, the players that allocate resource `e` (§2, p.5). -/
def MatroidGame.users (_G : MatroidGame N E) (e : E) (B : N → Finset E) : Finset N :=
  Finset.univ.filter fun i => e ∈ B i

/-- The profile `(Bᵢ + f − e, B₋ᵢ)` in which player `i` exchanges `e` for `f` (§3, p.6).

**Formalization Note.** `Bᵢ + f − e` is `(Bᵢ ∖ {e}) ∪ {f}`; for `f = e ∈ Bᵢ` it is `Bᵢ` itself. -/
def MatroidGame.swap (_G : MatroidGame N E) (B : N → Finset E) (i : N) (e f : E) :
    N → Finset E :=
  Function.update B i (insert f ((B i).erase e))

/-- **Total cost** `C(B) = Σ_{e∈∪_{i∈N}Bᵢ} cₑ(B) + Σ_{i∈N} Σ_{e∈Bᵢ} dᵢ,ₑ` (§2, p.5, with the
set-function costs `cₑ(B) := cₑ(Nₑ(B))` of §3, p.6). Only resources used by at least one player
are charged. -/
def MatroidGame.cost (G : MatroidGame N E) (B : N → Finset E) : ℝ :=
  (∑ e ∈ Finset.univ.filter (fun e => (G.users e B).Nonempty), G.c e (G.users e B)) +
    ∑ i : N, ∑ e ∈ B i, G.d i e

/-- `rkᵢ`, the rank of `𝓜ᵢ` (§3, p.6: "every base B of a matroid 𝓜ᵢ = (Eᵢ, 𝓑ᵢ) has the same
cardinality which we denote with rkᵢ"). Mathlib's `eRank` is finite here since `E` is finite. -/
noncomputable def MatroidGame.rank (G : MatroidGame N E) (i : N) : ℕ :=
  (G.M i).eRank.toNat

/-- `rk(𝓑) = max_{i∈N} rkᵢ` (Theorem 5, p.7); `0` when there are no players. -/
noncomputable def MatroidGame.rkMax (G : MatroidGame N E) : ℕ :=
  Finset.univ.sup fun i => G.rank i

end SepCostShare


