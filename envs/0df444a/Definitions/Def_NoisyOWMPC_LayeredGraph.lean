-- Prove2me | Definitions.Def_NoisyOWMPC_LayeredGraph
-- name    : NoisyOWMPC_LayeredGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:41:06.653559+00:00
-- url     : https://prove2.me/theorems/1819eff5-7f25-41ee-8a1a-18da618ab3cc
-- title:
--   Layered bipartite graphs and list recoverability
-- statement:
--   A **layered bipartite graph** with $d$ layers has left vertices $\{0,1\}^\kappa$, right vertices $[d]\times H$, and neighbor maps $\gamma_i$, so that the neighbor of $f$ in layer $i$ is $(i,\gamma_i(f))$; it comes with a recovery algorithm $\mathrm{Rec}_G(\Lambda)$ returning a list of left vertices for a right set $\Lambda$.
--
--   For $1\le T\le d$ the graph is **$(B,T,L)$-list-recoverable** if for every $\Lambda$ with $|\Lambda|\le B$:
--   1. *expansion*: at most $L$ left vertices have at least $T$ neighbors in $\Lambda$;
--   2. *recovery*: $\mathrm{Rec}_G(\Lambda)=\{f:|\Gamma_G(f)\cap\Lambda|\ge T\}$.
--
--   Left regularity holds for every layered graph. These expanders are how the recovery algorithms of the tests and the selector turn row lists into a short list of seeds.
--
--   **Formalization Note** The labels $H$ are $[h]$. Efficiency of $\mathrm{Rec}_G$ is a property of a family of graphs and is stated in `IsA8Family`.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Definition 3.6, p.17

import Mathlib

namespace NoisyOWMPC

/-- A **layered bipartite graph** (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256
3a9569fa…), Definition 3.6, p.17: "We call the graph layered if `R = [d] × H` for a finite set `H`
and `Γ_G(f, i) = (i, γ_i(f))`, so that each left vertex has exactly one neighbor in each layer"):
left vertices `{0,1}^κ`, right vertices `[d] × [h]` (labels `H = [h]`), neighbor maps `γ_i`, and
the recovery algorithm `Rec_G(Λ)` returning a list of left vertices. The number `d` of layers (the
left degree) is a parameter of the type. -/
structure LayeredGraph (d : ℕ) where
  /-- the left vertices are `{0,1}^κ` -/
  κ : ℕ
  /-- the number of labels `|H|` -/
  h : ℕ
  /-- the neighbor in layer `i`: `Γ_G(f, i) = (i, γ_i(f))` -/
  γ : Fin d → (Fin κ → Bool) → Fin h
  /-- the recovery algorithm `Rec_G(Λ)` -/
  recov : Finset (Fin d × Fin h) → List (Fin κ → Bool)

open Classical in
/-- The number `|Γ_G(f) ∩ Λ|` of neighbors of the left vertex `f` in the right set `Λ`. -/
noncomputable def LayeredGraph.hits {d : ℕ} (G : LayeredGraph d) (Λ : Finset (Fin d × Fin G.h))
    (f : Fin G.κ → Bool) : ℕ :=
  (Finset.univ.filter fun i => (i, G.γ i f) ∈ Λ).card

open Classical in
/-- The graph is **`(B, T, L)`-list-recoverable** (Definition 3.6, p.17), for `1 ≤ T ≤ d`:
* *expansion*: for every `Λ ⊆ R` with `|Λ| ≤ B`, at most `L` left vertices have at least `T`
  neighbors in `Λ`;
* *recovery*: for every such `Λ`, `Rec_G(Λ) = {f ∈ {0,1}^κ : |Γ_G(f) ∩ Λ| ≥ T}`.
Left regularity (`d` distinct neighbors) holds for every layered graph.

**Formalization Note** The efficiency of `Rec_G` is a property of a family of graphs and is stated
where a family is constructed (Corollary A.8). -/
def LayeredGraph.IsListRec {d : ℕ} (G : LayeredGraph d) (B T L : ℕ) : Prop :=
  1 ≤ T ∧ T ≤ d ∧
  (∀ Λ : Finset (Fin d × Fin G.h), Λ.card ≤ B →
    (Finset.univ.filter fun f => T ≤ G.hits Λ f).card ≤ L) ∧
  ∀ Λ : Finset (Fin d × Fin G.h), Λ.card ≤ B →
    (G.recov Λ).toFinset = Finset.univ.filter fun f => T ≤ G.hits Λ f

end NoisyOWMPC


