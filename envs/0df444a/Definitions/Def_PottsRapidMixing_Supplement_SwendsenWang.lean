-- Prove2me | Definitions.Def_PottsRapidMixing_Supplement_SwendsenWang
-- name    : PottsRapidMixing_Supplement_SwendsenWang
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:27:41.741932+00:00
-- url     : https://prove2.me/theorems/17908cea-bbdd-425c-a442-febc581bd3f5
-- title:
--   Swendsen–Wang dynamics $P_{\mathrm{SW}}$ of the $q$-state Potts model
-- statement:
--   Let $G=(V,E)$ be a finite graph, $q\ge1$ an integer, $\beta>0$, and $p=1-e^{-\beta}$. The *Swendsen–Wang dynamics* $P_{\mathrm{SW}}$ is the Markov chain on spin configurations $\sigma\in[q]^V$ that, from $\sigma$, makes the following two moves.
--
--   1. *Percolation.* Independently for each edge $e=xy$, include $e$ in an edge set $\omega$ with probability $p$ if $\sigma_x=\sigma_y$, and never include it if $\sigma_x\neq\sigma_y$.
--   2. *Recolouring.* Independently colour each connected component $C$ of $(V,\omega)$, isolated vertices included, with a uniform colour $a_C\in\{1,\dots,q\}$, and set $\sigma'_v=a_C$ for every $v\in C$.
--
--   Writing $\mathrm{mono}(\sigma)$ for the set of monochromatic edges and $c(V,\omega)$ for the number of connected components, the transition probabilities are
--   $$P_{\mathrm{SW}}(\sigma,\tau)=\sum_{\omega\subseteq \mathrm{mono}(\sigma)} p^{|\omega|}(1-p)^{|\mathrm{mono}(\sigma)|-|\omega|}\,\mathbf 1\{\tau\text{ is constant on every component of }(V,\omega)\}\,q^{-c(V,\omega)}.$$
--
--   The chain is the Edwards–Sokal coupling of the Potts and random-cluster models used as a sampler; its stationary law is the Potts law $\mu_{G,\beta,q}$. It is the chain of Theorem 1.3.
--
--   **Formalization Note** The percolation probability of $\omega$ is a product over the edges of $G$ (factor $p$ or $1-p$ on a monochromatic edge, $0$ or $1$ on a bichromatic one), so no natural-number subtraction occurs. Components, their number, and $p=1-e^{-\beta}$ are the mission's published `edgeGraph`, `numComps` and `pOf`. On the one-edge graph with two colours the transition probabilities and row sums are checked by proof in `Solutions/verification/PottsRapidMixing_Supplement_Sanity`.
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, §1, p.3 (steps 1–2 of the Swendsen–Wang dynamics)

import Mathlib
import Definitions.Def_PottsRapidMixing_RandomCluster
import Definitions.Def_PottsRapidMixing_Threshold

open scoped Classical

namespace PottsRapidMixing.Supplement

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edge `e` of `G` is monochromatic under the spin configuration `σ`: both endpoints carry the
same spin (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.3, step 1 of the Swendsen–Wang chain). -/
def IsMonoEdge (G : SimpleGraph V) {q : ℕ} (σ : V → Fin q) (e : G.edgeSet) : Prop :=
  ∀ a ∈ (e : Sym2 V), ∀ b ∈ (e : Sym2 V), σ a = σ b

/-- The percolation step of the Swendsen–Wang chain (arXiv:2610.42059, p.3, step 1): the probability
that, from `σ`, the edge configuration `ω` is drawn, when each monochromatic edge is included
independently with probability `p` and no other edge is included. -/
noncomputable def percWeight (G : SimpleGraph V) (p : ℝ) {q : ℕ} (σ : V → Fin q)
    (ω : G.edgeSet → Bool) : ℝ :=
  ∏ e : G.edgeSet,
    if IsMonoEdge G σ e then (if ω e = true then p else 1 - p) else (if ω e = true then 0 else 1)

/-- `τ` is constant on every connected component of `(V, ω)`. -/
def ConstOnClusters (G : SimpleGraph V) (ω : G.edgeSet → Bool) {q : ℕ} (τ : V → Fin q) : Prop :=
  ∀ x y : V, (edgeGraph G ω).Reachable x y → τ x = τ y

/-- The **Swendsen–Wang dynamics** `P_SW` of the `q`-state Potts model at inverse temperature `β` on
the finite graph `G` (arXiv:2610.42059, p.3, steps 1–2; [SW87]). From `σ`:

1. *percolation*: each edge `e = xy` is put in `ω` independently with probability `p = 1 − e^{−β}` if
   `σ_x = σ_y`, and never if `σ_x ≠ σ_y`;
2. *recolouring*: every connected component `C` of `(V, ω)` (isolated vertices included) gets an
   independent uniform colour `a_C ∈ {1, …, q}`, and `σ_v(t+1) = a_C` for `v ∈ C`.

So `P_SW(σ, τ) = Σ_ω percWeight(σ, ω) · 1{τ constant on the clusters of ω} · q^{−c(V, ω)}`.

**Formalization Note.** Spins are `Fin q`, `p` is the published `pOf β`, clusters are the components of
the published `edgeGraph G ω`, and `c(V, ω)` is the published `numComps`. The recolouring probability
`q^{−c(V, ω)}` is the probability that `q^{c}` independent uniform colours produce exactly the
configuration `τ`, given that `τ` is constant on the clusters. -/
noncomputable def swKernel (G : SimpleGraph V) (β : ℝ) (q : ℕ) :
    Matrix (V → Fin q) (V → Fin q) ℝ :=
  fun σ τ => ∑ ω : G.edgeSet → Bool, percWeight G (pOf β) σ ω *
    (if ConstOnClusters G ω τ then ((q : ℝ) ^ numComps (edgeGraph G ω))⁻¹ else 0)

end PottsRapidMixing.Supplement


