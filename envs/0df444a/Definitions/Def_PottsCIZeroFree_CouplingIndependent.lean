-- Prove2me | Definitions.Def_PottsCIZeroFree_CouplingIndependent
-- name    : PottsCIZeroFree_CouplingIndependent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:27:51.061126+00:00
-- url     : https://prove2.me/theorems/5e598896-41b4-4e0a-9bc1-bad6e389a2fe
-- title:
--   Pinned Gibbs law (4), $W_{1,\mathrm{Ham}}$, graph classes and Potts coupling independence (Definition 1.2)
-- statement:
--   Let $G=(V,E)$ be a finite simple graph, $\tau$ a pinning on $\Lambda$ and $x\in[0,1]$ with $\widehat Z^\tau_G(x)>0$. The **pinned Gibbs law** is the probability distribution on colorings $\varphi:V^\tau\to[q]$ of the free vertices given by
--   $$\mu^\tau_{G,x}(\varphi)=\frac{x^{m_G(\tau\cup\varphi)-m_G(\tau)}}{\widehat Z^\tau_G(x)}.$$
--   For $x=0$ it is uniform on the colorings of $V^\tau$ that create no monochromatic edge outside $G[\Lambda]$, also when $\tau$ is improper. For two distributions on colorings of a common vertex set, $W_{1,\mathrm{Ham}}$ is the minimum, over all couplings, of the expected number of vertices at which the two colorings differ.
--
--   A **class** $\mathcal G$ of finite simple graphs has maximum degree at most $\Delta$ if all its members do; it is **closed under taking induced subgraphs** if every induced subgraph of a member is a member; $\mathcal G_\Delta$ is the class of all finite simple graphs of maximum degree at most $\Delta$.
--
--   **Definition 1.2 (Potts coupling independence).** Let $C\in[0,\infty)$ and $J\subseteq[0,1]$. A class $\mathcal G$ satisfies **$C$-coupling independence on $J$** if, for every $G\in\mathcal G$, every pinning $\tau$, every $r\in V^\tau$, all $a,b\in[q]$ and every $x\in J$, the two pinned laws $\mu^{\tau^{r=a}}_{G,x}$, $\mu^{\tau^{r=b}}_{G,x}$ are well defined and
--   $$W_{1,\mathrm{Ham}}\bigl(\mu^{\tau^{r=a}}_{G,x},\mu^{\tau^{r=b}}_{G,x}\bigr)\le C .$$
--   Both laws live on the common free set $V^\tau\setminus\{r\}$, where the Hamming distance is taken. When $J=\{x\}$ this is coupling independence at $x$.
--
--   Coupling independence is the probabilistic input of the transfer theorem (Theorem 1.3) and is what Section 4 establishes for $q\ge 11\Delta/6$.
--
--   **Formalization Note** The law of a child pinning is the law (4) of the pinning $\tau\cup\{r\mapsto a\}$ on $\Lambda\cup\{r\}$, so the two laws live on the same type, the colorings of $V^\tau\setminus\{r\}$. $W_{1,\mathrm{Ham}}$ is the published transportation metric `MarkovMixing.transportDist` with the Hamming cost. "Well defined" is the positivity of both normalizing constants, which is part of the definition. A class is a predicate on graphs with vertex set `Fin n` for each `n`; closure under induced subgraphs is closure under graph embeddings `H ↪g G`, which reflect adjacency. The constant $C$ is a real number; the statements using the definition assume $C\ge0$.
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.3, display (4), Definition 1.2 and display (5); §2.1, p.7 ($\mathcal G_\Delta$); §2.3, p.8, display (9) and Ham

import Mathlib
import Definitions.Def_mm_transport
import Definitions.Def_PottsCIZeroFree_normPinnedPoly

open Classical

namespace PottsCIZeroFree

noncomputable section

/-- The pinned Gibbs law (4) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*,
arXiv:2610.12456 (PDF sha256 831a1633…), p.3: for a real `x`, the weight of a coloring
`φ : V^τ → [q]` of the free vertices is
`µ^τ_{G,x}(φ) = x^{m_G(τ∪φ) − m_G(τ)} / Ẑ^τ_G(x)`.

**Formalization Note.** The paper uses (4) only when `Ẑ^τ_G(x) > 0`; every statement of this
mission that uses the law carries (or proves) that positivity. With `0^0 = 1` the law at `x = 0`
is uniform on the colorings that create no monochromatic edge outside `G[Λ]`, also for improper
`τ`. -/
def pinnedGibbs {V : Type*} [Fintype V] (G : SimpleGraph V) (Λ : Set V) {q : ℕ}
    (τ : V → Fin q) (x : ℝ) (φ : {v // v ∉ Λ} → Fin q) : ℝ :=
  x ^ pinExp G Λ τ φ / normPinnedAt G Λ τ x

/-- The Hamming distance `Ham(σ, σ') = |{u : σ_u ≠ σ'_u}|` of p.8, on colorings of a common
vertex set. -/
def ham {α : Type*} {q : ℕ} (σ σ' : α → Fin q) : ℝ :=
  (Set.ncard {u : α | σ u ≠ σ' u} : ℝ)

/-- The law `µ^{τ^{r=a}}_{G,x}` of the child pinning `τ^{r=a}`, p.3. It is the pinned Gibbs
law (4) of the pinning `τ ∪ {r ↦ a}` on `Λ ∪ {r}`, so it lives on the colorings of
`V^τ \ {r}`, the common free set of Definition 1.2. At `x = 0` with `a` blocked at `r` it is
defined by the child weights, not by conditioning the parent law (p.8). -/
def childLaw {V : Type*} [Fintype V] (G : SimpleGraph V) (Λ : Set V) {q : ℕ} (τ : V → Fin q)
    (r : V) (a : Fin q) (x : ℝ) : ({v // v ∉ childSet Λ r} → Fin q) → ℝ :=
  pinnedGibbs G (childSet Λ r) (childPin τ r a) x

/-- `W_{1,Ham}(µ^{τ^{r=a}}_{G,x}, µ^{τ^{r=b}}_{G,x})`, the left side of (5), p.3: the
Wasserstein distance (9), p.8, with respect to the Hamming metric on colorings of
`V^τ \ {r}`. It is the published transportation metric `MarkovMixing.transportDist`. -/
def childW1 {V : Type*} [Fintype V] (G : SimpleGraph V) (Λ : Set V) {q : ℕ} (τ : V → Fin q)
    (r : V) (a b : Fin q) (x : ℝ) : ℝ :=
  MarkovMixing.transportDist (fun σ σ' => ham σ σ') (childLaw G Λ τ r a x) (childLaw G Λ τ r b x)

/-- A class of finite simple graphs, p.3.

**Formalization Note.** A class is a predicate on the graphs with vertex set `Fin n`, for all
`n`. Every finite simple graph is isomorphic to one of these, and a class closed under induced
subgraphs in the sense of `ClosedInduced` is closed under isomorphism. -/
abbrev GraphClass : Type := (n : ℕ) → SimpleGraph (Fin n) → Prop

/-- Every graph of the class has maximum degree at most `Δ` (p.3, p.7). -/
def DegBounded (𝒢 : GraphClass) (Δ : ℕ) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)), 𝒢 n G → MaxDegLE G Δ

/-- The class is closed under taking induced subgraphs (p.3, p.7). An embedding `H ↪g G`
reflects adjacency, so `H` is (isomorphic to) an induced subgraph of `G`. -/
def ClosedInduced (𝒢 : GraphClass) : Prop :=
  ∀ n m (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)), 𝒢 n G → Nonempty (H ↪g G) → 𝒢 m H

/-- The class `G_Δ` of all finite simple graphs of maximum degree at most `Δ`, §2.1, p.7. -/
def GDelta (Δ : ℕ) : GraphClass := fun _ G => MaxDegLE G Δ

/-- Definition 1.2 (Potts coupling independence), p.3. A class `𝒢` satisfies `C`-coupling
independence on `J ⊆ [0,1]` if, for every `G ∈ 𝒢`, every pinning `τ`, every `r ∈ V^τ`, all
`a, b ∈ [q]` and every `x ∈ J`, the two pinned laws are well defined
(`Ẑ^{τ^{r=a}}_G(x) > 0` and `Ẑ^{τ^{r=b}}_G(x) > 0`) and
`W_{1,Ham}(µ^{τ^{r=a}}_{G,x}, µ^{τ^{r=b}}_{G,x}) ≤ C` (5). With `J = {x}` this is coupling
independence at `x`.

**Formalization Note.** The pinning is any `Λ ⊆ V` with any `τ`, proper or not. The paper's
`C ∈ [0, ∞)` is a hypothesis `0 ≤ C` of the statements using this definition. -/
def CouplingIndependent (q : ℕ) (𝒢 : GraphClass) (C : ℝ) (J : Set ℝ) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)), 𝒢 n G →
    ∀ (Λ : Set (Fin n)) (τ : Fin n → Fin q) (r : Fin n), r ∉ Λ →
      ∀ a b : Fin q, ∀ x ∈ J,
        0 < normPinnedAt G (childSet Λ r) (childPin τ r a) x ∧
        0 < normPinnedAt G (childSet Λ r) (childPin τ r b) x ∧
        childW1 G Λ τ r a b x ≤ C

end

end PottsCIZeroFree


