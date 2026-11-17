-- Prove2me | Definitions.Def_GraphonCheeger_Supplement_homDens
-- name    : GraphonCheeger_Supplement_homDens
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:18:13.992026+00:00
-- url     : https://prove2.me/theorems/36b8355c-21f6-4d88-99ed-af5f357860cf
-- title:
--   Coloured graphons, coloured graphs, homomorphism densities $t(F,W)$, $t(F,G)$, equivalence $\cong$ and coloured graph limits $\widehat{\mathcal W}_\kappa$
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space and $\kappa\ge1$. A **(mixed) $\kappa$-colouring** of $\Omega$ is a measurable map $\Psi=(\psi_\ell)_{\ell=1}^\kappa:\Omega\to\Delta_\kappa$ into the simplex $\Delta_\kappa=\{x\in[0,\infty)^\kappa:\sum_\ell x_\ell=1\}$; a **pure** colouring is a measurable $\chi:\Omega\to[\kappa]$, identified with the point-mass colouring $\psi_\ell=\mathbf 1_{\{\chi=\ell\}}$. A **$\kappa$-coloured graphon** is a pair $(W,\Psi)$ of a graphon $W$ (a measurable symmetric $W:\Omega^2\to[0,1]$) and a colouring $\Psi$. A **coloured graph** $F$ on $[n]$ is a simple graph together with a colour $\ell_i\in[\kappa]$ of each vertex $i$.
--
--   For a coloured graph $F$ on $[n]$ the **homomorphism density** of $F$ in $(W,\Psi)$ is
--   $$
--   t(F,(W,\Psi))=\int_{\Omega^n}\prod_{i=1}^n\psi_{\ell_i}(x_i)\prod_{ij\in E(F)}W(x_i,x_j)\,d\mu(x_1)\cdots d\mu(x_n),
--   $$
--   and for a coloured graph $G$, $t(F,G)$ is the probability that a uniformly random map $V(F)\to V(G)$ sends every edge to an edge and every vertex to a vertex of the same colour. The vector $\tau(W)=(t(F,W))_F$ collects all densities, and similarly $\tau(G)=(t(F,G))_F$.
--
--   Two coloured graphons, possibly on different probability spaces, are **equivalent**, $W_1\cong W_2$, if $t(F,W_1)=t(F,W_2)$ for every coloured graph $F$. Uncoloured graphons are the case $\kappa=1$, whose only colouring is $\psi_1\equiv1$. A sequence of uncoloured graphs $G_n$ **converges** to a graphon $W$, $G_n\to W$, if $|G_n|\to\infty$ and $t(F,G_n)\to t(F,W)$ for every finite simple graph $F$. The space $\widehat{\mathcal W}_\kappa$ of **$\kappa$-coloured graph limits** is the set of limits, in the product topology, of $\tau(G_n)$ along sequences of coloured graphs with $|G_n|\to\infty$.
--
--   These are the objects of §§2–3 of the paper on which every statement about coloured graph limits, equivalence and convergence rests.
--
--   **Formalization Note** Colours are `Fin κ`, a colouring is `Ψ : Ω → Fin κ → ℝ` with measurable nonnegative coordinates summing to $1$ at every point (`IsKColouring`), and `ofColour χ` is the point-mass colouring of a pure $\chi$. Coloured graphs are `CGraph κ n` on `Fin n`. The densities are indexed by the labelled coloured graphs on `Fin (n+1)` (`LIdx κ`) instead of the unlabelled ones; all densities are invariant under relabelling, so equality, convergence and limits are the same. Graph limits (`GraphLimitSpace κ`) are a subset of $\mathbb R^{L}$ with the product topology (Definition 3.5 (W1)). `GEquiv` and `GConv` are the uncoloured ($\kappa=1$) equivalence and convergence. For a coloured graph on zero vertices $t(F,G)$ takes the junk value $0$, which plays no role along $|G_n|\to\infty$.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Definition 2.1, p.6; Remark 2.3, p.7; (2.1)–(2.2) and Definition 2.6, p.8; §2.3.1 and Definition 2.9, pp.8–9; Definition 3.5 (W1), p.22

import Mathlib
import Definitions.Def_GraphonCheeger_IsGraphon

open MeasureTheory Filter Topology

namespace GraphonCheeger.Supplement

/-!
# Coloured graphons, coloured graphs, homomorphism densities, equivalence and coloured graph limits

Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…): Definition 2.1 (p.6), Remark 2.3 (p.7),
(2.1)–(2.2) (p.8), Definition 2.6 (p.8), §2.3.1 (pp.8–9), Definition 2.9 (p.9) and
Definition 3.5 (W1) (p.22).

**Formalization Note.**
* A (mixed) `κ`-colouring `Ψ = (ψ_ℓ)_{ℓ ∈ [κ]}` of `Ω` is a function `Ψ : Ω → Fin κ → ℝ` with
  every coordinate measurable, nonnegative, and `Σ_ℓ ψ_ℓ(x) = 1` at every point (`IsKColouring`).
  A pure colouring is a measurable `χ : Ω → Fin κ`, identified with the point-mass colouring
  `ofColour χ` (Def. 2.1, p.7). Colours are `Fin κ = {0, …, κ − 1}` instead of `[κ]`.
* A coloured graph on `[n]` is `CGraph κ n`: a simple graph on `Fin n` and a colour map
  `Fin n → Fin κ` (pure colouring, Remark 2.3).
* The index set of graph limits is `LIdx κ`, the coloured graphs on `Fin (n + 1)`, `n ≥ 0`, i.e.
  the labelled graphs `L = ⋃_{n ≥ 1} L_n` instead of the unlabelled `U`. All densities are
  invariant under relabelling (p.8), so `[0,1]^U` and the closed subset of `ℝ^L` used here carry the
  same limits, with homeomorphic embeddings; equality of all `t(F, ·)` over `L` is equality over
  `U`. Points of `ℝ^L` carry the product topology.
* Equivalence `≅` (Def. 2.6) is condition (i) of Lemma 2.5: `t(F, W₁) = t(F, W₂)` for every
  coloured graph `F` (`CEquiv`). Uncoloured graphons are the case `κ = 1` with the only colouring
  `ψ_1 ≡ 1` (p.6), so uncoloured equivalence is `GEquiv`.
* For uncoloured graphs, `G_n → W` is Definition 2.9 with Theorem 2.11(iii): `|G_n| → ∞` and
  `t(F, G_n) → t(F, W)` for every finite simple graph `F` (`GConv`).
* Graph limits `Ŵ_κ` (Def. 3.5 (W1)) are the limits in `ℝ^L` of `τ(G_n)` along sequences of
  coloured graphs with `|G_n| → ∞` (`GraphLimitSpace κ`).
* `t(F, G)` for a coloured graph `G` on `Fin m` is the number of homomorphisms `Fin n → Fin m`
  divided by `m^n`; at `m = 0` it is the junk value `0`, irrelevant along `|G_n| → ∞`.
-/

universe u

/-- A (mixed) `κ`-colouring `Ψ = (ψ_ℓ)_ℓ : Ω → Δ_κ` (Def. 2.1, p.6): each `ψ_ℓ` measurable,
`ψ_ℓ ≥ 0`, and `Σ_ℓ ψ_ℓ = 1` everywhere. -/
def IsKColouring {Ω : Type u} [MeasurableSpace Ω] {κ : ℕ} (Ψ : Ω → Fin κ → ℝ) : Prop :=
  (∀ ℓ, Measurable fun x => Ψ x ℓ) ∧ (∀ x ℓ, 0 ≤ Ψ x ℓ) ∧ (∀ x, ∑ ℓ, Ψ x ℓ = 1)

/-- The point-mass colouring of a pure colouring `χ : Ω → [κ]`: `ψ_ℓ = 1_{χ = ℓ}` (p.7). -/
def ofColour {Ω : Type u} {κ : ℕ} (χ : Ω → Fin κ) (x : Ω) (ℓ : Fin κ) : ℝ :=
  if χ x = ℓ then 1 else 0

/-- A `κ`-coloured (simple) graph on the vertex set `[n] = Fin n` (Remark 2.3, p.7). -/
structure CGraph (κ n : ℕ) where
  /-- The underlying simple graph. -/
  graph : SimpleGraph (Fin n)
  /-- The colour of each vertex. -/
  col : Fin n → Fin κ

/-- The index set of coloured graph limits: coloured graphs on `Fin (n + 1)`, `n ≥ 0`. -/
abbrev LIdx (κ : ℕ) : Type := Σ n : ℕ, CGraph κ (n + 1)

open Classical in
/-- The coloured homomorphism density (2.2), p.8:
`t(F, (W, Ψ)) = ∫_{Ωⁿ} ∏_i ψ_{ℓ_i}(x_i) ∏_{ij ∈ E(F)} W(x_i, x_j) dµ(x_1) ⋯ dµ(x_n)`, with one
factor per (unordered) edge `ij`, `i < j`. -/
noncomputable def homDens {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) {κ n : ℕ}
    (W : Ω → Ω → ℝ) (Ψ : Ω → Fin κ → ℝ) (F : CGraph κ n) : ℝ :=
  ∫ x : Fin n → Ω, (∏ i, Ψ (x i) (F.col i)) *
      ∏ i, ∏ j, (if i < j ∧ F.graph.Adj i j then W (x i) (x j) else 1)
    ∂(Measure.pi fun _ => μ)

/-- The vector `τ(W) = (t(F, W))_{F}` of all homomorphism densities of a coloured graphon
(p.11 and (3.43), p.22). -/
noncomputable def tau {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) {κ : ℕ}
    (W : Ω → Ω → ℝ) (Ψ : Ω → Fin κ → ℝ) : LIdx κ → ℝ :=
  fun F => homDens μ W Ψ F.2

open Classical in
/-- `t(F, G)` for coloured graphs (§2.3.1, p.8): the probability that a uniformly random map
`V(F) → V(G)` maps every edge to an edge and every vertex to a vertex of the same colour. -/
noncomputable def homDensG {κ n m : ℕ} (F : CGraph κ n) (G : CGraph κ m) : ℝ :=
  ((Finset.univ.filter (fun f : Fin n → Fin m =>
      (∀ i j, F.graph.Adj i j → G.graph.Adj (f i) (f j)) ∧ ∀ i, G.col (f i) = F.col i)).card : ℝ) /
    (m : ℝ) ^ n

/-- `τ(G) = (t(F, G))_{F}` for a coloured graph `G` ((3.43), p.22). -/
noncomputable def tauG {κ m : ℕ} (G : CGraph κ m) : LIdx κ → ℝ :=
  fun F => homDensG F.2 G

/-- Equivalence `W₁ ≅ W₂` of coloured graphons, possibly on different probability spaces
(Definition 2.6 via Lemma 2.5(i), p.8): `t(F, W₁) = t(F, W₂)` for every coloured graph `F`. -/
def CEquiv {Ω₁ : Type u} {Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {κ : ℕ}
    (μ₁ : Measure Ω₁) (W₁ : Ω₁ → Ω₁ → ℝ) (Ψ₁ : Ω₁ → Fin κ → ℝ)
    (μ₂ : Measure Ω₂) (W₂ : Ω₂ → Ω₂ → ℝ) (Ψ₂ : Ω₂ → Fin κ → ℝ) : Prop :=
  tau μ₁ W₁ Ψ₁ = tau μ₂ W₂ Ψ₂

/-- The only `1`-colouring, `ψ_1 ≡ 1`: an uncoloured graphon is a `1`-coloured one (p.6). -/
def trivCol {Ω : Type u} : Ω → Fin 1 → ℝ := fun _ _ => 1

/-- Equivalence of uncoloured graphons (Definition 2.6 with `κ = 1`): equal homomorphism
densities `t(F, W₁) = t(F, W₂)` for every finite simple graph `F`. -/
def GEquiv {Ω₁ : Type u} {Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ₁ : Measure Ω₁) (W₁ : Ω₁ → Ω₁ → ℝ) (μ₂ : Measure Ω₂) (W₂ : Ω₂ → Ω₂ → ℝ) : Prop :=
  CEquiv μ₁ W₁ trivCol μ₂ W₂ trivCol

/-- An uncoloured graph regarded as a `1`-coloured graph. -/
def uncolG {m : ℕ} (G : SimpleGraph (Fin m)) : CGraph 1 m := ⟨G, fun _ => 0⟩

/-- Convergence `G_n → W` of uncoloured graphs `G_n` on `Fin (N n)` to an uncoloured graphon
(Definition 2.9 with Theorem 2.11(iii), `κ = 1`): `|G_n| = N n → ∞` and `t(F, G_n) → t(F, W)`
for every finite simple graph `F`. -/
def GConv {Ω : Type u} [MeasurableSpace Ω] (N : ℕ → ℕ) (G : (n : ℕ) → SimpleGraph (Fin (N n)))
    (μ : Measure Ω) (W : Ω → Ω → ℝ) : Prop :=
  Tendsto N atTop atTop ∧
    ∀ F : LIdx 1, Tendsto (fun n => homDensG F.2 (uncolG (G n))) atTop (𝓝 (homDens μ W trivCol F.2))

/-- The space `Ŵ_κ` of `κ`-coloured graph limits (Definition 3.5 (W1), p.22): the limits in
`ℝ^L` (product topology) of `τ(G_n)` over sequences of coloured graphs with `|G_n| → ∞`. -/
def GraphLimitSpace (κ : ℕ) : Set (LIdx κ → ℝ) :=
  {w | ∃ (N : ℕ → ℕ) (G : (k : ℕ) → CGraph κ (N k)),
    Tendsto N atTop atTop ∧ Tendsto (fun k => tauG (G k)) atTop (𝓝 w)}

end GraphonCheeger.Supplement


