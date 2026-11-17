-- Prove2me | Definitions.Def_GraphonCheeger_Supplement_sampleGraph
-- name    : GraphonCheeger_Supplement_sampleGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:18:42.380312+00:00
-- url     : https://prove2.me/theorems/87cc4711-769d-4fba-b0bf-0eeac62bb29b
-- title:
--   The random coloured graphs $G(n,W)$, all induced subgraphs of one $G(\infty,W)$
-- statement:
--   Let $(W,\Psi)$ be a $\kappa$-coloured graphon on a probability space $(\Omega,\mathcal F,\mu)$. The random coloured graph $G(\infty,W)$ on the vertex set $\mathbb N$ is obtained by sampling i.i.d. points $X_1,X_2,\ldots\in\Omega$ with law $\mu$ and then, conditionally on them and independently, adding each edge $ij$ with probability $W(X_i,X_j)$ and giving each vertex $i$ colour $\ell$ with probability $\psi_\ell(X_i)$. The random graph $G(n,W)$ is the induced coloured subgraph of $G(\infty,W)$ on $[n]$, so all $G(n,W)$ live on one probability space.
--
--   This coupling is the one in which Theorem 2.11(iv) asserts almost sure convergence $G(n,W)\to W$.
--
--   **Formalization Note** The sample space is $\Omega\times[0,1]\times[0,1]^{\mathbb N}$ raised to the power $\mathbb N$, with the product probability measure `sampleMeasure μ` (Mathlib's `Measure.infinitePi`): the $i$-th coordinate $(X_i,V_i,(U_{ij})_j)$ holds $X_i\sim\mu$ and independent uniform variables on $[0,1]$. For $i<j$ the edge $ij$ is present iff $U_{ij}<W(X_i,X_j)$, and vertex $i$ receives colour `colourOf (Ψ X_i) V_i`, the number of $\ell$ with $\psi_0(X_i)+\dots+\psi_\ell(X_i)\le V_i$ (capped at $\kappa-1$, which matters only on the null event $V_i=1$); it equals $\ell$ with probability $\psi_\ell(X_i)$. Hence the joint law of $(G(n,W))_n$ is the one of the paper, and `sampleGraph W Ψ n ω` is the induced subgraph on `Fin n` for every $n$.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), §2.1.1, p.7

import Mathlib
import Definitions.Def_GraphonCheeger_stepGraphon
import Definitions.Def_GraphonCheeger_Supplement_homDens

open MeasureTheory

namespace GraphonCheeger.Supplement

/-!
# The random coloured graphs `G(n, W)` and `G(∞, W)` on one probability space

Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…), §2.1.1, p.7.

**Formalization Note.**
* The page samples i.i.d. points `X_i ∼ µ`, then, conditionally on them and independently, adds
  each edge `ij` with probability `W(X_i, X_j)` and gives vertex `i` colour `ℓ` with probability
  `ψ_ℓ(X_i)`; `G(n, W)` is the induced subgraph of `G(∞, W)` on the first `n` vertices.
* This is realized on the sample space `samplePt Ω = ℕ → Ω × [0,1] × [0,1]^ℕ` with the product
  probability measure `sampleMeasure μ` (`Measure.infinitePi`), whose `i`-th coordinate
  `(X_i, V_i, (U_{ij})_j)` holds the point `X_i ∼ µ` and independent uniform variables. For
  `i < j` the edge `ij` is present iff `U_{ij} < W(X_i, X_j)` (probability `W(X_i, X_j)`), and
  vertex `i` gets the colour `colourOf (Ψ(X_i)) V_i`, which equals `ℓ` with probability
  `ψ_ℓ(X_i)`. All these variables are independent, so the joint law of the whole sequence
  `(G(n, W))_n` is the page's; `sampleGraph … n ω` is `G(n, W)` and is the induced subgraph on
  `Fin n` of the infinite graph for every `n`.
* `colourOf p v` is the number of `ℓ` with `p_0 + ⋯ + p_ℓ ≤ v`, capped at `κ − 1` (the cap only
  matters on the null event `V_i = 1`).
-/

universe u

/-- The colour drawn from the distribution `p ∈ Δ_κ` with the uniform variable `v ∈ [0, 1]`:
the number of `ℓ` with `Σ_{l ≤ ℓ} p_l ≤ v`, capped at `κ − 1`. -/
noncomputable def colourOf {κ : ℕ} [NeZero κ] (p : Fin κ → ℝ) (v : ℝ) : Fin κ :=
  clampFin κ (Finset.univ.filter (fun ℓ : Fin κ =>
    (Finset.univ.filter (fun l : Fin κ => l ≤ ℓ)).sum p ≤ v)).card

/-- The sample space: the `i`-th coordinate is `(X_i, V_i, (U_{ij})_{j ∈ ℕ})`. -/
abbrev samplePt (Ω : Type u) : Type u := ℕ → Ω × unitInterval × (ℕ → unitInterval)

/-- The product probability measure on `samplePt Ω`: `X_i ∼ µ`, and `V_i`, `U_{ij}` uniform on
`[0, 1]`, all independent. -/
noncomputable def sampleMeasure {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) :
    Measure (samplePt Ω) :=
  Measure.infinitePi fun _ : ℕ =>
    μ.prod ((volume : Measure unitInterval).prod
      (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)))

/-- The random coloured graph `G(n, W)` (§2.1.1, p.7) at the sample point `ω`: vertices `Fin n`,
edge `ij` (`i < j`) iff `U_{ij} < W(X_i, X_j)`, colour of `i` drawn from `Ψ(X_i)` with `V_i`. -/
noncomputable def sampleGraph {Ω : Type u} {κ : ℕ} [NeZero κ] (W : Ω → Ω → ℝ)
    (Ψ : Ω → Fin κ → ℝ) (n : ℕ) (ω : samplePt Ω) : CGraph κ n :=
  ⟨SimpleGraph.fromRel (fun i j : Fin n =>
      i < j ∧ (((ω i.val).2.2 j.val : unitInterval) : ℝ) < W (ω i.val).1 (ω j.val).1),
    fun i => colourOf (Ψ (ω i.val).1) (((ω i.val).2.1 : unitInterval) : ℝ)⟩

end GraphonCheeger.Supplement


