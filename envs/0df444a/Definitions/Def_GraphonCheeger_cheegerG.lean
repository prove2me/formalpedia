-- Prove2me | Definitions.Def_GraphonCheeger_cheegerG
-- name    : GraphonCheeger_cheegerG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:39:51.26872+00:00
-- url     : https://prove2.me/theorems/72ead8a6-3128-4f25-87f3-2a27be352046
-- title:
--   Cheeger constant $h(G)$ of a finite graph
-- statement:
--   Let $G$ be a finite simple graph with no isolated vertices, with degrees $d_v$. For $A\subseteq V(G)$ let $e_G(A,A^c)$ be the number of edges with one end in $A$ and the other in $A^c$, and let $\mathrm{vol}_G(A)=\sum_{v\in A}d_v$. The **Cheeger constant** of $G$ is
--
--   $$h(G)=\min_{\emptyset\ne A\subsetneq V(G)}\frac{e_G(A,A^c)}{\min\{\mathrm{vol}_G(A),\mathrm{vol}_G(A^c)\}}.$$
--
--   It measures the worst bottleneck of $G$: a small value means some vertex set of substantial volume is joined to its complement by few edges.
--
--   **Formalization Note** The volume is the published platform definition `SpectralSparsify.Decomp.vol`. `edgesBetween G A` counts the pairs $(u,v)\in A\times A^c$ with $u\sim v$. The definition is total: for a graph with isolated vertices a denominator can be $0$ (and $x/0=0$ in Lean), and for $n\le1$ the minimum is over the empty set (value $0$). Every statement that uses $h(G)$ assumes no isolated vertices, or follows from an assumption that implies it.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Definition 4.19, (4.75), p.42

import Mathlib
import Definitions.Def_SpectralSparsify_Decomp_vol

namespace GraphonCheeger

open SpectralSparsify.Decomp

/-!
# The Cheeger constant of a finite graph

Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…), Definition 4.19, (4.75), p.42.

**Formalization Note.**
* Graphs have vertex set `Fin n`. The volume `vol_G(A) = Σ_{v∈A} d_v` is the published platform
  definition `SpectralSparsify.Decomp.vol` (real-valued).
* `edgesBetween G A` counts the ordered pairs `(u, v) ∈ A × Aᶜ` with `u ∼ v`, which is the number
  `e_G(A, Aᶜ)` of edges with one end in `A` and the other in `Aᶜ`.
* `cheegerG G` is the infimum (for a finite nonempty index set, the minimum) over nonempty proper
  `A ⊊ V(G)` of `e_G(A, Aᶜ) / min{vol(A), vol(Aᶜ)}`. The paper defines it only for graphs with no
  isolated vertices; otherwise Lean's total conventions give junk values (`x / 0 = 0`, and
  `sInf ∅ = 0` when `n ≤ 1`). Every statement that needs the paper's value carries the
  hypothesis.
-/

/-- `e_G(A, Aᶜ)`: the number of edges between `A` and its complement. -/
def edgesBetween {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) : ℕ :=
  ((A ×ˢ Aᶜ).filter (fun p => G.Adj p.1 p.2)).card

/-- The **Cheeger constant** `h(G) = min_{∅ ≠ A ⊊ V(G)} e_G(A, Aᶜ) / min{vol_G(A), vol_G(Aᶜ)}`
((4.75), p.42). -/
noncomputable def cheegerG {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℝ :=
  sInf ((fun A : Finset (Fin n) => (edgesBetween G A : ℝ) / min (vol G A) (vol G Aᶜ)) ''
    {A : Finset (Fin n) | A.Nonempty ∧ A ≠ Finset.univ})

end GraphonCheeger


