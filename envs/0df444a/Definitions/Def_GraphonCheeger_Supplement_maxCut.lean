-- Prove2me | Definitions.Def_GraphonCheeger_Supplement_maxCut
-- name    : GraphonCheeger_Supplement_maxCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:21:20.766723+00:00
-- url     : https://prove2.me/theorems/616392f5-fe8f-49b1-b081-9cb4c120a6f1
-- title:
--   Maximum cut: $\mathrm{MC}(G)$, $\mathrm{MC}_{\mathrm{frac}}(G)$, $\mathrm{MC}_{\mathrm{pure}}(W)$, $\mathrm{MC}_{\mathrm{mix}}(W)$
-- statement:
--   For a graph $G$ on $[n]$ the normalised maximum cut and its fractional version are
--   $$
--   \mathrm{MC}(G)=\frac1{n^2}\max_{S\subseteq V(G)}e_G(S,S^c),\qquad
--   \mathrm{MC}_{\mathrm{frac}}(G)=\sup_{\psi:V(G)\to[0,1]}\frac1{n^2}\sum_{u,v\in V(G)}\mathbf 1_{uv\in E(G)}\,\psi(u)(1-\psi(v)),
--   $$
--   where $e_G(S,S^c)$ is the number of edges crossing the cut. For a graphon $W$ on a probability space $(\Omega,\mathcal F,\mu)$ and a mixed 2-colouring $\Psi=(\psi,1-\psi)$, let $C(W,\psi)=\iint W(x,y)\psi(x)(1-\psi(y))\,d\mu(x)\,d\mu(y)$. Then
--   $$
--   \mathrm{MC}_{\mathrm{pure}}(W)=\sup_{S\subseteq\Omega}\iint_{S\times S^c}W\,d\mu\,d\mu,\qquad
--   \mathrm{MC}_{\mathrm{mix}}(W)=\sup_{\psi:\Omega\to[0,1]}C(W,\psi),
--   $$
--   the suprema over measurable sets $S$ and measurable $\psi$; the paper sets $\mathrm{MC}(W):=\mathrm{MC}_{\mathrm{mix}}(W)$.
--
--   These are the parameters of Theorems 4.2, 4.5, 4.7, 4.9 and 4.10.
--
--   **Formalization Note** Graphs are on `Fin n`; $e_G(S,S^c)$ is the base `edgesBetween` and the double sum is the base `fracF`; at $n=0$ both normalisations give the junk value $0$. A mixed 2-colouring is identified with $\psi$ (base `IsColouring`; `IsPureColouring` for $\psi=\mathbf 1_S$), and $C(W,\psi)$ is the base `cutVal`. Both suprema are over nonempty sets bounded by $1$.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), §4.1, (4.5)–(4.16) and (4.32), pp.31–35

import Mathlib
import Definitions.Def_GraphonCheeger_cheegerG
import Definitions.Def_GraphonCheeger_fracCheeger
import Definitions.Def_GraphonCheeger_cheegerW

open MeasureTheory

namespace GraphonCheeger.Supplement

/-!
# Maximum cut of graphs and graphons: `MC(G)`, `MC_frac(G)`, `MC_pure(W)`, `MC_mix(W)`

Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…), §4.1, (4.5)–(4.16) and (4.32), pp.31–35.

**Formalization Note.**
* Graphs have vertex set `Fin n`. `MC(G) = n^{-2} max_S e_G(S, Sᶜ)` (4.5) uses the base
  `edgesBetween` (the number of edges between `S` and `Sᶜ`), and
  `MC_frac(G) = sup_{ψ : V → [0,1]} C(G, ψ)` (4.13), (4.15) uses the base
  `fracF G ψ = Σ_{u,v} 1_{uv ∈ E} ψ(u)(1 − ψ(v))`, divided by `n²`. At `n = 0` both are the junk
  `x / 0 = 0`.
* A mixed 2-colouring `Ψ = (ψ, 1 − ψ)` is identified with `ψ` (p.31–32), as in the base
  `IsColouring` / `IsPureColouring`, and `C(W, ψ)` (4.14) is the base `cutVal`.
  `MC_pure(W) = sup_S ∬_{S × Sᶜ} W` (4.6) is the supremum over pure colourings `ψ = 1_S`, and
  `MC_mix(W)` (4.16) over all mixed ones. Both sets are nonempty and bounded by `1` for a graphon
  on a probability space. `MC(W) := MC_mix(W)` (4.32).
-/

universe u

/-- `MC(G) = n^{-2} max_{S ⊆ V(G)} e_G(S, Sᶜ)` ((4.5), p.31). -/
noncomputable def maxCutG {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℝ :=
  ((Finset.univ.sup fun S : Finset (Fin n) => edgesBetween G S : ℕ) : ℝ) / (n : ℝ) ^ 2

/-- `MC_frac(G) = sup_{ψ : V(G) → [0,1]} n^{-2} Σ_{u,v} 1_{uv ∈ E(G)} ψ(u)(1 − ψ(v))`
((4.13), (4.15), p.32). -/
noncomputable def maxCutFrac {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℝ :=
  sSup {r : ℝ | ∃ p : Fin n → ℝ, (∀ v, p v ∈ Set.Icc (0 : ℝ) 1) ∧ r = fracF G p / (n : ℝ) ^ 2}

/-- `MC_pure(W) = sup_{S ⊆ Ω measurable} ∬_{S × Sᶜ} W dµ dµ` ((4.6), (4.8), p.31): the supremum of
`C(W, ψ)` over pure 2-colourings `ψ = 1_S`. -/
noncomputable def maxCutPure {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : Ω → Ω → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ ψ : Ω → ℝ, IsPureColouring ψ ∧ r = cutVal μ W ψ}

/-- `MC_mix(W) = sup_{ψ : Ω → [0,1]} C(W, ψ)` ((4.16), p.32), and `MC(W) := MC_mix(W)` (4.32). -/
noncomputable def maxCutMix {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : Ω → Ω → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ ψ : Ω → ℝ, IsColouring ψ ∧ r = cutVal μ W ψ}

end GraphonCheeger.Supplement


