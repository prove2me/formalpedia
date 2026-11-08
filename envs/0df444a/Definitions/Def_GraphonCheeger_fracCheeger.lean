-- Prove2me | Definitions.Def_GraphonCheeger_fracCheeger
-- name    : GraphonCheeger_fracCheeger
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:39:55.603099+00:00
-- url     : https://prove2.me/theorems/2d069ecc-e818-4c80-af8b-a4d9c0d71225
-- title:
--   Fractional Cheeger constant $\tilde h(G)$ of a finite graph
-- statement:
--   Let $G$ be a graph on $[n]$ with adjacency matrix $(A_{uv})$, degrees $d_v$ and $\mathrm{vol}(G)=\sum_v d_v$. For $p=(p_1,\dots,p_n)\in[0,1]^n$ put
--
--   $$F(p)=\sum_{u,v=1}^nA_{uv}\,p_u(1-p_v),\qquad L(p)=\sum_{v=1}^nd_vp_v .$$
--
--   The **fractional Cheeger constant** is
--
--   $$\tilde h(G)=\inf_{\substack{p\in[0,1]^n\\0<L(p)<\mathrm{vol}(G)}}\frac{F(p)}{\min\{L(p),\mathrm{vol}(G)-L(p)\}} .$$
--
--   It relaxes the vertex sets of $h(G)$ to fractional memberships $p_v$; taking $p$ an indicator vector recovers the ratios defining $h(G)$.
--
--   **Formalization Note** The paper prints the admissibility condition as $0<L(p)<T$ without defining $T$; it is read as $T=\mathrm{vol}(G)$, the value for which the denominator is positive. If no $p$ is admissible (a graph without edges) the value is the junk $0$.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), (4.84)–(4.85), p.43

import Mathlib
import Definitions.Def_SpectralSparsify_Decomp_vol

namespace GraphonCheeger

open SpectralSparsify.Decomp

/-!
# The fractional Cheeger constant of a finite graph

Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…), (4.84)–(4.85), p.43 (after [KM24]).

**Formalization Note.**
* Graphs have vertex set `Fin n` (the paper's `[n]`), `A_{uv} = 1` iff `u ∼ v`.
* The admissibility condition printed as `0 < L(p) < T` is read with `T = vol(G)`: the paper never
  defines `T`, and the denominator `min{L(p), vol(G) − L(p)}` is positive exactly when
  `0 < L(p) < vol(G)`.
* If no `p` is admissible (a graph without edges) the value is the junk `sInf ∅ = 0`.
-/

/-- `F(p) = Σ_{u,v} A_{uv} p_u (1 − p_v)` ((4.84), p.43). -/
noncomputable def fracF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : Fin n → ℝ) : ℝ :=
  ∑ u, ∑ v, (if G.Adj u v then (1 : ℝ) else 0) * p u * (1 - p v)

/-- `L(p) = Σ_v d_v p_v` ((4.84), p.43). -/
noncomputable def fracL {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : Fin n → ℝ) : ℝ :=
  ∑ v, (G.degree v : ℝ) * p v

/-- The **fractional Cheeger constant**
`h̃(G) = inf_{p ∈ [0,1]ⁿ, 0 < L(p) < vol(G)} F(p) / min{L(p), vol(G) − L(p)}` ((4.85), p.43). -/
noncomputable def fracCheeger {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℝ :=
  sInf {r : ℝ | ∃ p : Fin n → ℝ, (∀ v, p v ∈ Set.Icc (0 : ℝ) 1) ∧
    0 < fracL G p ∧ fracL G p < vol G Finset.univ ∧
    r = fracF G p / min (fracL G p) (vol G Finset.univ - fracL G p)}

end GraphonCheeger


