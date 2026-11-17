-- Prove2me | Definitions.Def_GraphonCheeger_Supplement_kSection
-- name    : GraphonCheeger_Supplement_kSection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:21:52.030794+00:00
-- url     : https://prove2.me/theorems/3887ab53-1ed5-43ae-a21a-b48efa9af0cc
-- title:
--   Minimum $k$-section: $\mathrm{MS}_k(G)$, $C_k(W,\Psi)$, $\mathrm{MS}_{k,\mathrm{mix}}(W)$, $\mathrm{MS}_{k,\mathrm{pure}}(W)$
-- statement:
--   Fix $k\ge2$. For a graph $G$ on $[n]$,
--   $$
--   \mathrm{MS}_k(G)=\frac1{n^2}\min_{\substack{A_1,\dots,A_k\text{ partition of }[n]\\|A_i|\in\{\lfloor n/k\rfloor,\lceil n/k\rceil\}}}\ \sum_{1\le i<j\le k}e_G(A_i,A_j),
--   $$
--   where $e_G(A_i,A_j)$ counts the edges between $A_i$ and $A_j$. For a graphon $W$ on $(\Omega,\mathcal F,\mu)$ and a mixed $k$-colouring $\Psi$, the colouring score is $C_k(W,\Psi)=\sum_{1\le i<j\le k}\iint W(x,y)\psi_i(x)\psi_j(y)\,d\mu\,d\mu$, and $\Psi$ is **balanced** if $\int\psi_i\,d\mu=1/k$ for all $i$. Then
--   $$
--   \mathrm{MS}_{k,\mathrm{mix}}(W)=\inf_{\Psi\text{ balanced}}C_k(W,\Psi),\qquad
--   \mathrm{MS}_{k,\mathrm{pure}}(W)=\inf_{\substack{S_1,\dots,S_k\text{ measurable partition}\\\mu(S_i)=1/k}}\ \sum_{1\le i<j\le k}\iint_{S_i\times S_j}W\,d\mu\,d\mu,
--   $$
--   with $\inf\emptyset=+\infty$ in the pure case; the paper sets $\mathrm{MS}_k(W):=\mathrm{MS}_{k,\mathrm{mix}}(W)$.
--
--   These are the parameters of Theorems 4.14–4.17.
--
--   **Formalization Note** A partition of `Fin n` into $k$ labelled parts is a map $\chi$ to `Fin k` (parts may be empty), with $\lceil n/k\rceil=(n+k-1)/k$; $\sum_{i<j}e_G(A_i,A_j)$ is the number of ordered adjacent pairs $(u,v)$ with $\chi(u)<\chi(v)$, which counts each edge between distinct parts once. The mixed infimum is over a nonempty set (the constant colouring $1/k$) bounded below by $0$. The pure version ranges over measurable $\chi:\Omega\to[k]$ with $\mu(\chi^{-1}(i))=1/k$ and is valued in `EReal`, so that the empty infimum is $+\infty$ as on p.37.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), §4.2, (4.42)–(4.49), pp.37–38

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_homDens

open MeasureTheory

namespace GraphonCheeger.Supplement

/-!
# Minimum `k`-section of graphs and graphons: `MS_k(G)`, `C_k(W, Ψ)`, `MS_{k,mix}(W)`,
`MS_{k,pure}(W)`

Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…), §4.2, (4.42)–(4.49), pp.37–38.

**Formalization Note.**
* Graphs have vertex set `Fin n`. A partition `A_1, …, A_k` of `[n]` is a map `χ : Fin n → Fin k`
  (`A_i = χ⁻¹(i)`, parts may be empty), balanced when every `|A_i|` is `⌊n/k⌋` or
  `⌈n/k⌉ = (n + k − 1)/k`. `Σ_{i<j} e_G(A_i, A_j)` is the number of ordered pairs `(u, v)` with
  `u ∼ v` and `χ(u) < χ(v)`: each edge between distinct parts is counted once.
* `C_k(W, Ψ) = Σ_{1 ≤ i < j ≤ k} ∬ W(x, y) ψ_i(x) ψ_j(y)` (4.46). `Ψ` is balanced if
  `∫ ψ_i dµ = 1/k` for every `i`. `MS_{k,mix}(W)` (4.48) is the infimum over balanced mixed
  colourings; the set is nonempty (`ψ_i ≡ 1/k`) and bounded below by `0`. `MS_k(W) := MS_{k,mix}(W)`
  (4.49).
* `MS_{k,pure}(W)` (4.43), (4.45) is the infimum over measurable partitions `S_1, …, S_k` of `Ω`
  with `µ(S_i) = 1/k`, i.e. over measurable `χ : Ω → [k]` with `µ(χ⁻¹(i)) = 1/k`, of
  `C_k(W, χ)`; it is valued in `EReal` with `inf ∅ = +∞`, as on p.37.
-/

universe u

open Classical in
/-- `MS_k(G) = n^{-2} min Σ_{1 ≤ i < j ≤ k} e_G(A_i, A_j)` over partitions `A_1, …, A_k` of `[n]`
with every `|A_i| ∈ {⌊n/k⌋, ⌈n/k⌉}` ((4.42), p.37). -/
noncomputable def minSectionG (k : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  sInf {r : ℝ | ∃ χ : Fin n → Fin k,
    (∀ i, (Finset.univ.filter (fun v => χ v = i)).card = n / k ∨
      (Finset.univ.filter (fun v => χ v = i)).card = (n + k - 1) / k) ∧
    r = ((Finset.univ.filter (fun p : Fin n × Fin n => χ p.1 < χ p.2 ∧ G.Adj p.1 p.2)).card : ℝ) /
      (n : ℝ) ^ 2}

/-- The colouring score `C_k(W, Ψ) = Σ_{1 ≤ i < j ≤ k} ∬ W(x, y) ψ_i(x) ψ_j(y) dµ dµ`
((4.12), (4.46), pp.31, 37). -/
noncomputable def colScore {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) {k : ℕ}
    (W : Ω → Ω → ℝ) (Ψ : Ω → Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, ∑ j : Fin k,
    if i < j then ∫ p, W p.1 p.2 * Ψ p.1 i * Ψ p.2 j ∂(μ.prod μ) else 0

/-- A colouring `Ψ ∈ Λ_k` is **balanced** if `∫ ψ_i dµ = 1/k` for every `i ∈ [k]` (p.37). -/
def IsBalanced {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) {k : ℕ}
    (Ψ : Ω → Fin k → ℝ) : Prop :=
  ∀ i, ∫ x, Ψ x i ∂μ = 1 / (k : ℝ)

/-- `MS_{k,mix}(W) = inf_{Ψ ∈ Λ_k balanced} C_k(W, Ψ)` ((4.48), p.37), and
`MS_k(W) := MS_{k,mix}(W)` (4.49). -/
noncomputable def minSectionMix (k : ℕ) {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : Ω → Ω → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ Ψ : Ω → Fin k → ℝ, IsKColouring Ψ ∧ IsBalanced μ Ψ ∧ r = colScore μ W Ψ}

/-- `MS_{k,pure}(W) = inf Σ_{1 ≤ i < j ≤ k} ∬_{S_i × S_j} W dµ dµ` over measurable partitions
`S_1, …, S_k` of `Ω` with `µ(S_i) = 1/k` ((4.43), (4.45), p.37), with `inf ∅ = +∞`. -/
noncomputable def minSectionPure (k : ℕ) {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : Ω → Ω → ℝ) : EReal :=
  sInf {r : EReal | ∃ χ : Ω → Fin k, Measurable χ ∧ (∀ i, μ (χ ⁻¹' {i}) = (k : ENNReal)⁻¹) ∧
    r = ((colScore μ W (ofColour χ) : ℝ) : EReal)}

end GraphonCheeger.Supplement


