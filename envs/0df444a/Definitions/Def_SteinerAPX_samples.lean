-- Prove2me | Definitions.Def_SteinerAPX_samples
-- name    : SteinerAPX_samples
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:35:57.621493+00:00
-- url     : https://prove2.me/theorems/38519b79-71f8-4e99-99fc-0f0847c06ae8
-- title:
--   The sampled terminals $P_\rho$ of a cable layout
-- statement:
--   Let $0<\rho\le 1/100$. For a cable segment $[a,b]$ of length $t$, place the $\lceil t/\rho^2\rceil+1$ equally spaced points
--   $$
--   a+\tfrac{j}{N}(b-a),\qquad j=0,1,\dots,N,\qquad N=\lceil t/\rho^2\rceil,
--   $$
--   including both endpoints. $P_\rho$ is the union of these points over all segments of all cables. The points on segments of $\Gamma_i$ are the **sampled terminals on $\Gamma_i$**, and the **edges between consecutive terminals** of $[a,b]$ are the $N$ segments joining the $j$-th and $(j+1)$-th points.
--
--   $P_\rho$ is the Euclidean Steiner Tree instance produced by the cable reduction; consecutive terminals are between $\rho^2/2$ and $\rho^2$ apart on segments of length at least $1$.
--
--   **Formalization Note** The sample set depends on how a cable is cut into segments, which the layout fixes. A degenerate segment (excluded by separation) would contribute the single point $a$.
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), §4.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_SteinerAPX_CableLayout

namespace SteinerAPX

open Inst3DM CableLayout

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Sampled terminals `Pρ`.** S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*, STOC
2027 submission (manuscript sha256 6f78a9ea…), §4.1, p.14 (PDF p.16): "For 0 < ρ ≤ 1/100, we form
Pρ by placing ⌈t/ρ2⌉ + 1 equally spaced terminals along each cable segment of length t, including
both endpoints. Consecutive terminals along a segment are at distance in [ρ2/2, ρ2], and the edges
between them have total length L, with |Pρ| = Θ(L/ρ2)."

`segSamples a b ρ` is the set of the `N + 1` points `a + (j/N)(b − a)`, `j = 0, …, N`, with
`N = ⌈t/ρ²⌉` and `t = |b − a|`. `samples L ρ` is `Pρ`, the union over all segments of all cables;
`cableSamples L ρ i` the sampled terminals on the cable `Γᵢ`; `sampleEdges a b ρ` the `N` edges
between consecutive samples of the segment `[a, b]`.

**Formalization Note** The range `0 < ρ ≤ 1/100` is a hypothesis of each statement. The sample
set of a cable depends on how the cable is cut into segments, which the layout fixes. For a
degenerate segment (`t = 0`, excluded by (S2)) the formula gives the single point `a`. -/
noncomputable def segSamples (a b : V) (ρ : ℝ) : Set V :=
  {x | ∃ j : ℕ, j ≤ ⌈dist a b / ρ ^ 2⌉₊ ∧
    x = AffineMap.lineMap a b ((j : ℝ) / (⌈dist a b / ρ ^ 2⌉₊ : ℝ))}

/-- `Pρ`: the sampled terminals of all cable segments. -/
noncomputable def samples {H : Inst3DM} (L : CableLayout H V) (ρ : ℝ) : Set V :=
  ⋃ i : Label H, ⋃ e ∈ L.cable i, segSamples e.1 e.2 ρ

/-- The sampled terminals on the cable `Γᵢ`. -/
noncomputable def cableSamples {H : Inst3DM} (L : CableLayout H V) (ρ : ℝ) (i : Label H) :
    Set V :=
  ⋃ e ∈ L.cable i, segSamples e.1 e.2 ρ

/-- The edges between consecutive samples of the segment `[a, b]`. -/
noncomputable def sampleEdges (a b : V) (ρ : ℝ) : Network V := by
  classical
  exact (Finset.range ⌈dist a b / ρ ^ 2⌉₊).image fun j =>
    (AffineMap.lineMap a b ((j : ℝ) / (⌈dist a b / ρ ^ 2⌉₊ : ℝ)),
     AffineMap.lineMap a b (((j : ℝ) + 1) / (⌈dist a b / ρ ^ 2⌉₊ : ℝ)))

end SteinerAPX


