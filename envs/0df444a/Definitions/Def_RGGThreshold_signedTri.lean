-- Prove2me | Definitions.Def_RGGThreshold_signedTri
-- name    : RGGThreshold_signedTri
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:59:03.277138+00:00
-- url     : https://prove2.me/theorems/f70b6f12-1491-4d68-9f68-9d1ca8b118bf
-- title:
--   Signed counts $N_\triangle$, $N_\square$, $N_\diamond$ of triangles, four-cycles and diamonds
-- statement:
--   For a graph $H$ on $[n]$ with adjacency matrix $A$ and a fixed graph $F$, the **signed count** of $F$ in $H$ is
--
--   $$
--   N_F(H)=\sum_{F\subseteq K_n}\ \prod_{ij\in E(F)}(A_{ij}-p),
--   $$
--
--   the sum running over all unlabeled copies of $F$ in $K_n$. Three cases are used: the triangle,
--
--   $$
--   N_\triangle(H)=\sum_{1\le i<j<k\le n}(A_{ij}-p)(A_{jk}-p)(A_{ik}-p),
--   $$
--
--   the four-cycle $N_\square$, and the diamond $N_\diamond$ (the unique graph with four vertices and five edges). Each count is also taken on the induced subgraph $H_s$ on $\{s+1,\dots,n\}$.
--
--   **Formalization Note** The counts are taken over a vertex set $S$ ($S$ = all vertices for $H$, the tail set for $H_s$). The copies are enumerated explicitly: a 4-set $i<j<k<l$ carries three 4-cycles ($ijkl$, $ijlk$, $ikjl$) and six diamonds (one for each pair left out of $K_4$). The sanity file checks that on $K_4$ at $p=0$ the three counts are $4$, $3$, $6$.
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), (1), p.2 (PDF p.4); §2.1, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_RGGThreshold_centredAdj

namespace RGGThreshold

/-- The signed triangle count of `H` on a vertex set `S` (Hunter–Milojević–Sudakov,
arXiv:2607.22480, held version, sha256 1a398ef9…, (1), p.2 (PDF p.4)):
`N_△ = ∑_{i<j<k in S} (A_{ij}-p)(A_{jk}-p)(A_{ik}-p)`.

**Formalization Note** `S = univ` gives `N_△(H)`; `S = tailSet n s` gives `N_△(H_s)` for the
induced subgraph `H_s` on the paper's `{s+1, …, n}`. -/
noncomputable def signedTri {n : ℕ} (p : ℝ) (H : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, ∑ k ∈ S,
    if i < j ∧ j < k then centredAdj p H i j * centredAdj p H j k * centredAdj p H i k else 0

/-- The signed four-cycle count `N_□` of `H` on a vertex set `S` (arXiv:2607.22480, held version,
§2.1, p.4 (PDF p.6): `N_F(H) = ∑_{F ⊆ K_n} ∏_{ij ∈ E(F)} (A_{ij} - p)`, the sum over all unlabeled
copies of `F` in `K_n`, for `F = C_4`).

**Formalization Note** The unlabeled copies of `C_4` are enumerated explicitly: every 4-set
`i < j < k < l` carries exactly three 4-cycles, `ijkl`, `ijlk` and `ikjl`. -/
noncomputable def signedC4 {n : ℕ} (p : ℝ) (H : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℝ :=
  let A := centredAdj p H
  ∑ i ∈ S, ∑ j ∈ S, ∑ k ∈ S, ∑ l ∈ S,
    if i < j ∧ j < k ∧ k < l then
      A i j * A j k * A k l * A l i + A i j * A j l * A l k * A k i +
        A i k * A k j * A j l * A l i
    else 0

/-- The signed diamond count `N_◇` of `H` on a vertex set `S` (arXiv:2607.22480, held version,
§2.1, p.4 (PDF p.6): "a diamond is the unique graph with four vertices and five edges";
`N_F(H) = ∑_{F ⊆ K_n} ∏_{ij ∈ E(F)} (A_{ij} - p)` over unlabeled copies).

**Formalization Note** The unlabeled copies of the diamond are enumerated explicitly: every 4-set
`i < j < k < l` carries exactly six diamonds, one for each of its six pairs left out; the summand
is the product of `A_{e} - p` over the five remaining pairs. -/
noncomputable def signedDia {n : ℕ} (p : ℝ) (H : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℝ :=
  let A := centredAdj p H
  ∑ i ∈ S, ∑ j ∈ S, ∑ k ∈ S, ∑ l ∈ S,
    if i < j ∧ j < k ∧ k < l then
      A i k * A i l * A j k * A j l * A k l + A i j * A i l * A j k * A j l * A k l +
        A i j * A i k * A j k * A j l * A k l + A i j * A i k * A i l * A j l * A k l +
        A i j * A i k * A i l * A j k * A k l + A i j * A i k * A i l * A j k * A j l
    else 0

end RGGThreshold


