-- Prove2me | Definitions.Def_TractableComposite_theta
-- name    : TractableComposite_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:35.305525+00:00
-- url     : https://prove2.me/theorems/7352c44c-8522-4926-b004-70e42291efd5
-- title:
--   The slope $\vartheta(\pi,i,j)$
-- statement:
--   For a movement vector $\pi$, let $m(i,j)$ be the index $k$ of the move that is the $j$-th step in direction $i$. Then
--
--   $$\vartheta(\pi,i,j)=\frac{\phi(\mathcal V_{\cdot n}(\pi,m(i,j)))-\phi(\mathcal V_{\cdot n}(\pi,m(i,j)-1))}{a_{ij}-a_{i,j-1}},\qquad 1\le j\le n,$$
--
--   the slope of $\phi$ along that move.
--
--   **Formalization Note.** $m(i,j)$ is the least $k$ with $\Pi(\pi,k)_i\ge j$.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), p.11

import Mathlib
import Definitions.Def_TractableComposite_gridPt

namespace TractableComposite

/-- **ϑ(π, i, j)**, p.11: `ϑ(π,i,j) = (φ(𝒱·ₙ(π, m(i,j))) − φ(𝒱·ₙ(π, m(i,j)−1)))/(aᵢⱼ − a_{i,j−1})`, where
`m(i,j)` is the index `k` of the move that is the `j`-th step in direction `i`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), p.11.

**Formalization Note.** `m(i,j)` is the least `k` with `Π(π,k)ᵢ ≥ j` (`sInf`; it exists for
`1 ≤ j ≤ n` and a movement vector). `𝒱·ₙ(π,k) = (a_{i', Π(π,k)ᵢ'})ᵢ'`. Used only for `1 ≤ j ≤ n`. -/
noncomputable def theta {d n : ℕ} (a : Fin d → Fin (n + 1) → ℝ) (φ : (Fin d → ℝ) → ℝ) (π : Fin (d * n) → Fin d)
    (i : Fin d) (j : Fin (n + 1)) : ℝ :=
  let m := sInf {k : ℕ | j.val ≤ (gridPt π k i).val}
  (φ (fun i' => a i' (gridPt π m i')) - φ (fun i' => a i' (gridPt π (m - 1) i'))) /
    (a i j - a i ⟨j.val - 1, by omega⟩)

end TractableComposite


