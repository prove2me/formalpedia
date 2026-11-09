-- Prove2me | Definitions.Def_HybridXorLift_cubeAvg
-- name    : HybridXorLift_cubeAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:46.040264+00:00
-- url     : https://prove2.me/theorems/0b5bb3fc-354c-4ca3-b1d9-285726791b42
-- title:
--   Average over a subcube $\mathbb E_{z : z_J = \xi}$
-- statement:
--   For $J \subseteq [n]$, an assignment $\xi \in \{0,1\}^J$ and a function $g$ on $\{0,1\}^n$, the **subcube average** is
--   $$
--   \mathbb E_{z : z_J = \xi}\, g(z) = \frac{1}{2^{n - |J|}} \sum_{z \in \{0,1\}^n,\ z_J = \xi} g(z).
--   $$
--
--   **Formalization Note** The partial assignment $\xi$ is given as a full string of which only the coordinates in $J$ are read, so the average depends only on $\xi|_J$.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §3.3, p.13 (PDF p.15)

import Mathlib

namespace HybridXorLift

/-- The uniform average `E_{z : z_J = ξ} g(z)` over the outer strings that agree with a partial
assignment `ξ ∈ {0,1}^J` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §3.3, p.13 (PDF p.15)).

**Formalization Note** The partial assignment `ξ` is a full function `Fin n → Bool` of which only
the values on `J` are read; the average is over the full strings `z` with `z_i = ξ_i` for
`i ∈ J`, so it depends on `ξ` only through `ξ|_J`. -/
noncomputable def cubeAvg {n : ℕ} (J : Finset (Fin n)) (ξ : Fin n → Bool)
    (g : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ z ∈ Finset.univ.filter (fun z : Fin n → Bool => ∀ i ∈ J, z i = ξ i), g z) /
    ((Finset.univ.filter (fun z : Fin n → Bool => ∀ i ∈ J, z i = ξ i)).card : ℝ)

end HybridXorLift


