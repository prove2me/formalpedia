-- Prove2me | Definitions.Def_EuclidDiamStream_hamBall
-- name    : EuclidDiamStream_hamBall
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:15.207222+00:00
-- url     : https://prove2.me/theorems/89ef07c6-4430-45ae-97d2-639060858468
-- title:
--   Hypercube, its embedding in the grid, Hamming distance and Hamming ball $\mathcal B(x,\tau)$
-- statement:
--   For $x,z\in\{0,1\}^d$, the **Hamming distance** is $\mathrm{Ham}(x,z)=|\{i\in[d]:x_i\ne z_i\}|$, and the **Hamming ball** of radius $\tau$ around $x$ is
--   $$\mathcal B(x,\tau)=\{z\in\{0,1\}^d:\mathrm{Ham}(x,z)\le\tau\}.$$
--   The hypercube is viewed as a subset of the grid $\{0,\dots,\Delta\}^d$ by sending bits to the values $0$ and $1$ coordinatewise.
--
--   The hard distribution and the ball-subspace-evasion property are both phrased with these balls.
--
--   **Formalization Note** The embedding is injective exactly when $\Delta\ge1$, which every theorem of the mission assumes.
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.7 (§3), p.8 (Def. 3.1)

import Mathlib
import Definitions.Def_EuclidDiamStream_Point

namespace EuclidDiamStream

/-- The Boolean hypercube `{0,1}^d` of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), §3, p.7. -/
abbrev Cube (d : ℕ) : Type := Fin d → Bool

/-- The embedding of `{0,1}^d` in `{0,…,Δ}^d` (Definition 3.1, p.8: "viewing `{0,1}^d` as a subset of
`{0,…,Δ}^d`"), with `false ↦ 0` and `true ↦ 1`.

**Formalization Note.** It is injective exactly when `Δ ≥ 1`, which every theorem of the mission
assumes. -/
def embed {d : ℕ} (Δ : ℕ) (b : Cube d) : Point d Δ :=
  fun i => if b i then 1 else 0

/-- The Hamming distance `Ham(x,z) = |{i ∈ [d] : x_i ≠ z_i}|`, p.7. -/
def ham {d : ℕ} (x z : Cube d) : ℕ :=
  hammingDist x z

/-- The Hamming ball `B(x,τ) = {z ∈ {0,1}^d : Ham(x,z) ≤ τ}`, p.7. -/
def hamBall {d : ℕ} (x : Cube d) (τ : ℕ) : Finset (Cube d) :=
  Finset.univ.filter (fun z => ham x z ≤ τ)

end EuclidDiamStream


