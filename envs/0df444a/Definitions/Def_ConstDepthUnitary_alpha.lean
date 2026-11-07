-- Prove2me | Definitions.Def_ConstDepthUnitary_alpha
-- name    : ConstDepthUnitary_alpha
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:31.168602+00:00
-- url     : https://prove2.me/theorems/6fd7dbc9-6e0f-412b-b793-876e10995b24
-- title:
--   The grid: $\alpha(a)$ and $L$
-- statement:
--   For $K$ points per dimension, with spacing $\Delta=\sqrt{2\pi/K}$, the integer $a$ sits at position
--   $$\alpha(a)=\Bigl(a-\frac{K-1}{2}\Bigr)\sqrt{\frac{2\pi}{K}},$$
--   applied coordinatewise on $[K]^N$. The grid extends over $[-L,L]$ with $L=\sqrt{K\pi/2}$, so $2L=\sqrt{2\pi K}=K\Delta$.
--
--   **Formalization Note** $[K]=\{0,\dots,K-1\}$ is `Fin K`. All statements using these objects assume $K>0$.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §5.1.1, pp.22–23

import Mathlib

namespace ConstDepthUnitary

/-- The position of the integer `a` on the grid of `K` points per dimension:
`α(a) = (a − (K−1)/2) Δ`, with spacing `Δ = √(2π/K)`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §5.1.1, p.23. -/
noncomputable def alpha (K : ℕ) (a : ℤ) : ℝ :=
  ((a : ℝ) - ((K : ℝ) - 1) / 2) * Real.sqrt (2 * Real.pi / K)

/-- `α` applied coordinatewise to `v ∈ [K]^N` (§5.1.1, p.23). -/
noncomputable def alphaVec {N : ℕ} (K : ℕ) (v : Fin N → Fin K) : Fin N → ℝ :=
  fun j => alpha K ((v j : ℕ) : ℤ)

/-- How far the grid extends in each direction, `L = √(Kπ/2)` (§5.1.1, p.22), so that `2L = √(2πK)`. -/
noncomputable def gridL (K : ℕ) : ℝ := Real.sqrt ((K : ℝ) * Real.pi / 2)

end ConstDepthUnitary


