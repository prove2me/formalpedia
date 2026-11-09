-- Prove2me | Definitions.Def_DerandSq_delta
-- name    : DerandSq_delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:57:09.244687+00:00
-- url     : https://prove2.me/theorems/da8dd903-7c88-47d7-b3a3-f6ac7913f551
-- title:
--   Indicator vectors $\delta_g$
-- statement:
--   For $g \in \Gamma$, $\delta_g \in \ell^2(\Gamma)$ is the indicator of $g$: $\delta_g(h) = 1$ if $h = g$ and $0$ otherwise. The $\delta_g$ form the standard orthonormal basis of $\ell^2(\Gamma)$.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Example 2.4, p.8

import Mathlib
import Definitions.Def_DerandSq_L2

namespace DerandSq

/-- The indicator `δ_g ∈ ℓ²(Γ)`, `δ_g(h) = 1[g = h]` (Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), Example 2.4, p.8). -/
noncomputable def delta {Γ : Type*} (g : Γ) : L2 Γ :=
  by classical exact lp.single 2 g (1 : ℂ)

end DerandSq


