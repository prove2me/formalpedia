-- Prove2me | Definitions.Def_DerandSq_L2
-- name    : DerandSq_L2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:53:54.610597+00:00
-- url     : https://prove2.me/theorems/19fe782c-1675-4033-89d0-d66d0de4c55a
-- title:
--   $\ell^2(\Gamma)$
-- statement:
--   For a discrete group $\Gamma$, $\ell^2(\Gamma) = \{\xi : \Gamma \to \mathbb C : \sum_{g} |\xi(g)|^2 < \infty\}$ is the Hilbert space of square-summable functions on $\Gamma$.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Example 2.4, p.8

import Mathlib

namespace DerandSq

/-- `ℓ²(Γ)`, the Hilbert space of square-summable complex functions on a discrete group `Γ`
(Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), Example 2.4, p.8). -/
noncomputable abbrev L2 (Γ : Type*) := lp (fun _ : Γ => ℂ) 2

end DerandSq


