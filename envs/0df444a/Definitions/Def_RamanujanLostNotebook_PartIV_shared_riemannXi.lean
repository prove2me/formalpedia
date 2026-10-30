-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIV_shared_riemannXi
-- name    : RamanujanLostNotebook_PartIV_shared_riemannXi
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T14:56:47.022299+00:00
-- url     : https://prove2.me/theorems/6047f872-eb45-4e57-9e50-6e12d734b555
-- title:
--   Ramanujan's Lost Notebook Part IV, shared: riemannXi
-- statement:
--   Riemann's entire function `ξ(s) = (1/2) s (s - 1) π^{-s/2} Γ(s/2) ζ(s)`
--   (equivalently `(s - 1) π^{-s/2} Γ(1 + s/2) ζ(s)`, the form in the book: equation (3.4.29),
--   p. 108, and Chapter 13, p. 293), written through Mathlib's entire function
--   `completedRiemannZeta₀`, which satisfies
--   `completedRiemannZeta s = completedRiemannZeta₀ s - 1/s - 1/(1 - s)` with
--   `completedRiemannZeta s = π^{-s/2} Γ(s/2) ζ(s)`.  Hence
--   `ξ(s) = (1/2) s (s - 1) completedRiemannZeta s` for `s ≠ 0, 1`, and the formula below also
--   gives the correct values `ξ(0) = ξ(1) = 1/2`.  Reference values: `ξ(1/2) = 0.4971207781…`,
--   `ξ(2) = π/6`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013.

import Mathlib

namespace RamanujanLostNotebook.PartIV

/-- Riemann's entire function `ξ(s) = (1/2) s (s - 1) π^{-s/2} Γ(s/2) ζ(s)`
(equivalently `(s - 1) π^{-s/2} Γ(1 + s/2) ζ(s)`, the form in the book: equation (3.4.29),
p. 108, and Chapter 13, p. 293), written through Mathlib's entire function
`completedRiemannZeta₀`, which satisfies
`completedRiemannZeta s = completedRiemannZeta₀ s - 1/s - 1/(1 - s)` with
`completedRiemannZeta s = π^{-s/2} Γ(s/2) ζ(s)`.  Hence
`ξ(s) = (1/2) s (s - 1) completedRiemannZeta s` for `s ≠ 0, 1`, and the formula below also
gives the correct values `ξ(0) = ξ(1) = 1/2`.  Reference values: `ξ(1/2) = 0.4971207781…`,
`ξ(2) = π/6`. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2

end RamanujanLostNotebook.PartIV


