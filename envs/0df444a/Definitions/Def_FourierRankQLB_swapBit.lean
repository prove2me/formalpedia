-- Prove2me | Definitions.Def_FourierRankQLB_swapBit
-- name    : FourierRankQLB_swapBit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:16.610584+00:00
-- url     : https://prove2.me/theorems/d90fe87e-adee-4556-8574-a3b815180e55
-- title:
--   The answer-bit flip on $\mathbb C^2\otimes W$
-- statement:
--   The unitary $|b\rangle\mapsto|b\oplus1\rangle$ on the answer bit, acting as the identity on the workspace $W$. It exchanges the two components of an element of $\mathbb C^2\otimes W$ and is an involution.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (6), p.14

import Mathlib

namespace FourierRankQLB

/-- The flip `|b⟩ ↦ |b ⊕ 1⟩` of the answer bit on `ℂ² ⊗ W`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (6), p. 14. -/
noncomputable def swapBit (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] :
    (PiLp 2 fun _ : Bool => W) ≃ₗᵢ[ℂ] (PiLp 2 fun _ : Bool => W) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ W Equiv.boolNot

theorem swapBit_swapBit (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (x : PiLp 2 fun _ : Bool => W) : swapBit W (swapBit W x) = x := by
  ext b
  simp [swapBit, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

end FourierRankQLB


