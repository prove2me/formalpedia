-- Prove2me | Definitions.Def_HolevoEntropyGain_ratioMatrix
-- name    : HolevoEntropyGain_ratioMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:07.384605+00:00
-- url     : https://prove2.me/theorems/42b18253-4271-431b-91d2-f1bebf415116
-- title:
--   The matrix $\Delta^{-1}\alpha$
-- statement:
--   For real $2s\times2s$ matrices $\Delta$ (invertible) and $\alpha$, the matrix $\Delta^{-1}\alpha$, regarded as a complex matrix. For a covariance matrix $\alpha$ its eigenvalues are $\pm i\alpha_j$, where $\alpha_j\ge\frac12$ are the symplectic eigenvalues of $\alpha$ (Appendix, p.8); it is diagonalizable but not normal in general.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, Lemma 2, eqs. (18)–(19), p.5; Appendix, p.8

import Mathlib

namespace HolevoEntropyGain

/-- The matrix `Δ⁻¹α`, as a complex matrix (Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, Lemma 2, eqs. (18)–(19), p.5, PDF p.5). Its
eigenvalues are `±iαⱼ` (Appendix, p.8). -/
noncomputable def ratioMatrix {s : ℕ} (Δ α : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ) :
    Matrix (Fin (2 * s)) (Fin (2 * s)) ℂ :=
  (Δ⁻¹ * α).map Complex.ofReal

end HolevoEntropyGain


