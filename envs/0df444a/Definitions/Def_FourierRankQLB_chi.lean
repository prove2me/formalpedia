-- Prove2me | Definitions.Def_FourierRankQLB_chi
-- name    : FourierRankQLB_chi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:32.617293+00:00
-- url     : https://prove2.me/theorems/5072e305-e045-4245-948b-6e21f10082fd
-- title:
--   The character $\chi_\Xi(Q)=e^{i\operatorname{Tr}(\Xi^TQ)}$
-- statement:
--   For a frequency matrix $\Xi\in\mathbb R^{n\times n}$ and $Q\in O(n)$,
--   $$
--   \chi_\Xi(Q)=e^{i\operatorname{Tr}(\Xi^TQ)} .
--   $$
--   The rank of $\Xi$ is the Fourier rank of $\chi_\Xi$, the quantity the lower-bound method tracks in place of polynomial degree.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Definition 3.1, Eq. (16), p.16

import Mathlib
import Definitions.Def_FourierRankQLB_Od

open Matrix

namespace FourierRankQLB

/-- The character `χ_Ξ(Q) = e^{i Tr(ΞᵀQ)}` of Eq. (16).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Definition 3.1, Eq. (16), p. 16. -/
noncomputable def chi {n : ℕ} (Ξ : Matrix (Fin n) (Fin n) ℝ) (Q : Od n) : ℂ :=
  Complex.exp (Complex.I * ((Ξᵀ * (Q : Matrix (Fin n) (Fin n) ℝ)).trace : ℝ))

end FourierRankQLB


