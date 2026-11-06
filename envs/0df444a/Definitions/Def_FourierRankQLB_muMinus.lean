-- Prove2me | Definitions.Def_FourierRankQLB_muMinus
-- name    : FourierRankQLB_muMinus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:45.612407+00:00
-- url     : https://prove2.me/theorems/2b94382e-d091-4a5e-bc15-9415b33aab81
-- title:
--   The conditional Haar law $\mu_{d,-}$ on the reflection component
-- statement:
--   The probability measure $\mu_{d,-}$: the Haar measure $\mu_d$ conditioned on the component $O_-(d)=\{Q\in O(d):\det Q=-1\}$.
--
--   It is the law of the hidden matrix on the negative determinant component.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §3.2, p.19

import Mathlib
import Definitions.Def_FourierRankQLB_haarO

open MeasureTheory

namespace FourierRankQLB

/-- `μ_{d,-}`: the Haar measure of `O(d)` conditioned on the component `det Q = -1`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §3.2, p. 19. -/
noncomputable def muMinus (d : ℕ) : Measure (Od d) :=
  ProbabilityTheory.cond (haarO d) {Q | (Q : Matrix (Fin d) (Fin d) ℝ).det = -1}

end FourierRankQLB


