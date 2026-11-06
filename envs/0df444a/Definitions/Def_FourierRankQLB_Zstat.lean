-- Prove2me | Definitions.Def_FourierRankQLB_Zstat
-- name    : FourierRankQLB_Zstat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:43:18.579466+00:00
-- url     : https://prove2.me/theorems/29a6c34f-ed75-4803-b82b-5cc0b69565e1
-- title:
--   The statistic $Z(Q,v)=\sqrt{a_d\,d\,v^TA_Q^{-1}v}$
-- statement:
--   For $Q\in O(d)$ and $v\in\mathbb R^d$,
--   $$
--   Z(Q,v)=\sqrt{a_d\,d\;v^TA_Q^{-1}v} .
--   $$
--   The factor $a_dd$ makes the thresholds absolute constants. By (52), $Z$ is a rescaled optimal value of the linear objective $\overline v$ over $K_{s,Q}$, and by Lemma 4.7 it separates the two determinant components.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (45), p.28

import Mathlib
import Definitions.Def_FourierRankQLB_AQ
import Definitions.Def_FourierRankQLB_ad

open Matrix

namespace FourierRankQLB

/-- The statistic `Z(Q, v) = √(a_d d vᵀ A_Q⁻¹ v)` of Eq. (45).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (45), p. 28.

**Formalization Note.** `(AQ Q)⁻¹` is the matrix inverse; `A_Q` is positive definite for `d ≥ 2`, so
this is the true inverse wherever the paper uses it. -/
noncomputable def Zstat {d : ℕ} (Q : Od d) (v : Fin d → ℝ) : ℝ :=
  √(ad d * d * (v ⬝ᵥ ((AQ Q)⁻¹ *ᵥ v)))

end FourierRankQLB


