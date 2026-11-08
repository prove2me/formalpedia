-- Prove2me | Definitions.Def_CausalFailureRank_Qanalytic
-- name    : CausalFailureRank_Qanalytic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:14:28.541134+00:00
-- url     : https://prove2.me/theorems/35104aa1-3955-41e9-816f-d23cf6fe4439
-- title:
--   Analytic observation quota, eq. (23)
-- statement:
--   With $d_i=\min_xD_{ix}$ and $b_{\max}=\log(C_N/\delta)$, the **analytic quota** is
--   $$Q_i=\Big\lceil\max\Big\{\frac{2(b_{\max}+L_i)}{d_i},\ \frac{8M_i^2}{d_i^2}\log\frac{2N}{\delta}\Big\}\Big\rceil.$$
--   It controls the overflow of the ideal test, and the certificate $\hat Q_i$ dominates it.
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.5, eq. (23), p.18

import Mathlib
import Definitions.Def_CausalFailureRank_coefficient
import Definitions.Def_CausalFailureRank_Qualifies

namespace CausalFailureRank

variable {N q : ℕ}

/-- `d_i = min_x D_ix`, App. B.5, p.18. -/
noncomputable def dmin (I : Instance N q) (i : Fin N) : ℝ := min (D I i false) (D I i true)

/-- `b_max = log (C_N / δ)`, App. B.5, p.18. -/
noncomputable def bmax (N : ℕ) (δ : ℝ) : ℝ := Real.log (CN N / δ)

/-- **The analytic observation quota** `Q_i = ⌈max {2 (b_max + L_i) / d_i, (8 M_i² / d_i²) log (2N/δ)}⌉`,
eq. (23), p.18, of Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC
2027 submission, version of 2026-11-03, sha256 721c8b0d…). Not to be confused with the certificate
`Qhat` of eq. (24), which uses `E_δ`, `M̄`, `L̄`, `d̲`. -/
noncomputable def Qanalytic (I : Instance N q) (δ : ℝ) (i : Fin N) : ℕ :=
  ⌈max (2 * (bmax N δ + Lbound I i) / dmin I i)
      (8 * Mbound I i ^ 2 / dmin I i ^ 2 * Real.log (2 * N / δ))⌉₊

end CausalFailureRank


