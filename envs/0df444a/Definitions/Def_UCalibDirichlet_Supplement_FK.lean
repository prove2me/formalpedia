-- Prove2me | Definitions.Def_UCalibDirichlet_Supplement_FK
-- name    : UCalibDirichlet_Supplement_FK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:11:38.770423+00:00
-- url     : https://prove2.me/theorems/1e089bc5-65d5-4f1e-bab3-fc43a206bf97
-- title:
--   The potential $F_K(p)=1-(K\min_j p_j)^{1/K}$ of Theorem 1.9
-- statement:
--   For $K\ge 1$ and $p\in\Delta_K$,
--   $$F_K(p)=1-\Big(K\min_{j\in[K]}p_j\Big)^{1/K}.$$
--   Since $p\mapsto\min_j p_j$ is concave and nonnegative on $\Delta_K$, $F_K$ is convex and continuous, vanishes at the uniform distribution $\mathbf 1/K$ (where it is minimal) and takes values in $[0,1]$.
--
--   This is the potential of Theorem 1.9, for which Algorithm 1 provably loses a factor $K$ against the minimax regret.
--
--   **Formalization Note** The minimum is the infimum over the finite index set; the power is the real power. Values off the simplex are irrelevant.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Theorem 1.9, p.6; proof of Theorem 1.9, p.33

import Mathlib

namespace UCalibDirichlet.Supplement

/-- **The potential `F_K` of Theorem 1.9.** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027
submission), Theorem 1.9, p.6: "For `K ≥ 3`, consider the loss function `ℓ_F` with a convex potential
`F(p) = 1 − (K min_{j∈[K]} p_j)^{1/K}`"; proof, p.33: "`F` is convex, continuous, normalized at
`u = 𝟏/K` (Eq. (4)), and bounded between zero and one".

`FK K p = 1 − (K · min_j p_j)^{1/K}`.

**Formalization Note.** `min_j p_j` is the real infimum `⨅ j, p j` over the finite index type
`Fin K` (a minimum when `K ≥ 1`); the power is `Real.rpow`. On the simplex `min_j p_j ≥ 0`, so the
base of the power is nonnegative. Values off `Δ_K` are irrelevant. -/
noncomputable def FK (K : ℕ) (p : Fin K → ℝ) : ℝ :=
  1 - ((K : ℝ) * ⨅ j, p j) ^ ((1 : ℝ) / K)

end UCalibDirichlet.Supplement


