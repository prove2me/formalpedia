-- Prove2me | Definitions.Def_GarberOLO_Alg3_extOracle
-- name    : GarberOLO_Alg3_extOracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:50:39.318369+00:00
-- url     : https://prove2.me/theorems/bb57351b-a9c8-46c9-8688-cf0429fe96e7
-- title:
--   The extended approximation oracle $\hat{\mathcal O}_K$ (eq. (2))
-- statement:
--   Given an oracle $\mathcal O_K$, the **extended approximation oracle** maps $c \in \mathbb R^d$ to the pair
--   $$\hat{\mathcal O}_K(c) = (v, s) := \begin{cases} \big(\mathcal O_K(c^+) - \alpha R\, \overline{c^-},\ \mathcal O_K(c^+)\big) & \alpha \ge 1,\\ \big(\mathcal O_K(-c^-) - R\, \overline{c^+},\ \mathcal O_K(-c^-)\big) & \alpha < 1.\end{cases}$$
--
--   The vector $v$ optimizes over $\alpha K$ in every direction of $\mathbb R^d$ (Lemma 1) but need not be feasible; $s \in K$ is a feasible point dominating $v$ on $\mathcal F$. Each evaluation makes exactly one call to $\mathcal O_K$, always at a vector of $\mathbb R^d_+$.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Lemma 1, eq. (2), p. 6

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting
import Definitions.Def_GarberOLO_Alg3_cPlus
import Definitions.Def_GarberOLO_Alg3_cMinus
import Definitions.Def_GarberOLO_Alg3_unitDir

namespace GarberOLO.Alg3

/-- **The extended approximation oracle Ô_K** (Lemma 1, eq. (2)).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Lemma 1, eq. (2), p. 6:
"Ô_K(c) = (v, s) := (O_K(c⁺) − αR c̄⁻, O_K(c⁺)) if α ≥ 1; (O_K(−c⁻) − R c̄⁺, O_K(−c⁻)) if α < 1".

`extOracle S OK c` is the pair `(v, s)`; `(extOracle S OK c).1 = v` and `(extOracle S OK c).2 = s`.
One call of Ô_K makes exactly one call of the oracle `OK`, always at a vector of ℝᵈ₊
(`cPlus c` or `-cMinus c`).

**Formalization Note.** The oracle `OK` is a parameter (any function); the guarantee
`IsApproxOracle` is a hypothesis of the theorems, not part of this definition. -/
noncomputable def extOracle {d : ℕ} (S : Setting d)
    (OK : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (c : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) :=
  if 1 ≤ S.α then
    (OK (cPlus c) - (S.α * S.R) • unitDir (cMinus c), OK (cPlus c))
  else
    (OK (-cMinus c) - S.R • unitDir (cPlus c), OK (-cMinus c))

end GarberOLO.Alg3


