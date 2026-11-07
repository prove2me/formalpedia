-- Prove2me | Definitions.Def_PRUPermLayer_cliffordLaw
-- name    : PRUPermLayer_cliffordLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:50.923205+00:00
-- url     : https://prove2.me/theorems/cf0eb172-24b0-48ec-90c3-a853e896b587
-- title:
--   Uniform distribution $\mu_{\mathrm{Cl}}$ on the 24 single-qubit Clifford gates
-- statement:
--   The **uniform Clifford distribution** is the uniform distribution on the 24 single-qubit Clifford gates modulo global phase:
--   $$
--   \mu_{\mathrm{Cl}} = \frac{1}{24} \sum_{k=0}^{23} \delta_{G_k},
--   $$
--   where $G_0, \dots, G_{23}$ are the representatives of the 24 classes. It is a probability measure on $U(2)$.
--
--   It is the single-qubit law of the construction $PL$ in Theorem 1.1.
--
--   **Formalization Note** The module also records that $\mu_{\mathrm{Cl}}$ has total mass one.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_PRUPermLayer_qubitUnitaryMeasurable
import Definitions.Def_PRUPermLayer_clifford24
open MeasureTheory
open scoped ENNReal

namespace PRUPermLayer

/-- The uniform distribution on the 24 single-qubit Clifford gates modulo global phase
(Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11): "Unless stated otherwise, µ is the uniform distribution on the 24
single-qubit Clifford gates modulo global phase"): `µ_Cl = (1/24) Σₖ δ_{clifford24 k}`.

**Formalization Note** One representative per phase class (`clifford24`). The instance below
records that it is a probability measure. -/
noncomputable def cliffordLaw : Measure (Matrix.unitaryGroup Bool ℂ) :=
  (24 : ℝ≥0∞)⁻¹ • ∑ k : Fin 24, Measure.dirac (clifford24 k)

instance cliffordLaw_isProbabilityMeasure : IsProbabilityMeasure cliffordLaw := by
  constructor
  simp only [cliffordLaw, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

end PRUPermLayer


