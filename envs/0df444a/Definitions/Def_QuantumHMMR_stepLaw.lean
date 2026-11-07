-- Prove2me | Definitions.Def_QuantumHMMR_stepLaw
-- name    : QuantumHMMR_stepLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:29.698479+00:00
-- url     : https://prove2.me/theorems/918a0a49-9e81-41fa-9f33-02328d380896
-- title:
--   One-step law $\nu_n = (1 - m^{-1})\chi_n + m^{-1}\xi_n$ of the walk, Eq. (8)
-- statement:
--   For an integer $m \ge 2$, one update of the walk is a local Clifford update with probability $1 - 1/m$ and an insertion with probability $1/m$:
--   $$
--   \nu_n = (1 - m^{-1})\,\chi_n + m^{-1}\,\xi_n. \tag{8}
--   $$
--   Every update acts on at most two neighbouring qubits.
--
--   **Formalization Note** The weights are written with `ENNReal.ofReal`; for every $m \ge 1$ they are the printed probabilities, and the verification file proves that $\nu_n$ has total mass one for $m \ge 1$, $n \ge 1$, $G \neq \emptyset$.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Eq. (8), p.12

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_chiLaw
import Definitions.Def_QuantumHMMR_xiLaw

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped ENNReal

namespace QuantumHMMR

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

/-- The one-step distribution of the walk, Eq. (8) (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), p.12):
`ν_n = (1 - m⁻¹) χ_n + m⁻¹ ξ_n`: with probability `1 - 1/m` a local Clifford update, with
probability `1/m` an insertion.

**Formalization Note** The weights are `ENNReal.ofReal (1 - m⁻¹)` and `ENNReal.ofReal m⁻¹`; for
every `m ≥ 1` they are the printed probabilities (the page takes `m ≥ 2`). -/
noncomputable def stepLaw (G : Finset (Clifford.ProjectiveGroup 2)) (n m : ℕ) : Measure (QMat n) :=
  ENNReal.ofReal (1 - (m : ℝ)⁻¹) • chiLaw G n + ENNReal.ofReal ((m : ℝ)⁻¹) • xiLaw n

end QuantumHMMR


