-- Prove2me | Definitions.Def_QThermalClassical_Supplement_maxCoeff
-- name    : QThermalClassical_Supplement_maxCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:36:47.698054+00:00
-- url     : https://prove2.me/theorems/2efec9ac-3d3b-4010-9b20-26cb27113d9c
-- title:
--   Largest coefficient $\max_{a\in A}|c_a|$
-- statement:
--   For $H=\sum_{a\in A}c_aP_a$, the largest coefficient in absolute value, $\max_{a\in A}|c_a|$, which enters the temperature range (41) of Theorem 5.
--
--   **Formalization Note** The maximum is over all Pauli words; words outside $A$ have coefficient $0$, so the value is the maximum over $A$ ($0$ for $H=0$).
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 5, eq. (41), p.17

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- `max_{a∈A} |c_a|`, the largest coefficient of `H = Σ_P c_P P` in absolute value.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 5, eq. (41), p.17.

**Formalization Note.** The maximum is taken over all words; words outside `A = {P : c P ≠ 0}`
contribute `0`, so this is the maximum over `A` (and `0` for `H = 0`). -/
noncomputable def maxCoeff {Q : Type} [Fintype Q] [DecidableEq Q] (c : PauliWord Q → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun P : PauliWord Q => |c P|

end QThermalClassical.Supplement


