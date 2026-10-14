-- Prove2me | Definitions.Def_Zeta5_SourceEnergy
-- name    : Zeta5_SourceEnergy
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-12T00:15:15.665825+00:00
-- url     : https://prove2.me/theorems/9611f499-3f4e-4be8-8773-cd93a8a66e07
-- title:
--   Zeta5: the potentials $U_\omega$, $U_\rho$ and the regularisation errors
-- statement:
--   The energy objects of Section 6 of the source attached to the Hankel determinant construction with $K = 40n$:
--
--   * the closed form (A.1) of the potential of the arcsine measure on $[a,b]$,
--
--   $$U_\omega(a,b,t) \;=\; \begin{cases}\log\frac{b-a}{4}, & a\le t\le b,\\[4pt] \log\frac{\left|t-\frac{a+b}{2}\right| + \sqrt{(t-a)(t-b)}}{2}, & \text{otherwise};\end{cases}$$
--
--   * the potential of the comparison measure $\rho$, $U_\rho(t) = \sum_{j=1}^{16} c_j U_\omega(a_j,b_j,t)$, where $(a_j,b_j,c_j)$ is Table 1;
--
--   * the midpoints $m_j = (a_j+b_j)/2$ and half-lengths $r_j = (b_j-a_j)/2$ of the Table 1 intervals;
--
--   * the regularisation error of the arcsine potential at a point, $\mathrm{err}_j(\varepsilon,t,m,r) = \frac{\varepsilon}{r} + \sqrt{\frac{\varepsilon}{r}\cdot\frac{\varepsilon + 2|t-m|}{r}}$;
--
--   * the total regularisation error $\mathrm{Err}(\varepsilon,t) = \sum_{j=1}^{16} c_j\, \mathrm{err}_j(\varepsilon,t,m_j,r_j)$.
--
--   These are exactly the objects in which the raw configuration inequality `energy_raw`, the potential inequality of Lemma 6.1, and the regularisation bounds of Section 6 are stated.
--
--   **Formalization Note** All six are `noncomputable def`s in the `Apery` namespace, verbatim from the source modules; no side conditions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Potential.lean#L20-L26, Apery/EnergyAtoms.lean#L27-L29, Apery/EnergyBlocks.lean#L94-L96, Apery/EnergyRaw.lean#L19-L21

import Mathlib
import Definitions.Def_Zeta5_SourceMeasure
import Definitions.Def_Zeta5_SourceAnalytic

/-!
# The energy objects of Section 6: the potentials and the regularisation error

* the closed form (A.1) of the potential of the arcsine measure on `[a,b]`,
  `Uω a b t`, and the potential `Uρ t = ∑_{j=1}^{16} c_j Uω(a_j, b_j, t)` of the comparison measure;
* the midpoints `mρ`, half-lengths `rρ` of the Table 1 intervals;
* the regularisation error `errj` of the arcsine potential at a point and the total
  regularisation error `Err = ∑_{j=1}^{16} c_j errj(ε, t, mρ j, rρ j)`.

Source: mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/Potential.lean` lines 20–26, `Apery/EnergyAtoms.lean` lines 27–29,
`Apery/EnergyBlocks.lean` lines 94–96, `Apery/EnergyRaw.lean` lines 19–21.
-/

open Finset

namespace Apery

/-- The closed form (A.1) of the potential of the arcsine measure on `[a, b]`. -/
noncomputable def Uω (a b t : ℝ) : ℝ :=
  if a ≤ t ∧ t ≤ b then Real.log ((b - a) / 4)
  else Real.log ((|t - (a + b) / 2| + Real.sqrt ((t - a) * (t - b))) / 2)

/-- The potential of `ρ`. -/
noncomputable def Uρ (t : ℝ) : ℝ := ∑ j ∈ Icc 1 16, cρ j * Uω (aρ j) (bρ j) t

/-- Midpoints of the intervals of Table 1. -/
noncomputable def mρ (j : ℕ) : ℝ := (aρ j + bρ j) / 2

/-- Half-lengths of the intervals of Table 1. -/
noncomputable def rρ (j : ℕ) : ℝ := (bρ j - aρ j) / 2

/-- The regularisation error of the arcsine potential at a real point `t`. -/
noncomputable def errj (ε t m r : ℝ) : ℝ :=
  ε / r + Real.sqrt (ε / r * ((ε + 2 * |t - m|) / r))

/-- The total regularisation error at a point. -/
noncomputable def Err (ε t : ℝ) : ℝ :=
  ∑ j : Fin 16, cρ (j + 1) * errj ε t (mρ (j + 1)) (rρ (j + 1))

end Apery


