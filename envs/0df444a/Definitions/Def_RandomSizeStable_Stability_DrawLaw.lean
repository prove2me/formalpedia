-- Prove2me | Definitions.Def_RandomSizeStable_Stability_DrawLaw
-- name    : RandomSizeStable_Stability_DrawLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:50:35.452208+00:00
-- url     : https://prove2.me/theorems/51a16e94-377d-4a02-a101-c8c12f8b8a53
-- title:
--   Positive-integer draw laws, generating functions and the fixed law
-- statement:
--   Let $D$ be any probability law on the positive integers. Its probability generating function, primitive and stability benchmark are
--   $$\phi_D(t)=\sum_{k\ge1}\Pr[D=k]t^k,\qquad
--   \Phi_D(u)=\int_0^u\phi_D(s)\,ds,\qquad
--   \mu_D=\sum_{k\ge1}\frac{\Pr[D=k]}{k+1}.$$
--   The benchmark equals $\Phi_D(1)$ mathematically; this identity is not assumed as a structure field. On $[0,1]$ the nonnegative series converge, without a moment or finite-support assumption. Only this domain of the generating function and primitive is used.
--
--   The fixed law $D^\star$ has masses $19/73,35/146,1/2$ at $1,2,32$, respectively, and zero elsewhere. It is constructed as a genuine probability mass function, with its normalization proved using exact arithmetic. This module supplies the common analytic quantities and the fixed law from Figure 3.
--
--   **Formalization Note** Real series and integrals are total outside the domain used by the source; no claim depends on those outside values. The law uses Mathlib's probability mass function type rather than a new probability model.
-- source:
--   Nisarg Shah, Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission #1342 (October 2026), p. 9, 11, 15, Definitions 2 and 4; Figure 3.

import Mathlib
import Definitions.Def_PctDistortion_Election

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory PctDistortion

namespace RandomSizeStable.Stability

/-- Definition 2 (p.9): the PGF of an arbitrary positive-integer law.
Only arguments in [0,1] are used; no support or moment bound is imposed. -/
noncomputable def pgf (D : PMF ℕ+) (t : ℝ) : ℝ :=
  ∑' k : ℕ+, (D k).toReal * t ^ (k : ℕ)

/-- Definition 4 (p.11): the integral of the PGF from zero. -/
noncomputable def primitive (D : PMF ℕ+) (u : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..u, pgf D s

/-- Definitions 2--4 (pp.9--11): E[1/(D+1)], also equal to Φ(1).
The latter equality is a mathematical identity, not an assumed field. -/
noncomputable def benchmark (D : PMF ℕ+) : ℝ :=
  ∑' k : ℕ+, (D k).toReal / ((k : ℕ) + 1 : ℝ)

/-- Figure 3 (p.15): the fixed draw law, formed on three indices then pushed to
positive draw counts. All probabilities are exact rationals. -/
noncomputable def dStar : PMF ℕ+ :=
  (PMF.ofFintype (fun i : Fin 3 =>
    ENNReal.ofReal (if i.val = 0 then (19 / 73 : ℝ) else if i.val = 1 then 35 / 146 else 1 / 2))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg (by intro i hi; split_ifs <;> norm_num)]
      norm_num [Fin.sum_univ_succ])).map
      (fun i : Fin 3 => if i.val = 0 then (1 : ℕ+) else if i.val = 1 then 2 else 32)

end RandomSizeStable.Stability


