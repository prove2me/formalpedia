-- Prove2me | Definitions.Def_SwitchingStable_Universal_Constants
-- name    : SwitchingStable_Universal_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:54:34.318465+00:00
-- url     : https://prove2.me/theorems/30eb48c4-4761-4b8a-b16a-5480cf0c63ac
-- title:
--   Exact geometric costs, layer weights and the Section 5 base
-- statement:
--   All logarithms are natural. The baseline cost and boundary costs are the convergent series
--   $$C=2\sum_{k=2}^{\infty}\frac{\log k}{(k+1)(k+2)},\qquad \delta_k=\sum_{j=k}^{\infty}\frac{2\log(1+1/j)}{(j+1)(j+2)(j+3)}.$$
--   The file defines $\alpha=\delta_1$, $\gamma=\delta_3$, the local constants $\eta,\zeta,\sigma,\lambda,\chi,\chi_{3,2}$, the elementary interactions $e_s$, and the weights $\omega_i$ and missing-layer penalties $\xi,\psi$. All eight $a_i$ and six $B$ coefficients use the Appendix E formulas. In particular,
--   $$\vartheta=\frac{\alpha+2\delta_2+3\gamma+2\delta_4+\delta_5+\omega_1+\omega_2+\omega_3}{3},\qquad\Omega=\exp(C-2\vartheta).$$
--   The separate series $C_2$ retains Lemma 18's private-witness clause. Convergence and numerical bounds are theorem conclusions, never parameters or axioms.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), pp. 4, 7–9, 11, 28–30, PDF pp. 5, 8–10, 12, 29–31, Sections 2, 4–5 and Appendices E–F

import Mathlib

namespace SwitchingStable.Universal

/-- Section 2 and Appendix B, averaged geometric reference cost. -/
noncomputable def C : ℝ := ∑' m : ℕ, 2 * Real.log (m + 2) / ((m + 3) * (m + 4))
/-- Section 4. Shifted sums start at precisely k. -/
noncomputable def deltaTerm (k m : ℕ) : ℝ :=
  2 * Real.log (1 + 1 / (m + k : ℝ)) /
    ((m + k + 1 : ℝ) * (m + k + 2) * (m + k + 3))
noncomputable def delta (k : ℕ) : ℝ := ∑' m : ℕ, deltaTerm k m
noncomputable def alpha : ℝ := delta 1
noncomputable def gamma : ℝ := delta 3
noncomputable def e (s : ℕ) : ℝ :=
  2 * Real.log ((s : ℝ)^2 / ((s : ℝ)^2 - 1)) /
    ((s + 1 : ℝ) * (s + 2) * (s + 3))
noncomputable def etaTerm (k m : ℕ) : ℝ :=
  Real.log (1 + 1 / (m + k : ℝ)) / ((m + k + 1 : ℝ) * (m + k + 2))
noncomputable def eta : ℝ := ∑' m : ℕ, etaTerm 1 m
noncomputable def zeta : ℝ := ∑' m : ℕ, etaTerm 2 m
noncomputable def sigma : ℝ := zeta + Real.log (4 / 3 : ℝ) / 20
noncomputable def lambda : ℝ := ∑' m : ℕ, e (m + 2)
noncomputable def chiTerm (m : ℕ) : ℝ :=
  deltaTerm 2 m + Real.log ((m + 4 : ℝ) / (m + 3)) / ((m + 4 : ℝ) * (m + 5))
noncomputable def chi : ℝ := ∑' m : ℕ, chiTerm m
noncomputable def chi32 : ℝ := chi - Real.log (3 / 2 : ℝ) / 30 - Real.log (4 / 3 : ℝ) / 20
noncomputable def K : ℝ := e 4 + 2 * e 5 + 3 * e 6 + 2 * e 7 + e 8
noncomputable def T : ℝ := e 5 + 2 * e 6 + 3 * e 7 + 2 * e 8 + e 9
noncomputable def omega (i : ℕ) : ℝ :=
  if i = 1 then 3 * K / 2 - T else if i = 2 then K / 2
  else if i = 3 then T - K / 2 else -(3 * K / 2 - T)
noncomputable def xi : ℝ := e 5 + e 6 + e 7
noncomputable def psi : ℝ := e 6 + e 7 + e 8
noncomputable def penalty (r : ℕ) : ℝ := if r = 1 then xi + psi else if r = 2 then psi else 0
noncomputable def theta : ℝ :=
  (alpha + 2 * delta 2 + 3 * gamma + 2 * delta 4 + delta 5 + omega 1 + omega 2 + omega 3) / 3
/-- The fixed Section 5 base, not an existentially selected upper bound. -/
noncomputable def Omega : ℝ := Real.exp (C - 2 * theta)
noncomputable def privateTerm (m : ℕ) : ℝ :=
  let k : ℝ := m + 2
  k * Real.log k * (1 / (2 * (k - 1) + 1) - 2 / (2 * k + 1) + 1 / (2 * (k + 1) + 1))
noncomputable def C2 : ℝ := ∑' m : ℕ, privateTerm m

/-- Appendix E: eight difference coefficients, indexed by the printed subscripts. -/
noncomputable def coeffA (i : ℕ) : ℝ :=
  let a3 := theta - gamma - delta 4 - delta 5 - omega 3
  let a6 := gamma + 2 * delta 4 + delta 5 + 2 * xi + 2 * psi
  match i with
  | 1 => theta - delta 2 - gamma - delta 4 - omega 2
  | 2 => eta - omega 1 - theta - a3
  | 3 => a3
  | 4 => gamma + delta 4 + delta 5 + omega 1 + omega 3
  | 5 => a3 - a6 - gamma - psi
  | 6 => a6
  | 7 => delta 4 + delta 5 + xi + psi
  | 8 => gamma + delta 4 + delta 5 + 3 * psi
  | _ => 0
/-- Appendix E: BS, BF, B0, B1, BE, BC, in that order. -/
noncomputable def coeffB (i : Fin 6) : ℝ :=
  match i.val with
  | 0 => sigma - omega 1 - theta - coeffA 4
  | 1 => delta 2 + omega 2 + coeffA 2 - xi - psi - theta - coeffA 8 - coeffA 4
  | 2 => delta 2 + lambda + coeffA 5 - 2 * omega 1 - coeffA 4 - coeffA 8 + psi
  | 3 => delta 2 - coeffA 4
  | 4 => zeta - delta 2 - omega 1 - omega 2 - gamma - delta 4 - coeffA 4
  | _ => coeffA 2 + coeffA 5 - delta 2 - xi

end SwitchingStable.Universal


