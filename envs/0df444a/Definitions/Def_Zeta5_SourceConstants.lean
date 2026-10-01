-- Prove2me | Definitions.Def_Zeta5_SourceConstants
-- name    : Zeta5_SourceConstants
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-01T10:29:39.04999+00:00
-- url     : https://prove2.me/theorems/106529cb-5a07-4642-b36e-b1687b85b74c
-- title:
--   Zeta5: normalization and analytic constants
-- statement:
--   This module fixes the exact rational constants
--   $$U=-\frac{2733991}{2000000},\qquad A_{\rm eff}=\frac{136}{100},\qquad K_n=40n,$$
--   together with the source's rational constants $A^*$, $A(M)$, and $A_{200}$. It includes the short exact arithmetic identities and inequalities proved in the source, in particular
--   $$A_{\rm eff}+U<0.$$
--   The actual normalization estimate in the repository uses $A_{\rm eff}$; $A_{200}$ and the stronger numerical margin from the paper are recorded separately and are not substituted for that estimate. The parameter $M$ in the total rational expression $A(M)$ is unrestricted; any later use with a positive cutoff must state that restriction.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Constants.lean#L1-L42

import Mathlib

/-!
# Numerical constants of the paper

`U` of (6.4), `A*` of (5.19), `A_M` of (5.20), the displayed value `A₂₀₀` of Appendix B.3,
the identity (5.20) at `M = 200` and the margin (7.2), both checked by `norm_num`.
-/

namespace Apery

/-- The constant `U` of Lemma 6.1 / (6.4). -/
def U : ℚ := -2733991 / 2000000

/-- The constant `A*` of (5.19). -/
def Astar : ℚ := 9928298118277006344769 / 7535670527041937280000

/-- `A_M` of (5.20), with `λ = 37/40`. -/
def A (M : ℚ) : ℚ := Astar + 7 * (37 / 40) / M - (2923 / 240 - 1 / 4) / M ^ 2 + 32 / M ^ 3

/-- The value `A₂₀₀` displayed in Appendix B.3. -/
def A200 : ℚ := 127125602969131786927559 / 94195881588024216000000

lemma A_200_eq : A 200 = A200 := by
  unfold A Astar A200; norm_num

/-- The rational margin (7.2): `-1600 (A₂₀₀ + U) > 139 / 5`. -/
lemma margin : (139 : ℚ) / 5 < -1600 * (A200 + U) := by
  unfold A200 U; norm_num

/-- The normalisation constant proved here (`Apery.Growth`): `limsup K⁻² log m_K ≤ A_eff`.
It is weaker than the paper's `A₂₀₀`, but still below `-U`. -/
def Aeff : ℚ := 136 / 100

/-- The margin used for irrationality: `A_eff + U < 0`. -/
lemma Aeff_margin : Aeff + U < 0 := by
  unfold Aeff U; norm_num

/-- `K = 40 n` as a real number. -/
noncomputable abbrev Kr (n : ℕ) : ℝ := 40 * (n : ℝ)

end Apery


