-- Prove2me | Definitions.Def_CrossLicensing_Innovation_ClosedForms
-- name    : CrossLicensing_Innovation_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:23.371103+00:00
-- url     : https://prove2.me/theorems/72aa4deb-961c-476d-b4e1-47fd56fbf87c
-- title:
--   Lemma 1 and proof of Proposition 2 — closed forms r_d, r_m, Π*_i (duopoly), T̂2(T1|β), T^I_i, T^B_i, k̂2(k1|β), T*_i(β)
-- statement:
--   The explicit formulas of Lemma 1 (p. 12) and of the proof of Proposition 2 (pp. A.1–A.2), transcribed as printed.
--
--   1. Duopoly and monopoly prices: $r_d = \tfrac14\big(2 + (T_1+T_2)(1+\beta)\big)$, $r_m = \tfrac12(1 + T_1\beta + T_2)$.
--   2. Duopoly gross profits:
--   $$\Pi^{d}_1 = \tfrac{1}{144}\big((5\beta-7)T_1 + (5-7\beta)T_2 - 2\big)^2,\qquad \Pi^{d}_2 = \tfrac{1}{144}\big((5\beta-7)T_2 + (5-7\beta)T_1 - 2\big)^2.$$
--   3. The duopoly boundary $\hat T_2(T_1\mid\beta) = \dfrac{2 - \sqrt3 + T_1(1 - \beta(\sqrt3 - 1))}{\sqrt3 - 1 - \beta}$ (used for $\beta < \sqrt3 - 1$).
--   4. The interior candidate, for $\{i, j\} = \{1, 2\}$:
--   $$T^I_i = \frac{(5\beta-7)(-5\beta^2 + 12\beta + 12k_j - 7)}{6k_j((7-5\beta)^2 - 144k_i) + (7-5\beta)^2(\beta^2 + 6k_i - 1)}.$$
--   5. The boundary candidate, with $D_B = (4\sqrt3-7)(\beta-1)(\beta+1)(5\beta-7) - 48(\sqrt3\beta + \sqrt3 - 3)k_1$:
--   $$T^B_2 = \frac{48(2\sqrt3-3)k_1 - (4\sqrt3-7)(\beta-1)(5\beta-7)}{D_B},\qquad T^B_1 = -\frac{(4\sqrt3-7)(\beta-1)(5\beta-7)}{D_B}.$$
--   6. The threshold
--   $$\hat k_2(k_1\mid\beta) = -\frac{(4\sqrt3-5)(\beta-1)(5\beta-7)k_1}{(4\sqrt3-7)(\beta-1)(5\beta-7) + 48(3-2\sqrt3)k_1}.$$
--   7. The equilibrium candidate (p. A.2): $T^*_i(\beta) = T^B_i$ if $k_2 < \hat k_2(k_1\mid\beta)$, and $T^*_i(\beta) = T^I_i$ otherwise.
--
--   These are plain real-number expressions; the theorems of the mission establish what they mean.
--
--   **Formalization Note** Real division by zero returns $0$ in Lean; every theorem that uses one of these quotients either proves its denominator nonzero in its regime or carries the paper's restriction ($\beta < \sqrt3 - 1$ for $\hat T_2$).
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), p. 12, Lemma 1; proof of Proposition 2, p. A.1 (PDF 33) and p. A.2 (PDF 34)

import Mathlib

namespace CrossLicensing.Innovation

/-- Lemma 1's duopoly wholesale price `r_d = (2 + (T1 + T2)(1 + β))/4`. -/
noncomputable def rd (β T1 T2 : ℝ) : ℝ := (2 + (T1 + T2) * (1 + β)) / 4

/-- Lemma 1's monopoly wholesale price `r_m = (1 + T1 β + T2)/2`. -/
noncomputable def rm (β T1 T2 : ℝ) : ℝ := (1 + T1 * β + T2) / 2

/-- Lemma 1's duopoly gross profit of manufacturer 1, `((5β − 7)T1 + (5 − 7β)T2 − 2)²/144`. -/
noncomputable def duoGross1 (β T1 T2 : ℝ) : ℝ :=
  ((5 * β - 7) * T1 + (5 - 7 * β) * T2 - 2) ^ 2 / 144

/-- Lemma 1's duopoly gross profit of manufacturer 2, `((5β − 7)T2 + (5 − 7β)T1 − 2)²/144`. -/
noncomputable def duoGross2 (β T1 T2 : ℝ) : ℝ :=
  ((5 * β - 7) * T2 + (5 - 7 * β) * T1 - 2) ^ 2 / 144

/-- Lemma 1's duopoly boundary `T̂2(T1|β) = (2 − √3 + T1(1 − β(√3 − 1)))/(√3 − 1 − β)`
(the paper uses it only for `β < √3 − 1`). -/
noncomputable def That2 (β T1 : ℝ) : ℝ :=
  (2 - Real.sqrt 3 + T1 * (1 - β * (Real.sqrt 3 - 1))) / (Real.sqrt 3 - 1 - β)

/-- `T^I_1` (p. A.1, `i = 1`, `j = 2`):
`(5β − 7)(−5β² + 12β + 12k2 − 7) / (6k2((7 − 5β)² − 144k1) + (7 − 5β)²(β² + 6k1 − 1))`. -/
noncomputable def TI1 (β k1 k2 : ℝ) : ℝ :=
  (5 * β - 7) * (-5 * β ^ 2 + 12 * β + 12 * k2 - 7) /
    (6 * k2 * ((7 - 5 * β) ^ 2 - 144 * k1) + (7 - 5 * β) ^ 2 * (β ^ 2 + 6 * k1 - 1))

/-- `T^I_2` (p. A.1, `i = 2`, `j = 1`):
`(5β − 7)(−5β² + 12β + 12k1 − 7) / (6k1((7 − 5β)² − 144k2) + (7 − 5β)²(β² + 6k2 − 1))`. -/
noncomputable def TI2 (β k1 k2 : ℝ) : ℝ :=
  (5 * β - 7) * (-5 * β ^ 2 + 12 * β + 12 * k1 - 7) /
    (6 * k1 * ((7 - 5 * β) ^ 2 - 144 * k2) + (7 - 5 * β) ^ 2 * (β ^ 2 + 6 * k2 - 1))

/-- The common denominator of `T^B_1`, `T^B_2` (p. A.1):
`(4√3 − 7)(β − 1)(β + 1)(5β − 7) − 48(√3β + √3 − 3)k1`. -/
noncomputable def TBden (β k1 : ℝ) : ℝ :=
  (4 * Real.sqrt 3 - 7) * (β - 1) * (β + 1) * (5 * β - 7) -
    48 * (Real.sqrt 3 * β + Real.sqrt 3 - 3) * k1

/-- `T^B_1 = −(4√3 − 7)(β − 1)(5β − 7) / TBden` (p. A.1). -/
noncomputable def TB1 (β k1 : ℝ) : ℝ :=
  -((4 * Real.sqrt 3 - 7) * (β - 1) * (5 * β - 7)) / TBden β k1

/-- `T^B_2 = (48(2√3 − 3)k1 − (4√3 − 7)(β − 1)(5β − 7)) / TBden` (p. A.1). -/
noncomputable def TB2 (β k1 : ℝ) : ℝ :=
  (48 * (2 * Real.sqrt 3 - 3) * k1 - (4 * Real.sqrt 3 - 7) * (β - 1) * (5 * β - 7)) / TBden β k1

/-- `k̂2(k1|β) = −(4√3 − 5)(β − 1)(5β − 7)k1 / ((4√3 − 7)(β − 1)(5β − 7) + 48(3 − 2√3)k1)`
(p. A.2). -/
noncomputable def khat2 (β k1 : ℝ) : ℝ :=
  -((4 * Real.sqrt 3 - 5) * (β - 1) * (5 * β - 7) * k1) /
    ((4 * Real.sqrt 3 - 7) * (β - 1) * (5 * β - 7) + 48 * (3 - 2 * Real.sqrt 3) * k1)

/-- `T*_1(β)` (p. A.2): `T^B_1` if `k2 < k̂2(k1|β)`, otherwise `T^I_1`. -/
noncomputable def Tstar1 (β k1 k2 : ℝ) : ℝ :=
  if k2 < khat2 β k1 then TB1 β k1 else TI1 β k1 k2

/-- `T*_2(β)` (p. A.2): `T^B_2` if `k2 < k̂2(k1|β)`, otherwise `T^I_2`. -/
noncomputable def Tstar2 (β k1 k2 : ℝ) : ℝ :=
  if k2 < khat2 β k1 then TB2 β k1 else TI2 β k1 k2

end CrossLicensing.Innovation


