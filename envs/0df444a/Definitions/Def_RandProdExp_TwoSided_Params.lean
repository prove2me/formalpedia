-- Prove2me | Definitions.Def_RandProdExp_TwoSided_Params
-- name    : RandProdExp_TwoSided_Params
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:17:50.941958+00:00
-- url     : https://prove2.me/theorems/659ba0cf-7b56-4c03-aaf5-25f013ec2896
-- title:
--   The explicit constants $C_\rho$, $A_{D,\rho}$, $\varepsilon_0(D,\rho)$, $N^*_{D,\varepsilon}$, $N_{D,\varepsilon}$, $C_{D,\rho,\varepsilon}$, $N_{D,q,\eta}$, $\gamma(\varepsilon,D)$ (Equation (16))
-- statement:
--   With $\log$ the natural logarithm and $e=\exp(1)$:
--   $$C_\rho=3\big(1+\rho^{-1/2}\big),\qquad A_{D,\rho}=2(4C_\rho)^D\Big(1+\frac4\rho\Big)^D,\qquad \varepsilon_0(D,\rho)=\frac1{2^{D+2}A_{D,\rho}^2},$$
--   $$N_{D,\varepsilon}=\max\Big\{16\Big(\frac{192D}{e}\Big)^{24},(2^D\varepsilon)^{-2}\Big\},\qquad N^*_{D,\varepsilon}=\big\lceil N_{D,\varepsilon}\big\rceil,$$
--   $$C_{D,\rho,\varepsilon}=2(4C_\rho)^D\Big(1+\frac4\rho\Big)^D\sqrt{2^D\varepsilon},\qquad N_{D,q,\eta}=\max\Big\{16\Big(\frac{192D}{e}\Big)^{24},\eta^{-2/q}\Big\},\qquad \gamma(\varepsilon,D)=\frac{\varepsilon^D}{D(2^D+1)^D}.$$
--   These are the parameters of Equation (16), Theorem 5.1, Lemmas 6.3 and 7.1 and Proposition 8.1.
--
--   **Formalization Note** $\rho^{-1/2}$ and $\eta^{-2/q}$ are real powers; $(2^D\varepsilon)^{-2}$ is an integer power; $N^*_{D,\varepsilon}$ is the integer ceiling `⌈·⌉`.
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 34, Equation (16) and Theorem 5.1; p. 35, Lemma 6.3; p. 46, Lemma 7.1; p. 55, Proposition 8.1

import Mathlib

namespace RandProdExp.TwoSided

/-!
# The explicit parameters of Part I

Chattopadhyay, Ringach, Spooner, *Product Expansion of Random Codes via Analytic Techniques*,
STOC 2027 submission: Equation (16) and Theorem 5.1 (p. 34); Lemma 6.3 and Lemma 7.1 (pp. 35, 46);
Proposition 8.1 (p. 55). `log` is the natural logarithm and `e = exp 1`.
-/

/-- `C_ρ = 3 (1 + ρ^{−1/2})` (Equation (16), Proposition 7.9). -/
noncomputable def Crho (ρ : ℝ) : ℝ := 3 * (1 + ρ ^ (-(1 / 2 : ℝ)))

/-- `A_{D,ρ} = 2 (4 C_ρ)^D (1 + 4/ρ)^D` (Equation (16)). -/
noncomputable def Aconst (D : ℕ) (ρ : ℝ) : ℝ := 2 * (4 * Crho ρ) ^ D * (1 + 4 / ρ) ^ D

/-- `ε₀(D, ρ) = 1 / (2^{D+2} A_{D,ρ}²)` (Equation (16)). -/
noncomputable def eps0 (D : ℕ) (ρ : ℝ) : ℝ := 1 / (2 ^ (D + 2) * Aconst D ρ ^ 2)

/-- `N_{D,ε} = max{16 (192 D / e)^{24}, (2^D ε)^{−2}}` (Lemmas 6.3, 7.1). -/
noncomputable def NDeps (D : ℕ) (ε : ℝ) : ℝ :=
  max (16 * (192 * (D : ℝ) / Real.exp 1) ^ 24) ((2 ^ D * ε) ^ (-2 : ℤ))

/-- `N*_{D,ε} = ⌈max{16 (192 D / e)^{24}, (2^D ε)^{−2}}⌉` (Equation (16)). -/
noncomputable def Nstar (D : ℕ) (ε : ℝ) : ℤ := ⌈NDeps D ε⌉

/-- `C_{D,ρ,ε} = 2 (4 C_ρ)^D (1 + 4/ρ)^D √(2^D ε)` (Lemmas 6.3, 7.1). -/
noncomputable def CDrhoEps (D : ℕ) (ρ ε : ℝ) : ℝ :=
  2 * (4 * Crho ρ) ^ D * (1 + 4 / ρ) ^ D * Real.sqrt (2 ^ D * ε)

/-- `N_{D,q,η} = max{16 (192 D / e)^{24}, η^{−2/q}}` (Proposition 8.1). -/
noncomputable def NDqEta (D q : ℕ) (η : ℝ) : ℝ :=
  max (16 * (192 * (D : ℝ) / Real.exp 1) ^ 24) (η ^ (-(2 : ℝ) / q))

/-- `γ(ε, D) = ε^D / (D (2^D + 1)^D)` (Theorem 5.1, Lemma 5.2). -/
noncomputable def gammaConst (ε : ℝ) (D : ℕ) : ℝ := ε ^ D / (D * (2 ^ D + 1) ^ D)

end RandProdExp.TwoSided


