-- Prove2me | Definitions.Def_GilesMLMC_Complexity_Choices
-- name    : GilesMLMC_Complexity_Choices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:48.783422+00:00
-- url     : https://prove2.me/theorems/156ce523-3e72-46d9-9fd6-8678a5c8331e
-- title:
--   The proof's choices: the finest level $L$ of (6), $c_5$, the sample sizes $N_l$ of cases (a)–(c) and the constants $c_4$ (§3)
-- statement:
--   This file defines the explicit quantities chosen in the proof of Theorem 3.1. Throughout, $M\ge2$, $T>0$, positive constants $\alpha,\beta,c_1,c_2,c_3$ and $\varepsilon>0$ are given, and $h_l=M^{-l}T$.
--
--   1. The **finest level** (an integer)
--   $$L=\left\lceil \frac{\log(\sqrt2\,c_1T^\alpha\varepsilon^{-1})}{\alpha\log M}\right\rceil .$$
--   2. The constant
--   $$c_5=\frac{1}{\alpha\log M}+\max\Big(0,\frac{\log(\sqrt2\,c_1T^\alpha)}{\alpha\log M}\Big)+2 .$$
--   3. The sample sizes of case (a) ($\beta=1$), case (b) ($\beta>1$) and case (c) ($\beta<1$):
--   $$N_l^{(a)}=\big\lceil 2\varepsilon^{-2}(L+1)c_2h_l\big\rceil,\qquad N_l^{(b)}=\Big\lceil 2\varepsilon^{-2}c_2T^{(\beta-1)/2}\big(1-M^{-(\beta-1)/2}\big)^{-1}h_l^{(\beta+1)/2}\Big\rceil,$$
--   $$N_l^{(c)}=\Big\lceil 2\varepsilon^{-2}c_2h_L^{-(1-\beta)/2}\big(1-M^{-(1-\beta)/2}\big)^{-1}h_l^{(\beta+1)/2}\Big\rceil .$$
--   4. The three constants
--   $$c_4^{(a)}=2c_3c_5^2c_2+c_3\frac{M^2}{M-1}(\sqrt2c_1)^{1/\alpha},\qquad c_4^{(b)}=2c_3c_2T^{\beta-1}\big(1-M^{-(\beta-1)/2}\big)^{-2}+c_3\frac{M^2}{M-1}(\sqrt2c_1)^{1/\alpha},$$
--   $$c_4^{(c)}=2c_3c_2(\sqrt2c_1)^{(1-\beta)/\alpha}M^{1-\beta}\big(1-M^{-(1-\beta)/2}\big)^{-2}+c_3\frac{M^2}{M-1}(\sqrt2c_1)^{1/\alpha}.$$
--
--   The constants $c_5$ and $c_4$ depend only on $M,T,\alpha,\beta,c_1,c_2,c_3$, not on $\varepsilon$; this is what makes them constants of the complexity theorem.
--
--   **Formalization Note** $L$ uses `Int.ceil` and may be negative; the statements that use it as a level assume it equals a natural number. The sample sizes use `Nat.ceil`, which agrees with the paper's $\lceil\cdot\rceil$ because the arguments are positive. $\varepsilon^{-2}$ and every power with a real exponent are real powers (`Real.rpow`). In case (c) the level $L$ in $h_L$ is an argument.
-- source:
--   Giles, Multilevel Monte Carlo path simulation, Operations Research 56(3) (2008), §3, proof of Theorem 3.1: L (before (6)), p. 609; c₅ and N_l of case (a), p. 609; c₄ of case (a), p. 610; N_l and c₄ of cases (b), (c), p. 610

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup

namespace GilesMLMC.Complexity

/-- The finest level chosen in the proof of Theorem 3.1 (Giles 2008, §3, p. 609, PDF 3):
`L = ⌈log(√2 c₁ T^α ε⁻¹) / (α log M)⌉`, an integer ceiling (`Int.ceil`). It can be negative
when `√2 c₁ T^α ε⁻¹` is small; the theorems that use it as a level assume it is a natural
number. -/
noncomputable def Lchoice (M : ℕ) (T α c₁ ε : ℝ) : ℤ :=
  ⌈Real.log (Real.sqrt 2 * c₁ * T ^ α * ε⁻¹) / (α * Real.log (M : ℝ))⌉

/-- The constant `c₅ = 1/(α log M) + max(0, log(√2 c₁ T^α)/(α log M)) + 2` of case (a) of the
proof of Theorem 3.1 (Giles 2008, §3, p. 609, PDF 3). -/
noncomputable def c₅ (M : ℕ) (T α c₁ : ℝ) : ℝ :=
  1 / (α * Real.log (M : ℝ))
    + max 0 (Real.log (Real.sqrt 2 * c₁ * T ^ α) / (α * Real.log (M : ℝ))) + 2

/-- Case (a) sample sizes `N_l = ⌈2 ε⁻² (L+1) c₂ h_l⌉` (Giles 2008, §3, proof of Theorem 3.1,
case (a), p. 609, PDF 3). `ε⁻²` is the real power `ε ^ (-2 : ℝ)`; the argument is positive for
`ε, c₂, T > 0`, so `Nat.ceil` agrees with the paper's `⌈·⌉`. -/
noncomputable def NA (M : ℕ) (T c₂ ε : ℝ) (L : ℕ) (l : ℕ) : ℕ :=
  ⌈2 * ε ^ (-2 : ℝ) * ((L : ℝ) + 1) * c₂ * h M T l⌉₊

/-- Case (b) sample sizes
`N_l = ⌈2 ε⁻² c₂ T^{(β−1)/2} (1 − M^{−(β−1)/2})⁻¹ h_l^{(β+1)/2}⌉` (Giles 2008, §3, proof of
Theorem 3.1, case (b), p. 610, PDF 4). Powers with real exponents are `Real.rpow`. -/
noncomputable def NB (M : ℕ) (T β c₂ ε : ℝ) (l : ℕ) : ℕ :=
  ⌈2 * ε ^ (-2 : ℝ) * c₂ * T ^ ((β - 1) / 2) * (1 - (M : ℝ) ^ (-(β - 1) / 2))⁻¹
      * h M T l ^ ((β + 1) / 2)⌉₊

/-- Case (c) sample sizes
`N_l = ⌈2 ε⁻² c₂ h_L^{−(1−β)/2} (1 − M^{−(1−β)/2})⁻¹ h_l^{(β+1)/2}⌉` (Giles 2008, §3, proof of
Theorem 3.1, case (c), p. 610, PDF 4). -/
noncomputable def NC (M : ℕ) (T β c₂ ε : ℝ) (L : ℕ) (l : ℕ) : ℕ :=
  ⌈2 * ε ^ (-2 : ℝ) * c₂ * h M T L ^ (-(1 - β) / 2) * (1 - (M : ℝ) ^ (-(1 - β) / 2))⁻¹
      * h M T l ^ ((β + 1) / 2)⌉₊

/-- The case (a) constant `c₄ = 2 c₃ c₅² c₂ + c₃ M²/(M−1) (√2 c₁)^{1/α}` (Giles 2008, §3,
proof of Theorem 3.1, p. 610, PDF 4). -/
noncomputable def c₄A (M : ℕ) (T α c₁ c₂ c₃ : ℝ) : ℝ :=
  2 * c₃ * c₅ M T α c₁ ^ 2 * c₂
    + c₃ * ((M : ℝ) ^ 2 / ((M : ℝ) - 1)) * (Real.sqrt 2 * c₁) ^ (1 / α)

/-- The case (b) constant
`c₄ = 2 c₃ c₂ T^{β−1} (1 − M^{−(β−1)/2})^{−2} + c₃ M²/(M−1) (√2 c₁)^{1/α}` (Giles 2008, §3,
proof of Theorem 3.1, p. 610, PDF 4). -/
noncomputable def c₄B (M : ℕ) (T α β c₁ c₂ c₃ : ℝ) : ℝ :=
  2 * c₃ * c₂ * T ^ (β - 1) * ((1 - (M : ℝ) ^ (-(β - 1) / 2))⁻¹) ^ 2
    + c₃ * ((M : ℝ) ^ 2 / ((M : ℝ) - 1)) * (Real.sqrt 2 * c₁) ^ (1 / α)

/-- The case (c) constant
`c₄ = 2 c₃ c₂ (√2 c₁)^{(1−β)/α} M^{1−β} (1 − M^{−(1−β)/2})^{−2} + c₃ M²/(M−1) (√2 c₁)^{1/α}`
(Giles 2008, §3, proof of Theorem 3.1, p. 610, PDF 4). -/
noncomputable def c₄C (M : ℕ) (α β c₁ c₂ c₃ : ℝ) : ℝ :=
  2 * c₃ * c₂ * (Real.sqrt 2 * c₁) ^ ((1 - β) / α) * (M : ℝ) ^ (1 - β)
      * ((1 - (M : ℝ) ^ (-(1 - β) / 2))⁻¹) ^ 2
    + c₃ * ((M : ℝ) ^ 2 / ((M : ℝ) - 1)) * (Real.sqrt 2 * c₁) ^ (1 / α)

end GilesMLMC.Complexity


