-- Prove2me | Definitions.Def_PrefixMixLearn_Proper_Ledger
-- name    : PrefixMixLearn_Proper_Ledger
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:45:22.623202+00:00
-- url     : https://prove2.me/theorems/9fd747c1-6ddf-4e0e-88ee-d26046ca9ff0
-- title:
--   The explicit ledger constant $\kappa(\alpha)$ of (H.1) and $C_{gen}(\alpha)=\kappa^{-20}$
-- statement:
--   With $u=\alpha(1-\alpha)$, the paper's ledger is
--   $$C_4=3+\tfrac1{4u^2},\ C_*=3+\tfrac1{16u^3},\ B_*=\tfrac{16C_*+1}{u},\ r_0=\min\Big\{\tfrac{u^2}{4C_*},\tfrac1{4B_*},\tfrac u{64}\Big\},\ c_0=\tfrac u{8C_*},\ C_0=4B_*,\ p_0=\tfrac1{128C_*},\ c_{TV}=\tfrac u{8C_4^2},$$
--   $$m_0=\min\{\alpha,u,r_0,c_0,p_0,c_{TV},(C_0+1)^{-1},2^{-20}\},\qquad \kappa=2^{-\lceil\log_2(1/m_0)\rceil},$$
--   so that $m_0/2<\kappa\le m_0$, and $C_{gen}(\alpha)=\kappa^{-20}$. These depend on $\alpha$ only.
--
--   **Formalization Note.** Every constant is an exact real function of $\alpha$ (for rational $\alpha$ the paper's rational value); $\lceil\log_2(1/m_0)\rceil$ is `⌈Real.logb 2 (1 / ledgerM0 α)⌉` and $\kappa$ the integer power `2 ^ (-⌈…⌉)`.
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 57–58 (PDF 59–60), (H.1); p. 4 (PDF 6), Theorem 3.1

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Laws

set_option autoImplicit false

noncomputable section

namespace PrefixMixLearn.Proper

/-!
# The ledger constant `κ(α)` of (H.1) and `C_gen(α) = κ^{-20}`

Saravanan, *Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional
Samples*, STOC 2027 submission (manuscript sha256 9c359910…), Appendix H.1, pp. 57–58 (PDF 59–60),
(H.1); Theorem 3.1, p. 4 (PDF 6): `C_gen(α) = κ^{-20}`.

With `u = α(1 − α)`:
`C_4 = 3 + 1/(4u²)`, `C_* = 3 + 1/(16u³)`, `B_* = (16C_* + 1)/u`,
`r_0 = min{u²/(4C_*), 1/(4B_*), u/64}`, `c_0 = u/(8C_*)`, `C_0 = 4B_*`, `p_0 = 1/(128C_*)`,
`c_TV = u/(8C_4²)`, `m_0 = min{α, u, r_0, c_0, p_0, c_TV, (C_0 + 1)^{-1}, 2^{-20}}`,
`κ = 2^{-⌈log₂(1/m_0)⌉}`.
These are exact real functions of `α`; for rational `α` they are the paper's rational constants.
-/

/-- `C_4 = 3 + 1/(4u²)`. -/
def ledgerC4 (α : ℝ) : ℝ := 3 + 1 / (4 * uOf α ^ 2)

/-- `C_* = 3 + 1/(16u³)`. -/
def ledgerCstar (α : ℝ) : ℝ := 3 + 1 / (16 * uOf α ^ 3)

/-- `B_* = (16C_* + 1)/u`. -/
def ledgerBstar (α : ℝ) : ℝ := (16 * ledgerCstar α + 1) / uOf α

/-- `r_0 = min{u²/(4C_*), 1/(4B_*), u/64}`. -/
def ledgerR0 (α : ℝ) : ℝ :=
  min (uOf α ^ 2 / (4 * ledgerCstar α)) (min (1 / (4 * ledgerBstar α)) (uOf α / 64))

/-- `c_0 = u/(8C_*)`. -/
def ledgerSmallC0 (α : ℝ) : ℝ := uOf α / (8 * ledgerCstar α)

/-- `C_0 = 4B_*`. -/
def ledgerBigC0 (α : ℝ) : ℝ := 4 * ledgerBstar α

/-- `p_0 = 1/(128C_*)`. -/
def ledgerP0 (α : ℝ) : ℝ := 1 / (128 * ledgerCstar α)

/-- `c_TV = u/(8C_4²)`. -/
def ledgerCTV (α : ℝ) : ℝ := uOf α / (8 * ledgerC4 α ^ 2)

/-- `m_0 = min{α, u, r_0, c_0, p_0, c_TV, (C_0 + 1)^{-1}, 2^{-20}}`. -/
def ledgerM0 (α : ℝ) : ℝ :=
  min α (min (uOf α) (min (ledgerR0 α) (min (ledgerSmallC0 α) (min (ledgerP0 α)
    (min (ledgerCTV α) (min (1 / (ledgerBigC0 α + 1)) ((2 : ℝ) ^ (-20 : ℤ))))))))

/-- The dyadic ledger constant `κ = 2^{-⌈log₂(1/m_0)⌉}` of (H.1). -/
def kappa (α : ℝ) : ℝ := (2 : ℝ) ^ (-⌈Real.logb 2 (1 / ledgerM0 α)⌉)

/-- `C_gen(α) = κ^{-20}`. -/
def Cgen (α : ℝ) : ℝ := kappa α ^ (-20 : ℤ)

end PrefixMixLearn.Proper


