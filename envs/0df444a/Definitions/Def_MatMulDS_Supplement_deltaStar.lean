-- Prove2me | Definitions.Def_MatMulDS_Supplement_deltaStar
-- name    : MatMulDS_Supplement_deltaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:14:41.990796+00:00
-- url     : https://prove2.me/theorems/7f79403a-2aad-486c-a004-643589b850de
-- title:
--   The frontier $\delta_*$ of (7.4) for the second parameter set of Table 1
-- statement:
--   Table 1 gives two parameter sets for the identity $T_5^{(4)}$ with $5^4$ products. Each assigns to the six classes of types $\tau\subseteq[4]$ ($\emptyset$; $|\tau|=1$; $\tau\in\{\{1,2\},\{3,4\}\}$; the other $|\tau|=2$; $|\tau|=3$; $[4]$) a total probability, split evenly among the types of the class, and a weight $w$, together with $\theta$ and $\eta_{\mathrm{pre}}$. For the second set the class probabilities are $0.540835107651$, $0.354067290473$, $0.034922491991$, $0.057987616385$, $0.011472698656$, $0.000714794844$, the weights $0$, $3.556530889947$, $6.680625831738$, $7.107657121293$, $10.202700223774$, $12.985018992011$, and $\theta=0.151039240214$, $\eta_{\mathrm{pre}}=1.812191155860$.
--
--   With the rates $\nu=H/(2\,\mathrm{len})$, $\Gamma=(H-f)/\mathrm{len}$, $Q=\xi/\mathrm{len}$ of (5.5), computed by the closed forms (7.2), let
--   $$\delta_0^*=\frac{2\Gamma}{(\nu-2Q)^2+4\Gamma Q},\qquad \delta_*=\frac12+\delta_0^*(1-Q).$$
--   The paper gives $\delta_*=0.5012157755649\ldots$; it is the largest inner-dimension exponent reached by Theorems 7.5 and 7.6.
--
--   **Formalization Note** The value is exact, from the printed decimals, not the truncated decimal. The closed forms are those of Proposition 7.1 (a published milestone), which do not depend on the choices in the construction of $T_5^{(4)}$; recomputing them gives $\nu=7.36827\ldots$, $\Gamma=0.06568\ldots$, $Q=0.65981\ldots$ as in Table 1 and $\delta_*=0.50121577556497\ldots$.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Table 1 and eq. (7.4), p.47 (PDF p.49); eq. (7.2), p.45

import Mathlib
import Definitions.Def_MatMulDS_outPos

set_option autoImplicit false

namespace MatMulDS.Supplement

/-- The per-type probability of the second parameter set of Table 1 (p.47, PDF p.49): the probability of the class of
`τ ⊆ [4]`, split evenly among the types of the class (0-based positions: `{1,2}, {3,4}` are `{0,1}, {2,3}`). -/
def tableProb2 (τ : Finset (Fin 4)) : ℚ :=
  if τ = ∅ then 0.540835107651
  else if τ.card = 1 then 0.354067290473 / 4
  else if τ = {0, 1} ∨ τ = {2, 3} then 0.034922491991 / 2
  else if τ.card = 2 then 0.057987616385 / 4
  else if τ.card = 3 then 0.011472698656 / 4
  else 0.000714794844

/-- The weight `w` of the second parameter set of Table 1, constant on each class of types. -/
noncomputable def tableWeight2 (τ : Finset (Fin 4)) : ℝ :=
  if τ = ∅ then 0
  else if τ.card = 1 then 3.556530889947
  else if τ = {0, 1} ∨ τ = {2, 3} then 6.680625831738
  else if τ.card = 2 then 7.107657121293
  else if τ.card = 3 then 10.202700223774
  else 12.985018992011

/-- `θ` of the second parameter set of Table 1. -/
noncomputable def tableTheta2 : ℝ := 0.151039240214

/-- `η_pre` of the second parameter set of Table 1. -/
noncomputable def tableEta2 : ℝ := 1.812191155860

/-- The entropy `H(π)` of the second parameter set, by Proposition 7.1 (7.2). -/
noncomputable def entropy2 : ℝ :=
  (∑ τ, Real.negMulLog (tableProb2 τ : ℝ)) + ∑ τ : Finset (Fin 4), (tableProb2 τ : ℝ) * ((4 - (τ.card : ℝ)) * Real.log 4)

/-- `len(π)` of the second parameter set, by (7.2). -/
noncomputable def len2 : ℝ := ∑ τ, (tableProb2 τ : ℝ) * Real.log (lenOfType τ)

/-- `f` of the second parameter set, by (7.2). -/
noncomputable def f2 : ℝ :=
  Real.log (∑ S : Finset (Fin 4), (4 : ℝ) ^ (4 - S.card) * Real.exp (-tableTheta2 * tableWeight2 S)) +
    tableTheta2 * tableEta2

/-- `ξ` of the second parameter set, by (7.2). -/
noncomputable def xi2 : ℝ :=
  (∑ τ : Finset (Fin 4), (tableProb2 τ : ℝ) *
    Real.log (∑ S ∈ τ.powerset, (4 : ℝ) ^ (τ.card - S.card) * Real.exp (-(tableWeight2 τ - tableWeight2 S)))) +
  (∑ τ, (tableProb2 τ : ℝ) * tableWeight2 τ) - tableEta2

/-- **The frontier `δ_*`** of (7.4), p.47 (PDF p.49; Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file
sha256 6c5a1c16…), for the second parameter set of Table 1: with the rates `ν = H/(2 len)`, `Γ = (H − f)/len`,
`Q = ξ/len` of (5.5),
`δ_0^* = 2Γ / ((ν − 2Q)² + 4ΓQ)` and `δ_* = 1/2 + δ_0^*(1 − Q)`.

**Formalization Note.** The rates are those of `T5^(4)` with the distribution and weights of the second parameter set, in
the closed forms (7.2) of Proposition 7.1 (published milestone `MatMulDS.proposition_7_1`), which are independent of the
choices in the construction of `T5^(4)`. The probabilities and weights are the exact printed decimals. The paper gives
`δ_* = 0.5012157755649…`; this definition is the exact value, not the decimal. -/
noncomputable def deltaStar : ℝ :=
  let ν := entropy2 / (2 * len2)
  let Γ := (entropy2 - f2) / len2
  let Q := xi2 / len2
  let δ0 := 2 * Γ / ((ν - 2 * Q) ^ 2 + 4 * Γ * Q)
  1 / 2 + δ0 * (1 - Q)

end MatMulDS.Supplement


