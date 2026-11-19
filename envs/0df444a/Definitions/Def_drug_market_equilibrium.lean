-- Prove2me | Definitions.Def_drug_market_equilibrium
-- name    : drug_market_equilibrium
-- status  : Definition
-- author  : @LG
-- created : 2026-11-16T13:34:59.951559+00:00
-- url     : https://prove2.me/theorems/647c29e0-35d1-4da1-bfe7-366335c9218f
-- title:
--   Drug-market vertical network: equilibrium objects
-- statement:
--   Equilibrium objects of the drug-market game, defined from the primitives. Retail price best responses are $p_a=t+(2w_a+w_b)/3$, $p_b=t+(2w_b+w_a)/3$, giving gross profit $\pi'_a=(t+(w_b-w_a)/3)^2/(2t)$. Writing $\rho_i=q^{1/v_{ri}}$ and $k_i=s\rho_i/(1-\rho_i)$, the wholesale equilibrium prices are $w_a^*=3t+c+(2k_a+k_b)/3$ and $w_b^*=3t+c+(2k_b+k_a)/3$. The retail violence best response is $v_i^*=v_r\ln(\hat q_i)/\ln q$ with $\hat q_i=-v_r/(\ln q\,(\pi'_i+s))$. Downstream equilibrium objects are the retail price $4t+c+(5k_a+4k_b)/9$, demand $\tfrac12+(k_b-k_a)/(18t)$, gross margin $t+(k_b-k_a)/9$, gross profit $(t+(k_b-k_a)/9)^2/(2t)$, and violence $v_r\ln(\hat q_i)/\ln q$ evaluated at equilibrium profit. NOTE: the printed closed forms (3.50), (3.53), (3.55), (3.59), (3.62) carry inconsistent constant factors ($3s$ versus $s/3$, a missing $1/(18t)$, $3t$ versus $4t$); the constants used here are those obtained by solving the model's own first-order conditions (3.48)–(3.49) composed with (3.21)–(3.25). All qualitative sign results are unaffected.
-- source:
--   Gilberto José Nogueira Júnior, *Mercado de Drogas e Repressão: Efeitos da Intervenção Governamental sobre a Violência gerada pelo Mercado de Drogas numa Rede Verticalmente Relacionada*, MSc dissertation, UFPE/PIMES, 2019, Chapter 3. Equations (3.21)–(3.35), (3.48)–(3.64); printed constant factors corrected as documented.

import Mathlib
import Definitions.Def_drug_market_model

noncomputable section

namespace DrugMarket
/-- Retailer A's equilibrium price as a function of wholesale prices (eq. 3.21). -/
def retailPriceA (t w_a w_b : ℝ) : ℝ := t + (2 * w_a + w_b) / 3

/-- Retailer B's equilibrium price as a function of wholesale prices (eq. 3.22). -/
def retailPriceB (t w_a w_b : ℝ) : ℝ := t + (2 * w_b + w_a) / 3

/-- Retailer A's gross profit at the retail price equilibrium, `π'_a` (eq. 3.25). -/
def grossProfitA (t w_a w_b : ℝ) : ℝ := (t + (w_b - w_a) / 3) ^ 2 / (2 * t)

/-- Retailer B's gross profit at the retail price equilibrium, `π'_b` (eq. 3.25). -/
def grossProfitB (t w_a w_b : ℝ) : ℝ := (t + (w_a - w_b) / 3) ^ 2 / (2 * t)

/-- The expected-repression cost markup `k_i = s ρ_i / (1 - ρ_i)`, where
`ρ_i = q ^ (1 / v_ri)` is the police success probability against wholesaler i
(appears in eq. 3.48–3.51). -/
def kappa (q s v_ri : ℝ) : ℝ :=
  s * catchWholesale q v_ri / (1 - catchWholesale q v_ri)

/-- The quantity `q̂_i = -v_r / (ln q · (π'_i + s))` (eq. 3.32–3.33). -/
def qHat (q s v_r g : ℝ) : ℝ := -v_r / (Real.log q * (g + s))

/-- The interior violence best response `v*_i = v_r · ln(q̂_i) / ln q`
(eq. 3.34–3.35). -/
def violenceBR (q s v_r g : ℝ) : ℝ := v_r * Real.log (qHat q s v_r g) / Real.log q

/-- Wholesaler A's equilibrium price (eq. 3.50, with the constant corrected to
`s/3` as obtained by solving (3.48)–(3.49)). -/
def wholesalePriceA (q s t c v_ra v_rb : ℝ) : ℝ :=
  3 * t + c + (2 * kappa q s v_ra + kappa q s v_rb) / 3

/-- Wholesaler B's equilibrium price (eq. 3.51, constant corrected to `s/3`). -/
def wholesalePriceB (q s t c v_ra v_rb : ℝ) : ℝ :=
  3 * t + c + (2 * kappa q s v_rb + kappa q s v_ra) / 3

/-- Retailer A's equilibrium gross margin `t + (k_b - k_a)/9` (eq. 3.62). -/
def eqMarginA (q s t c v_ra v_rb : ℝ) : ℝ :=
  t + (kappa q s v_rb - kappa q s v_ra) / 9

/-- Retailer B's equilibrium gross margin `t + (k_a - k_b)/9`. -/
def eqMarginB (q s t c v_ra v_rb : ℝ) : ℝ :=
  t + (kappa q s v_ra - kappa q s v_rb) / 9

/-- Retailer A's equilibrium retail price (eq. 3.55 / 3.63, constant corrected:
`4t + c + (5k_a + 4k_b)/9`). -/
def eqRetailPriceA (q s t c v_ra v_rb : ℝ) : ℝ :=
  4 * t + c + (5 * kappa q s v_ra + 4 * kappa q s v_rb) / 9

/-- Retailer B's equilibrium retail price (eq. 3.56 / 3.63, constant corrected). -/
def eqRetailPriceB (q s t c v_ra v_rb : ℝ) : ℝ :=
  4 * t + c + (5 * kappa q s v_rb + 4 * kappa q s v_ra) / 9

/-- Retailer A's equilibrium demand (eq. 3.53 / 3.64, constant corrected:
`1/2 + (k_b - k_a)/(18t)`). -/
def eqDemandA (q s t c v_ra v_rb : ℝ) : ℝ :=
  (1 : ℝ) / 2 + (kappa q s v_rb - kappa q s v_ra) / (18 * t)

/-- Retailer B's equilibrium demand (eq. 3.54, constant corrected). -/
def eqDemandB (q s t c v_ra v_rb : ℝ) : ℝ :=
  (1 : ℝ) / 2 + (kappa q s v_ra - kappa q s v_rb) / (18 * t)

/-- Retailer A's equilibrium gross profit `π'_a = (t + (k_b - k_a)/9)² / (2t)`
(eq. 3.59 / 3.62, constant corrected). -/
def eqGrossProfitA (q s t c v_ra v_rb : ℝ) : ℝ :=
  eqMarginA q s t c v_ra v_rb ^ 2 / (2 * t)

/-- Retailer B's equilibrium gross profit (eq. 3.59, constant corrected). -/
def eqGrossProfitB (q s t c v_ra v_rb : ℝ) : ℝ :=
  eqMarginB q s t c v_ra v_rb ^ 2 / (2 * t)

/-- Retailer A's equilibrium violence (eq. 3.57), as a function of the repression
intensities through the equilibrium gross profit. -/
def eqViolenceA (q s t c v_r v_ra v_rb : ℝ) : ℝ :=
  violenceBR q s v_r (eqGrossProfitA q s t c v_ra v_rb)

/-- Retailer B's equilibrium violence (eq. 3.58). -/
def eqViolenceB (q s t c v_r v_ra v_rb : ℝ) : ℝ :=
  violenceBR q s v_r (eqGrossProfitB q s t c v_ra v_rb)


end DrugMarket
end


