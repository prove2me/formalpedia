-- Prove2me | Definitions.Def_DynTradeFinance_UniformFinancing
-- name    : DynTradeFinance_UniformFinancing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:12.454762+00:00
-- url     : https://prove2.me/theorems/a75f949b-c3f2-4db4-8e93-033a3c6b2961
-- title:
--   Uniform financing: repayment, expected repayment (4), net cost of capital (5), seller's payoff (3), competitive pricing (2), and the rate $r^*$ (6)
-- statement:
--   Under **uniform financing (UF)** the bank charges one rate $r$ over the whole process and the seller repays $c\,e^{r(\tilde T_1+\tilde T_2)}$ at completion. For the model's clocks:
--
--   1. the expected repayment of the bank, Eq. (4): $\mathrm{EP}_U(r)=(1-p_1)l_1+p_1(1-p_2)l_2+p_1p_2\,\mathbb E\big[c\,e^{r(\tilde T_1+\tilde T_2)}\big]$;
--   2. the net cost of holding regulatory capital, Eq. (5): $\mathrm{NCC}_U=(c-l_1)\big[(1-p_1)(\mathbb E[e^{\delta\tilde T_1}]-1)+p_1(\mathbb E[e^{\delta(\tilde T_1+\tilde T_2)}]-1)\big]$;
--   3. the seller's payoff, Eq. (3): $\Pi_U(r)=p_1p_2\big(w-\mathbb E\big[c\,e^{r(\tilde T_1+\tilde T_2)}\big]\big)$;
--   4. $r$ is a **competitive UF rate** if it satisfies the bank's competitive loan pricing equation (2), "Expected Repayment = Loan Principal + Net Cost of Holding Regulatory Capital Reserve":
--   $$\mathrm{EP}_U(r)=c+\mathrm{NCC}_U ;$$
--   5. the rate of Proposition 1, Eq. (6):
--   $$r^*=\tfrac12\Big(1+\mu-\sqrt{1+\mu^2-\mu\Big(2-\frac{4cp_1p_2}{c-(1-p_1)l_1-p_1(1-p_2)l_2+\frac{(\mu+p_1-\delta)(c-l_1)\delta}{(1-\delta)(\mu-\delta)}}\Big)}\Big).$$
--
--   **Formalization Note** Expectations are Bochner integrals, which take the value $0$ on non-integrable functions; the competitive-pricing predicate therefore also requires the repayment $c\,e^{r(\tilde T_1+\tilde T_2)}$ to be integrable (a finite expected repayment, which the paper's equation presupposes). Under the standing assumptions the capital-cost expectations are finite.
-- source:
--   Lee, Tang, Yang, Zhang, Dynamic trade finance in the presence of information frictions and FinTech, SSRN 3632563 (Feb. 2022 revision), §4, Eq. (2), p. 11; §4.1, Eqs. (3)–(5), p. 12; Proposition 1, Eq. (6), p. 12

import Mathlib
import Definitions.Def_DynTradeFinance_Params

open MeasureTheory

namespace DynTradeFinance

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Expected UF repayment** `E[c·e^{r(T̃₁+T̃₂)}]`, SSRN 3632563 (Lee, Tang, Yang, Zhang),
§4.1, Eqs. (3)–(4), p. 12: under uniform financing at rate `r` the seller repays
`c·e^{r(T₁+T₂)}` at completion (continuous compounding, p. 9).

**Formalization Note.** A Bochner integral; it equals `0` when the integrand is not integrable,
which is why `IsCompetitiveUF` also requires integrability. -/
noncomputable def ufRepay (θ : Params) (P : Measure Ω) (T₁ T₂ : Ω → ℝ) (r : ℝ) : ℝ :=
  ∫ ω, θ.c * Real.exp (r * (T₁ ω + T₂ ω)) ∂P

/-- **Net cost of holding regulatory capital under UF, Eq. (5)**, SSRN 3632563, p. 12:
`NCC = (c − l₁)[(1 − p₁)(E[e^{δT̃₁}] − 1) + p₁(E[e^{δ(T̃₁+T̃₂)}] − 1)]`. -/
noncomputable def nccU (θ : Params) (P : Measure Ω) (T₁ T₂ : Ω → ℝ) : ℝ :=
  (θ.c - θ.l₁) * ((1 - θ.p₁) * ((∫ ω, Real.exp (θ.δ * T₁ ω) ∂P) - 1) +
    θ.p₁ * ((∫ ω, Real.exp (θ.δ * (T₁ ω + T₂ ω)) ∂P) - 1))

/-- **Bank's expected repayment under UF, Eq. (4)**, SSRN 3632563, p. 12:
`EP = (1 − p₁)l₁ + p₁(1 − p₂)l₂ + p₁p₂E[c e^{r(T̃₁+T̃₂)}]`. -/
noncomputable def epU (θ : Params) (P : Measure Ω) (T₁ T₂ : Ω → ℝ) (r : ℝ) : ℝ :=
  (1 - θ.p₁) * θ.l₁ + θ.p₁ * (1 - θ.p₂) * θ.l₂ + θ.p₁ * θ.p₂ * ufRepay θ P T₁ T₂ r

/-- **Seller's payoff under UF at rate `r`, Eq. (3)**, SSRN 3632563, p. 12:
`Π_U = p₁p₂(w − E[c e^{r(T̃₁+T̃₂)}])`. -/
noncomputable def payoffU (θ : Params) (P : Measure Ω) (T₁ T₂ : Ω → ℝ) (r : ℝ) : ℝ :=
  θ.p₁ * θ.p₂ * (θ.w - ufRepay θ P T₁ T₂ r)

/-- **Competitive UF rate**: `r` satisfies the bank's competitive loan pricing equation (2),
SSRN 3632563, p. 11 ("Expected Repayment = Loan Principal + Net Cost of Holding Regulatory
Capital Reserve"), in the UF form `EP = c + NCC` of p. 12.

**Formalization Note.** The repayment `c·e^{r(T₁+T₂)}` is required to be integrable, i.e. the
expected repayment is finite, as the paper's equation between real numbers presupposes; without
this, Lean's convention `∫ = 0` for non-integrable functions would change the equation. -/
def IsCompetitiveUF (θ : Params) (P : Measure Ω) (T₁ T₂ : Ω → ℝ) (r : ℝ) : Prop :=
  Integrable (fun ω => θ.c * Real.exp (r * (T₁ ω + T₂ ω))) P ∧
    epU θ P T₁ T₂ r = θ.c + nccU θ P T₁ T₂

/-- **The equilibrium UF rate, Eq. (6)** (Proposition 1, SSRN 3632563, p. 12):
`r* = ½(1 + μ − √(1 + μ² − μ(2 − 4cp₁p₂ / (c − (1 − p₁)l₁ − p₁(1 − p₂)l₂ +
(μ + p₁ − δ)(c − l₁)δ/((1 − δ)(μ − δ))))))`. -/
noncomputable def rStarUF (θ : Params) : ℝ :=
  (1 / 2) * (1 + θ.μ - Real.sqrt (1 + θ.μ ^ 2 - θ.μ * (2 - 4 * θ.c * θ.p₁ * θ.p₂ /
    (θ.c - (1 - θ.p₁) * θ.l₁ - θ.p₁ * (1 - θ.p₂) * θ.l₂ +
      (θ.μ + θ.p₁ - θ.δ) * (θ.c - θ.l₁) * θ.δ / ((1 - θ.δ) * (θ.μ - θ.δ))))))

end DynTradeFinance


