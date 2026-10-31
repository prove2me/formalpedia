-- Prove2me | Definitions.Def_DynTradeFinance_DynamicFinancing
-- name    : DynTradeFinance_DynamicFinancing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:12.313991+00:00
-- url     : https://prove2.me/theorems/edcac70d-5489-4982-9270-c2a223b4fb0e
-- title:
--   Dynamic trade finance: repayment, expected repayment and net cost of capital (58), seller's payoff (8), competitive pricing (2), thresholds (30), (31)
-- statement:
--   Under **dynamic trade finance (DTF)** the bank offers a schedule $(r_1,r_2)$: the rate is $r_1$ from time $0$ and changes to $r_2$ when the bank verifies the passing of Step 1 at $\tilde T_1+\tilde d$. If $\tilde d<\tilde T_2$ the seller repays $c\,e^{r_1(\tilde T_1+\tilde d)+r_2(\tilde T_2-\tilde d)}$; if $\tilde d\ge\tilde T_2$ it repays $c\,e^{r_1(\tilde T_1+\tilde T_2)}$. For the model's clocks:
--
--   1. the expected DTF repayment
--   $$R_D(r_1,r_2)=\Pr(\tilde d<\tilde T_2)\,\mathbb E\big[c\,e^{r_1(\tilde T_1+\tilde d)+r_2(\tilde T_2-\tilde d)}\,\big|\,\tilde d<\tilde T_2\big]+\Pr(\tilde d\ge\tilde T_2)\,\mathbb E\big[c\,e^{r_1(\tilde T_1+\tilde T_2)}\,\big|\,\tilde d\ge\tilde T_2\big];$$
--   2. the net cost of holding regulatory capital (right side of (58) minus $c$): the bank holds $c-l_1$ until $\tilde T_1$ if Step 1 fails; if Step 1 passes it holds $c-l_1$ until $\tilde T_1+\tilde d$ and then $c-l_2$ until $\tilde T_1+\tilde T_2$ when $\tilde d<\tilde T_2$, and $c-l_1$ until $\tilde T_1+\tilde T_2$ otherwise:
--   $$\mathrm{NCC}_D=(1-p_1)(c-l_1)(\mathbb E[e^{\delta\tilde T_1}]-1)+p_1\Pr(\tilde d<\tilde T_2)\big[(c-l_2)(\mathbb E[e^{\delta(\tilde T_1+\tilde T_2)}\mid\tilde d<\tilde T_2]-1)+(l_2-l_1)(\mathbb E[e^{\delta(\tilde T_1+\tilde d)}\mid\tilde d<\tilde T_2]-1)\big]+p_1\Pr(\tilde d\ge\tilde T_2)(c-l_1)(\mathbb E[e^{\delta(\tilde T_1+\tilde T_2)}\mid\tilde d\ge\tilde T_2]-1);$$
--   3. the bank's expected repayment (left side of (58)): $\mathrm{EP}_D(r_1,r_2)=(1-p_1)l_1+p_1(1-p_2)l_2+p_1p_2R_D(r_1,r_2)$;
--   4. the seller's payoff, Eq. (8): $\Pi_D(r_1,r_2)=p_1p_2\big(w-R_D(r_1,r_2)\big)$;
--   5. $(r_1,r_2)$ is a **competitive DTF schedule** if $\mathrm{EP}_D(r_1,r_2)=c+\mathrm{NCC}_D$ (the pricing equation (2), i.e. (58));
--   6. the thresholds of Proposition B.1, Eqs. (30)–(31), and $\bar r_2^*=\min(r_2^{C,0},\bar r_2)$:
--   $$r_2^{C,0}=\frac{\mu(c-l_2)[\mu(1-p_2)+\delta p_2]}{\mu(c-l_2)+l_2p_2(\mu-\delta)},\qquad \bar r_2=\frac{1+\mu-\sqrt{(1-\mu)^2+4\mu p_1p_2c\,\Big(c+\frac{\delta}{1-\delta}\Big[(c-l_1)\big(1+\frac{p_1}{\lambda+\mu-\delta}\big)+\frac{(c-l_2)\lambda p_1}{(\lambda+\mu-\delta)(\mu-\delta)}\Big]-(1-p_1)l_1-p_1(1-p_2)l_2\Big)^{-1}}}{2}.$$
--
--   **Formalization Note** Each term $\Pr(A)\,\mathbb E[X\mid A]$ is written as $\mathbb E[X\mathbf 1_A]$, so $R_D$ is the expectation of the pathwise repayment and the two $p_1$-terms of $\mathrm{NCC}_D$ are one expectation of the pathwise capital cost; no division by $\Pr(A)$ occurs. The competitive-pricing predicate requires the pathwise repayment to be integrable, as for UF. The contract's ordering $r_1>r_2$ (p. 10) is not part of the pricing equation; the theorems state it where the paper does.
-- source:
--   Lee, Tang, Yang, Zhang, Dynamic trade finance in the presence of information frictions and FinTech, SSRN 3632563 (Feb. 2022 revision), §3, p. 10 (DTF contract); §4.2, Eq. (8), p. 13; proof of Proposition 2, Eq. (58), p. 39; Proposition B.1, Eqs. (30)–(31), p. 33

import Mathlib
import Definitions.Def_DynTradeFinance_Params

open MeasureTheory

namespace DynTradeFinance

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Pathwise DTF repayment**, SSRN 3632563 (Lee, Tang, Yang, Zhang), §4.2, case (iii), p. 13:
under the schedule `(r₁, r₂)` the rate is `r₁` from time 0 and switches to `r₂` when the bank
verifies the passing of Step 1 at `T₁ + d`. If `d < T₂` the seller repays
`c·e^{r₁(T₁+d) + r₂(T₂−d)}`; if `d ≥ T₂` there is no refinancing and it repays `c·e^{r₁(T₁+T₂)}`. -/
noncomputable def dtfRepayPath (θ : Params) (T₁ T₂ d : Ω → ℝ) (r₁ r₂ : ℝ) (ω : Ω) : ℝ :=
  if d ω < T₂ ω then θ.c * Real.exp (r₁ * (T₁ ω + d ω) + r₂ * (T₂ ω - d ω))
  else θ.c * Real.exp (r₁ * (T₁ ω + T₂ ω))

/-- **Expected DTF repayment**
`Pr(d̃ < T̃₂)E[c e^{r₁(T̃₁+d̃)+r₂(T̃₂−d̃)} | d̃ < T̃₂] + Pr(d̃ ≥ T̃₂)E[c e^{r₁(T̃₁+T̃₂)} | d̃ ≥ T̃₂]`,
the braced term of Eqs. (8), p. 13, and (58), p. 39, of SSRN 3632563.

**Formalization Note.** Each `Pr(A)·E[X | A]` is written as `E[X·1_A]`, so the sum is the
expectation of `dtfRepayPath`; this avoids dividing by `Pr(A)`. A Bochner integral (`0` if the
integrand is not integrable). -/
noncomputable def dtfRepay (θ : Params) (P : Measure Ω) (T₁ T₂ d : Ω → ℝ) (r₁ r₂ : ℝ) : ℝ :=
  ∫ ω, dtfRepayPath θ T₁ T₂ d r₁ r₂ ω ∂P

/-- **Net cost of holding regulatory capital under DTF**, the right-hand side of Eq. (58) minus
the principal `c`, SSRN 3632563, p. 39 (cases (i)–(iii) of §4.2, p. 13):
`NCC_D = (1 − p₁)(c − l₁)(E[e^{δT̃₁}] − 1)
  + p₁Pr(d̃ < T̃₂)[(c − l₂)(E[e^{δ(T̃₁+T̃₂)} | d̃ < T̃₂] − 1) + (l₂ − l₁)(E[e^{δ(T̃₁+d̃)} | d̃ < T̃₂] − 1)]
  + p₁Pr(d̃ ≥ T̃₂)[(c − l₁)(E[e^{δ(T̃₁+T̃₂)} | d̃ ≥ T̃₂] − 1)]`.

**Formalization Note.** `Pr(A)(E[X | A] − 1) = E[(X − 1)·1_A]`; the two `p₁` terms are written
as one expectation of the pathwise capital cost: on `{d < T₂}` the bank holds `c − l₁` until
`T₁ + d` and `c − l₂` from then to `T₁ + T₂`, on `{d ≥ T₂}` it holds `c − l₁` until `T₁ + T₂`. -/
noncomputable def nccD (θ : Params) (P : Measure Ω) (T₁ T₂ d : Ω → ℝ) : ℝ :=
  (1 - θ.p₁) * (θ.c - θ.l₁) * ((∫ ω, Real.exp (θ.δ * T₁ ω) ∂P) - 1) +
    θ.p₁ * ∫ ω, (if d ω < T₂ ω then
        (θ.c - θ.l₂) * (Real.exp (θ.δ * (T₁ ω + T₂ ω)) - 1) +
          (θ.l₂ - θ.l₁) * (Real.exp (θ.δ * (T₁ ω + d ω)) - 1)
      else (θ.c - θ.l₁) * (Real.exp (θ.δ * (T₁ ω + T₂ ω)) - 1)) ∂P

/-- **Bank's expected repayment under DTF**, the left-hand side of Eq. (58), SSRN 3632563, p. 39:
`(1 − p₁)l₁ + p₁(1 − p₂)l₂ + p₁p₂·{expected DTF repayment}`. -/
noncomputable def epD (θ : Params) (P : Measure Ω) (T₁ T₂ d : Ω → ℝ) (r₁ r₂ : ℝ) : ℝ :=
  (1 - θ.p₁) * θ.l₁ + θ.p₁ * (1 - θ.p₂) * θ.l₂ + θ.p₁ * θ.p₂ * dtfRepay θ P T₁ T₂ d r₁ r₂

/-- **Seller's payoff under the DTF schedule `(r₁, r₂)`, Eq. (8)**, SSRN 3632563, p. 13:
`Π = p₁p₂{w − Pr(d̃ < T̃₂)E[c e^{r₁(T̃₁+d̃)+r₂(T̃₂−d̃)} | d̃ < T̃₂] − Pr(d̃ ≥ T̃₂)E[c e^{r₁(T̃₁+T̃₂)} | d̃ ≥ T̃₂]}`. -/
noncomputable def payoffD (θ : Params) (P : Measure Ω) (T₁ T₂ d : Ω → ℝ) (r₁ r₂ : ℝ) : ℝ :=
  θ.p₁ * θ.p₂ * (θ.w - dtfRepay θ P T₁ T₂ d r₁ r₂)

/-- **Competitive DTF schedule**: `(r₁, r₂)` satisfies the bank's competitive loan pricing
equation (2), SSRN 3632563, p. 11, in the DTF form (58), p. 39: expected repayment = `c + NCC_D`.

**Formalization Note.** The pathwise repayment is required to be integrable (a finite expected
repayment, which the paper's equation presupposes); otherwise Lean's convention `∫ = 0` would
change the equation. The contract's ordering `r₁ > r₂` (p. 10) is not part of the pricing
equation; theorems state it where the paper does. -/
def IsCompetitiveDTF (θ : Params) (P : Measure Ω) (T₁ T₂ d : Ω → ℝ) (r₁ r₂ : ℝ) : Prop :=
  Integrable (dtfRepayPath θ T₁ T₂ d r₁ r₂) P ∧
    epD θ P T₁ T₂ d r₁ r₂ = θ.c + nccD θ P T₁ T₂ d

/-- **The refinancing threshold `r₂^{C,0}`, Eq. (30)** (Proposition B.1, SSRN 3632563, p. 33;
also (66), p. 40): `r₂^{C,0} = μ(c − l₂)[μ(1 − p₂) + δp₂] / (μ(c − l₂) + l₂p₂(μ − δ))`. -/
noncomputable def r2C0 (θ : Params) : ℝ :=
  θ.μ * (θ.c - θ.l₂) * (θ.μ * (1 - θ.p₂) + θ.δ * θ.p₂) /
    (θ.μ * (θ.c - θ.l₂) + θ.l₂ * θ.p₂ * (θ.μ - θ.δ))

/-- **The threshold `r̄₂`, Eq. (31)** (Proposition B.1, SSRN 3632563, p. 33; also (65), p. 40):
`r̄₂ = (1 + μ − √((1 − μ)² + 4μp₁p₂c·(c + δ/(1−δ)[(c − l₁)(1 + p₁/(λ+μ−δ)) +
(c − l₂)λp₁/((λ+μ−δ)(μ−δ))] − (1 − p₁)l₁ − p₁(1 − p₂)l₂)⁻¹)) / 2`. -/
noncomputable def r2bar (θ : Params) : ℝ :=
  (1 + θ.μ - Real.sqrt ((1 - θ.μ) ^ 2 + 4 * θ.μ * θ.p₁ * θ.p₂ * θ.c *
    (θ.c + θ.δ / (1 - θ.δ) * ((θ.c - θ.l₁) * (1 + θ.p₁ / (θ.lam + θ.μ - θ.δ)) +
        (θ.c - θ.l₂) * θ.lam * θ.p₁ / ((θ.lam + θ.μ - θ.δ) * (θ.μ - θ.δ))) -
      (1 - θ.p₁) * θ.l₁ - θ.p₁ * (1 - θ.p₂) * θ.l₂)⁻¹)) / 2

/-- **The threshold of Proposition 2**, `r̄₂* := min(r₂^{C,0}, r̄₂)`, SSRN 3632563, proof of
Proposition 2, p. 39. -/
noncomputable def r2barStar (θ : Params) : ℝ :=
  min (r2C0 θ) (r2bar θ)

end DynTradeFinance


