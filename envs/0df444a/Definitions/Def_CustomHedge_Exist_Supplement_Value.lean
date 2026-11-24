-- Prove2me | Definitions.Def_CustomHedge_Exist_Supplement_Value
-- name    : CustomHedge_Exist_Supplement_Value
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:37:00.393262+00:00
-- url     : https://prove2.me/theorems/3e2924e1-e765-439d-b8fe-a30fbedb5634
-- title:
--   (10), Definitions 1–2, pp. 12–13 — optimal value 𝒰*_𝓗 of the hedge design problem, value of flexibility (11), combination value 𝒞𝒱_{X→X+I}
-- statement:
--   Work in the combined custom hedging market of the base mission: a probability space $(\Omega,\mathcal F,\mathbb P)$, the position $\pi=\pi(X,Y)\in L^2$, the pricing kernel $d\mathbb Q/d\mathbb P$, the risk-neutral expectation $\mathbb E_{\mathbb Q}[Z]=\mathbb E[Z\,d\mathbb Q/d\mathbb P]$, the mean–variance criterion $\mathscr U(Z)=\varrho\,\mathbb E[Z]-\tfrac a2\operatorname{Var}[Z]$ and the optimal hedging kernel $\mathcal K=\pi+\tfrac{\varrho}{a}\tfrac{d\mathbb Q}{d\mathbb P}$.
--
--   1. The **optimal centered hedging kernel** is $\mathcal K_0=\mathcal K-\mathbb E[\mathcal K]$.
--   2. For a class $\mathcal H\subseteq L^2(\Omega)$ of contingent claims, the optimal value of the **hedge design problem** (10) is
--   $$\mathscr U^*_{\mathcal H}=\sup\big\{\mathscr U(\pi+H)\;:\;H\in\mathcal H,\ \mathbb E_{\mathbb Q}[H]=0\big\}.$$
--   3. The **value of a financial hedging flexibility shift** from $\mathcal G$ to $\mathcal H$ (Definition 1) is the monetary amount $m$ with $\mathscr U(\pi+H^*_{\mathcal G}+m)=\mathscr U(\pi+H^*_{\mathcal H})$; since $\mathscr U(Z+m)=\mathscr U(Z)+\varrho m$ it equals
--   $$\mathcal V_{\mathcal G\to\mathcal H}=\varrho^{-1}\big(\mathscr U^*_{\mathcal H}-\mathscr U^*_{\mathcal G}\big).\qquad(11)$$
--   4. $\mathcal H_X$ is the class of $\sigma(X)$-measurable claims with finite variance, and $\mathcal H_{XI}=\mathcal H_X+\mathcal H_I$ the class of sums $H+G$ with $H\in\mathcal H_X$, $G\in\mathcal H_I$.
--   5. The **combination value** of $X$ and $I$ over $X$ (Definition 2) is $\mathcal{CV}_{X\to X+I}=\mathcal V_{\mathcal H_X\to\mathcal H_{XI}}$.
--
--   These are the objects of the paper's combination value assessment (§4): the monetary gain from adding a claim on a side index $I$ to a claim on the hedgeable term $X$.
--
--   **Formalization Note** $\mathscr U^*_{\mathcal H}$ is a real supremum (`sSup`), so attainment is a theorem rather than part of the definition; for the classes used here the feasible set contains $H=0$ and $\mathscr U(\pi+H)$ is bounded above (Lemma EC.1), so the supremum is the paper's maximum whenever that exists. $\mathcal V$ is encoded by its closed form (11), which is how the paper evaluates it; $\varrho^{-1}$ is Lean's `0⁻¹ = 0` at $\varrho=0$, a case Theorem 3 excludes by its hypothesis $\varrho>0$.
-- source:
--   Guiotto & Roncoroni, Combined custom hedging: optimal design, noninsurable exposure, and operational risk management, manuscript OPRE-2019-01-058.R3 (Operations Research 2022), p. 10 (PDF 10), optimal centered hedging kernel; p. 12 (PDF 12), problem (10), Example 5 (𝓗_XI = 𝓗_X + 𝓗_I); p. 13 (PDF 13), Definition 1, (11), Definition 2

import Mathlib
import Definitions.Def_CustomHedge_Exist_Model

namespace CustomHedge.Exist.Supplement

open MeasureTheory ProbabilityTheory

variable {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
  [MeasurableSpace EY] [MeasurableSpace EI]

/-- The optimal centered hedging kernel `K₀ = K - E[K]`, with `K = π + (ϱ/a) dQ/dP` (p. 10). -/
noncomputable def K0 (M : Market Ω EX EY EI) : Ω → ℝ :=
  fun ω => M.K ω - ∫ ω', M.K ω' ∂M.P

/-- The optimal value `𝒰*_𝓗` of the hedge design problem (10) for a class `𝓗 ⊆ L²(Ω)` of
claims: the supremum of `U(π + H)` over the claims `H ∈ 𝓗` with `E_Q[H] = 0`. (Real `sSup`:
`0` on an empty or unbounded-above set.) -/
noncomputable def Ustar (M : Market Ω EX EY EI) (C : Set (Ω → ℝ)) : ℝ :=
  sSup ((fun H => M.U (M.pos + H)) '' {H | H ∈ C ∧ M.EQ H = 0})

/-- The value `𝒱_{𝒢→𝓗}` of a financial hedging flexibility shift from `𝒢` to `𝓗`
(Definition 1, in the closed form (11)): `𝒱_{𝒢→𝓗} = ϱ⁻¹ (𝒰*_𝓗 - 𝒰*_𝒢)`. -/
noncomputable def flexValue (M : Market Ω EX EY EI) (C₁ C₂ : Set (Ω → ℝ)) : ℝ :=
  M.rho⁻¹ * (Ustar M C₂ - Ustar M C₁)

/-- The single-claim class `𝓗_X`: `σ(X)`-measurable claims of finite variance. -/
def claimsX (M : Market Ω EX EY EI) : Set (Ω → ℝ) :=
  {H | InClaims M.P M.FX H}

/-- The combined class `𝓗_XI = 𝓗_X + 𝓗_I`: sums `H + G` of a claim on `X` and a claim on `I`. -/
def claimsXI (M : Market Ω EX EY EI) : Set (Ω → ℝ) :=
  {Z | ∃ H G : Ω → ℝ, InClaims M.P M.FX H ∧ InClaims M.P M.FI G ∧ Z = H + G}

/-- The combination value `𝒞𝒱_{X→X+I} := 𝒱_{𝓗_X → 𝓗_XI}` of `X` and `I` over `X`
(Definition 2). -/
noncomputable def CV (M : Market Ω EX EY EI) : ℝ :=
  flexValue M (claimsX M) (claimsXI M)

end CustomHedge.Exist.Supplement


