-- Prove2me | Definitions.Def_PrefDeals_aagDeal
-- name    : PrefDeals_aagDeal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:21:15.999963+00:00
-- url     : https://prove2.me/theorems/9a402c53-2416-4668-9e99-21c2d3ef58b5
-- title:
--   Deal $(\rho_j,\mu_j,\mathcal I)$ proposed by Auction-Adjusted Greedy
-- statement:
--   For a stream $A$, a set of buyers $S$ and $j\in S_1$ with threshold $\theta_j$, the algorithm proposes to buyer $j$ the deal $(\rho_j,\mu_j,A)$ with
--
--   $$
--   \mu_j=\Pr_A[v_j\ge\theta_j]=\frac{P(A\cap\{v_j\ge\theta_j\})}{P(A)},\qquad
--   \rho_j=\mathrm E_A[v_j\mid v_j\ge\theta_j]=\frac{\int_{A\cap\{v_j\ge\theta_j\}}v_j\,dP}{P(A\cap\{v_j\ge\theta_j\})}.
--   $$
--
--   When $S_1=\{i\}$, the algorithm instead returns the deal $(\mathrm E_A[v_i],1,A)$ with $\mathrm E_A[v_i]=\int_A v_i\,dP/P(A)$ (`aagSingletonDeal`).
--
--   The price $\rho_j$ is the average value of the impressions buyer $j$ buys under the deal, so the deal extracts his whole surplus.
--
--   **Formalization Note** A ratio with a null denominator is $0$ in Lean; the algorithm uses these quantities only where the denominators are positive.
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, Figure 1, p.11

import Mathlib
import Definitions.Def_PrefDeals_aagTheta
import Definitions.Def_PrefDeals_Deal

open MeasureTheory

namespace PrefDeals

/-- The minimum purchase requirement `µⱼ = Pr_𝓘[vⱼ ≥ θⱼ]` of Figure 1, p.11, on the stream `A`. -/
noncomputable def aagMu {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : ValuationModel P n) (A : Set Ω) (S : Finset (Fin n)) (j : Fin n) : ℝ :=
  P.real (A ∩ {ω | aagTheta M A S j ≤ M.v j ω}) / P.real A

/-- The price per impression `ρⱼ = E_𝓘[vⱼ | vⱼ ≥ θⱼ]` of Figure 1, p.11, on the stream `A`. -/
noncomputable def aagRho {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : ValuationModel P n) (A : Set Ω) (S : Finset (Fin n)) (j : Fin n) : ℝ :=
  (∫ ω in A ∩ {ω | aagTheta M A S j ≤ M.v j ω}, M.v j ω ∂P) /
    P.real (A ∩ {ω | aagTheta M A S j ≤ M.v j ω})

/-- The deal `(ρᵢ = E_𝓘[vᵢ], µᵢ = 1, 𝓘ᵢ = 𝓘)` that Figure 1, p.11, returns when `S₁ = {i}`. -/
noncomputable def aagSingletonDeal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : ValuationModel P n) (A : Set Ω) (i : Fin n) : Deal Ω :=
  ⟨(∫ ω in A, M.v i ω ∂P) / P.real A, 1, A⟩

/-- **The deal Auction-Adjusted Greedy proposes to buyer `j`.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, Figure 1, p.11: "For each buyer
`j ∈ S₁`: Choose the smallest `θⱼ` such that `Pr_𝓘[vⱼ ≥ θⱼ] = Pr_𝓘[vⱼ = v₍₁₎(S₁)]`.
`ρⱼ ← E_𝓘[vⱼ|vⱼ ≥ θⱼ]`. `µⱼ ← Pr_𝓘[vⱼ ≥ θⱼ]`. `𝓘ⱼ ← 𝓘`."

On the stream `A` with buyers `S`, `aagDeal M A S j = (ρⱼ, µⱼ, A)` with
`µⱼ = P(A ∩ {vⱼ ≥ θⱼ}) / P(A)` (`aagMu`) and
`ρⱼ = (∫_{A ∩ {vⱼ ≥ θⱼ}} vⱼ dP) / P(A ∩ {vⱼ ≥ θⱼ})` (`aagRho`), `θⱼ = aagTheta M A S j`.
`aagSingletonDeal M A i = ((∫_A vᵢ dP) / P(A), 1, A)` is the deal of the case `S₁ = {i}`.

**Formalization Note.** `Pr_𝓘` and `E_𝓘[·|·]` are the conditional probability and expectation given
the stream `A`, i.e. ratios of set integrals and measures. A ratio with a null denominator is `0`
in Lean; this happens only off the cases the algorithm uses (`j ∈ S₁` gives
`P(A ∩ {vⱼ ≥ θⱼ}) > 0` once `θⱼ` is attained). -/
noncomputable def aagDeal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : ValuationModel P n) (A : Set Ω) (S : Finset (Fin n)) (j : Fin n) : Deal Ω :=
  ⟨aagRho M A S j, aagMu M A S j, A⟩

end PrefDeals


