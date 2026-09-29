-- Prove2me | Definitions.Def_SeasonalPricing_MyopicExp_contingentMyopicRevenue
-- name    : SeasonalPricing_MyopicExp_contingentMyopicRevenue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:15:02.207372+00:00
-- url     : https://prove2.me/theorems/970c279b-5330-40f3-b10c-927f4184b7c0
-- title:
--   Expected revenues with unlimited inventory: contingent pricing with myopic customers (C/N) and a fixed price, Eq. (9)
-- statement:
--   Fix the arrival rate $\lambda$, the decline factor $\alpha$, the discount time $T$, the horizon $H$ and the base-valuation tail $\bar F$, and suppose inventory is unlimited, so that every customer who wants a unit gets one.
--
--   **Contingent pricing with myopic customers (C/N).** A myopic customer arriving at time $t < T$ buys at the premium price $p_1$ if his valuation is at least $p_1$; otherwise he waits until $T$ and buys if his valuation then is at least the discount price $z$; customers arriving at or after $T$ buy if their valuation is at least $z$. The purchasing threshold is thus $\psi \equiv p_1$, and the expected revenue is
--
--   $$
--   R_{C/N}(p_1, z) = p_1 \cdot \Lambda_I(p_1) + z \cdot \big(\Lambda_W(p_1, z) + \Lambda_L(z)\big),
--   $$
--
--   with the segment rates $\Lambda_I, \Lambda_W, \Lambda_L$ of §4.2.
--
--   **Fixed price.** A single price $p$ on the whole season yields
--
--   $$
--   R_F(p) = p \cdot \lambda \int_0^H \bar F\big(p\, e^{\alpha t}\big)\,dt .
--   $$
--
--   The optimal revenues $\pi^*_{C/N}$ and $\pi^*_F$ of the paper are the maxima of these functions over $z \le p_1$, respectively over $p$.
--
--   **Formalization Note** The paper's revenue expressions on p. 349 carry a finite inventory $Q$ through the truncated Poisson mean $N(q, \Lambda) = \sum_x \min(x, q) P(x \mid \Lambda)$. With unlimited inventory ($Q = \infty$, p. 348; "inventory is practically unlimited", p. 350) the truncation disappears, $N(q, \Lambda)$ becomes $\Lambda$, and the formulas above result. The seller's discount $z$ at time $T$ is a best response to $p_1$ in the paper ($R(q \mid p_1) = \max_{z \le p_1}\{\dots\}$); with unlimited inventory it does not depend on the realized sales, and maximizing the total jointly over $(p_1, z)$ with $z \le p_1$ gives the same optimum. The names are `contingentMyopicRevenue` and `fixedPriceRevenue`.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 349, §6 (myopic purchase rule, π*_{C/N} with ψ(p1) = p1 and R(q | p1), Eq. (9) for π*_F); p. 346, Eq. (3) and N(q, Λ); p. 348 (Q = ∞); p. 350, §7.1

import Mathlib
import Definitions.Def_SeasonalPricing_Shared_LambdaI

namespace SeasonalPricing.MyopicExp

/-- Expected revenue of the contingent two-price policy with myopic customers (C/N) and unlimited
inventory (Aviv–Pazgal 2008, §6, p. 349, with the truncated mean `N(q, Λ)` replaced by `Λ`):
premium price `p₁` on `[0, T)`, discount price `z` from `T` on. Myopic customers use the constant
threshold `ψ ≡ p₁`, so the premium-price sales have mean `Λ_I(p₁)`; at time `T` the waiting
customers (mean `Λ_W(p₁, z)`) and the late arrivals (mean `Λ_L(z)`) buy at `z`:
`p₁ · Λ_I(p₁) + z · (Λ_W(p₁, z) + Λ_L(z))`. -/
noncomputable def contingentMyopicRevenue (lam α T H : ℝ) (Fbar : ℝ → ℝ) (p1 z : ℝ) : ℝ :=
  p1 * Shared.LambdaI lam α T Fbar (fun _ => p1) + z * (Shared.LambdaW lam α T Fbar p1 z + Shared.LambdaL lam α T H Fbar z)

/-- Expected revenue of a single price `p` held over the whole season `[0, H]` with unlimited
inventory (Aviv–Pazgal 2008, Eq. (9), p. 349, with `N(Q, Λ)` replaced by `Λ`):
`p · λ ∫_0^H F̄(p e^{αt}) dt`. -/
noncomputable def fixedPriceRevenue (lam α H : ℝ) (Fbar : ℝ → ℝ) (p : ℝ) : ℝ :=
  p * (lam * ∫ t in (0)..H, Fbar (p * Real.exp (α * t)))

end SeasonalPricing.MyopicExp


