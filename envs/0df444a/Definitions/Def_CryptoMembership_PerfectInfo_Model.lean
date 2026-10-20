-- Prove2me | Definitions.Def_CryptoMembership_PerfectInfo_Model
-- name    : CryptoMembership_PerfectInfo_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:14.37632+00:00
-- url     : https://prove2.me/theorems/87255340-5fc2-4ffb-a653-aeb8bc490a9e
-- title:
--   §1–§2, pp. 7–15 — membership cryptocurrency: Cobb–Douglas matched trade, households' purchase rule, miners' supply, market-clearing equilibrium, Π_D, U₀
-- statement:
--   This file sets up the perfect-information model of a cryptocurrency as a membership in a trading platform (Sockin and Xiong, §1–§2).
--
--   **Parameters.** $\eta_c$ is the Cobb–Douglas weight on the partner's good, $\tau_\varepsilon$ the precision of the households' idiosyncratic endowment shocks, $\tau_e$ the precision of the miners' idiosyncratic cost shocks, and $\rho_s$ the developer's share of the proceeds. The **standing assumptions** are $\eta_c\in(0,1)$, $\tau_\varepsilon>0$, $\tau_e>0$ and $\rho_s\in(0,1)$ (so that the miners' share $1-\rho_s$ lies in $(0,1)$). $\Phi$ is the standard normal cdf.
--
--   **Goods trade at $t=2$.** A household's utility from consuming $C_i$ of its own good and $C_j$ of its partner's good is
--   $$U(C_i,C_j)=\Big(\frac{C_i}{1-\eta_c}\Big)^{1-\eta_c}\Big(\frac{C_j}{\eta_c}\Big)^{\eta_c}.$$
--   In a matched pair, household $i$ owns $e^{A_i}$ units of good $i$ and household $j$ owns $e^{A_j}$ units of good $j$. A **pairwise competitive equilibrium** consists of positive prices $p_i,p_j$ and consumptions such that each household maximizes $U$ over the nonnegative bundles on its budget line ($p_iC_i+p_jC_j=p_ie^{A_i}$ for $i$, symmetrically for $j$) and both goods markets clear. The realized utility of a member with endowment exponent $A_i$ matched with a member with exponent $A_j$ is $e^{(1-\eta_c)A_i+\eta_cA_j}$ (Proposition 1).
--
--   **Purchase decision at $t=1$.** The common fundamental $A$ and the mining-cost shock $\xi$ are observed. Endowment exponents are $A_i=A+\varepsilon_i$ with $\varepsilon_i\sim N(0,\tau_\varepsilon^{-1})$. If the households that buy are those with $A_j\in B$, a buyer with exponent $a$ has expected utility
--   $$E[U_i\mid\mathcal I_i]=\int \mathbf 1_B(A+\varepsilon)\,e^{(1-\eta_c)a+\eta_c(A+\varepsilon)}\,dN(0,\tau_\varepsilon^{-1})(\varepsilon),$$
--   since trade happens only when the randomly matched partner also holds the currency. The **mass of buyers** is the $N(A,\tau_\varepsilon^{-1})$-measure of $B$.
--
--   **Miners.** Miner $i$ has productivity $\omega_i=\xi+e_i$, $e_i\sim N(0,\tau_e^{-1})$, and mines iff $(1-\rho_s)P\ge e^{-\omega_i}$; the **mass of miners** at price $P$ is the probability of this event.
--
--   **Equilibrium.** A pair $(B,P)$ is an equilibrium if $B$ is a measurable set, $P>0$, a household with exponent $a$ buys exactly when $E[U_i\mid\mathcal I_i]\ge P$ (that is, $a\in B\iff P\le E[U_i\mid\mathcal I_i](a)$), and the mass of buyers equals the mass of miners. The **high-price (low-price) equilibrium** is a cutoff equilibrium $B=[a,\infty)$ whose cutoff is the smallest (largest) among all cutoff equilibria.
--
--   **Payoffs.** The developer's revenue is $\Pi_D=\rho_s\,P\cdot(\text{mass of buyers})$ and the ex ante utility is $U_0=E\big[\max\{E[U_i\mid\mathcal I_i]-P,0\}\big]$ over $A_i\sim N(A,\tau_\varepsilon^{-1})$.
--
--   **Equation (15).** With $s=A^*-A$, the two sides of (15) are
--   $$\mathrm{LHS}(s)=e^{(1-\eta_c+\sqrt{\tau_\varepsilon/\tau_e})s}\,\Phi\big(\eta_c\tau_\varepsilon^{-1/2}-s\,\tau_\varepsilon^{1/2}\big),\qquad \mathrm{RHS}(A,\xi)=e^{-A-\xi-\frac12\eta_c^2\tau_\varepsilon^{-1}-\log(1-\rho_s)}.$$
--
--   These objects carry every statement of the mission: the equilibrium is defined from the agents' optimization and market clearing, not as a solution of (15).
--
--   **Formalization Note** Normal laws are Mathlib's `gaussianReal` with variance `(τ⁻¹).toNNReal`, which equals $\tau^{-1}$ under the standing assumptions. Expected utilities and $U_0$ are Bochner integrals; their integrands are dominated by Gaussian moment generating functions for measurable $B$, which is why measurability of $B$ is part of the equilibrium. The mining cost is $e^{-\omega_i}=e^{-(\xi+e_i)}$ as in (4); display (5) prints $e^{-\xi+e_i}$, a sign slip that leaves the mass of miners unchanged because $e_i$ is symmetric. Ties are broken as on the page: a household buys iff $E[U\mid\mathcal I_i]\ge P$, a miner mines iff $(1-\rho_s)P\ge e^{-\omega_i}$. The $t=2$ payoff `matchUtility` is the realized utility of the pairwise equilibrium, which the milestone on Proposition 1 establishes from `IsPairEquilibrium`; goods prices are taken positive.
-- source:
--   Sockin & Xiong, A Model of Cryptocurrencies, preliminary draft (March 2018), pp. 8–15 (PDF 9–16), §1 eqs. (1)–(5), §1.3 Π_D, §1.4, §2.1, Proposition 1 (U₀), and A.2 p. 33 (PDF 34) eq. (15)

import Mathlib

namespace CryptoMembership.PerfectInfo

open MeasureTheory ProbabilityTheory

/-- Parameters of the model: `eta` = η_c (Cobb–Douglas weight on the partner's good),
`tauEps` = τ_ε (precision of the idiosyncratic endowment shock ε_i), `tauE` = τ_e (precision of
the miners' idiosyncratic cost shock e_i), `rho` = ρ_s (developer's share of the ICO proceeds). -/
structure Params where
  eta : ℝ
  tauEps : ℝ
  tauE : ℝ
  rho : ℝ

/-- Standing assumptions of §1 (pp. 8–11): η_c ∈ (0,1), τ_ε > 0, τ_e > 0, 1 − ρ_s ∈ (0,1). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.eta ∧ P.eta < 1 ∧ 0 < P.tauEps ∧ 0 < P.tauE ∧ 0 < P.rho ∧ P.rho < 1

/-- Φ, the standard normal cumulative distribution function. -/
noncomputable def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- Law of the idiosyncratic endowment shock ε_i ~ N(0, τ_ε⁻¹). -/
noncomputable def epsLaw (P : Params) : Measure ℝ := gaussianReal 0 (P.tauEps⁻¹).toNNReal

/-- Cross-sectional law of the endowment exponents A_i = A + ε_i ~ N(A, τ_ε⁻¹). -/
noncomputable def endowLaw (P : Params) (A : ℝ) : Measure ℝ := gaussianReal A (P.tauEps⁻¹).toNNReal

/-- Law of the miners' idiosyncratic cost shock e_i ~ N(0, τ_e⁻¹). -/
noncomputable def minerLaw (P : Params) : Measure ℝ := gaussianReal 0 (P.tauE⁻¹).toNNReal

/-- Cobb–Douglas utility (1): U(C_i, C_j) = (C_i/(1−η_c))^{1−η_c} (C_j/η_c)^{η_c}. -/
noncomputable def U (eta Ci Cj : ℝ) : ℝ := (Ci / (1 - eta)) ^ (1 - eta) * (Cj / eta) ^ eta

/-- Competitive equilibrium of a matched pair at t = 2 (budget (2), goods-market clearing).
Household i owns e^{A_i} of good i and consumes `cii` of good i and `cij` of good j;
household j owns e^{A_j} of good j and consumes `cjj` of good j and `cji` of good i.
`pi`, `pj` are the (positive) goods prices. -/
structure IsPairEquilibrium (eta Ai Aj pi pj cii cij cjj cji : ℝ) : Prop where
  pi_pos : 0 < pi
  pj_pos : 0 < pj
  i_feasible : 0 ≤ cii ∧ 0 ≤ cij ∧ pi * cii + pj * cij = pi * Real.exp Ai
  i_optimal : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → pi * x + pj * y = pi * Real.exp Ai →
    U eta x y ≤ U eta cii cij
  j_feasible : 0 ≤ cjj ∧ 0 ≤ cji ∧ pj * cjj + pi * cji = pj * Real.exp Aj
  j_optimal : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → pj * x + pi * y = pj * Real.exp Aj →
    U eta x y ≤ U eta cjj cji
  clear_i : cii + cji = Real.exp Ai
  clear_j : cij + cjj = Real.exp Aj

/-- Realized t = 2 utility of a member with endowment exponent `Ai` matched with a member with
endowment exponent `Aj` (Proposition 1): e^{(1−η_c)A_i + η_c A_j}. -/
noncomputable def matchUtility (eta Ai Aj : ℝ) : ℝ := Real.exp ((1 - eta) * Ai + eta * Aj)

/-- E[U_i | I_i] at t = 1 for a household with endowment exponent `a` that buys, when the
households that buy are those with A_j ∈ `B`: its partner has A_j = A + ε, and trade (hence
utility) happens only if A_j ∈ B. -/
noncomputable def expUtility (P : Params) (A : ℝ) (B : Set ℝ) (a : ℝ) : ℝ :=
  ∫ ε, B.indicator (fun Aj => matchUtility P.eta a Aj) (A + ε) ∂(epsLaw P)

/-- Mass of households that buy: ∫ X_i dΦ(ε_i), the N(A, τ_ε⁻¹)-mass of the purchase set. -/
noncomputable def buyerMass (P : Params) (A : ℝ) (B : Set ℝ) : ℝ := (endowLaw P A).real B

/-- Mass of miners that mine at price `price` ((4)): miner i mines iff
(1 − ρ_s) P ≥ e^{−ω_i}, ω_i = ξ + e_i. -/
noncomputable def minerMass (P : Params) (xi price : ℝ) : ℝ :=
  (minerLaw P).real {e | Real.exp (-(xi + e)) ≤ (1 - P.rho) * price}

/-- Equilibrium of the perfect-information setting (§1.4, §2): a measurable purchase set `B`
of endowment exponents and a price `price > 0` such that households in `B` are exactly those
whose expected utility weakly exceeds the price, and the cryptocurrency market clears. -/
structure IsEquilibrium (P : Params) (A xi : ℝ) (B : Set ℝ) (price : ℝ) : Prop where
  measurableSet : MeasurableSet B
  price_pos : 0 < price
  household : ∀ a : ℝ, a ∈ B ↔ price ≤ expUtility P A B a
  clearing : buyerMass P A B = minerMass P xi price

/-- The set of all equilibria (purchase set, price) at fundamentals `A`, `xi`. -/
def equilibria (P : Params) (A xi : ℝ) : Set (Set ℝ × ℝ) :=
  {e | IsEquilibrium P A xi e.1 e.2}

/-- Developer's revenue Π_D = ρ_s P ∫ X_i dΦ(ε_i). -/
noncomputable def devRevenue (P : Params) (A : ℝ) (B : Set ℝ) (price : ℝ) : ℝ :=
  P.rho * buyerMass P A B * price

/-- Ex ante utility U₀ = E[max{E[U_i | I_i] − P, 0}], the expectation over A_i ~ N(A, τ_ε⁻¹). -/
noncomputable def exAnteUtility (P : Params) (A : ℝ) (B : Set ℝ) (price : ℝ) : ℝ :=
  ∫ x, max (expUtility P A B x - price) 0 ∂(endowLaw P A)

/-- High-price equilibrium: a cutoff equilibrium whose cutoff is the lowest among all cutoff
equilibria at (A, ξ). -/
def IsHighPriceEq (P : Params) (A xi a price : ℝ) : Prop :=
  IsEquilibrium P A xi (Set.Ici a) price ∧
    ∀ a' p' : ℝ, IsEquilibrium P A xi (Set.Ici a') p' → a ≤ a'

/-- Low-price equilibrium: a cutoff equilibrium whose cutoff is the highest among all cutoff
equilibria at (A, ξ). -/
def IsLowPriceEq (P : Params) (A xi a price : ℝ) : Prop :=
  IsEquilibrium P A xi (Set.Ici a) price ∧
    ∀ a' p' : ℝ, IsEquilibrium P A xi (Set.Ici a') p' → a' ≤ a

/-- Left-hand side of (15) as a function of s = A* − A:
e^{(1−η_c+√(τ_ε/τ_e)) s} Φ(η_c τ_ε^{−1/2} − s/τ_ε^{−1/2}). -/
noncomputable def lhs15 (P : Params) (s : ℝ) : ℝ :=
  Real.exp ((1 - P.eta + Real.sqrt (P.tauEps / P.tauE)) * s) *
    Phi (P.eta / Real.sqrt P.tauEps - Real.sqrt P.tauEps * s)

/-- Right-hand side of (15): e^{−A−ξ−½η_c²τ_ε^{−1}−log(1−ρ_s)}. -/
noncomputable def rhs15 (P : Params) (A xi : ℝ) : ℝ :=
  Real.exp (-A - xi - P.eta ^ 2 / (2 * P.tauEps) - Real.log (1 - P.rho))

end CryptoMembership.PerfectInfo


