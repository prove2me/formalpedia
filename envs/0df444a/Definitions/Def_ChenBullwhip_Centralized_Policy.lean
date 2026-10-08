-- Prove2me | Definitions.Def_ChenBullwhip_Centralized_Policy
-- name    : ChenBullwhip_Centralized_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:16:36.64001+00:00
-- url     : https://prove2.me/theorems/bcc95cfe-cd59-4d3d-b604-a14c2cf64b40
-- title:
--   Moving-average estimators, the order-up-to point and the retailer's order, Eqs. (2)–(3) and §2.2
-- statement:
--   Fix an AR(1) demand process $(D_t)_{t\in\mathbb Z}$, a window length $p \in \mathbb N$, a lead-time parameter $L \in \mathbb N$, a safety factor $z \in \mathbb R$ and a real constant $C$ (the paper's $C_{L,\rho}$). The retailer's moving-average quantities in period $t$ are:
--
--   1. the estimate of the mean lead-time demand
--   $$\hat D^L_t = L\left(\frac{\sum_{i=1}^p D_{t-i}}{p}\right);$$
--   2. the one-period forecast error $e_t = D_t - \hat D^1_t$;
--   3. the estimate of the standard deviation of the $L$-period forecast error
--   $$\hat\sigma^L_{et} = C_{L,\rho}\sqrt{\frac{\sum_{i=1}^p (e_{t-i})^2}{p}}; \tag{3}$$
--   4. the order-up-to point $y_t = \hat D^L_t + z\,\hat\sigma^L_{et}$ (Eq. (2));
--   5. the order placed in period $t$,
--   $$q_t = y_t - y_{t-1} + D_{t-1}.$$
--
--   The order $q_t$ may be negative; as in the paper, excess inventory is returned without cost, so $q_t$ is used as it is, never truncated at $0$. All five quantities are functions of the demand path, defined for every outcome.
--
--   These are the objects of Lemma 2.1 and Theorem 2.2; the stage orders of the multistage chain are built from the same functions.
--
--   **Formalization Note** The paper leaves $C_{L,\rho}$ unspecified ("a constant function of $L$, $\rho$ and $p$", referring to Ryan 1997); it is a free real parameter $C$, and every result of the mission holds for each value. The sums $\sum_{i=1}^p$ run over $i \in \{1,\dots,p\}$ (`Finset.Icc 1 p`), and $L/p$ is real division. Results using these quantities assume $p \ge 1$.
-- source:
--   Chen, Drezner, Ryan and Simchi-Levi, Quantifying the Bullwhip Effect in a Simple Supply Chain, Management Science 46 (2000), p. 437, Eqs. (2), (3) and the definition of q_t in §2.2

import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand

open MeasureTheory ProbabilityTheory

namespace ChenBullwhip.Centralized

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- p. 437, the display before Eq. (3): the moving-average estimate of the mean lead-time demand,
`D̂ᴸₜ = L (∑_{i=1}^p D_{t-i}) / p`. -/
noncomputable def AR1Demand.Dhat (X : AR1Demand P) (L p : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  (L : ℝ) * ((∑ i ∈ Finset.Icc 1 p, X.D (t - i) ω) / p)

/-- p. 437, below Eq. (3): the one-period forecast error `eₜ = Dₜ - D̂¹ₜ`. -/
noncomputable def AR1Demand.err (X : AR1Demand P) (p : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  X.D t ω - X.Dhat 1 p t ω

/-- p. 437, Eq. (3): `σ̂ᴸₑₜ = C_{L,ρ} √(∑_{i=1}^p (e_{t-i})² / p)`. The paper leaves the constant
`C_{L,ρ}` unspecified ("a constant function of `L`, `ρ` and `p`"); it is the free real `C`. -/
noncomputable def AR1Demand.sigmaHat (X : AR1Demand P) (C : ℝ) (p : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  C * Real.sqrt ((∑ i ∈ Finset.Icc 1 p, (X.err p (t - i) ω) ^ 2) / p)

/-- p. 437, Eq. (2): the order-up-to point `yₜ = D̂ᴸₜ + z σ̂ᴸₑₜ`. -/
noncomputable def AR1Demand.orderUpTo (X : AR1Demand P) (C z : ℝ) (L p : ℕ) (t : ℤ) (ω : Ω) :
    ℝ :=
  X.Dhat L p t ω + z * X.sigmaHat C p t ω

/-- p. 437, §2.2: the (signed) order `qₜ = yₜ - y_{t-1} + D_{t-1}`. -/
noncomputable def AR1Demand.order (X : AR1Demand P) (C z : ℝ) (L p : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  X.orderUpTo C z L p t ω - X.orderUpTo C z L p (t - 1) ω + X.D (t - 1) ω

end ChenBullwhip.Centralized


