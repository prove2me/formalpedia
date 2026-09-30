-- Prove2me | Definitions.Def_InventoryControl_clarkScarf
-- name    : InventoryControl_clarkScarf
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T00:16:21.722687+00:00
-- url     : https://prove2.me/theorems/b610da6c-2ef5-4808-af8a-1a5660760ebd
-- title:
--   The two-level serial system of the Clark-Scarf model: period costs, their reallocation, and the total cost $\hat C_2(y_2)$ of Sect. 10.1.1
-- statement:
--   The two-echelon serial system of Axsäter, *Inventory Control*, Sect. 10.1.1, in the
--   infinite-horizon periodic-review form of Federgruen and Zipkin. Installation 1 faces the
--   customer demand and replenishes from installation 2, which replenishes from an outside
--   supplier with infinite supply. Period demands are independent and normally distributed with
--   mean $\mu$ and standard deviation $\sigma$, so the demand over $n$ periods, $D(n)$, is normal
--   with mean $n\mu$ and standard deviation $\sqrt n\,\sigma$: this is `csDemand mu sigma n`, the
--   same Gaussian law as the newsboy model's `newsboyDemand`. Lead-times $L_1, L_2$ are integral
--   numbers of periods; unmet demand is backordered; there are echelon holding costs $e_1, e_2 \ge 0$
--   per unit and period, so that the installation holding costs are $h_1 = e_1 + e_2$ and
--   $h_2 = e_2$, and a shortage cost $b_1$ per unit and period; there are no ordering costs.
--
--   In an arbitrary period $t$, $y_2$ is the echelon inventory position of installation 2 after
--   ordering, and $y_1$ is the realized echelon inventory position of installation 1 after its
--   order in period $t + L_2$, which cannot exceed the echelon stock $y_2 - D(L_2)$ then
--   available (Eq. 10.1). Writing $\mu_2' = L_2\mu$ and $\mu_1'' = (L_1+1)\mu$,
--
--   * `csPeriodCost e1 e2 b1 mu sigma L1 L2 y2 y1` is the sum of the period costs (10.2) and (10.3),
--     $h_2\,\mathbb{E}(y_2 - D(L_2) - y_1) + h_1\,\mathbb{E}(y_1 - D(L_1+1))^{+} + b_1\,\mathbb{E}(y_1 - D(L_1+1))^{-}$;
--   * `csStage2Cost e2 mu L2 y2` is the reallocated cost $\tilde C_2 = h_2(y_2 - \mu_2')$ of Eq. (10.4);
--   * `csStage1Cost e1 e2 b1 mu sigma L1 y1` is the reallocated cost
--     $\tilde C_1 = e_1y_1 - h_1\mu_1'' + (h_1 + b_1)\,\mathbb{E}(y_1 - D(L_1+1))^{-}$ of Eq. (10.5),
--     which is also the function $\hat C_1(\hat y_1)$ of Eq. (10.6) when $\hat y_1$ is free;
--   * `csTotalCost e1 e2 b1 mu sigma L1 L2 S1 y2` is the total expected cost $\hat C_2(y_2)$ of
--     Eq. (10.9) when installation 1 uses the echelon order-up-to level $S_1$:
--     $$ \hat C_2(y_2) \;=\; h_2(y_2 - \mu_2') + \hat C_1(S_1) + \int_{y_2 - S_1}^{\infty}\big[\hat C_1(y_2 - u) - \hat C_1(S_1)\big]\,\frac{1}{\sigma_2'}\varphi\!\Big(\frac{u - \mu_2'}{\sigma_2'}\Big)\mathrm{d}u, $$
--     the integral being taken against the law of $D(L_2)$.
--
--   **Formalization Note** The costs are parametrized by the echelon costs $e_1, e_2$, and
--   $h_1 = e_1 + e_2$, $h_2 = e_2$ are written out, so the relation between the two cost systems
--   is built in rather than assumed. All expectations are Bochner integrals against the Gaussian
--   laws; integrability holds because the integrands grow at most linearly, and the arbitrary
--   allocation rules of the main theorem carry an explicit integrability hypothesis. $L_2 = 0$ is
--   allowed, in which case $D(L_2)$ is the point mass at $0$. The order-up-to level $S_1$ is a
--   parameter of $\hat C_2$; the theorems fix it by the fractile condition (10.8).
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, Sect. 10.1.1 pp. 192-196: the model and notation pp. 193-194, Eq. (10.1)-(10.5) pp. 194-195, Eq. (10.9) p. 196

import Definitions.Def_InventoryControl_newsboy

open MeasureTheory ProbabilityTheory

namespace InventoryControl

/-- `D(n)`: the demand over `n` periods, normal with mean `n μ` and standard deviation `√n σ`.
Axsäter, *Inventory Control*, Sect. 10.1.1 p. 194. -/
noncomputable def csDemand (mu sigma : ℝ) (n : ℕ) : Measure ℝ :=
  newsboyDemand (n * mu) (Real.sqrt n * sigma)

/-- Eq. (10.4): the reallocated cost at installation 2, `h₂ (y₂ − μ'₂)` with `h₂ = e₂`. -/
noncomputable def csStage2Cost (e2 mu : ℝ) (L2 : ℕ) (y2 : ℝ) : ℝ := e2 * (y2 - L2 * mu)

/-- Eq. (10.5) and (10.6): the reallocated cost at installation 1,
`e₁ y₁ − h₁ μ''₁ + (h₁ + b₁) E((y₁ − D(L₁+1))⁻)` with `h₁ = e₁ + e₂`. -/
noncomputable def csStage1Cost (e1 e2 b1 mu sigma : ℝ) (L1 : ℕ) (y1 : ℝ) : ℝ :=
  e1 * y1 - (e1 + e2) * ((L1 + 1) * mu)
    + (e1 + e2 + b1) * ∫ x, max (x - y1) 0 ∂(csDemand mu sigma (L1 + 1))

/-- Eq. (10.2) + (10.3): the period costs before reallocation,
`h₂ E(y₂ − D(L₂) − y₁) + h₁ E((y₁ − D(L₁+1))⁺) + b₁ E((y₁ − D(L₁+1))⁻)`. -/
noncomputable def csPeriodCost (e1 e2 b1 mu sigma : ℝ) (L1 L2 : ℕ) (y2 y1 : ℝ) : ℝ :=
  e2 * ((y2 - L2 * mu) - y1)
    + (e1 + e2) * ∫ x, max (y1 - x) 0 ∂(csDemand mu sigma (L1 + 1))
    + b1 * ∫ x, max (x - y1) 0 ∂(csDemand mu sigma (L1 + 1))

/-- Eq. (10.9): the total expected cost `Ĉ₂(y₂)` when installation 1 orders up to `S₁`. -/
noncomputable def csTotalCost (e1 e2 b1 mu sigma : ℝ) (L1 L2 : ℕ) (S1 y2 : ℝ) : ℝ :=
  csStage2Cost e2 mu L2 y2 + csStage1Cost e1 e2 b1 mu sigma L1 S1
    + ∫ u in Set.Ioi (y2 - S1),
        (csStage1Cost e1 e2 b1 mu sigma L1 (y2 - u) - csStage1Cost e1 e2 b1 mu sigma L1 S1)
          ∂(csDemand mu sigma L2)

end InventoryControl


