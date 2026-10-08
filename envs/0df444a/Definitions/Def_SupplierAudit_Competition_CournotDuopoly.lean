-- Prove2me | Definitions.Def_SupplierAudit_Competition_CournotDuopoly
-- name    : SupplierAudit_Competition_CournotDuopoly
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:51.658259+00:00
-- url     : https://prove2.me/theorems/ee4340c8-2779-464e-a4be-e1db3f35f843
-- title:
--   Linear differentiated Cournot duopoly: payoffs and pure Nash equilibrium
-- statement:
--   Two firms choose quantities $q_1, q_2 \ge 0$ simultaneously. Firm $i$ has demand intercept $A_i$ and constant unit cost $c_i$, and sells at the inverse-demand price $p_i = A_i - q_i - \beta q_{i'}$, where $i' \neq i$ is the rival and $\beta$ is the substitution parameter between the two products. Firm $i$'s payoff is
--
--   $$\pi_i(q_i, q_{i'}) = (A_i - q_i - \beta q_{i'} - c_i)\, q_i .$$
--
--   A pair $(q_1, q_2)$ is a **pure Nash equilibrium** if $q_1, q_2 \ge 0$ and, for each firm $i$, $\pi_i(q_i, q_{i'}) \ge \pi_i(x, q_{i'})$ for every $x \ge 0$.
--
--   This is the generalized quantity-competition model of Dixit (1979) and Singh and Vives (1984), used for the buyers' second stage in Chen, Qi and Dawande (Sec. 3, p. 8). It is kept separate from the paper-specific model so that it can be reused by any statement about linear differentiated duopolies.
--
--   **Formalization Note** No restriction on $\beta$, $A_i$ or $c_i$ is built into the definition; the statements that use it supply them.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), Sec. 3, p. 8 (inverse demand p_i = α − q_i − βq_{i'}, resp. α − d_M − q_i − βq_{i'})

import Mathlib

namespace SupplierAudit.Competition

/-- Payoff of a firm in a linear differentiated Cournot (quantity) duopoly (Dixit 1979; Singh and
Vives 1984): a firm with demand intercept `A`, unit cost `c`, own quantity `q` facing a rival
quantity `q'` sells at the inverse-demand price `A − q − β q'` and earns `(A − q − β q' − c) q`;
`β` is the substitution parameter. -/
def cournotPayoff (β A c q q' : ℝ) : ℝ := (A - q - β * q' - c) * q

/-- Pure Nash equilibrium `(q₁, q₂)` of the linear differentiated Cournot duopoly in which firm `i`
has demand intercept `Aᵢ` and unit cost `cᵢ`: both quantities are nonnegative, and each firm's
quantity maximizes its payoff over all nonnegative quantities, given the rival's quantity. -/
def IsCournotNash (β A₁ c₁ A₂ c₂ q₁ q₂ : ℝ) : Prop :=
  0 ≤ q₁ ∧ 0 ≤ q₂ ∧
  (∀ x : ℝ, 0 ≤ x → cournotPayoff β A₁ c₁ x q₂ ≤ cournotPayoff β A₁ c₁ q₁ q₂) ∧
  (∀ x : ℝ, 0 ≤ x → cournotPayoff β A₂ c₂ x q₁ ≤ cournotPayoff β A₂ c₂ q₂ q₁)

end SupplierAudit.Competition


