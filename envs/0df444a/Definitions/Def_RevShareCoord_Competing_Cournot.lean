-- Prove2me | Definitions.Def_RevShareCoord_Competing_Cournot
-- name    : RevShareCoord_Competing_Cournot
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T20:39:42.975458+00:00
-- url     : https://prove2.me/theorems/29b87d4f-a373-46d1-8668-a76dc320ca89
-- title:
--   Sec. 3.2 Eq. (7), Sec. 4.1.2 — Cournot revenues R_i(q̄) = q_i(1 − q_i − βΣ_{j≠i} q_j) and the closed forms q^N, q^I, w^I
-- statement:
--   The paper's Cournot example. With a substitution parameter $\beta$ (the paper takes $0 \le \beta < 1$), the revenue at location $i$ is
--   $$R_i(\bar q) = q_i\Big(1 - q_i - \beta\sum_{j\neq i} q_j\Big). \tag{7}$$
--   For $n$ symmetric retailers, the following closed forms appear in Section 4.1.2:
--
--   1. the symmetric equilibrium quantity at a common wholesale price $w$, $\;q^N_i = \dfrac{1-w}{2+\beta(n-1)}$;
--   2. the symmetric integrated-channel quantity, $\;q^I_i = \dfrac{1-c}{2+2\beta(n-1)}$;
--   3. the coordinating wholesale price, $\;w^I = c + \dfrac{\beta(n-1)(1-c)}{2+2\beta(n-1)}$.
--
--   These are only the formulas; the theorems of the mission establish that they are the equilibrium, the integrated optimum and the coordinating price of the game.
--
--   **Formalization Note** $n$ is a natural number cast to the reals in the formulas, so $n - 1$ is real subtraction.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 12 (PDF p. 13), Section 3.2, Eq. (7); p. 19 (PDF p. 20), Section 4.1.2

import Mathlib

/-!
# The Cournot instance (7) and its closed forms (Sec. 3.2, p. 12; Sec. 4.1.2, pp. 19–20)

Cachon–Lariviere, *Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and
Limitations*, working paper (June 2000).
-/

namespace RevShareCoord.Competing

open Finset

/-- The Cournot revenue functions (7) (Sec. 3.2, p. 12):
`Rᵢ(q̄) = qᵢ (1 − qᵢ − β Σ_{j≠i} qⱼ)`, with `0 ≤ β < 1` in the paper. -/
def cournotRevenue {n : ℕ} (β : ℝ) (i : Fin n) (q : Fin n → ℝ) : ℝ :=
  q i * (1 - q i - β * ∑ j ∈ univ.erase i, q j)

/-- The symmetric equilibrium quantity `q_i^N = (1 − w)/(2 + β(n − 1))` at the common wholesale
price `w` (Sec. 4.1.2, p. 19). -/
noncomputable def cournotQN (β : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  (1 - w) / (2 + β * ((n : ℝ) - 1))

/-- The symmetric integrated-channel quantity `q_i^I = (1 − c)/(2 + 2β(n − 1))`
(Sec. 4.1.2, p. 19). -/
noncomputable def cournotQI (β : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  (1 - c) / (2 + 2 * β * ((n : ℝ) - 1))

/-- The coordinating wholesale price `w^I = c + β(n − 1)(1 − c)/(2 + 2β(n − 1))`
(Sec. 4.1.2, p. 19). -/
noncomputable def cournotWI (β : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  c + β * ((n : ℝ) - 1) * (1 - c) / (2 + 2 * β * ((n : ℝ) - 1))

end RevShareCoord.Competing


