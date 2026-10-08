-- Prove2me | Definitions.Def_MitigateSupplyRisk_DualSourcing_Regions
-- name    : MitigateSupplyRisk_DualSourcing_Regions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:53.123504+00:00
-- url     : https://prove2.me/theorems/a6eb26cf-bbdb-4dea-b2ff-7b854d885473
-- title:
--   Theorem 2, pp. 494–495 — generalized inverse G_i^{-1}, the demand regions Ω₁ and Ω₃ ∪ Ω₄ ∪ Ω₅, and the optimal total order q₁* + q₂*
-- statement:
--   This file defines the quantities in which Theorem 2 of Wang, Gilland and Tomlin (2010) describes the optimal dual-sourcing orders under deterministic demand.
--
--   1. The **generalized inverse** of supplier $i$'s capacity-loss distribution at reliability index $a$ is
--   $$G_i^{-1}(u) = \inf\{t \ge 0 : G_i(t, a) \ge u\}.$$
--   When $G_i(\cdot, a)$ is continuous and strictly increasing on its support $[0, b_i]$ with $G_i(b_i, a) = 1$, this is the ordinary inverse on $(0, 1]$.
--   2. With reliability indices $a = (a_1, a_2)$, write $A_1 = G_1^{-1}(\phi_2)$, $A_2 = G_2^{-1}(\phi_1)$, $B = G_1^{-1}\big(\tfrac{\phi_2}{\phi_1} G_2(K_2)\big)$ and $S = K_1 + K_2$.
--   3. The **single-sourcing region** is $\Omega_1 = \{x : 0 \le x \le K_1 - B\}$.
--   4. The **quantity-hedge region** is $\Omega_3 \cup \Omega_4 \cup \Omega_5 = \{x : S - (A_1 + A_2) < x \le S\}$.
--   5. The **optimal total order** $q_1^* + q_2^*$ as a function of demand $x$, read off Theorem 2's table with the corrected bounds:
--   $$q_1^* + q_2^* = \begin{cases} x, & x \le S - (A_1 + A_2) \ (\Omega_1 \cup \Omega_2),\\ 2x - S + A_1 + A_2, & x \le S - \max(A_1, A_2) \ (\Omega_3),\\ x + \min(A_1, A_2), & x \le S - \min(A_1, A_2) \ (\Omega_4),\\ S, & \text{otherwise} \ (\Omega_5 \cup \Omega_6). \end{cases}$$
--   In $\Omega_4$ the table gives $(x - (K_2 - A_2), K_2)$ if $A_1 \ge A_2$ and $(K_1, x - (K_1 - A_1))$ otherwise; both sum to $x + \min(A_1, A_2)$.
--
--   The quantity $[q_1^* + q_2^* - x]^+$ is the **quantity hedge**: the amount the firm over-orders beyond demand. Corollary 1 is a statement about these regions and this hedge.
--
--   **Formalization Note.** The printed Theorem 2 swaps $\min$ and $\max$ in the bounds of $\Omega_3, \Omega_4, \Omega_5$; the definitions here use the corrected bounds (see Theorem 2's item). The union $\Omega_3 \cup \Omega_4 \cup \Omega_5$ is the same under either version. The generalized inverse is a function of the model, so no inverse value is a free variable; it is an infimum of a set bounded below by $0$, nonempty whenever $u \le G_i(K_i, a)$.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), pp. 494–495 (PDF pp. 6–7), Theorem 2 and Figure 1; p. 496 (PDF p. 8), Corollary 1

import Mathlib
import Definitions.Def_MitigateSupplyRisk_DualSourcing_Model

namespace MitigateSupplyRisk.DualSourcing

namespace Model

/-- Generalized inverse `G_i^{-1}(u)` of the capacity-loss distribution at reliability index `a`:
the least `t ≥ 0` with `G_i(t, a) ≥ u`. When `G_i(·, a)` is continuous and strictly increasing on
its support `[0, b_i]` with `G_i(b_i, a) = 1`, this is the ordinary inverse on `(0, 1]`. -/
noncomputable def Ginv (M : Model) (i : Fin 2) (a u : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ u ≤ M.G i t a}

/-- `A₁ = G₁^{-1}(φ₂)` at the reliability indices `a` (Theorem 2). -/
noncomputable def A1 (M : Model) (a : Fin 2 → ℝ) : ℝ := M.Ginv 0 (a 0) (M.phi 1)

/-- `A₂ = G₂^{-1}(φ₁)` at the reliability indices `a` (Theorem 2). -/
noncomputable def A2 (M : Model) (a : Fin 2 → ℝ) : ℝ := M.Ginv 1 (a 1) (M.phi 0)

/-- `B = G₁^{-1}((φ₂/φ₁) G₂(K₂))` at the reliability indices `a`, the quantity in the upper end
`K₁ − B` of the single-sourcing region `Ω₁` of Theorem 2, in its printed form. -/
noncomputable def B (M : Model) (a : Fin 2 → ℝ) : ℝ :=
  M.Ginv 0 (a 0) (M.phi 1 / M.phi 0 * M.G 1 (M.K 1) (a 1))

/-- The single-sourcing region `Ω₁ = {x : 0 ≤ x ≤ K₁ − G₁^{-1}((φ₂/φ₁) G₂(K₂))}` of Theorem 2. -/
noncomputable def singleRegion (M : Model) (a : Fin 2 → ℝ) : Set ℝ :=
  Set.Icc 0 (M.K 0 - M.B a)

/-- The quantity-hedge region `Ω₃ ∪ Ω₄ ∪ Ω₅ = {x : K₁ + K₂ − (G₁^{-1}(φ₂) + G₂^{-1}(φ₁)) < x ≤ K₁ + K₂}`
of Theorem 2 (the union is the same under the printed and the corrected bounds of `Ω₃, Ω₄, Ω₅`). -/
noncomputable def hedgeRegion (M : Model) (a : Fin 2 → ℝ) : Set ℝ :=
  Set.Ioc (M.K 0 + M.K 1 - (M.A1 a + M.A2 a)) (M.K 0 + M.K 1)

/-- Total order quantity `q₁* + q₂*` of the optimal vector of Theorem 2 (deterministic demand `x`,
`η = 0`), read off its region table with the corrected region bounds. With
`A₁ = G₁^{-1}(φ₂)`, `A₂ = G₂^{-1}(φ₁)` and `S = K₁ + K₂`:
`x` on `Ω₁ ∪ Ω₂` (`x ≤ S − (A₁ + A₂)`), where `q₁* + q₂* = x`;
`Ω₃` (up to `S − max(A₁, A₂)`), where `q* = (x − (K₂ − A₂), x − (K₁ − A₁))`;
`Ω₄` (up to `S − min(A₁, A₂)`), where `q* = (x − (K₂ − A₂), K₂)` if `A₁ ≥ A₂` and
`q* = (K₁, x − (K₁ − A₁))` otherwise; and `Ω₅ ∪ Ω₆`, where `q* = (K₁, K₂)`. -/
noncomputable def qstarTotal (M : Model) (a : Fin 2 → ℝ) (x : ℝ) : ℝ :=
  let A₁ := M.A1 a
  let A₂ := M.A2 a
  let S := M.K 0 + M.K 1
  if x ≤ S - (A₁ + A₂) then x
  else if x ≤ S - max A₁ A₂ then (x - (M.K 1 - A₂)) + (x - (M.K 0 - A₁))
  else if x ≤ S - min A₁ A₂ then
    (if A₂ ≤ A₁ then (x - (M.K 1 - A₂)) + M.K 1 else M.K 0 + (x - (M.K 0 - A₁)))
  else S

end Model

end MitigateSupplyRisk.DualSourcing


