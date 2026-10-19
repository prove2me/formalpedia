-- Prove2me | Definitions.Def_MultiRegCournot_Equilibrium_Model
-- name    : MultiRegCournot_Equilibrium_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:30.525984+00:00
-- url     : https://prove2.me/theorems/4ca992e2-1f5c-4417-990f-60e8c5550e20
-- title:
--   §3, Definition 3.1, (1), (2), Proposition 4.2, pp. 7–11, 35 — multiregional Cournot model
-- statement:
--   A market has N firms and R regions. Firm i chooses nonnegative sales qⁱᵣ with total production at most κⁱ. Region r has inverse demand pᵣ, firm i pays unit production cost aⁱ and unit transport cost tⁱᵣ, and its profit is
--
--   $$\pi^i(Q)=\sum_r(p_r(q_r^{tot})-t_r^i)q_r^i-a^i q_{tot}^i.$$
--
--   A Nash equilibrium is a feasible profile with no profitable feasible unilateral deviation. The definition also gives marginal profit gⁱᵣ, complementarity condition (2), the unique allocation Q̂(ρ) satisfying it when one exists, reservation prices wᵣ, the vector box [0,w̄]ᴺ, and the operator Φ defined by the output-capacity inverse.
--
--   **Formalization Note** The Lean model uses firms and regions indexed from zero, firm-first allocations, a C² inverse demand on ℝ that is decreasing and concave for nonnegative quantities, nonnegative reservation prices, positive capacities, and nonnegative production and transport costs. Q̂ returns zero when the unique allocation does not exist; all theorem uses of Q̂ are on the box, where Proposition 4.2 establishes uniqueness. Φ uses the infimum of the inverse image; its existence is part of the mathematical development.
-- source:
--   Alsabah, Bernard, Capponi, Iyengar & Sethuraman, Multiregional oligopoly with capacity constraints, SSRN 3280688 (version of June 6, 2020), pp. 7–11, 35, §3, Assumptions 1–2, Definition 3.1, (1), (2), Proposition 4.2, Φ, Appendix C display

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_PureGame

namespace MultiRegCournot.Equilibrium

/-- The data of the multiregional Cournot market in §3. -/
structure Market (N R : ℕ) where
  p : Fin R → ℝ → ℝ
  ac : Fin N → ℝ
  tc : Fin N → Fin R → ℝ
  kap : Fin N → ℝ

/-- The regularity and sign conventions used throughout §4. -/
def Market.Standing {N R : ℕ} (M : Market N R) : Prop :=
  (∀ r, ContDiff ℝ 2 (M.p r) ∧
    StrictAntiOn (M.p r) (Set.Ici 0) ∧
    ConcaveOn ℝ (Set.Ici 0) (M.p r) ∧
    0 ≤ M.p r 0) ∧
  (∀ i, 0 ≤ M.ac i ∧ 0 < M.kap i) ∧
  (∀ i r, 0 ≤ M.tc i r)

/-- Total quantity sold in a region. -/
def qTotRegion {N R : ℕ} (Q : Fin N → Fin R → ℝ) (r : Fin R) : ℝ :=
  ∑ i, Q i r

/-- Total production of a firm. -/
def qTotFirm {N R : ℕ} (Q : Fin N → Fin R → ℝ) (i : Fin N) : ℝ :=
  ∑ r, Q i r

/-- Profit in §3, p. 7. -/
def Market.profit {N R : ℕ} (M : Market N R)
    (Q : Fin N → Fin R → ℝ) (i : Fin N) : ℝ :=
  (∑ r, (M.p r (qTotRegion Q r) - M.tc i r) * Q i r) -
    M.ac i * qTotFirm Q i

/-- A firm strategy in Definition 3.1. -/
def Market.feasible {N R : ℕ} (M : Market N R) (i : Fin N) : Set (Fin R → ℝ) :=
  {q | (∀ r, 0 ≤ q r) ∧ (∑ r, q r) ≤ M.kap i}

/-- Pure Nash equilibrium of Definition 3.1. -/
def Market.IsEquilibrium {N R : ℕ} (M : Market N R)
    (Q : Fin N → Fin R → ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash M.feasible (fun i Q' => M.profit Q' i) Q

/-- Marginal profit (1). -/
noncomputable def Market.margProfit {N R : ℕ} (M : Market N R)
    (Q : Fin N → Fin R → ℝ) (i : Fin N) (r : Fin R) : ℝ :=
  deriv (M.p r) (qTotRegion Q r) * Q i r +
    M.p r (qTotRegion Q r) - M.tc i r - M.ac i

/-- Complementarity condition (2). -/
def Market.Cond2 {N R : ℕ} (M : Market N R)
    (Q : Fin N → Fin R → ℝ) (i : Fin N) (rhoi : ℝ) : Prop :=
  ∀ r, M.margProfit Q i r ≤ rhoi ∧
    Q i r * (M.margProfit Q i r - rhoi) = 0

/-- The unique allocation satisfying (2), where it exists. -/
noncomputable def Market.Qhat {N R : ℕ} (M : Market N R)
    (rho : Fin N → ℝ) : Fin N → Fin R → ℝ := by
  classical
  exact if h : ∃! Q : Fin N → Fin R → ℝ,
      (∀ i r, 0 ≤ Q i r) ∧ ∀ i, M.Cond2 Q i (rho i)
  then h.exists.choose else 0

/-- Reservation price w_r. -/
def Market.w {N R : ℕ} (M : Market N R) (r : Fin R) : ℝ := M.p r 0

/-- Maximum reservation price, with the empty-region supremum equal to zero. -/
noncomputable def Market.wbar {N R : ℕ} (M : Market N R) : ℝ :=
  ⨆ r, M.w r

/-- The vector box [0, wbar]^N. -/
noncomputable def Market.box {N R : ℕ} (M : Market N R) : Set (Fin N → ℝ) :=
  Set.Icc 0 (fun _ => M.wbar)

/-- Best-response operator Φ of §4.2, p. 11. -/
noncomputable def Market.Phi {N R : ℕ} (M : Market N R)
    (rho : Fin N → ℝ) : Fin N → ℝ :=
  fun i =>
    if qTotFirm (M.Qhat (Function.update rho i 0)) i < M.kap i then 0
    else sInf {x : ℝ | x ∈ Set.Icc 0 M.wbar ∧
      qTotFirm (M.Qhat (Function.update rho i x)) i = M.kap i}

end MultiRegCournot.Equilibrium


