-- Prove2me | Definitions.Def_RepairSched_Model_IsBellman
-- name    : RepairSched_Model_IsBellman
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:22.987321+00:00
-- url     : https://prove2.me/theorems/ad53cb79-cd57-48b2-a351-b31b0e39e14e
-- title:
--   The Bellman system (13) for $(f,B,\gamma)$
-- statement:
--   A triple $(f,B,\gamma)$ with $f\in C^2$, $B>0$, $\gamma\ge0$ solves the Bellman system if
--   $$\tfrac12\Sigma f''(w)+\theta f'(w)+\min_{q\in\mathcal A(w)}\sum_i\Big(b_i-\frac{\lambda_i}{\mu_i}f'(w)\Big)(q_i-S_i)^+=\gamma,\quad w\in[0,B],$$
--   the same expression is $\ge\gamma$ for $w>B$, and $0\le f'(w)\le c_k\mu_k$ for $w\ge0$, $f'(0)=0$, $f'(B)=c_k\mu_k$.
--
--   Here $f$ is the relative cost function, $B$ the barrier level and $\gamma$ the long-run average backorder and emergency repair cost.
--
--   **Formalization Note** $f$ is $C^2$ on all of $\mathbb R$ and the system is imposed for $w\ge0$; a $C^2$ function on $[0,\infty)$ extends to $\mathbb R$, so no solution is lost. The minimum is written out: every $q\in\mathcal A(w)$ gives at least $\gamma$, and on $[0,B]$ some $q\in\mathcal A(w)$ gives exactly $\gamma$.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), (13), p.19

import Mathlib
import Definitions.Def_RepairSched_Model
import Definitions.Def_RepairSched_Model_allocSet
import Definitions.Def_RepairSched_Model_allocCost
import Definitions.Def_RepairSched_Model_emergencyRate

namespace RepairSched

/-- **The Bellman system (13)** for the triple `(f, B, γ)`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), p.19: `f ∈ C₂`, `B ∈ ℝ₊₊`, `γ ∈ ℝ₊` with
`½Σf″(w) + θf′(w) + min_{q∈A(w)} Σᵢ (bᵢ − (λᵢ/μᵢ)f′(w))(qᵢ − Sᵢ)⁺ = γ` on `[0,B]` (13a),
`≥ γ` for `w > B` (13b), `0 ≤ f′(w) ≤ ckμk` on `ℝ₊` (13c), `f′(0) = 0` and `f′(B) = ckμk` (13d).

**Formalization Note.** `f : ℝ → ℝ` is `C²` on all of `ℝ` and (13) is imposed only for `w ≥ 0`;
a `C²` function on `[0,∞)` extends to `ℝ`, so no solution is lost. The inner minimum is written
out: in (13a) every `q ∈ A(w)` has value at least `γ` and some `q ∈ A(w)` has value exactly `γ`;
in (13b) every `q ∈ A(w)` has value at least `γ`. -/
def Model.IsBellman {n : ℕ} [NeZero n] (M : Model n) (S : Fin n → ℝ) (f : ℝ → ℝ) (B γ : ℝ) :
    Prop :=
  ContDiff ℝ 2 f ∧ 0 < B ∧ 0 ≤ γ ∧
    (∀ w, 0 ≤ w → w ≤ B →
      (∀ q ∈ M.allocSet w, γ ≤ 1 / 2 * M.Sigma * deriv (deriv f) w + M.theta * deriv f w +
        M.allocCost S (deriv f w) q) ∧
      ∃ q ∈ M.allocSet w, 1 / 2 * M.Sigma * deriv (deriv f) w + M.theta * deriv f w +
        M.allocCost S (deriv f w) q = γ) ∧
    (∀ w, B < w → ∀ q ∈ M.allocSet w, γ ≤ 1 / 2 * M.Sigma * deriv (deriv f) w +
      M.theta * deriv f w + M.allocCost S (deriv f w) q) ∧
    (∀ w, 0 ≤ w → 0 ≤ deriv f w ∧ deriv f w ≤ M.emergencyRate) ∧
    deriv f 0 = 0 ∧ deriv f B = M.emergencyRate

end RepairSched


