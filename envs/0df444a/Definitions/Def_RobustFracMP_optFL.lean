-- Prove2me | Definitions.Def_RobustFracMP_optFL
-- name    : RobustFracMP_optFL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:59:12.546107+00:00
-- url     : https://prove2.me/theorems/8c90df59-1a6f-4145-8e9f-414e69c25886
-- title:
--   Optimal fractional value $\widehat{\mathrm{OPT}}^{\mathrm{fl}}_z(\lambda)$ of Power-$z$ Facility Location
-- statement:
--   Let $(P,\mathrm{dist})$ be a finite metric space, $z\ge1$ and $\lambda>0$ an opening cost. In Power-$z$ Facility Location with facilities chosen from the data ($F=P$) one seeks a fractional solution $y\in\mathbb R^P_{\ge0}$ with $\|y\|_1\ge1$ minimizing $\lambda\|y\|_1+\mathrm{cost}_z(y)$. The optimal value is
--
--   $$\widehat{\mathrm{OPT}}^{\mathrm{fl}}_z(\lambda)=\min_{y\in\mathbb R^P_{\ge0}:\ \|y\|_1\ge1}\ \lambda\cdot\|y\|_1+\mathrm{cost}_z(y).$$
--
--   It is the benchmark of the LMP (Lagrangian multiplier preserving) inequality $\mathrm{cost}_z(y)\le\alpha\,(\widehat{\mathrm{OPT}}^{\mathrm{fl}}_z(\lambda)-\lambda\|y\|_1)$.
--
--   **Formalization Note** $\|y\|_1$ is written $\sum_p y_p$, which is the $\ell_1$ norm for $y\ge0$. The minimum is an infimum; for nonempty $P$ the set is nonempty (open one point) and bounded below by $0$, and the value is attained (it is the optimum of the linear program $\mathrm{LP}^{\mathrm{fl}}_\lambda$ on p.20). For empty $P$ the Lean value is the junk $0$; all theorems of the mission assume $P$ nonempty.
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Section 3, Power-z Facility Location, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_RobustFracMP_fracCost

set_option autoImplicit false

namespace RobustFracMP

/-- **Optimal fractional value of Power-z Facility Location, \widehat{OPT}^{fl}_z(λ).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering:
Constant Approximation in Constant Rounds*, arXiv:2604.00954 (version of November 3, 2026;
manuscript sha256 c65896fe6f32051527c00d1bcd269746784374658ddefb707cff5f35bd3551d8), Section 3, "Power-z Facility Location", p.11 (PDF p.13): with `P = F` and opening cost
`λ > 0`, "\widehat{OPT}^{fl}_z(P, λ) := min_{y∈ℝ^P_{≥0}: ‖y‖₁≥1} λ · ‖y‖₁ + cost_z(P, y)".

**Formalization Note.** `‖y‖₁` is written `∑ p, y p`, which equals the ℓ₁ norm for `y ≥ 0`. The
minimum is `sInf`; for `λ ≥ 0` the set is bounded below by `0`, and for nonempty `P` it is nonempty
(the indicator of one point). The value is attained (it is the optimum of the linear program
`LP^fl_λ`, p.20), so `sInf` is the paper's `min`. For empty `P` the set is empty and the value is the
junk `0`; the theorems of the mission assume `Nonempty P`. `P` is an explicit argument. -/
noncomputable def optFL (P : Type*) [Fintype P] [MetricSpace P] (z : ℕ) (lam : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ y : P → ℝ, (∀ p, 0 ≤ y p) ∧ 1 ≤ ∑ p, y p ∧ v = lam * ∑ p, y p + fracCost z y}

end RobustFracMP


