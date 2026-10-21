-- Prove2me | Definitions.Def_ExtrapBias_Beliefs_Model
-- name    : ExtrapBias_Beliefs_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:21.868249+00:00
-- url     : https://prove2.me/theorems/7033a7d1-28c9-45b6-8d0d-1361408a1c89
-- title:
--   §2, (18), (25)–(31), (36)–(38), §4.1 — scaled liquidity model and worst-case beliefs
-- statement:
--   Let a firm have size δ and cash M, with cash per unit of size m=M/δ. Investment i costs g(i)=i+θi²/2 per unit of size. Permanent and temporary Brownian shocks have volatilities σδ and σY. A manager who distrusts the reference model considers drift distortions (hᴾ,hᵀ) in the ellipse
--   $$
--   (h^{P}/\kappa_P)^2+(h^{T}/\kappa_T)^2\leq 1.
--   $$
--   The definitions give both HJB expressions, the ambiguity-only benchmark qᴬ, the increasing concave scaled value function F solving the attained variational system (25)–(31), the optimizing angle and investment in (26), the worst-case distortions in (27), and their four shock sensitivities from §4.1.
--
--   The shared definitions let the milestone theorems and the extrapolation-bias target refer to exactly the same cash-management model.
--
--   **Formalization Note** The scaled F is a global C² real function restricted to nonnegative cash. The angle in (25) ranges over the closed interval [0,2π]. The HJB and cash-boundary extrema are expressed through attainment rather than a real supremum or infimum. Strict positivity of κP, κT, σY, ω, and qᴬ selects the nondegenerate parameter regime; (38) corrects the stray δ in (16).
-- source:
--   Lee & Rivera, Extrapolation Bias and Dynamic Liquidity Management, working paper (May 24, 2019), pp. 6–21, 39–40, §2, (8), (11)–(13), (18), (25)–(31), (36)–(38), §4.1 sensitivity display

import Mathlib

noncomputable section

namespace ExtrapBias.Beliefs

/-- Parameters of §2; the strictly positive ambiguity radii, temporary volatility,
and liquidation fraction select the nondegenerate §4 regime. -/
structure Params where
  r : ℝ
  mu : ℝ
  alpha : ℝ
  lam : ℝ
  sigD : ℝ
  sigY : ℝ
  theta : ℝ
  kapP : ℝ
  kapT : ℝ
  omega : ℝ
  rho0 : ℝ
  rho1 : ℝ
  r_pos : 0 < r
  lam_pos : 0 < lam
  lam_le_r : lam ≤ r
  sigD_pos : 0 < sigD
  sigY_pos : 0 < sigY
  theta_pos : 0 < theta
  kapP_pos : 0 < kapP
  kapT_pos : 0 < kapT
  omega_pos : 0 < omega
  omega_le_one : omega ≤ 1
  rho0_nonneg : 0 ≤ rho0
  rho1_gt_one : 1 < rho1

/-- Investment expenditure per unit of firm size, §2.1, p. 7. -/
def g (p : Params) (i : ℝ) : ℝ := i + p.theta * i ^ 2 / 2

/-- The HJB expression in (18), with partial derivatives passed as values. -/
def bracket18 (p : Params) (Vd VM Vdd VMM δ M i φ : ℝ) : ℝ :=
  Vd * δ * (p.mu + i - p.sigD * p.kapP * Real.cos φ) +
  VM * (δ * (p.alpha - g p i - p.sigY * p.kapT * Real.sin φ) +
    (p.r - p.lam) * M) +
  Vdd * p.sigD ^ 2 * δ ^ 2 / 2 + VMM * p.sigY ^ 2 * δ ^ 2 / 2

/-- The scaled HJB expression in (25); F0, F1 and F2 are F(m), F′(m), F″(m). -/
def bracket25 (p : Params) (F0 F1 F2 m i φ : ℝ) : ℝ :=
  (F0 - F1 * m) * (p.mu + i - p.sigD * p.kapP * Real.cos φ) +
  F1 * (p.alpha - g p i - p.sigY * p.kapT * Real.sin φ +
    (p.r - p.lam) * m) +
  F2 * (p.sigY ^ 2 + m ^ 2 * p.sigD ^ 2) / 2

/-- The filled ambiguity ellipse of (8), with γ = 2 from §2.3. -/
def ellipseH (p : Params) : Set (ℝ × ℝ) :=
  {h | (h.1 / p.kapP) ^ 2 + (h.2 / p.kapT) ^ 2 ≤ 1}

/-- Lemma 4's h-form, corrected with the volatility factors of (11)–(12). -/
def bracketH (p : Params) (F0 F1 F2 m i : ℝ) (h : ℝ × ℝ) : ℝ :=
  (F0 - F1 * m) * (p.mu + i + p.sigD * h.1) +
  F1 * (p.alpha - g p i + p.sigY * h.2 + (p.r - p.lam) * m) +
  F2 * (p.sigY ^ 2 + m ^ 2 * p.sigD ^ 2) / 2

/-- The ambiguity benchmark of Proposition 2, with (36)–(38) and transversality. -/
def IsAmbBenchmark (p : Params) (qA iA φA : ℝ) : Prop :=
  0 < qA ∧
  qA = 1 + p.theta * iA ∧
  φA = Real.arctan (p.sigY * p.kapT / (qA * p.sigD * p.kapP)) ∧
  p.r * qA = p.alpha - g p iA - p.sigY * p.kapT * Real.sin φA +
    qA * (p.mu + iA - p.kapP * p.sigD * Real.cos φA) ∧
  0 < p.r - p.mu - iA

/-- The increasing concave C² solution of (25)–(31) assumed in Lemma 7.
The extrema in (25) and (29) are represented as attained. -/
def IsScaledValue (p : Params) (qA mstar : ℝ) (F : ℝ → ℝ) : Prop :=
  0 < mstar ∧
  ContDiff ℝ 2 F ∧
  MonotoneOn F (Set.Ici 0) ∧
  ConcaveOn ℝ (Set.Ici 0) F ∧
  (∀ m ∈ Set.Icc 0 mstar,
    (∃ i : ℝ, ∀ φ ∈ Set.Icc 0 (2 * Real.pi),
      p.r * F m ≤ bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m i φ) ∧
    (∀ i : ℝ, ∃ φ ∈ Set.Icc 0 (2 * Real.pi),
      bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m i φ ≤ p.r * F m)) ∧
  deriv F mstar = 1 ∧
  deriv (deriv F) mstar = 0 ∧
  p.omega * qA ≤ F 0 ∧
  (∀ m : ℝ, 0 ≤ m → F m - p.rho1 * (m + p.rho0) ≤ F 0) ∧
  (F 0 = p.omega * qA ∨
    ∃ m : ℝ, 0 ≤ m ∧ F 0 = F m - p.rho1 * (m + p.rho0)) ∧
  (∀ m : ℝ, 0 < m →
    F 0 = F m - p.rho1 * (m + p.rho0) → deriv F m = p.rho1) ∧
  (∀ m : ℝ, mstar < m → F m = F mstar + (m - mstar))

/-- Worst-case allocation angle, (26). -/
def phiOpt (p : Params) (F : ℝ → ℝ) (m : ℝ) : ℝ :=
  Real.arctan ((deriv F m / (F m - deriv F m * m)) *
    (p.sigY * p.kapT / (p.sigD * p.kapP)))

/-- Optimal investment rate, (26). -/
def iOpt (p : Params) (F : ℝ → ℝ) (m : ℝ) : ℝ :=
  (F m - deriv F m * (m + 1)) / (p.theta * deriv F m)

/-- Worst-case permanent-shock distortion, (27). -/
def hP (p : Params) (F : ℝ → ℝ) (m : ℝ) : ℝ :=
  -p.kapP * Real.cos (phiOpt p F m)

/-- Worst-case temporary-shock distortion, (27). -/
def hT (p : Params) (F : ℝ → ℝ) (m : ℝ) : ℝ :=
  -p.kapT * Real.sin (phiOpt p F m)

/-- hᴾ sensitivity to a permanent shock, §4.1, p. 21. -/
def sensPP (p : Params) (F : ℝ → ℝ) (m : ℝ) : ℝ :=
  -deriv (hP p F) m * m * p.sigD

/-- hᴾ sensitivity to a temporary shock, §4.1, p. 21. -/
def sensPT (p : Params) (F : ℝ → ℝ) (m : ℝ) : ℝ :=
  deriv (hP p F) m * p.sigY

/-- hᵀ sensitivity to a permanent shock, §4.1, p. 21. -/
def sensTP (p : Params) (F : ℝ → ℝ) (m : ℝ) : ℝ :=
  -deriv (hT p F) m * m * p.sigD

/-- hᵀ sensitivity to a temporary shock, §4.1, p. 21. -/
def sensTT (p : Params) (F : ℝ → ℝ) (m : ℝ) : ℝ :=
  deriv (hT p F) m * p.sigY

end ExtrapBias.Beliefs


