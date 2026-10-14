-- Prove2me | Definitions.Def_ThreeSum1960614_Analysis
-- name    : ThreeSum1960614_Analysis
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:06:31.105618+00:00
-- url     : https://prove2.me/theorems/4f989e3e-71e0-4d7d-ad99-06cb29a25354
-- title:
--   Entropy, quartic integer switch, twelve costs and fixed-expansion model
-- statement:
--   Defines binary entropy in bits $H(t)$, $E_c=(c/2)H(1/c)$, $\kappa_c=2cH(1/(2c))-cH(1/c)-1$, and $\gamma_c(t)=cH(1/c)-cH((1-t)/c)$ for natural expansion $c$. The quartic is $P(t)=7.85174904t+0.72447023t^2+0.24044466t^3+0.12022459t^4$, with its polynomial derivative. The fixed rational parameters are $e=0.203889696$, $b=-0.062656016$, $S=0.193175570$, $\theta=0.040409899$, $\tau=13/20$, $\rho=0.27905030$, and $u=0.17200068185091493$. The principal cost cap is $1.96061388$ and the campaign target is the rational $1.960614$.
--
--   The ledger lists all twelve source costs in their source order. `costs` instantiates them at the fixed parameters and $c=232$. The natural-number predicate `clearedSwitch` is the degree-four integer comparison of Section 4.2, with $v=S-2b=159243801/500000000$. `ModelFeasible` describes the relaxed fixed-expansion real cost model, including its whole-interval entropy inequality and all twelve charges. It is not a model of arbitrary 3SUM algorithms. Total logarithms, division and natural subtraction are unrestricted in these definitions; theorem hypotheses delimit the intended domains. The shared machine and decision-problem definitions are imported unchanged.
-- source:
--   User-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md (14 October 2026); Sections 1–5 and 7; upstream https://github.com/c0ldzy17/three-sum-lean/tree/2b639655e07421b9ac743de9090459bab473a7c0

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ThreeSum1960614

noncomputable def entropy (t : ℝ) : ℝ := Real.binEntropy t / Real.log 2
noncomputable def E (c : ℕ) : ℝ := (c : ℝ) / 2 * entropy (1 / c)
noncomputable def kappa (c : ℕ) : ℝ :=
  2 * c * entropy (1 / (2 * c)) - c * entropy (1 / c) - 1
noncomputable def gamma (c : ℕ) (t : ℝ) : ℝ :=
  c * entropy (1 / c) - c * entropy ((1 - t) / c)
def phi (t : ℝ) : ℝ :=
  (785174904 * t + 72447023 * t ^ 2 + 24044466 * t ^ 3 + 12022459 * t ^ 4) / 100000000
def phiDeriv (t : ℝ) : ℝ :=
  (785174904 + 2 * 72447023 * t + 3 * 24044466 * t ^ 2 + 4 * 12022459 * t ^ 3) / 100000000
def epsilon : ℝ := 203889696 / 1000000000
def beta : ℝ := -(62656016 / 1000000000)
def saving : ℝ := 193175570 / 1000000000
def theta : ℝ := 40409899 / 1000000000
def tau : ℝ := 13 / 20
def rho : ℝ := 2790503 / 10000000
def tangentPoint : ℝ := 17200068185091493 / 100000000000000000
def principal : ℝ := 196061388 / 100000000
def target : ℚ := 1960614 / 1000000
def v : ℝ := saving - 2 * beta
def threshold (a : ℝ) : ℝ := (v + a) / (1 - a)
def ledger (e b S terminal ratio EE kk hh : ℝ) : List ℝ :=
  [2 * e * EE,
   1 + e * (EE - b),
   2 - e * S,
   2 - e * (1 / 2 + b - hh),
   2 - e * (1 / 2 - b - kk - ratio * (1 + S - 2 * b)),
   2 - e * (terminal - 1 / 2 - b - kk),
   e * (8 / 5) * (EE + 1 / 2),
   2 + e * (4 / 5 - (2 / 5) * EE - 2 * b),
   1 + e * (1 / 2 - b),
   2 - e * (EE + b),
   2 - 2 * e * (EE + b), 1]
noncomputable def costs : List ℝ :=
  ledger epsilon beta saving tau rho (E 232) (kappa 232) (entropy theta)
def clearedSwitch (J s j q : ℕ) : Prop :=
  let r := (J - j) * s
  500000000 * (J - j) *
    (785174904 * q * r ^ 3 + 72447023 * q ^ 2 * r ^ 2 +
     24044466 * q ^ 3 * r + 12022459 * q ^ 4) ≥
    100000000 * (159243801 * J + 500000000 * j) * r ^ 4
noncomputable def ModelFeasible (c : ℕ) (e b S th terminal ratio R : ℝ) : Prop :=
  0 < e ∧ e < 1 ∧ b < 0 ∧ 0 < S ∧
  0 ≤ th ∧ th ≤ 1 / 2 ∧ 0 ≤ terminal ∧ terminal < 1 ∧
  0 < ratio ∧ S - 2 * b ≤ gamma c th ∧
  (∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), entropy t ≤ ratio * (1 + gamma c t)) ∧
  ∀ z ∈ ledger e b S terminal ratio (E c) (kappa c) (entropy th), z ≤ R

end ThreeSum1960614


