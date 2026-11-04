-- Prove2me | Definitions.Def_GOLiQ_Model
-- name    : GOLiQ_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:21.946727+00:00
-- url     : https://prove2.me/theorems/396d8aba-63f4-4c55-939e-b9dc950bf0f4
-- title:
--   Pricing-and-staffing model: the box $B$, demand rate $\lambda$, staffing cost $c$, holding cost $h_0$ (Assumption 1)
-- statement:
--   A single-server queue charges each customer a fee $p>0$ and is staffed at service rate $\mu$. The **model data** are
--
--   1. the box $\mathcal B=[\underline\mu,\bar\mu]\times[\underline p,\bar p]$ of admissible decisions $x=(\mu,p)$, with $0<\underline\mu<\bar\mu$ and $0<\underline p<\bar p$;
--   2. the arrival (demand) rate $\lambda(p)$, continuously differentiable and non-increasing on $[\underline p,\bar p]$, with $\lambda(\bar p)>0$ (Assumption 1(a));
--   3. the staffing cost rate $c(\mu)$, continuously differentiable and non-decreasing on $[\underline\mu,\bar\mu]$ (Assumption 1(b));
--   4. the holding cost $h_0$ per customer per unit time;
--   5. uniform stability: $\lambda(\underline p)<\underline\mu$ (Assumption 1(c)).
--
--   Decisions are points of the Euclidean plane, coordinate $0$ being $\mu$ and coordinate $1$ being $p$, with the Euclidean norm. The module also defines the projection $\Pi_{\mathcal B}$ onto the box (which clamps each coordinate to its interval) and the derivatives $\lambda'$, $c'$ taken within the closed intervals.
--
--   This is the deterministic layer of every statement of the mission.
--
--   **Formalization Note** The intervals are nondegenerate so that $\lambda'$, $c'$ and the gradient of the objective on $\mathcal B$ are determined. No sign is imposed on $h_0$, since the paper states none.
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, §3.1, pp.10–11, problem (2) and Assumption 1; §3.2, p.12 (Π_B, Euclidean norm)

import Mathlib

namespace GOLiQ

/-- A decision `x = (µ, p)`: a point of the Euclidean plane, coordinate `0` = service rate `µ`,
coordinate `1` = service fee `p`. The norm is the Euclidean norm (Chen, Liu, Hong,
arXiv:2009.02911v3, p.12: "‖·‖ denote the Euclidean norm"). -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- **The deterministic data of the pricing-and-staffing problem and Assumption 1**
(Chen, Liu, Hong, *An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service
Systems*, arXiv:2009.02911v3, §3.1, pp.10–11, problem (2) and Assumption 1).

* the box `B = [µ̲, µ̄] × [p̲, p̄]` of service rates and fees;
* the arrival (demand) rate `λ(p)`, continuously differentiable and non-increasing (Assumption 1(a));
* the staffing cost rate `c(µ)`, continuously differentiable and non-decreasing (Assumption 1(b));
* the holding cost `h₀` per job per unit time;
* uniform stability `λ(p̲) < µ̲` (Assumption 1(c)).

**Formalization Note.** The fee is positive (`p > 0`, p.10), so `0 < p̲`; service rates are positive,
so `0 < µ̲`; the arrival rate is positive on the box, which, `λ` being non-increasing, is
`0 < λ(p̄)`. The intervals are nondegenerate (`µ̲ < µ̄`, `p̲ < p̄`), so that `λ′`, `c′` and the gradient
of the objective on `B` are determined. Continuous differentiability is on the closed intervals,
and `λ′`, `c′` are the derivatives within them (`Model.dlam`, `Model.dc`). No sign is imposed on
`h₀` (the paper states none). -/
structure Model where
  /-- `µ̲`, the lower bound of the service rate. -/
  muLo : ℝ
  /-- `µ̄`, the upper bound of the service rate. -/
  muHi : ℝ
  /-- `p̲`, the lower bound of the fee. -/
  pLo : ℝ
  /-- `p̄`, the upper bound of the fee. -/
  pHi : ℝ
  /-- The arrival rate `λ(p)`. -/
  lam : ℝ → ℝ
  /-- The staffing cost rate `c(µ)`. -/
  c : ℝ → ℝ
  /-- The holding cost `h₀`. -/
  h0 : ℝ
  muLo_pos : 0 < muLo
  muLo_lt_muHi : muLo < muHi
  pLo_pos : 0 < pLo
  pLo_lt_pHi : pLo < pHi
  lam_pHi_pos : 0 < lam pHi
  /-- Assumption 1(a): `λ` is continuously differentiable ... -/
  lam_contDiffOn : ContDiffOn ℝ 1 lam (Set.Icc pLo pHi)
  /-- ... and non-increasing. -/
  lam_antitoneOn : AntitoneOn lam (Set.Icc pLo pHi)
  /-- Assumption 1(b): `c` is continuously differentiable ... -/
  c_contDiffOn : ContDiffOn ℝ 1 c (Set.Icc muLo muHi)
  /-- ... and non-decreasing. -/
  c_monotoneOn : MonotoneOn c (Set.Icc muLo muHi)
  /-- Assumption 1(c): uniform stability `λ(p̲) < µ̲`. -/
  stable : lam pLo < muLo

namespace Model

variable (M : Model)

/-- The box `B = [µ̲, µ̄] × [p̲, p̄]` of (2), as a subset of the Euclidean plane. -/
def box : Set Point :=
  {x | x 0 ∈ Set.Icc M.muLo M.muHi ∧ x 1 ∈ Set.Icc M.pLo M.pHi}

/-- The Euclidean projection `Π_B` onto the box `B`: on a box it clamps each coordinate to its
interval. -/
noncomputable def proj (x : Point) : Point :=
  !₂[max M.muLo (min M.muHi (x 0)), max M.pLo (min M.pHi (x 1))]

/-- `λ′(p)`, the derivative of `λ` within `[p̲, p̄]`. -/
noncomputable def dlam (p : ℝ) : ℝ := derivWithin M.lam (Set.Icc M.pLo M.pHi) p

/-- `c′(µ)`, the derivative of `c` within `[µ̲, µ̄]`. -/
noncomputable def dc (mu : ℝ) : ℝ := derivWithin M.c (Set.Icc M.muLo M.muHi) mu

end Model

end GOLiQ


