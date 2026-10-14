-- Prove2me | Definitions.Def_RiskExposure_Complementarity_Model
-- name    : RiskExposure_Complementarity_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:19.877087+00:00
-- url     : https://prove2.me/theorems/055e7fb3-2e20-4503-8b95-cdb67de9f00a
-- title:
--   §2, Definition 1, (1)–(5), pp. 5–9; IA pp. 8–9 — interbank network, greatest payment equilibrium d*, profit, expected profit, best response, cross-subsidy D_i, Ω^{f+}_{−i}, D*_i
-- statement:
--   This file sets up the financial-network model of Shu, §2.
--
--   **Network.** A finite set $\mathcal N$ of banks is given. For banks $i,j$, $\bar d_{ij}\ge 0$ is the face value of the interbank debt owed by bank $j$ to bank $i$; $\bar d_j=\sum_i \bar d_{ij}$ is bank $j$'s total interbank liability and $\theta_{ij}=\bar d_{ij}/\bar d_j$ is bank $i$'s share of it. Each bank also owes a deposit $v_i$, senior to its interbank debt.
--
--   **Projects and states.** Bank $i$ chooses a project $Z_i$; it pays $Z_i$ with probability $P(Z_i)$ and $0$ otherwise, independently across banks (equation (1)). A state of nature is $\omega\in\{s,f\}^{\mathcal N}$ (success or failure of each project), and the realized cash flow of bank $i$ is $e_i(\omega_i,Z_i)=Z_i$ if $\omega_i=s$ and $0$ if $\omega_i=f$. The probability of a state is $\Pr(\omega)=\prod_j \Pr(\omega_j)$ with $\Pr(\omega_j=s)=P(Z_j)$.
--
--   **Payment equilibrium (Definition 1).** A vector $d$ solves the clearing system (2) when, for every bank $i$,
--   $$d_i=\Big\{\min\Big[\sum_j\theta_{ij}d_j+e_i(\omega_i,Z_i)-v_i,\ \bar d_i\Big]\Big\}^+ .$$
--   The payment equilibrium $d^*(\omega;Z)$ is the **greatest** solution of (2): the componentwise supremum of all solutions $d$ with $0\le d_i\le\bar d_i$ (every solution lies in this box).
--
--   **Profit and best response.** Bank $i$'s profit (3) is $\Pi_i(\omega;Z)=\big(\sum_j\theta_{ij}d_j^*(\omega;Z)+e_i(\omega_i,Z_i)-v_i-d_i^*(\omega;Z)\big)^+$, its expected profit is $\mathbb E[\Pi_i(\omega;Z)]=\sum_{\omega}\Pi_i(\omega;Z)\Pr(\omega)$, and its best-response set (4) at a profile $Z$ is the set of maximizers over $y\in[\underline Z,\overline Z]$ of $\mathbb E[\Pi_i(\omega;y,Z_{-i})]$.
--
--   **Cross-subsidies.** With $\omega^{i=s}$ (resp. $\omega^{i=f}$) the state with bank $i$'s coordinate set to success (failure) and $\Pr(\omega_{-i})=\prod_{j\ne i}\Pr(\omega_j)$,
--   $$\mathcal D_i(Z_{-i})=\sum_{\omega_{-i}}\Big(\bar d_i-\sum_j\theta_{ij}d_j^*(\omega^{i=s})\Big)\Pr(\omega_{-i}) \qquad (5),$$
--   $\Omega^{f+}_{-i}=\{\omega_{-i}:\ \sum_j\theta_{ij}d^*_j(\omega^{i=f})-d^*_i(\omega^{i=f})-v_i>0\}$ (the counterparty states in which bank $i$ survives its own failure), and
--   $$\mathcal D^*_i(Z_{-i})=\sum_{\omega_{-i}\notin\Omega^{f+}_{-i}}\Big[v_i+\Big(\bar d_i-\sum_j\theta_{ij}d_j^*(\omega^{i=s})\Big)\Big]\Pr(\omega_{-i}).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Banks form a finite type `ι`; a state is `ω : ι → Bool` with `true` = success. Sums over $\omega_{-i}$ are sums over all `ω` with `ω i = true` (the states $\omega^{i=s}$), weighted by the product over `j ≠ i`. `paymentEq` is the `sSup` of the solutions of (2) in the box $[0,\bar d]$; under $\bar d_{ij}\ge 0$ and $\bar d_j>0$ it is itself a solution and the greatest one (Knaster–Tarski). Lemma 1 of the paper only asserts generic uniqueness, so a selection is needed; the greatest solution is the one Eisenberg–Noe's algorithm computes and agrees with the unique one whenever (2) has one solution. `paymentEq`, `OmegaFPlus` and `distortionStar` keep the argument `Z`, as the paper writes $d^*(\omega;Z)$. `OmegaFPlus Z ω i` reads `ω` with its `i`-th coordinate overwritten by failure.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), pp. 5–9, §2, (1), Assumption 1, Definition 1 (2), (3), (4), (5); Internet Appendix pp. 8–9, Ω^{f+}_{−i} and D*_i

import Mathlib

namespace RiskExposure.Complementarity

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `dbar i j` is the face value `d̄_ij` of the interbank debt owed by bank `j` to bank `i`;
`dbarTot dbar j = d̄_j = ∑_i d̄_ij` is bank `j`'s total interbank liability (p. 5). -/
def dbarTot (dbar : ι → ι → ℝ) (j : ι) : ℝ := ∑ i, dbar i j

/-- `θ_ij = d̄_ij / d̄_j`, bank `i`'s share of bank `j`'s total interbank liabilities (p. 5). -/
noncomputable def theta (dbar : ι → ι → ℝ) (i j : ι) : ℝ := dbar i j / dbarTot dbar j

/-- The realized cash flow `e_i(ω_i, Z_i)` of (1): `Z_i` if bank `i`'s project succeeds
(`ω i = true`, the paper's `ω_i = s`) and `0` if it fails (`ω i = false`, `ω_i = f`). -/
def cash (ω : ι → Bool) (Z : ι → ℝ) (i : ι) : ℝ := if ω i then Z i else 0

/-- The right-hand side of (2):
`{min[∑_j θ_ij d_j + e_i(ω_i, Z_i) − v_i, d̄_i]}^+`. -/
noncomputable def clearingMap (dbar : ι → ι → ℝ) (v : ι → ℝ) (ω : ι → Bool) (Z : ι → ℝ)
    (d : ι → ℝ) (i : ι) : ℝ :=
  max (min (∑ j, theta dbar i j * d j + cash ω Z i - v i) (dbarTot dbar i)) 0

/-- `d` solves the payment-equilibrium system (2) of Definition 1 in state `ω` under the risk
vector `Z`. -/
def IsPaymentEq (dbar : ι → ι → ℝ) (v : ι → ℝ) (ω : ι → Bool) (Z : ι → ℝ) (d : ι → ℝ) : Prop :=
  ∀ i, d i = clearingMap dbar v ω Z d i

/-- The payment equilibrium `d*(ω; Z)`: the greatest solution of (2), taken as the
(componentwise) supremum of all solutions `d` with `0 ≤ d_i ≤ d̄_i` (every solution of (2) lies in
this box). -/
noncomputable def paymentEq (dbar : ι → ι → ℝ) (v : ι → ℝ) (ω : ι → Bool) (Z : ι → ℝ) :
    ι → ℝ :=
  sSup {d : ι → ℝ | (∀ i, 0 ≤ d i ∧ d i ≤ dbarTot dbar i) ∧ IsPaymentEq dbar v ω Z d}

/-- Bank `i`'s profit (3): `(∑_j θ_ij d*_j + e_i − v_i − d*_i)^+`. -/
noncomputable def profit (dbar : ι → ι → ℝ) (v : ι → ℝ) (ω : ι → Bool) (Z : ι → ℝ) (i : ι) :
    ℝ :=
  max (∑ j, theta dbar i j * paymentEq dbar v ω Z j + cash ω Z i - v i
    - paymentEq dbar v ω Z i) 0

/-- `Pr(ω) = ∏_j Pr(ω_j)` with `Pr(ω_j = s) = P(Z_j)`, `Pr(ω_j = f) = 1 − P(Z_j)` (independent
projects, p. 7). -/
def stateProb (P : ℝ → ℝ) (Z : ι → ℝ) (ω : ι → Bool) : ℝ :=
  ∏ j, if ω j then P (Z j) else 1 - P (Z j)

/-- Expected profit `E[Π_i(ω; Z)] = ∑_{ω ∈ {s,f}^N} Π_i(ω; Z) · Pr(ω)` (p. 7). -/
noncomputable def expProfit (dbar : ι → ι → ℝ) (v : ι → ℝ) (P : ℝ → ℝ) (Z : ι → ℝ) (i : ι) :
    ℝ :=
  ∑ ω, profit dbar v ω Z i * stateProb P Z ω

/-- Bank `i`'s best-response set (4): the maximizers over `y ∈ [Z̲, Z̄]` of
`E[Π_i(ω; y, Z_{−i})]`. Only `Z_{−i}` matters, since coordinate `i` is overwritten. -/
def bestResponse (dbar : ι → ι → ℝ) (v : ι → ℝ) (P : ℝ → ℝ) (Zlo Zhi : ℝ) (Z : ι → ℝ)
    (i : ι) : Set ℝ :=
  {z | z ∈ Set.Icc Zlo Zhi ∧ ∀ y ∈ Set.Icc Zlo Zhi,
    expProfit dbar v P (Function.update Z i y) i ≤ expProfit dbar v P (Function.update Z i z) i}

/-- The cross-subsidy (5):
`D_i(Z_{−i}) = ∑_{ω_{−i}} (d̄_i − ∑_j θ_ij d*_j(ω^{i=s})) · Pr(ω_{−i})`, written as a sum over
the states `ω` with `ω i = true` and `Pr(ω_{−i}) = ∏_{j ≠ i} Pr(ω_j)`. -/
noncomputable def distortion (dbar : ι → ι → ℝ) (v : ι → ℝ) (P : ℝ → ℝ) (Z : ι → ℝ) (i : ι) :
    ℝ :=
  ∑ ω ∈ univ.filter (fun ω : ι → Bool => ω i = true),
    (dbarTot dbar i - ∑ j, theta dbar i j * paymentEq dbar v ω Z j) *
      ∏ j ∈ univ.erase i, (if ω j then P (Z j) else 1 - P (Z j))

/-- `ω_{−i} ∈ Ω^{f+}_{−i}` (Internet Appendix p. 8): with bank `i`'s project failed
(`ω^{i=f}`), `∑_j θ_ij d*_j(ω^{i=f}) − d*_i(ω^{i=f}) − v_i > 0`. Coordinate `i` of `ω` is
ignored. -/
def OmegaFPlus (dbar : ι → ι → ℝ) (v : ι → ℝ) (Z : ι → ℝ) (ω : ι → Bool) (i : ι) : Prop :=
  0 < ∑ j, theta dbar i j * paymentEq dbar v (Function.update ω i false) Z j
    - paymentEq dbar v (Function.update ω i false) Z i - v i

/-- `OmegaFPlus` is a strict inequality between reals, hence decidable (classically). -/
noncomputable instance (dbar : ι → ι → ℝ) (v : ι → ℝ) (Z : ι → ℝ) (ω : ι → Bool) (i : ι) :
    Decidable (OmegaFPlus dbar v Z ω i) :=
  inferInstanceAs (Decidable (0 < _))

/-- `D*_i(Z_{−i}) = ∑_{ω_{−i} ∉ Ω^{f+}_{−i}} [v_i + (d̄_i − ∑_j θ_ij d*_j(ω^{i=s}))] · Pr(ω_{−i})`
(Internet Appendix p. 9). -/
noncomputable def distortionStar (dbar : ι → ι → ℝ) (v : ι → ℝ) (P : ℝ → ℝ) (Z : ι → ℝ)
    (i : ι) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω : ι → Bool => ω i = true ∧ ¬ OmegaFPlus dbar v Z ω i),
    (v i + (dbarTot dbar i - ∑ j, theta dbar i j * paymentEq dbar v ω Z j)) *
      ∏ j ∈ univ.erase i, (if ω j then P (Z j) else 1 - P (Z j))

end RiskExposure.Complementarity


