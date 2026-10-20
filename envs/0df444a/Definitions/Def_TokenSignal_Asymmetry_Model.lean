-- Prove2me | Definitions.Def_TokenSignal_Asymmetry_Model
-- name    : TokenSignal_Asymmetry_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:12.2267+00:00
-- url     : https://prove2.me/theorems/fed5133d-206c-448a-bbc6-9ff8cca3ad1c
-- title:
--   Two-type token and equity signaling model
-- statement:
--   There are high- and low-quality ventures $H,L$, and two financing methods, equity $E$ and tokens $T$. Let $\mu_H>\mu_L$ be the means of the normal shocks $X_i=\xi_i^2$, with common standard deviation $\sigma>0$. Revenue is $R_i=X_i/4$. The entrepreneur pays fixed cost $C$ and initial investment $I$, and has CARA coefficient $\gamma>0$.
--
--   For an entrepreneur of type $i$ perceived as type $j$, the expected utility from selling fraction $\alpha$ is
--
--   $$U_{ij}(\alpha)=\mathbb E_i\left[u_\gamma\!\left(\alpha\mathbb E_j[R_j]+(1-\alpha)R_i-C-I\right)\right].$$
--
--   Financing requires $\alpha\ge\bar\alpha^E_j=I/(\mathbb E_j[R_j]-C)$ for equity and $\alpha\ge\bar\alpha^T_j=I/\mathbb E_j[R_j]$ for tokens. Investors believe the venture is high-quality when $\alpha\le t$ and low-quality when $\alpha>t$. Conditions (23) and (24) compare each type’s best feasible payoff on the two sides of this threshold. A separating equilibrium satisfies both, and a least-cost separating equilibrium is not Pareto-dominated by another separating equilibrium. The closed-form $\alpha^*$ of (25) and certainty equivalent $V_{ij}$ of (38) are also defined here.
--
--   The model supports the paper’s comparison of when token financing allows separation while equity financing does not.
--
--   **Formalization Note** The normal law is assigned to $X_i=\xi_i^2$ directly, with variance $\sigma^2$. The standing domain adds $C>0$ and $I\le\mu_L/4-C$ to secure strict financing-threshold order and low-type feasibility. Equilibrium thresholds satisfy $t<1$.
-- source:
--   Chod & Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (version of Dec. 14, 2019), pp. 12, 18–20 (PDF 13, 19–21), Assumption 1 and §4, eqs. (20)–(25)

import Mathlib
import Definitions.Def_TokenSignal_Asymmetry_CARA

namespace TokenSignal.Asymmetry

open MeasureTheory ProbabilityTheory

inductive Ty | H | L deriving DecidableEq
inductive Method | equity | token deriving DecidableEq

structure Params where
  μH : ℝ
  μL : ℝ
  σ : ℝ
  γ : ℝ
  C : ℝ
  I : ℝ

def Params.Standing (P : Params) : Prop :=
  0 < P.γ ∧ 0 < P.σ ∧ P.μL < P.μH ∧ 0 < P.C ∧ 0 < P.I ∧
    P.I ≤ P.μL / 4 - P.C

def Params.μ (P : Params) : Ty → ℝ
  | .H => P.μH
  | .L => P.μL

noncomputable def revLaw (P : Params) (i : Ty) : Measure ℝ :=
  gaussianReal (P.μ i) ⟨P.σ ^ 2, sq_nonneg _⟩

noncomputable def ER (P : Params) (j : Ty) : ℝ :=
  ∫ x, x / 4 ∂revLaw P j

noncomputable def U (P : Params) (i j : Ty) (α : ℝ) : ℝ :=
  ∫ x, cara P.γ (α * ER P j + (1 - α) * (x / 4) - P.C - P.I) ∂revLaw P i

noncomputable def αbar (P : Params) : Method → Ty → ℝ
  | .equity, j => P.I / (ER P j - P.C)
  | .token, j => P.I / ER P j

def Hset (P : Params) (m : Method) (t : ℝ) : Set ℝ :=
  Set.Icc (αbar P m .H) t

def Lset (P : Params) (m : Method) (t : ℝ) : Set ℝ :=
  {α | αbar P m .L ≤ α ∧ t < α ∧ α ≤ 1}

def HighIC (P : Params) (m : Method) (t : ℝ) : Prop :=
  ∀ α ∈ Lset P m t, ∃ α' ∈ Hset P m t, U P .H .L α ≤ U P .H .H α'

def LowIC (P : Params) (m : Method) (t : ℝ) : Prop :=
  ∃ α ∈ Lset P m t, ∀ α' ∈ Hset P m t, U P .L .H α' ≤ U P .L .L α

def IsSE (P : Params) (m : Method) (t : ℝ) : Prop :=
  αbar P m .H ≤ t ∧ t < 1 ∧ HighIC P m t ∧ LowIC P m t

noncomputable def payH (P : Params) (m : Method) (t : ℝ) : ℝ :=
  sSup (U P .H .H '' Hset P m t)

noncomputable def payL (P : Params) (m : Method) (t : ℝ) : ℝ :=
  sSup (U P .L .L '' Lset P m t)

def IsLCSE (P : Params) (m : Method) (t : ℝ) : Prop :=
  IsSE P m t ∧ ¬ ∃ t', IsSE P m t' ∧
    payH P m t ≤ payH P m t' ∧ payL P m t ≤ payL P m t' ∧
    (payH P m t < payH P m t' ∨ payL P m t < payL P m t')

noncomputable def αStar (P : Params) : ℝ :=
  (4 * P.μH - 4 * P.μL + P.σ ^ 2 * P.γ -
    Real.sqrt ((4 * P.μH - 4 * P.μL) * (4 * P.μH - 4 * P.μL + 2 * P.σ ^ 2 * P.γ))) /
    (P.σ ^ 2 * P.γ)

noncomputable def V (P : Params) (i j : Ty) (α : ℝ) : ℝ :=
  α * P.μ j / 4 + (1 - α) * P.μ i / 4 - P.γ * (1 - α) ^ 2 * P.σ ^ 2 / 32

def SignalingAdvantage (P : Params) : Prop :=
  (∃ t, IsSE P .token t) ∧ ¬ ∃ t, IsSE P .equity t

end TokenSignal.Asymmetry


