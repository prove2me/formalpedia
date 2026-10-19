-- Prove2me | Definitions.Def_CropMSP_MarketUnc_Model
-- name    : CropMSP_MarketUnc_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:24.920295+00:00
-- url     : https://prove2.me/theorems/5d4184c5-f457-415f-a853-82b625628193
-- title:
--   §3–§4 — credit-based minimum support price, threshold equilibrium, and welfare quantities
-- statement:
--   A unit mass of farmers each has capacity one and a cultivation cost uniformly distributed on $[0,1]$. Market potential is $a$, the market price at aggregate quantity $q$ is $p(q,\epsilon)=a-q+\epsilon$, and the shock is uniform on $[-\theta,\theta]$. With minimum support price $m$, a farmer receives $\hat p=\max\{m,p\}$ and finds cultivation lucrative when $\Pr(\hat p\le c)\le\alpha$.
--
--   The equilibrium quantity is the mass of farmers whose costs make cultivation lucrative at that same quantity. An MSP is admissible when it lies between the smallest and largest market prices at equilibrium. Farmer surplus $F$ integrates expected revenue minus cultivation cost over sowers; government expenditure $E$ integrates the positive support payment; consumer surplus $C$ is the area below inverse demand and above market price. The policy metrics are
--
--   $$B(m)=F(m)-E(m),\qquad V(m)=F(m)+C(m)-E(m).$$
--
--   This model supplies the common definitions for the equilibrium and welfare statements in the mission.
--
--   **Formalization Note** Both uniform distributions use Lebesgue measure. The standing assumptions are $0<\alpha<1/2$, $\theta>0$, $1+\theta<a$, and $\tau_0<1$, where $\tau_0=(a-(1-2\alpha)\theta)/2$. The condition $\theta>0$ makes the continuous uniform law and its normalization well defined. The displayed $\tau(m)=\min\{1,\max\{m,\tau_0\}\}$ is only a candidate quantity here; equilibrium is defined independently as a fixed point.
-- source:
--   Chintapalli & Tang, The Value and Cost of Crop Minimum Support Price, SSRN 3681588 manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3831), pp. 6–12, §3, §4, Assumptions 1–2, eqs. (1)–(12)

import Mathlib

namespace CropMSP.MarketUnc

open MeasureTheory

structure Params where
  a : ℝ
  θ : ℝ
  α : ℝ

noncomputable def tau0 (P : Params) : ℝ := (P.a - (1 - 2 * P.α) * P.θ) / 2
noncomputable def tau (P : Params) (m : ℝ) : ℝ := min 1 (max m (tau0 P))

def Params.Standing (P : Params) : Prop :=
  0 < P.α ∧ P.α < 1 / 2 ∧ 0 < P.θ ∧ 1 + P.θ < P.a ∧ tau0 P < 1

def price (P : Params) (q ε : ℝ) : ℝ := P.a - q + ε
def effPrice (P : Params) (m q ε : ℝ) : ℝ := max m (price P q ε)

noncomputable def lossProb (P : Params) (m q c : ℝ) : ℝ :=
  (volume {ε ∈ Set.Icc (-P.θ) P.θ | effPrice P m q ε ≤ c}).toReal / (2 * P.θ)

def Lucrative (P : Params) (m q c : ℝ) : Prop := lossProb P m q c ≤ P.α
def sowers (P : Params) (m q : ℝ) : Set ℝ :=
  {c ∈ Set.Icc (0 : ℝ) 1 | Lucrative P m q c}

def IsEquilibrium (P : Params) (m q : ℝ) : Prop :=
  q ∈ Set.Icc (0 : ℝ) 1 ∧ (volume (sowers P m q)).toReal = q

def Admissible (P : Params) (m q : ℝ) : Prop :=
  P.a - q - P.θ ≤ m ∧ m ≤ P.a - q + P.θ

noncomputable def expEps (P : Params) (g : ℝ → ℝ) : ℝ :=
  (∫ ε in (-P.θ)..P.θ, g ε) / (2 * P.θ)

noncomputable def farmerSurplus (P : Params) (m q : ℝ) : ℝ :=
  ∫ c in sowers P m q, (expEps P (fun ε => effPrice P m q ε) - c)

noncomputable def expenditure (P : Params) (m q : ℝ) : ℝ :=
  q * expEps P (fun ε => max 0 (m - price P q ε))

noncomputable def consumerSurplus (P : Params) (q : ℝ) : ℝ :=
  expEps P (fun ε => ∫ x in (0 : ℝ)..q, (price P x ε - price P q ε))

noncomputable def netBenefit (P : Params) (m q : ℝ) : ℝ :=
  farmerSurplus P m q - expenditure P m q

noncomputable def netSocialValue (P : Params) (m q : ℝ) : ℝ :=
  farmerSurplus P m q + consumerSurplus P q - expenditure P m q

end CropMSP.MarketUnc


