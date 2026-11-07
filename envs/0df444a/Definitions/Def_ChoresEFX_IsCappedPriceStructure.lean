-- Prove2me | Definitions.Def_ChoresEFX_IsCappedPriceStructure
-- name    : ChoresEFX_IsCappedPriceStructure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:06:14.432923+00:00
-- url     : https://prove2.me/theorems/0c28e222-9ff9-4e5d-80aa-cf80c518b7da
-- title:
--   Prices, MPB ratios, capped prices, capped income and capped-price structures (Definition 2.3)
-- statement:
--   For positive prices $p$, write $p(S)=\sum_{g\in S}p_g$. Agent $i$'s **minimum pain per buck ratio** is $\gamma_i=\min_g c_i(g)/p_g$, and $A_i(a)=\{g:c_i(g)\le a\gamma_ip_g\}$. For a cap $\beta>0$, the **capped prices** are $q_g=\min\{p_g,\beta\}$, and agent $i$'s **capped income** under a fractional allocation $w$ is $E_i=\sum_g q_gw_{ig}$.
--
--   For a strictly positive cost matrix, $0<t\le1/100$ and $0<\beta<1$, a **capped-price structure** consists of positive prices $p_g$, ratios $\gamma_i$ and shares $w_{ig}\ge0$ with:
--
--   1. $\sum_i w_{ig}=1$ for every chore $g$;
--   2. $E_i\in[1-t,1+t]$ for every agent $i$;
--   3. $c_i(g)\ge\gamma_ip_g$ for all $i,g$;
--   4. $w_{ig}>0$ implies $c_i(g)\le(1+t)\gamma_ip_g$.
--
--   The parameters of the analysis are $\beta_k(t)=(1+2t)/(k+1)$ and $\rho_k(t)=1-t-\beta_k(t)$. For $k=1$ these are Eq. (1), $\beta=1/2+t$ and $\rho=1/2-2t$.
--
--   This structure is the price certificate that the first stage of the algorithm computes and the later stages use.
--
--   **Formalization Note** The structure carries $\gamma$ as data, as the paper does. `mpbRatio` is a real infimum over the finite chore set, so it is a minimum when there is a chore; its value on an empty chore set is never used.
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), §2, p.5; Definition 2.3, pp.5–6; Eq. (1), p.6; EFkX Extension, p.13

import Mathlib
import Definitions.Def_ChoresEFX_IsAlphaEFX

namespace ChoresEFX

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The price of a bundle, `p(S) = ∑_{g ∈ S} p_g`.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC
2027 submission (manuscript sha256 b26d14cf…), §2, p.5. The same sum gives `q(S)` for the capped
prices. -/
def priceOf (p : κ → ℝ) (S : Finset κ) : ℝ := ∑ g ∈ S, p g

/-- **The minimum pain per buck ratio**, `γ_i = min{c_i(g)/p_g : g ∈ M}`, §2, p.5 (Qin et al., STOC
2027 submission).

**Formalization Note.** A real `⨅` over the finite type `κ`, so it is attained when `κ` is nonempty.
On empty `κ` it is the junk value `0`: every statement that uses it has `[Nonempty κ]` (or a hypothesis
implying it) and positive prices. -/
noncomputable def mpbRatio (c : ι → κ → ℝ) (p : κ → ℝ) (i : ι) : ℝ := ⨅ g, c i g / p g

/-- **The a-MPB set**, `A_i(a) = {g ∈ M : c_i(g) ≤ a γ_i p_g}`, §2, p.5 (Qin et al., STOC 2027
submission). -/
noncomputable def mpbSet (c : ι → κ → ℝ) (p : κ → ℝ) (a : ℝ) (i : ι) : Set κ :=
  {g | c i g ≤ a * mpbRatio c p i * p g}

/-- **Capped prices**, `q_g = min{p_g, β}`, §2, p.5 (Qin et al., STOC 2027 submission). -/
noncomputable def capped (β : ℝ) (p : κ → ℝ) (g : κ) : ℝ := min (p g) β

/-- **Total capped income**, `E_i = ∑_{g ∈ M} q_g · w_ig`, §2, p.5 (Qin et al., STOC 2027 submission). -/
noncomputable def cappedIncome (β : ℝ) (p : κ → ℝ) (w : ι → κ → ℝ) (i : ι) : ℝ :=
  ∑ g, capped β p g * w i g

/-- **Definition 2.3 (capped-price structure)**, pp.5–6 (Qin et al., STOC 2027 submission): for a
strictly positive cost matrix, `0 < t ≤ 1/100` and `0 < β < 1`, positive prices `p`, MPB ratios `γ` and
fractional shares `w ≥ 0` with (1) `∑_i w_ig = 1`, (2) `E_i ∈ [1 − t, 1 + t]`, (3) `c_i(g) ≥ γ_i p_g`,
(4) `w_ig > 0 ⟹ c_i(g) ≤ (1 + t) γ_i p_g`.

**Formalization Note.** The structure carries `γ` as data, as the paper does; it is not forced to equal
`mpbRatio` here (Lemma 3.1 proves that for the output of MFCP). `w_ig ≥ 0` is the standing condition on
fractional solutions from p.5. -/
structure IsCappedPriceStructure (c : ι → κ → ℝ) (t β : ℝ) (p : κ → ℝ) (γ : ι → ℝ)
    (w : ι → κ → ℝ) : Prop where
  t_pos : 0 < t
  t_le : t ≤ 1 / 100
  beta_pos : 0 < β
  beta_lt : β < 1
  cost_pos : ∀ i g, 0 < c i g
  price_pos : ∀ g, 0 < p g
  share_nonneg : ∀ i g, 0 ≤ w i g
  completeness : ∀ g, ∑ i, w i g = 1
  income_lower : ∀ i, 1 - t ≤ cappedIncome β p w i
  income_upper : ∀ i, cappedIncome β p w i ≤ 1 + t
  cost_lower : ∀ i g, γ i * p g ≤ c i g
  mpb_support : ∀ i g, 0 < w i g → c i g ≤ (1 + t) * γ i * p g

/-- **The cap** `β = (1 + 2t)/(k + 1)`: Eq. (1), p.6, for `k = 1`, and "EFkX Extension", p.13, for
`k ≥ 2` (Qin et al., STOC 2027 submission). -/
noncomputable def betaParam (k : ℕ) (t : ℝ) : ℝ := (1 + 2 * t) / ((k : ℝ) + 1)

/-- **The price lower bound** `ρ = 1 − t − β`: Eq. (1), p.6, for `k = 1` (where `ρ = 1/2 − 2t`), and
"EFkX Extension", p.13, for `k ≥ 2` (Qin et al., STOC 2027 submission). -/
noncomputable def rhoParam (k : ℕ) (t : ℝ) : ℝ := 1 - t - betaParam k t

end ChoresEFX


