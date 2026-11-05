-- Prove2me | Definitions.Def_ReviewInfoShare_Commission
-- name    : ReviewInfoShare_Commission
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:39:23.771345+00:00
-- url     : https://prove2.me/theorems/5c91cfed-1980-44ca-91ef-1dd7fa5ff7c0
-- title:
--   Commission contract — pricing equilibrium and profits, §4.1
-- statement:
--   The pricing game of the commission contract with rate $u$, for fixed regime, arrangement $i$ and quality $q$. The manufacturer sets the retail price and pays the platform $u\,p_t$ per unit.
--
--   1. **Second stage.** For every estimate $t$ and belief $z$, the price $p_2(t,z)$ maximizes $((1-u)p-c_q)(\alpha+tz-p)$. On the path, $p_2^*=p_2(\tilde\theta,\hat q_2)$.
--   2. **First stage.** $p_1^*$ maximizes $((1-u)p-c_q)(\alpha+\mu_\theta q-p)+\bar\Pi^M_{i,2}(q)$.
--   3. **Profits.** With $d_1=\alpha+\theta q-p_1^*$ and $d_2=\alpha+\theta\hat q_2-p_2^*$, the manufacturer's stage-$t$ profit is $E[((1-u)p_t^*-c_q)d_t]$ and the platform's is $E[u\,p_t^*d_t]$; $\bar\Pi^k_i(q)$ is their sum over the two stages. A family of equilibria gives a table of profits for the fee game.
--
--   As for the wholesale contract, no price or profit is defined by a closed form.
--
--   **Formalization Note** The platform's stage profit is $u\,p\,d$, the commission on every unit sold, which is what (61) and (62) compute.
-- source:
--   Shin–Zeevi, Product Quality and Information Sharing in the Presence of Reviews, SSRN 3886954, §4, pp.21–22; (61), p.43

import Mathlib
import Definitions.Def_ReviewInfoShare_Model
import Definitions.Def_ReviewInfoShare_FeeGame

open MeasureTheory

namespace ReviewInfoShare

/-- A pricing profile of the commission contract, SSRN 3886954, §4.1, p.22: the manufacturer's
second-stage retail price `p₂ t z` on its estimate `t` of `θ` and the quality belief `z`, and its
first-stage retail price `p₁`. -/
structure CommissionProfile where
  p₂ : ℝ → ℝ → ℝ
  p₁ : ℝ

/-- Second-stage optimality, SSRN 3886954, p.22: `p₂* = arg max_p ((1 − u)p − c_q)(α + θ̃ q̂₂ − p)`,
for every estimate and belief. -/
def IsCommissionStage2Eq (P : Params) (u : ℝ) (q : Quality) (p₂ : ℝ → ℝ → ℝ) : Prop :=
  ∀ t z, IsMaxOn (fun p => ((1 - u) * p - P.cost q) * (P.α + t * z - p)) Set.univ (p₂ t z)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The realized second-stage retail price `p₂*`, on `θ̃` and `q̂₂`, SSRN 3886954, p.22. -/
noncomputable def CommissionProfile.p2Star (σ : CommissionProfile) (P : Params) (S : Signals Ω)
    (r : Regime) (i : Info) (q : Quality) (ω : Ω) : ℝ :=
  σ.p₂ (estimate P S i ω) (qHat2 P S r q ω)

/-- The platform's second-stage profit `Π̄ᴾ_{i,2}(q) = E[u p₂* (α + θ q̂₂ − p₂*)]`: the manufacturer
pays the platform `u p_t` per unit sold, SSRN 3886954, p.21, (61), p.43. -/
noncomputable def CommissionProfile.stage2Platform (σ : CommissionProfile) (P : Params)
    (S : Signals Ω) (u : ℝ) (r : Regime) (i : Info) (q : Quality) : ℝ :=
  ∫ ω, u * σ.p2Star P S r i q ω *
    (P.α + S.θ ω * qHat2 P S r q ω - σ.p2Star P S r i q ω) ∂S.prob

/-- The manufacturer's second-stage profit
`Π̄ᴹ_{i,2}(q) = E[((1 − u)p₂* − c_q)(α + θ q̂₂ − p₂*)]`, SSRN 3886954, p.22, (61), p.43. -/
noncomputable def CommissionProfile.stage2Manufacturer (σ : CommissionProfile) (P : Params)
    (S : Signals Ω) (u : ℝ) (r : Regime) (i : Info) (q : Quality) : ℝ :=
  ∫ ω, ((1 - u) * σ.p2Star P S r i q ω - P.cost q) *
    (P.α + S.θ ω * qHat2 P S r q ω - σ.p2Star P S r i q ω) ∂S.prob

/-- A pricing equilibrium of the commission contract for fixed regime, information arrangement and
quality, SSRN 3886954, §4.1, p.22: second-stage optimality and
`p₁* = arg max_p ((1 − u)p − c_q)(α + µ_θ q − p) + Π̄ᴹ_{i,2}(q)`. -/
def IsCommissionEq (P : Params) (S : Signals Ω) (u : ℝ) (r : Regime) (i : Info) (q : Quality)
    (σ : CommissionProfile) : Prop :=
  IsCommissionStage2Eq P u q σ.p₂ ∧
  IsMaxOn (fun p => ((1 - u) * p - P.cost q) * (P.α + P.μ * P.qual q - p) +
    σ.stage2Manufacturer P S u r i q) Set.univ σ.p₁

/-- The platform's first-stage profit `Π̄ᴾ_{i,1}(q) = E[u p₁* (α + θ q − p₁*)]`, SSRN 3886954, p.21. -/
noncomputable def CommissionProfile.stage1Platform (σ : CommissionProfile) (P : Params)
    (S : Signals Ω) (u : ℝ) (q : Quality) : ℝ :=
  ∫ ω, u * σ.p₁ * (P.α + S.θ ω * P.qual q - σ.p₁) ∂S.prob

/-- The manufacturer's first-stage profit `Π̄ᴹ_{i,1}(q) = E[((1 − u)p₁* − c_q)(α + θ q − p₁*)]`,
SSRN 3886954, p.22. -/
noncomputable def CommissionProfile.stage1Manufacturer (σ : CommissionProfile) (P : Params)
    (S : Signals Ω) (u : ℝ) (q : Quality) : ℝ :=
  ∫ ω, ((1 - u) * σ.p₁ - P.cost q) * (P.α + S.θ ω * P.qual q - σ.p₁) ∂S.prob

/-- The platform's total profit `Π̄ᴾᵢ(q) = Π̄ᴾ_{i,1}(q) + Π̄ᴾ_{i,2}(q)`, SSRN 3886954, p.22. -/
noncomputable def CommissionProfile.profitPlatform (σ : CommissionProfile) (P : Params)
    (S : Signals Ω) (u : ℝ) (r : Regime) (i : Info) (q : Quality) : ℝ :=
  σ.stage1Platform P S u q + σ.stage2Platform P S u r i q

/-- The manufacturer's total profit `Π̄ᴹᵢ(q) = Π̄ᴹ_{i,1}(q) + Π̄ᴹ_{i,2}(q)`, SSRN 3886954, p.22. -/
noncomputable def CommissionProfile.profitManufacturer (σ : CommissionProfile) (P : Params)
    (S : Signals Ω) (u : ℝ) (r : Regime) (i : Info) (q : Quality) : ℝ :=
  σ.stage1Manufacturer P S u q + σ.stage2Manufacturer P S u r i q

/-- A family of commission pricing equilibria in a regime, one for each `(i, q)`. -/
def IsCommissionFamily (P : Params) (S : Signals Ω) (u : ℝ) (r : Regime)
    (σ : Info → Quality → CommissionProfile) : Prop :=
  ∀ i q, IsCommissionEq P S u r i q (σ i q)

/-- The profit table of a family of commission profiles in a regime. -/
noncomputable def commissionTable (P : Params) (S : Signals Ω) (u : ℝ) (r : Regime)
    (σ : Info → Quality → CommissionProfile) : ProfitTable where
  manufacturer i q := (σ i q).profitManufacturer P S u r i q
  platform i q := (σ i q).profitPlatform P S u r i q

end ReviewInfoShare


