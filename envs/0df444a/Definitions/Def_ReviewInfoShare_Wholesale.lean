-- Prove2me | Definitions.Def_ReviewInfoShare_Wholesale
-- name    : ReviewInfoShare_Wholesale
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:39:39.65633+00:00
-- url     : https://prove2.me/theorems/ebb3a73e-a3a9-4fc4-b069-5477427c92e9
-- title:
--   Wholesale price contract — backward-induction pricing equilibrium and profits, §3.1
-- statement:
--   The pricing game of the wholesale price contract, for fixed regime, arrangement $i$ and quality $q$. Demand is $d_1=\alpha+\theta q-p_1$ and $d_2=\alpha+\theta\hat q_2-p_2$.
--
--   1. **Second stage.** For every wholesale price $w$, estimate $t$ and belief $z$, the platform's retail price maximizes $(p-w)(\alpha+tz-p)$; call it $p_2(w;t,z)$. For every $t,z$ the manufacturer's wholesale price $w_2(t,z)$ maximizes $(w-c_q)(\alpha+tz-p_2(w;t,z))$.
--   2. **On the path.** $w_2^*=w_2(\tilde\theta,\hat q_2)$, with $\tilde\theta=\hat\theta$ under sharing and $\tilde\theta=\mu_\theta$ otherwise, and $p_2^*=p_2(w_2^*;\hat\theta,\hat q_2)$, since the platform holds the signal in both cases. The second-stage profits are
--   $$
--   \Pi^P_{i,2}(q)=E[(p_2^*-w_2^*)(\alpha+\theta\hat q_2-p_2^*)],\qquad \Pi^M_{i,2}(q)=E[(w_2^*-c_q)(\alpha+\theta\hat q_2-p_2^*)].
--   $$
--   3. **First stage.** $p_1(w)$ maximizes $(p-w)(\alpha+\mu_\theta q-p)+\Pi^P_{i,2}(q)$ for every $w$, and $w_1^*$ maximizes $(w-c_q)(\alpha+\mu_\theta q-p_1(w))+\Pi^M_{i,2}(q)$. With $p_1^*=p_1(w_1^*)$,
--   $$
--   \Pi^P_{i,1}(q)=E[(p_1^*-w_1^*)(\alpha+\theta q-p_1^*)],\qquad \Pi^M_{i,1}(q)=E[(w_1^*-c_q)(\alpha+\theta q-p_1^*)].
--   $$
--   4. **Totals.** $\Pi^k_i(q)=\Pi^k_{i,1}(q)+\Pi^k_{i,2}(q)$. A family of equilibria, one for each $(i,q)$, gives a table of profits for the fee game.
--
--   No price or profit is defined by a closed form: the formulas (5), (6), (38), (39) are theorems about these predicates.
--
--   **Formalization Note** The plain $c$ of p.14 is $c_q$. Without sharing the manufacturer solves its problem at $t=\mu_\theta$: it does not observe $\hat\theta$, and p.14's $p_2(w)$ is read with $\hat\theta$ replaced by its mean, which is what gives (5). Prices are maximizers of `IsMaxOn` over all of $\mathbb R$, so demand is not constrained to be positive, as in the paper's first-order analysis.
-- source:
--   Shin–Zeevi, Product Quality and Information Sharing in the Presence of Reviews, SSRN 3886954, §3.1, p.14; demand (1), p.9, (3), p.10

import Mathlib
import Definitions.Def_ReviewInfoShare_Model
import Definitions.Def_ReviewInfoShare_FeeGame

open MeasureTheory

namespace ReviewInfoShare

/-- A pricing profile of the wholesale price contract, SSRN 3886954, §3.1, p.14: the platform's
second-stage retail price `p₂ w t z` given the wholesale price `w`, its estimate `t` of `θ` and the
quality belief `z`; the manufacturer's second-stage wholesale price `w₂ t z`, with `t` its own
estimate of `θ`; the platform's first-stage retail price `p₁ w`; the first-stage wholesale price
`w₁`. -/
structure WholesaleProfile where
  p₂ : ℝ → ℝ → ℝ → ℝ
  w₂ : ℝ → ℝ → ℝ
  p₁ : ℝ → ℝ
  w₁ : ℝ

/-- Second-stage subgame perfection, SSRN 3886954, p.14: `p₂(w) = arg max_p (p − w)(α + t z − p)`
and `w₂ = arg max_w (w − c_q)(α + t z − p₂(w))`, for every estimate `t` and belief `z`.

**Formalization Note.** The `c` of p.14 is `c_q`. With sharing, `t = θ̂` on the path. Without sharing
the manufacturer solves the same problem at `t = µ_θ`: it does not observe `θ̂`, and p.14's
`p₂(w)` is read at the mean of `θ̂`, which gives (5). -/
def IsWholesaleStage2Eq (P : Params) (q : Quality) (p₂ : ℝ → ℝ → ℝ → ℝ) (w₂ : ℝ → ℝ → ℝ) : Prop :=
  (∀ w t z, IsMaxOn (fun p => (p - w) * (P.α + t * z - p)) Set.univ (p₂ w t z)) ∧
  (∀ t z, IsMaxOn (fun w => (w - P.cost q) * (P.α + t * z - p₂ w t z)) Set.univ (w₂ t z))

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The realized second-stage wholesale price `w₂*`: the manufacturer prices on its estimate
`θ̃` and on `q̂₂`, SSRN 3886954, p.14. -/
noncomputable def WholesaleProfile.w2Star (σ : WholesaleProfile) (P : Params) (S : Signals Ω)
    (r : Regime) (i : Info) (q : Quality) (ω : Ω) : ℝ :=
  σ.w₂ (estimate P S i ω) (qHat2 P S r q ω)

/-- The realized second-stage retail price `p₂*`: the platform, which holds the signal under both
arrangements, prices on `θ̂` and `q̂₂`, SSRN 3886954, p.14. -/
noncomputable def WholesaleProfile.p2Star (σ : WholesaleProfile) (P : Params) (S : Signals Ω)
    (r : Regime) (i : Info) (q : Quality) (ω : Ω) : ℝ :=
  σ.p₂ (σ.w2Star P S r i q ω) (thetaHat P S ω) (qHat2 P S r q ω)

/-- The platform's second-stage profit `Πᴾ_{i,2}(q) = E[(p₂* − w₂*)(α + θ q̂₂ − p₂*)]`, demand (3),
SSRN 3886954, p.14. -/
noncomputable def WholesaleProfile.stage2Platform (σ : WholesaleProfile) (P : Params)
    (S : Signals Ω) (r : Regime) (i : Info) (q : Quality) : ℝ :=
  ∫ ω, (σ.p2Star P S r i q ω - σ.w2Star P S r i q ω) *
    (P.α + S.θ ω * qHat2 P S r q ω - σ.p2Star P S r i q ω) ∂S.prob

/-- The manufacturer's second-stage profit `Πᴹ_{i,2}(q) = E[(w₂* − c_q)(α + θ q̂₂ − p₂*)]`,
SSRN 3886954, p.14. -/
noncomputable def WholesaleProfile.stage2Manufacturer (σ : WholesaleProfile) (P : Params)
    (S : Signals Ω) (r : Regime) (i : Info) (q : Quality) : ℝ :=
  ∫ ω, (σ.w2Star P S r i q ω - P.cost q) *
    (P.α + S.θ ω * qHat2 P S r q ω - σ.p2Star P S r i q ω) ∂S.prob

/-- First-stage subgame perfection, SSRN 3886954, p.14:
`p₁(w) = arg max_p (p − w)(α + µ_θ q − p) + Πᴾ_{i,2}(q)` and
`w₁* = arg max_w (w − c_q)(α + µ_θ q − p₁(w)) + Πᴹ_{i,2}(q)`. -/
def IsWholesaleStage1Eq (P : Params) (S : Signals Ω) (r : Regime) (i : Info) (q : Quality)
    (σ : WholesaleProfile) : Prop :=
  (∀ w, IsMaxOn (fun p => (p - w) * (P.α + P.μ * P.qual q - p) + σ.stage2Platform P S r i q)
    Set.univ (σ.p₁ w)) ∧
  IsMaxOn (fun w => (w - P.cost q) * (P.α + P.μ * P.qual q - σ.p₁ w) +
    σ.stage2Manufacturer P S r i q) Set.univ σ.w₁

/-- A pricing equilibrium of the wholesale price contract for fixed regime, information arrangement
and quality: backward induction over both stages, SSRN 3886954, §3.1, p.14. -/
def IsWholesaleEq (P : Params) (S : Signals Ω) (r : Regime) (i : Info) (q : Quality)
    (σ : WholesaleProfile) : Prop :=
  IsWholesaleStage2Eq P q σ.p₂ σ.w₂ ∧ IsWholesaleStage1Eq P S r i q σ

/-- The platform's first-stage profit `Πᴾ_{i,1}(q) = E[(p₁* − w₁*)(α + θ q − p₁*)]`, with
`p₁* = p₁(w₁*)`, demand (1), SSRN 3886954, p.14. -/
noncomputable def WholesaleProfile.stage1Platform (σ : WholesaleProfile) (P : Params)
    (S : Signals Ω) (q : Quality) : ℝ :=
  ∫ ω, (σ.p₁ σ.w₁ - σ.w₁) * (P.α + S.θ ω * P.qual q - σ.p₁ σ.w₁) ∂S.prob

/-- The manufacturer's first-stage profit `Πᴹ_{i,1}(q) = E[(w₁* − c_q)(α + θ q − p₁*)]`,
SSRN 3886954, p.14. -/
noncomputable def WholesaleProfile.stage1Manufacturer (σ : WholesaleProfile) (P : Params)
    (S : Signals Ω) (q : Quality) : ℝ :=
  ∫ ω, (σ.w₁ - P.cost q) * (P.α + S.θ ω * P.qual q - σ.p₁ σ.w₁) ∂S.prob

/-- The platform's total profit `Πᴾᵢ(q) = Πᴾ_{i,1}(q) + Πᴾ_{i,2}(q)`, SSRN 3886954, p.12. -/
noncomputable def WholesaleProfile.profitPlatform (σ : WholesaleProfile) (P : Params)
    (S : Signals Ω) (r : Regime) (i : Info) (q : Quality) : ℝ :=
  σ.stage1Platform P S q + σ.stage2Platform P S r i q

/-- The manufacturer's total profit `Πᴹᵢ(q) = Πᴹ_{i,1}(q) + Πᴹ_{i,2}(q)`, SSRN 3886954, p.12. -/
noncomputable def WholesaleProfile.profitManufacturer (σ : WholesaleProfile) (P : Params)
    (S : Signals Ω) (r : Regime) (i : Info) (q : Quality) : ℝ :=
  σ.stage1Manufacturer P S q + σ.stage2Manufacturer P S r i q

/-- A family of wholesale pricing equilibria in a regime, one for each `(i, q)`. -/
def IsWholesaleFamily (P : Params) (S : Signals Ω) (r : Regime)
    (σ : Info → Quality → WholesaleProfile) : Prop :=
  ∀ i q, IsWholesaleEq P S r i q (σ i q)

/-- The profit table of a family of wholesale profiles in a regime. -/
noncomputable def wholesaleTable (P : Params) (S : Signals Ω) (r : Regime)
    (σ : Info → Quality → WholesaleProfile) : ProfitTable where
  manufacturer i q := (σ i q).profitManufacturer P S r i q
  platform i q := (σ i q).profitPlatform P S r i q

end ReviewInfoShare


