-- Prove2me | Definitions.Def_BanditCovariates_ABSE_ProofObjects
-- name    : BanditCovariates_ABSE_ProofObjects
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:09:47.609284+00:00
-- url     : https://prove2.me/theorems/1f482e7b-e3ff-46b2-bb2b-7904badcadad
-- title:
--   §5 — live and born regret of a cell, and the conditional margin mass q_B
-- statement:
--   Fix the ABSE run on a sample path. A cell $B$ is *live* at time $t$ if it belongs to the current partition $L_t$, and *born by* $t$ if it belonged to some $L_s$, $s\le t$. The live and born regrets of $B$ are the pathwise sums
--
--   $$r_n^{\mathrm{live}}(B)=\sum_{t=1}^n\big[f^\star(X_t)-f^{(\tilde\pi_t(X_t))}(X_t)\big]\mathbf 1(X_t\in B)\mathbf 1(B\in L_t),$$
--
--   $$r_n^{\mathrm{born}}(B)=\sum_{t=1}^n\big[f^\star(X_t)-f^{(\tilde\pi_t(X_t))}(X_t)\big]\mathbf 1(X_t\in B)\mathbf 1(B\text{ born by }t).$$
--
--   The conditional margin mass of a cell is
--
--   $$q_B=P_X\big(0<f^\star-f^\sharp\le c_1|B|^\beta\,\big|\,X\in B\big)=\frac{P_X(\{0<f^\star-f^\sharp\le c_1|B|^\beta\}\cap B)}{P_X(B)},\qquad c_1=2^{3+\beta}c_0.$$
--
--   These quantities organize the regret along the adaptive tree, as in (5.5) and the display before (5.6).
--
--   **Formalization Note** Time starts at $0$ in Lean. The run used is the one of the `Policy` definition, which reads only the covariates and the rewards of the chosen arms.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, pp. 23–25, definitions preceding (5.5) and q_B before (5.6)

import Mathlib
import Definitions.Def_BanditCovariates_ABSE_Policy

noncomputable section

namespace BanditCovariates.ABSE

attribute [local instance] Classical.propDecidable

/-- Whether a cell has appeared in the live partition by time t. -/
def bornBy {d K n : ℕ} {Ω : Type*} (hK : 0 < K) (β L : ℝ)
    (X : ℕ → Ω → Covariate d) (Y : ℕ → Ω → Fin K → ℝ)
    (B : Cell d) (t : ℕ) (ω : Ω) : Prop :=
  ∃ s ≤ t, ((stateAt (n := n) hK β L X Y s ω) B).isSome

/-- The pathwise regret charged to B while B is live. -/
def liveRegret {d K n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Machine d K Ω) (hK : 0 < K) (β L : ℝ)
    (B : Cell d) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range n,
    if M.X t ω ∈ cellSet B ∧
      ((stateAt (n := n) hK β L M.X M.Y t ω) B).isSome then
      fStar M (M.X t ω) -
        M.f (abse (n := n) hK β L M.X M.Y t ω) (M.X t ω)
    else 0

/-- The pathwise regret charged to B after its birth, including descendants. -/
def bornRegret {d K n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Machine d K Ω) (hK : 0 < K) (β L : ℝ)
    (B : Cell d) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range n,
    if M.X t ω ∈ cellSet B ∧
      bornBy (n := n) hK β L M.X M.Y B t ω then
      fStar M (M.X t ω) -
        M.f (abse (n := n) hK β L M.X M.Y t ω) (M.X t ω)
    else 0

/-- The conditional margin mass of a cell (p. 25):
`q_B = P_X(0 < f⋆ − f♯ ≤ c₁|B|^β | X ∈ B)`, with `c₁ = 2^{3+β} c₀`. -/
def qB {d K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Machine d K Ω) (β L : ℝ) (B : Cell d) : ℝ :=
  (M.PX ({x | 0 < fStar M x - fSharp M x ∧
      fStar M x - fSharp M x ≤ c1 d β L * side B ^ β} ∩ cellSet B)).toReal /
    (M.PX (cellSet B)).toReal

end BanditCovariates.ABSE


