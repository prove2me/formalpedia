-- Prove2me | Definitions.Def_SecondBestMatch_Supplement_IsFullPotentialFeasible
-- name    : SecondBestMatch_Supplement_IsFullPotentialFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:43:12.74492+00:00
-- url     : https://prove2.me/theorems/6bb6068d-6728-4430-a715-b8e8e6f1334a
-- title:
--   Full-potential feasible tuple (Definition A.1)
-- statement:
--   A tuple $\big((x_i)_{i\in B},(y_j)_{j\in S},(U_k)_{k\in K}\big)$ is **full-potential feasible** if $(x,y)\in\mathcal R$ and the following hold.
--
--   1. **(P1)** For every buyer $i$, $U_i:[0,1]\to\mathbb R_{\ge0}$ is convex, nondecreasing and $d_i$-Lipschitz, and $x_i(v)\in\partial_I U_i(v)$ for $F_i$-almost every $v$.
--   2. **(P2)** For every seller $j$, $U_j:[0,1]\to\mathbb R_{\ge0}$ is convex, nonincreasing and $d_j$-Lipschitz, and $-y_j(c)\in\partial_I U_j(c)$ for $G_j$-almost every $c$.
--   3. **(P3)** The interim transfers implied by the potentials balance in expectation:
--
--   $$
--   \sum_{i\in B}\mathbb E_{v_i}\big[v_i x_i(v_i)-U_i(v_i)\big]=\sum_{j\in S}\mathbb E_{c_j}\big[c_j y_j(c_j)+U_j(c_j)\big].\qquad(16)
--   $$
--
--   Here $d_k$ is the activity indicator and $\partial_I$ is the subdifferential relative to $[0,1]$. The potentials are the agents' interim utilities. (P1) and (P2) encode Bayesian incentive compatibility and interim individual rationality on the full report domain, and (P3) is expected budget balance.
--
--   **Formalization Note** Potentials are functions $\mathbb R\to\mathbb R$ constrained only on $[0,1]$: nonnegative there, `ConvexOn`, `MonotoneOn`/`AntitoneOn` and `LipschitzOnWith d_k` on `Icc 0 1`. The expectations in (P3) are integrals against the marginal priors `m.buyerLaw i`, `m.sellerLaw j`. On an instance with priors on $[0,1]$ the integrands are bounded and almost everywhere measurable, so these are genuine integrals.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea7cce1bbfc7757c56937ec4ac13847b6d0025758a63fa8d6a25314385), Definition A.1, p.27 (eq. (16))

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_Supplement_activityBound
import Definitions.Def_SecondBestMatch_Supplement_relSubdiff
import Definitions.Def_SecondBestMatch_Supplement_InReducedForms
import Definitions.Def_SecondBestMatch_Supplement_FullPotentialTuple

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch.Supplement

/-- **Full-potential feasibility** (Definition A.1, Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), p.27). The tuple
`((xᵢ), (yⱼ), (U_k))` is full-potential feasible if `(x, y) ∈ ℛ` and
* (P1) every buyer potential `Uᵢ : [0, 1] → ℝ≥0` is convex, nondecreasing and `dᵢ`-Lipschitz, and
  `xᵢ(v) ∈ ∂_I Uᵢ(v)` for `Fᵢ`-almost every `v`;
* (P2) every seller potential `Uⱼ : [0, 1] → ℝ≥0` is convex, nonincreasing and `dⱼ`-Lipschitz,
  and `−yⱼ(c) ∈ ∂_I Uⱼ(c)` for `Gⱼ`-almost every `c`;
* (P3) `Σᵢ E_{vᵢ}[vᵢ xᵢ(vᵢ) − Uᵢ(vᵢ)] = Σⱼ E_{cⱼ}[cⱼ yⱼ(cⱼ) + Uⱼ(cⱼ)]` (16).

**Formalization Note** Potentials are functions `ℝ → ℝ` constrained on `[0, 1]` only:
nonnegative there, `ConvexOn`, `MonotoneOn`/`AntitoneOn` and `LipschitzOnWith d_k` on
`Icc 0 1`. The expectations in (P3) are integrals against the marginal priors `Fᵢ = m.buyerLaw i`
and `Gⱼ = m.sellerLaw j`; on an instance with priors on `[0, 1]` the integrands are bounded and
almost everywhere measurable (the service rules agree a.e. with interim service rules, the
potentials are continuous on `[0, 1]`), so these are genuine integrals. -/
def IsFullPotentialFeasible {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (τ : FullPotentialTuple B S) : Prop :=
  InReducedForms m τ.x τ.y ∧
  (∀ i : B,
    (∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ τ.U (Sum.inl i) v) ∧
    ConvexOn ℝ (Icc (0 : ℝ) 1) (τ.U (Sum.inl i)) ∧
    MonotoneOn (τ.U (Sum.inl i)) (Icc (0 : ℝ) 1) ∧
    LipschitzOnWith (activityBound m (Sum.inl i)) (τ.U (Sum.inl i)) (Icc (0 : ℝ) 1) ∧
    ∀ᵐ v ∂m.buyerLaw i, τ.x i v ∈ relSubdiff (τ.U (Sum.inl i)) v) ∧
  (∀ j : S,
    (∀ c ∈ Icc (0 : ℝ) 1, 0 ≤ τ.U (Sum.inr j) c) ∧
    ConvexOn ℝ (Icc (0 : ℝ) 1) (τ.U (Sum.inr j)) ∧
    AntitoneOn (τ.U (Sum.inr j)) (Icc (0 : ℝ) 1) ∧
    LipschitzOnWith (activityBound m (Sum.inr j)) (τ.U (Sum.inr j)) (Icc (0 : ℝ) 1) ∧
    ∀ᵐ c ∂m.sellerLaw j, -τ.y j c ∈ relSubdiff (τ.U (Sum.inr j)) c) ∧
  ∑ i, ∫ v, (v * τ.x i v - τ.U (Sum.inl i) v) ∂m.buyerLaw i =
    ∑ j, ∫ c, (c * τ.y j c + τ.U (Sum.inr j) c) ∂m.sellerLaw j

end SecondBestMatch.Supplement


