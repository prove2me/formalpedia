-- Prove2me | Definitions.Def_OfflineStochMatching_UnitPatience_algValue
-- name    : OfflineStochMatching_UnitPatience_algValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:35:43.347472+00:00
-- url     : https://prove2.me/theorems/817571a9-376f-47a9-9c0c-2242b83ca56a
-- title:
--   Expected weight $\mathbb E[\mathrm{ALG}]$ matched by the algorithm of Section 4
-- statement:
--   The expected weight matched by the algorithm of Section 4 is
--
--   $$
--   \mathbb E[\mathrm{ALG}]=\mathbb E\Big[\sum_{v\in V_2}W(v)\Big]=\sum_{Y}\sum_{P}\mu(Y)\,\Pr[P]\sum_{v\in V_2}W(v)(Y,P),
--   $$
--
--   with $Y\sim\mu$ the rounded vector and $P$ the independent activeness realization. It is the quantity bounded in Theorem 2.
--
--   **Formalization Note** A finite sum over $\{0,1\}^E\times\{0,1\}^E$; no measure theory.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §4, p. 16 (E[ALG] := E[Σ_{v∈V2} W(v)] = Σ_{v∈V2} E[W(v)])

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_activeProb
import Definitions.Def_OfflineStochMatching_UnitPatience_starWeight

namespace OfflineStochMatching.UnitPatience

/-- **The expected weight `E[ALG]` matched by the algorithm of §4.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §4, p. 16: "The expected value
achieved by this strategy is `E[ALG] := E[Σ_{v∈V2} W(v)] = Σ_{v∈V2} E[W(v)]`".

`algValue G V2 σ μ = Σ_Y Σ_P μ(Y) · Pr[P] · Σ_{v∈V2} W(v)(Y, P)`, with `Y ∼ μ` the rounded
vector, `P` the independent activeness realization and `W(v)` = `starWeight`.

**Formalization Note.** A finite sum over `{0,1}^E × {0,1}^E`; no measure theory. -/
def algValue {V E : Type*} [Fintype E] [DecidableEq E] (G : StochGraph V E) (V2 : Finset V)
    (σ : V → List E) (μ : (E → Bool) → ℝ) : ℝ :=
  ∑ Y : E → Bool, ∑ P : E → Bool, μ Y * activeProb G P * ∑ v ∈ V2, starWeight G σ Y P v

end OfflineStochMatching.UnitPatience


