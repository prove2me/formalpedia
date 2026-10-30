-- Prove2me | Definitions.Def_OfflineStochMatching_UnitPatience_expectStar
-- name    : OfflineStochMatching_UnitPatience_expectStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:34:37.303288+00:00
-- url     : https://prove2.me/theorems/3d73de5a-d38d-4eee-93e7-30e72e02fc9b
-- title:
--   Expected weight $\mathbb E[W(v)]$ matched at a vertex of $V_2$
-- statement:
--   The expected weight matched at $v$ is
--
--   $$
--   \mathbb E[W(v)]=\sum_{Y\in\{0,1\}^E}\ \sum_{P\in\{0,1\}^E}\mu(Y)\,\Pr[P]\,W(v)(Y,P),
--   $$
--
--   where the rounded vector $Y$ is drawn from the rounding distribution $\mu$ and the activeness realization $P$ independently of $Y$, with independent edges. It is the left-hand side of Lemmas 7 and 9.
--
--   **Formalization Note** A finite sum over $\{0,1\}^E\times\{0,1\}^E$; no measure theory.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §4, p. 16 (E[W(v)], Lemma 7); p. 17 (independence of the P_j from the Y_j′); p. 18 (Lemma 9)

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_activeProb
import Definitions.Def_OfflineStochMatching_UnitPatience_starWeight

namespace OfflineStochMatching.UnitPatience

/-- **The expected weight `E[W(v)]` matched at a vertex of `V2`.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §4, p. 16 (`E[W(v)]`, Lemma 7)
and p. 18 (Lemma 9); proof of Lemma 7, p. 17: "the independence of each `P_j` from both `P_j′`
(for all `j′ ≠ j`) and from `Y_j′` for all `j′`".

`expectStar G σ μ v = Σ_Y Σ_P μ(Y) · Pr[P] · W(v)(Y, P)`: the rounded vector `Y` is drawn from
`μ`, the activeness realization `P` independently of `Y` with independent edges
(`activeProb`), and `W(v)` is `starWeight`.

**Formalization Note.** A finite sum over `{0,1}^E × {0,1}^E`; no measure theory. -/
def expectStar {V E : Type*} [Fintype E] [DecidableEq E] (G : StochGraph V E)
    (σ : V → List E) (μ : (E → Bool) → ℝ) (v : V) : ℝ :=
  ∑ Y : E → Bool, ∑ P : E → Bool, μ Y * activeProb G P * starWeight G σ Y P v

end OfflineStochMatching.UnitPatience


