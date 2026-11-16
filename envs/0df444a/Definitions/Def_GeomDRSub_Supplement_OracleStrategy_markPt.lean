-- Prove2me | Definitions.Def_GeomDRSub_Supplement_OracleStrategy_markPt
-- name    : GeomDRSub_Supplement_OracleStrategy_markPt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:40:58.821672+00:00
-- url     : https://prove2.me/theorems/be1f17d5-a28a-4703-8594-e8428ea8ef26
-- title:
--   The $t$-th emitted point of an execution
-- statement:
--   The $t$-th emitted point ($t=0,1,\dots$) is the point $p$ of the emission $c_k$ made at the unique time $k$ at which exactly $t$ points have been emitted before. Offline, $t=0$ gives the returned point $p$; online, it gives the action $p_t$ of round $t$. If the execution emits fewer than $t+1$ points, the value is $0$.
--
--   **Formalization Note** The default $0$ is never used: the achievability definitions require that the relevant points are emitted on every execution.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Definition 6.1, p.33, and Section 3.2, p.8

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_OracleStrategy_call

namespace GeomDRSub.Supplement

/-- **The `t`-th emitted point** (0-based). Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Definition 6.1 (p.33, the returned
point `p`) and Section 3.2 (p.8, the action `p_t` committed on round `t`).

`A.markPt d x ans ω t` is the point `p` of the call `Sum.inr (Sum.inr p)` made at the (unique) time
`k` at which the call is a mark and exactly `t` marks were emitted before it; it is `0` if the
execution emits fewer than `t + 1` marks.

**Formalization Note.** The default `0` is never used: `OfflineAchievable` and `OnlineAchievable`
require that the relevant marks are emitted on every execution. -/
noncomputable def OracleStrategy.markPt {Ω : Type} [MeasurableSpace Ω] {m : ℕ}
    (A : OracleStrategy Ω m) (d : ℕ) (x : Fin m → ℝ) (ans : ℕ → OCall d → OResp d) (ω : Ω)
    (t : ℕ) : EuclideanSpace ℝ (Fin d) := by
  classical
  exact
    if h : ∃ k, (A.call d x ans ω k).elim (fun _ => false) Sum.isRight = true ∧
        (A.state d x ans ω k).2 = t then
      (A.call d x ans ω (Nat.find h)).elim (fun _ => 0) (fun c => c.elim (fun _ => 0) id)
    else 0

end GeomDRSub.Supplement


