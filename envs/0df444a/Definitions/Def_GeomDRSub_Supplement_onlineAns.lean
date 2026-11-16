-- Prove2me | Definitions.Def_GeomDRSub_Supplement_onlineAns
-- name    : GeomDRSub_Supplement_onlineAns
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:42:08.01459+00:00
-- url     : https://prove2.me/theorems/a645904c-ec90-4dd9-bb7c-b0446d91113a
-- title:
--   Online oracle answers: queries after the commit of round $t$ refer to $f_t$
-- statement:
--   In the online model the learner commits an action $p_t$ on round $t$ and only then queries the current objective. Let $n$ be the number of actions committed before a call. An objective query at $y\in[0,1]^d$ with $n=t+1$, made after the commit of round $t$, is answered by $(f_t(y),\nabla f_t(y))$. A projection call on $z$ is answered by $\mathrm{proj}(z)$. A commit, and a query made before the first commit (when there is no current objective), receive the uninformative response $0$.
--
--   **Formalization Note** Rounds are numbered from $0$: `f 0` is the paper's $f_1$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 3.2, p.8, and Section 7.2, p.52

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_OCall
import Definitions.Def_GeomDRSub_Supplement_OResp
import Definitions.Def_GeomDRSub_gradQ

namespace GeomDRSub.Supplement

/-- **Online oracle answers.** Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Section 3.2 (p.8): "On round `t`, the learner first
commits an action `p_t ∈ K` and earns `f_t(p_t)`, after which it can query the current objective at
points of `Q`. Every response on that round refers to `f_t`"; Section 7.2 (p.52): "Objective
queries on a round occur after the action for that round has been committed. Each query returns the
full value-and-gradient response".

`onlineAns f proj n c`, where `n` is the number of actions committed before the call `c`: an
objective query at `y` made after the commit of round `t` (that is, `n = t + 1`) is answered by
`(f_t(y), ∇f_t(y))`; a projection call on `z` by `proj z`; a commit, and a query made before the
first commit (no current objective), by the uninformative `Sum.inr 0`.

**Formalization Note.** Rounds are 0-based (`f 0` is the paper's `f_1`). -/
noncomputable def onlineAns {d : ℕ} (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : ℕ → OCall d → OResp d :=
  fun n c =>
    match n, c with
    | 0, Sum.inl _ => Sum.inr 0
    | t + 1, Sum.inl y => Sum.inl (f t y, gradQ (f t) y)
    | _, Sum.inr (Sum.inl z) => Sum.inr (proj z)
    | _, Sum.inr (Sum.inr _) => Sum.inr 0

end GeomDRSub.Supplement


