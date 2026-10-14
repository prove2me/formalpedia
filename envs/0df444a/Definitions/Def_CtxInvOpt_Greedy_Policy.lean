-- Prove2me | Definitions.Def_CtxInvOpt_Greedy_Policy
-- name    : CtxInvOpt_Greedy_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:15.645995+00:00
-- url     : https://prove2.me/theorems/be8ec945-40f4-463d-b7c8-5b19118d3fa6
-- title:
--   §4.1, p. 13 — runs of the greedy circumcenter policy π_greedy
-- statement:
--   The **greedy circumcenter policy** applies, in every period, the offline circumcenter policy to the current knowledge set:
--
--   $$\pi_{greedy}=\big\{x^\pi_t\in\psi\big(\hat c(C(\mathcal I_t)),\mathcal X_t,f_t\big),\ \text{for every } t\le T\big\}.$$
--
--   A **run** of the policy against an initial knowledge set $C_0$, a true cost $c^\star$ and nature's sequences $(\mathcal X_t)$, $(f_t)$ consists of sequences $\hat c_t$, $x^\pi_t$, $x^\star_t$ such that, in every period $t$,
--
--   1. $\hat c_t$ is a circumcenter of the current knowledge set $C(\mathcal I_t)$;
--   2. the policy's action $x^\pi_t$ minimizes $f_t(x)'\hat c_t$ over $\mathcal X_t$;
--   3. the revealed expert action $x^\star_t$ minimizes $f_t(x)'c^\star$ over $\mathcal X_t$.
--
--   Every choice of circumcenter and every tie-break among minimizers gives a run, and nature's sequences are arbitrary, so statements about all runs cover every adaptive adversary.
--
--   **Formalization Note** Periods are $0$-based (Lean period $t$ is the paper's $t+1$) and the run condition is imposed in every period $t\in\mathbb N$; only the periods $t<T$ enter the regret over horizon $T$.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 13, §4.1 (definition of π_greedy)

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry
import Definitions.Def_CtxInvOpt_Greedy_Online

namespace CtxInvOpt.Greedy

/-- **§4.1, p. 13.** A run of the greedy circumcenter policy
`π_greedy = { x^π_t ∈ ψ(ĉ(C(I_t)), X_t, f_t), for every t ≤ T }` against nature's sequences
`X`, `f` and the true cost `cstar`.

In every (0-based) period `t`:
* `chat t` is a circumcenter (Definition 2) of the current knowledge set (5),
  `knowledgeSet C0 X f xstar t` (the paper's `C(I_{t+1})`);
* the policy's action `xpi t` minimizes `f t (x)′ chat t` over `X t` (any minimizer);
* the expert action `xstar t` minimizes `f t (x)′ cstar` over `X t` (any minimizer), and it is
  revealed, so it enters the later knowledge sets.

Nature's sequences are arbitrary, and every circumcenter choice and every tie-break is a run. -/
def IsGreedyRun {n d : ℕ} (C0 : Set (EuclideanSpace ℝ (Fin d))) (cstar : EuclideanSpace ℝ (Fin d))
    (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
    (xpi xstar : ℕ → EuclideanSpace ℝ (Fin n)) (chat : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ t, CtxInvOpt.Offline.IsCircumcenter (knowledgeSet C0 X f xstar t) (chat t) ∧
    xpi t ∈ CtxInvOpt.Offline.argminSet (chat t) (X t) (f t) ∧ xstar t ∈ CtxInvOpt.Offline.argminSet cstar (X t) (f t)

end CtxInvOpt.Greedy


