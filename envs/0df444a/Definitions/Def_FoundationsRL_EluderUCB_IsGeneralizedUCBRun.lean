-- Prove2me | Definitions.Def_FoundationsRL_EluderUCB_IsGeneralizedUCBRun
-- name    : FoundationsRL_EluderUCB_IsGeneralizedUCBRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:21:41.529441+00:00
-- url     : https://prove2.me/theorems/25ea8100-dc54-4513-876b-73e0ec0010df
-- title:
--   (4.4)–(4.6): the generalized UCB algorithm on one sample path
-- statement:
--   A sample path $(\pi^t,r^t)_{t\le T}$ with functions $\hat f^t$ is a run of generalized UCB with parameter $\beta$ if for each $t\in[T]$, $\hat f^t$ is an empirical minimizer (4.4) and
--
--   $$
--   \pi^t=\arg\max_{\pi\in\Pi}\bar f^t(\pi),
--   $$
--
--   with $\bar f^t$ computed from the confidence set (4.5).
--
--   **Formalization Note** On an arbitrary $\Pi$ the source's notation presupposes that the maximizer exists. Here it is part of the run, and every tie-breaking rule is allowed.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (4.4)–(4.6), p. 58

import Mathlib
import Definitions.Def_FoundationsRL_EluderUCB_IsEmpiricalMinimizer
import Definitions.Def_FoundationsRL_EluderUCB_ucbIndex

namespace FoundationsRL.EluderUCB

/-- **The generalized UCB algorithm, on one sample path.** Foster & Rakhlin, arXiv:2312.16730v1,
(4.4)–(4.6), p. 58: on each round `t ∈ [T]`, `f̂ᵗ` is an empirical minimizer and
`πᵗ = argmax_{π ∈ Π} f̄ᵗ(π)`.

**Formalization Note.** The maximizer `πᵗ` is presupposed by the source's notation on an arbitrary
`Π`: it is a hypothesis of the run, not a construction, and every tie-breaking rule is allowed. -/
def IsGeneralizedUCBRun {Act : Type*} (F : Set (Act → ℝ)) (β : ℝ) (T : ℕ) (π : ℕ → Act)
    (r : ℕ → ℝ) (fhat : ℕ → Act → ℝ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, IsEmpiricalMinimizer F π r t (fhat t) ∧
    ∀ p, ucbIndex F β π r t (fhat t) p ≤ ucbIndex F β π r t (fhat t) (π t)

end FoundationsRL.EluderUCB


