-- Prove2me | Definitions.Def_NonstatNV_Model_IsPolicy
-- name    : NonstatNV_Model_IsPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:39.762103+00:00
-- url     : https://prove2.me/theorems/4719eb18-04d7-4d6d-b2f4-455c720ea75c
-- title:
--   Deterministic nonanticipating policy with orders in $Q$
-- statement:
--   A **policy** for horizon $T$ assigns to every period $t\in\{1,\dots,T\}$ and every demand path $\omega$ an order $q_t(\omega)$ such that
--
--   1. $q_t(\omega)\in Q$;
--   2. $q_t$ is measurable;
--   3. $q_t(\omega)$ depends only on the past demands $\omega_1,\dots,\omega_{t-1}$.
--
--   This is the paper's notion of a policy as a sequence of mappings from $d_1,\dots,d_{t-1}$ (and the deterministic predictions $a_1,\dots,a_t$, which are fixed data) to $Q$.
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, §2.3, p.14; §4.1, p.20

import Definitions.Def_NonstatNV_Model

namespace NonstatNV

/-- A (deterministic) policy over the horizon `{1, …, T}` (An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, §2.3, p.14, and §4.1, p.20):
the order `q_t` is a mapping from the past demands `d_1, …, d_{t−1}` (and the deterministic
predictions, which are fixed data) to `Q`. Here `q t ω` is the order of period `t` on the demand
path `ω`; for `1 ≤ t ≤ T` it lies in `Q`, is measurable, and depends only on `ω 1, …, ω (t−1)`. -/
def Model.IsPolicy (M : Model) (T : ℕ) (q : ℕ → (ℕ → ℝ) → ℝ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, Measurable (q t) ∧ (∀ ω, q t ω ∈ M.Q) ∧
    ∀ ω ω' : ℕ → ℝ, (∀ s, 1 ≤ s → s < t → ω s = ω' s) → q t ω = q t ω'

end NonstatNV


