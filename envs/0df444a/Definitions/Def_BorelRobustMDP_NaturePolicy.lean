-- Prove2me | Definitions.Def_BorelRobustMDP_NaturePolicy
-- name    : BorelRobustMDP_NaturePolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:04.135659+00:00
-- url     : https://prove2.me/theorems/38c2daee-73d9-4d76-a74c-ba855bbfb9a0
-- title:
--   Policies of nature $\Gamma$
-- statement:
--   A **policy of nature** is a sequence $\gamma=(\gamma_0,\dots,\gamma_{N-1})$ of decision rules $\gamma_n:\mathcal H_n\times A\to\mathcal Q_{n+1}$: nature reacts to the controller's action $a_n$ in scenario $h_n$. The rules are measurable for the Borel σ-algebra of the weak* topology.
--
--   **Formalization Note.** The paper uses this measurability in the proof of Lemma 2.4. The rules are defined on raw histories. The helper `NaturePolicy.act` returns the law of the disturbance, and $0$ beyond the horizon, where it is unused.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, pp.4–5

import Mathlib
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BorelRobustMDP_RobustModel

open MeasureTheory
open MDPFinance.Bellman (Hist)

namespace BorelRobustMDP

universe u v

variable {E A : Type u} {Z : Type v} [MeasurableSpace E] [MeasurableSpace A] [MeasurableSpace Z]
  {N : ℕ}

/-- A policy of nature `γ = (γ_0, …, γ_{N−1}) ∈ Γ` (Bäuerle & Glauner, arXiv:2007.13103v1, pp.4–5):
measurable decision rules `γ_n : 𝓗_n × A → 𝒬_{n+1}`, for the Borel σ-algebra of the weak* topology.

**Formalization Note.** The paper does not repeat "measurable" for these rules, but Lemma 2.4 and
its proof (p.24) compose them with a Borel map. They are defined on raw histories: a measurable rule
on `𝓗_n × A` extends by a constant, as `𝓗_n` is measurable and `𝒬_{n+1}` non-empty. -/
structure NaturePolicy (R : RobustModel E A Z N) where
  rule : (n : Fin N) → Hist E A n × A → R.Amb (n + 1)
  measurable_rule : ∀ n, Measurable (rule n)

/-- The law of the disturbance at time `k` given history and action, `0` beyond the horizon, where
it is never used. -/
noncomputable def NaturePolicy.act {R : RobustModel E A Z N} (γ : NaturePolicy R) (k : ℕ)
    (w : Hist E A k × A) : Measure Z :=
  if hk : k < N then (γ.rule ⟨k, hk⟩ w).measure else 0

end BorelRobustMDP


