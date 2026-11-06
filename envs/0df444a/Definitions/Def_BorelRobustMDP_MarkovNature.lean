-- Prove2me | Definitions.Def_BorelRobustMDP_MarkovNature
-- name    : BorelRobustMDP_MarkovNature
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:05.36286+00:00
-- url     : https://prove2.me/theorems/b0dcb38e-57fc-4695-a228-ec43ca3ac612
-- title:
--   Markov policies of nature $\Gamma^M$
-- statement:
--   A **Markov decision rule of nature** at time $n$ is a measurable map $\gamma_n:D_n\to\mathcal Q_{n+1}$, and a **Markov policy of nature** is a sequence $\gamma=(\gamma_0,\dots,\gamma_{N-1})$ of such rules.
--
--   **Formalization Note.** The rules are total on $E\times A$; only their values on $D_n$ enter a value.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, pp.4–5

import Mathlib
import Definitions.Def_BorelRobustMDP_RobustModel

open MeasureTheory

namespace BorelRobustMDP

universe u v

variable {E A : Type u} {Z : Type v} [MeasurableSpace E] [MeasurableSpace A] [MeasurableSpace Z]
  {N : ℕ}

/-- A Markov policy of nature `γ = (γ_0, …, γ_{N−1}) ∈ Γ^M` (Bäuerle & Glauner, arXiv:2007.13103v1,
p.4): measurable maps `γ_n : D_n → 𝒬_{n+1}`.

**Formalization Note.** The rules are total on `E × A`; a measurable map on the measurable set `D_n`
extends by a constant, and only values on `D_n` enter a value. -/
structure MarkovNature (R : RobustModel E A Z N) where
  rule : (n : Fin N) → E × A → R.Amb (n + 1)
  measurable_rule : ∀ n, Measurable (rule n)

/-- The law of the disturbance at time `k` in state-action pair `y`, `0` beyond the horizon, where
it is never used. -/
noncomputable def MarkovNature.act {R : RobustModel E A Z N} (γ : MarkovNature R) (k : ℕ)
    (y : E × A) : Measure Z :=
  if hk : k < N then (γ.rule ⟨k, hk⟩ y).measure else 0

end BorelRobustMDP


