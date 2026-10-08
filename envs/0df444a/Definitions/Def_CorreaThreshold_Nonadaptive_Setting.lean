-- Prove2me | Definitions.Def_CorreaThreshold_Nonadaptive_Setting
-- name    : CorreaThreshold_Nonadaptive_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:04.749288+00:00
-- url     : https://prove2.me/theorems/1e4e080d-31a8-47ce-aed5-cde4f17f1c19
-- title:
--   §1.4, p. 1455 — strict threshold acceptance and the 0/0 = 0 reward ratio
-- statement:
--   Fix $n\ge 1$ real observations $X_1,\ldots,X_n$ and fixed thresholds $\tau_i\in[0,\infty]$. The accepted set contains precisely those indices with $X_i>\tau_i$. The reward associated with a realized set is its average prize:
--
--   $$R_\tau(X)=\frac{\sum_{i:X_i>\tau_i}X_i}{|\{i:X_i>\tau_i\}|},\qquad 0/0:=0.$$
--
--   Under a uniformly random arrival order, this is the conditional expected reward of taking the first observation that crosses its threshold. The definition is the objective in Theorem 1.
--
--   **Formalization Note** Indices are 0-based. Thresholds are extended nonnegative reals so $\tau_i=\infty$ can exclude an observation, as in the paper's proof. The ratio is computed in real numbers before taking a nonnegative expectation; real division sets $0/0=0$. The maximum $X^*$ is imported from the published `SamuelCahnProphet.Median.Setting` definition.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), pp. 1454–1455, §1.2 and Theorem 1; https://doi.org/10.1287/moor.2020.1105

import Mathlib
import Definitions.Def_SamuelCahnProphet_Median_Setting

namespace CorreaThreshold.Nonadaptive

open MeasureTheory

/-- The indices whose values strictly exceed their fixed thresholds. -/
noncomputable def accepted {Ω : Type*} {n : ℕ}
    (τ : Fin n → ENNReal) (X : Fin n → Ω → ℝ) (ω : Ω) : Finset (Fin n) :=
  Finset.univ.filter (fun i => τ i < ENNReal.ofReal (X i ω))

/-- The random-order reward conditional on the realized set of accepted indices. -/
noncomputable def ratio {Ω : Type*} {n : ℕ}
    (τ : Fin n → ENNReal) (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ accepted τ X ω, X i ω) / ((accepted τ X ω).card : ℝ)

end CorreaThreshold.Nonadaptive


