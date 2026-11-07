-- Prove2me | Definitions.Def_NSWBetter_lpVal
-- name    : NSWBetter_lpVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:34.30248+00:00
-- url     : https://prove2.me/theorems/b68e7e5d-8adb-4b70-8a1a-dba961265c43
-- title:
--   Configuration LP objective $\frac1n\sum_{i,S}y_{i,S}\ln v_i(S)$
-- statement:
--   The objective value of a configuration LP solution,
--   $$\frac1n\sum_{i\in N}\sum_{S\subseteq G}y_{i,S}\ln v_i(S).$$
--
--   **Formalization Note** It is only used for solutions with a finite objective, where every bundle of value $0$ has weight $0$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 2.1, p.10 (objective of the configuration LP)

import Mathlib

namespace NSWBetter

/-- **Objective of the configuration LP.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 2.1, p.10: "max (1/n) Σ_(i∈N) Σ_(S⊆G) yi,S ln vi(S)".

`lpVal v y = (1/n) Σ_i Σ_S y_(i,S) · ln v_i(S)`.

**Formalization Note.** The value is used only for solutions with a finite objective (`FiniteObj`), where every term with `v_i(S) = 0` has weight `0`; Lean's `Real.log 0 = 0` is then multiplied by `0`. -/
noncomputable def lpVal {n m : ℕ} (v : Fin n → Fin m → ℝ) (y : Fin n → Finset (Fin m) → ℝ) : ℝ :=
  (1 / n : ℝ) * ∑ i, ∑ S, y i S * Real.log (∑ g ∈ S, v i g)

end NSWBetter


