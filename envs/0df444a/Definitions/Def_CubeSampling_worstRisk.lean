-- Prove2me | Definitions.Def_CubeSampling_worstRisk
-- name    : CubeSampling_worstRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:19:55.591168+00:00
-- url     : https://prove2.me/theorems/bedfddb7-fdf0-4933-ab1a-875b58c21c45
-- title:
--   Definition 1.1 — worst-subspace minimax risk $R_{n,\delta}(d,k,m)$
-- statement:
--   **Definition 1.1.** The worst-subspace minimax risk is
--   $$
--   R_{n,\delta}(d,k,m) = \sup_{V \subseteq P_{d,k},\ \dim V = m} R^*_{n,\delta}(V).
--   $$
--
--   **Formalization Note** $V$ ranges over the spans of orthonormal families $\Phi$ of $m$ functions in $P_{d,k}$; every $m$-dimensional $V \subseteq P_{d,k}$ has such a basis, and $R^*_{n,\delta}(V)$ does not depend on its choice.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Definition 1.1, p.3

import Mathlib
import Definitions.Def_CubeSampling_minimaxRisk
import Definitions.Def_CubeSampling_IsOrthonormalFamily
import Definitions.Def_CubeSampling_lowDeg
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSampling

/-- Definition 1.1, the worst-subspace minimax risk
`R_{n,δ}(d, k, m) = sup_{V ⊆ P_{d,k}, dim V = m} R*_{n,δ}(V)` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Definition 1.1, p.3).

**Formalization Note** `V` is given by an orthonormal family `Φ` of `m` functions in `P_{d,k}`
(then `dim V = m`); every `m`-dimensional `V ⊆ P_{d,k}` has such a basis. -/
noncomputable def worstRisk (d k m : ℕ) (σ : ℝ) (n : ℕ) (δ : ℝ) : ℝ≥0∞ :=
  ⨆ (Φ : Fin m → Cube d → ℝ) (_ : IsOrthonormalFamily Φ ∧ ∀ j, Φ j ∈ lowDeg d k),
    minimaxRisk Φ σ n δ

end CubeSampling


