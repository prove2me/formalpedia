-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_chiBar
-- name    : NoPerfectRandComp_Supplement_chiBar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:15:48.396979+00:00
-- url     : https://prove2.me/theorems/d3cbefc9-0dcb-47d4-a9f9-6ee84251334a
-- title:
--   Max-conflict complexity $\bar\chi(h)$
-- statement:
--   For a distribution $Q$ over pairs $(\mu_0,\mu_1)$ supported on $h^{-1}(0)$ and $h^{-1}(1)$, write $\chi(T,Q) = \mathbb E_{(\mu_0,\mu_1)\sim Q}\bigl[\chi(T,(\mu_0,\mu_1))\bigr]$. The **max-conflict complexity** is
--   $$
--   \bar\chi(h) = \max_Q\ \min_T\ \chi(T,Q),
--   $$
--   the minimum over deterministic decision trees computing $h$. A single tree must do well against the whole ensemble $Q$; that quantifier order is the only difference from $\chi(h)$, and $\chi\le\bar\chi$.
--
--   **Formalization Note** Valued in $[0,\infty]$. $Q$ ranges over discrete distributions on pairs. On a finite input set this gives the same value as general distributions: only finitely many trees (those without repeated queries) matter for the minimum, the conflict is bounded by the input length, and the minimum of finitely many averages is continuous and concave, so finite mixtures attain the supremum.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Definition 2.1, p.5

import Mathlib
import Definitions.Def_NoPerfectRandComp_PartialFn
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_NoPerfectRandComp_Supplement_chiPair
open scoped ENNReal

namespace NoPerfectRandComp

namespace Supplement

/-- Max-conflict complexity (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), Definition 2.1, p.5): for a distribution `Q` over
admissible pairs, `χ(T, Q) = E_{(μ₀,μ₁)∼Q}[χ(T, (μ₀, μ₁))]`, and `χ̄(h) = max_Q min_T χ(T, Q)`, the
minimum over deterministic trees computing `h`. The quantifier order (one tree against the whole
ensemble `Q`) is the only difference from `χ`.

**Formalization Note** Valued in `ℝ≥0∞`. `Q` is a discrete distribution (`PMF`) over pairs whose
members are supported on `Dom(h) ∩ h⁻¹(0)` and `Dom(h) ∩ h⁻¹(1)`. Restricting to discrete `Q`
does not change the value on finite `ι`: only the finitely many trees without repeated queries
matter for the minimum (a repeated query adds no conflict and only deepens later nodes), the
conflict is bounded by the input length, and the minimum of finitely many averages is continuous
and concave, so its supremum over the closed convex hull is reached by finite mixtures. -/
noncomputable def chiBar {ι : Type} (h : PartialFn ι) : ℝ≥0∞ :=
  ⨆ (Q : PMF (PMF (ι → Bool) × PMF (ι → Bool)))
    (_ : ∀ p ∈ Q.support, (∀ x ∈ p.1.support, x ∈ h.dom ∧ h.val x = false) ∧
      (∀ x ∈ p.2.support, x ∈ h.dom ∧ h.val x = true)),
    ⨅ (T : QAlgorithms.DecisionTree ι Bool Bool) (_ : ∀ x ∈ h.dom, T.eval x = h.val x),
      ∑' p, Q p * ENNReal.ofReal (chiPair T p.1 p.2)

end Supplement

end NoPerfectRandComp


