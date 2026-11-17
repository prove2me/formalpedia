-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_chi
-- name    : NoPerfectRandComp_Supplement_chi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:15:20.053261+00:00
-- url     : https://prove2.me/theorems/dc85b3f1-6818-4faa-bed2-9d4ffda10bee
-- title:
--   Conflict complexity $\chi(h)$
-- statement:
--   For a possibly partial Boolean function $h$, the **conflict complexity** is
--   $$
--   \chi(h) = \max_{\mu_0,\mu_1}\ \min_T\ \chi\bigl(T,(\mu_0,\mu_1)\bigr),
--   $$
--   the maximum over pairs of distributions $\mu_0, \mu_1$ supported on $h^{-1}(0)$ and $h^{-1}(1)$, and the minimum over deterministic decision trees $T$ computing $h$.
--
--   **Formalization Note** Valued in $[0,\infty]$ as a supremum of infima; $T$ computes $h$ when its output equals $h(x)$ at every $x\in\mathrm{Dom}(h)$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Definition 2.1, p.5

import Mathlib
import Definitions.Def_NoPerfectRandComp_PartialFn
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_NoPerfectRandComp_Supplement_chiPair
open scoped ENNReal

namespace NoPerfectRandComp

namespace Supplement

/-- Conflict complexity (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), Definition 2.1, p.5, after [13, §3]):
`χ(h) = max_{μ₀, μ₁} min_T χ(T, (μ₀, μ₁))`, the maximum over pairs of distributions supported on
`h⁻¹(0)` and `h⁻¹(1)` and the minimum over deterministic trees `T` computing `h`.

**Formalization Note** Valued in `ℝ≥0∞` as a supremum of infima. `μ_b` is supported inside
`Dom(h) ∩ h⁻¹(b)`; `T` computes `h` when its leaf label equals `h(x)` at every `x ∈ Dom(h)`. -/
noncomputable def chi {ι : Type} (h : PartialFn ι) : ℝ≥0∞ :=
  ⨆ (μ₀ : PMF (ι → Bool)) (μ₁ : PMF (ι → Bool))
    (_ : (∀ x ∈ μ₀.support, x ∈ h.dom ∧ h.val x = false) ∧
      (∀ x ∈ μ₁.support, x ∈ h.dom ∧ h.val x = true)),
    ⨅ (T : QAlgorithms.DecisionTree ι Bool Bool) (_ : ∀ x ∈ h.dom, T.eval x = h.val x),
      ENNReal.ofReal (chiPair T μ₀ μ₁)

end Supplement

end NoPerfectRandComp


