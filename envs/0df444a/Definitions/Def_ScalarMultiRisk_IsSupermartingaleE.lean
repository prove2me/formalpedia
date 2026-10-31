-- Prove2me | Definitions.Def_ScalarMultiRisk_IsSupermartingaleE
-- name    : ScalarMultiRisk_IsSupermartingaleE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:25.710281+00:00
-- url     : https://prove2.me/theorems/fb44529e-b11d-4a56-bbda-aea1fafb391e
-- title:
--   $\mathbb Q$-supermartingale, for an extended-valued process
-- statement:
--   An extended-valued process $(V_t)$ is a **$\mathbb Q$-supermartingale** if it is $\mathbb Q$-a.s. equal to a real process $(W_t)$ that is adapted, $\mathbb Q$-integrable, and satisfies $\mathbb E^{\mathbb Q}[W_s\mid\mathcal F_t]\le W_t$ for $t\le s$. In particular each $V_t$ is $\mathbb Q$-a.s. finite.
--
--   **Formalization Note** The comparison is with a version because the filtration need not contain the null sets.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Theorem 4.15(5), p.25

import Mathlib
import Definitions.Def_ScalarMultiRisk_FilteredSpace

open MeasureTheory

namespace ScalarMultiRisk

/-- **`ℚ`-supermartingale, for an `EReal`-valued process.** The meaning of "is a
`ℚ`-supermartingale" in arXiv:1807.10694v5, Theorem 4.15(5), p.25.

**Formalization Note.** `V` is `ℚ`-a.s. equal to a real process that is a `ℚ`-supermartingale in
Mathlib's sense for `(F_t)`, that is, adapted, `ℚ`-integrable, with `ℚ[W_s|F_t] ≤ W_t` for
`t ≤ s`. So each `V_t` is `ℚ`-a.s. finite. The process is compared with a version because the
filtration need not contain the null sets, and `V_t` is only a.e. `F_t`-measurable. -/
def IsSupermartingaleE {Ω : Type*} [m : MeasurableSpace Ω] {T : ℕ} (B : FilteredSpace Ω T)
    (Q : Measure Ω) (V : Fin (T + 1) → Ω → EReal) : Prop :=
  ∃ W : Fin (T + 1) → Ω → ℝ, Supermartingale W B.F Q ∧
    ∀ t, V t =ᵐ[Q] fun ω => (W t ω : EReal)

end ScalarMultiRisk


