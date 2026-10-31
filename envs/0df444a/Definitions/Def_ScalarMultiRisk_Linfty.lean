-- Prove2me | Definitions.Def_ScalarMultiRisk_Linfty
-- name    : ScalarMultiRisk_Linfty
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:11.52296+00:00
-- url     : https://prove2.me/theorems/b2d67cf6-8a37-49c6-81fb-afaab3e8762d
-- title:
--   $L^\infty_t(D)$ for a possibly random target set $D$
-- statement:
--   For a time $t$ and a set $D(\omega)$ depending on $\omega$, $L^\infty_t(D)$ is the set of $\mathcal F_t$-measurable, essentially bounded random vectors $X$ with $X(\omega)\in D(\omega)$ almost surely.
--
--   This covers $L^\infty_s(K_s)$ for a random cone $K_s$ and $L^\infty_t([0,1])$ for a deterministic interval.
--
--   **Formalization Note** Random vectors are functions, and membership does not change under a.e. modification.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, §2, p.5

import Mathlib
import Definitions.Def_ScalarMultiRisk_FilteredSpace

open MeasureTheory

namespace ScalarMultiRisk

/-- **`L∞_t(D)`.** arXiv:1807.10694v5, §2, p.5: the `F_t`-measurable essentially bounded random
vectors with values a.s. in `D`. Here `D` may be a random set, as in `L∞_s(K_s)` (p.7) and
`L∞_t(K_t⁺)` (4.3).

**Formalization Note.** Random vectors are functions `Ω → E`, not a.e.-classes: membership is
invariant under `P`-a.e. modification, and every statement of the mission concludes a.e.
(in)equalities. -/
def Linfty {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} {E : Type*} [NormedAddCommGroup E]
    (B : FilteredSpace Ω T) (t : Fin (T + 1)) (D : Ω → Set E) : Set (Ω → E) :=
  {X | AEStronglyMeasurable[B.F t] X B.P ∧ MemLp X ⊤ B.P ∧ ∀ᵐ ω ∂B.P, X ω ∈ D ω}

end ScalarMultiRisk


