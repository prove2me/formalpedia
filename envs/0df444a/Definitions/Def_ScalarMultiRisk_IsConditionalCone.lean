-- Prove2me | Definitions.Def_ScalarMultiRisk_IsConditionalCone
-- name    : ScalarMultiRisk_IsConditionalCone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:17.909642+00:00
-- url     : https://prove2.me/theorems/f4a8fdd7-1da3-48b8-89f3-358e15723b39
-- title:
--   Conditional cone
-- statement:
--   A set $C$ of random vectors is a **conditional cone** at time $t$ if $\lambda X\in C$ for every $X\in C$ and $\lambda\in L^\infty_t(\mathbb R_+)$.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Proposition 4.6, p.20

import Mathlib
import Definitions.Def_ScalarMultiRisk_Linfty

open MeasureTheory

namespace ScalarMultiRisk

/-- **Conditional cone.** arXiv:1807.10694v5, Proposition 4.6, p.20 (used, not defined, there): a
set `C` with `λX ∈ C` for every `X ∈ C` and `λ ∈ L∞_t(ℝ₊)`. -/
def IsConditionalCone {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : FilteredSpace Ω T) (t : Fin (T + 1)) (C : Set (Ω → E)) : Prop :=
  ∀ X ∈ C, ∀ l ∈ Linfty B t (fun _ => Set.Ici (0 : ℝ)), (fun ω => l ω • X ω) ∈ C

end ScalarMultiRisk


