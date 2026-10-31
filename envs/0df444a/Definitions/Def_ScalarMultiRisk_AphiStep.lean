-- Prove2me | Definitions.Def_ScalarMultiRisk_AphiStep
-- name    : ScalarMultiRisk_AphiStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:24.200969+00:00
-- url     : https://prove2.me/theorems/a118002c-67fe-457f-a573-aa63680b18e9
-- title:
--   The stepped acceptance set $A^\phi_{t,s}$
-- statement:
--   $A^\phi_{t,s}=A^\phi_t\cap L^\infty_s(\mathbb R)$, the acceptance set of the restriction $\phi^S_{t,s}$ of $\phi^S_t$ to $L^\infty_s(\mathbb R)$. It is used for $t\le s$.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Proof of Corollary 4.11, p.23

import Mathlib
import Definitions.Def_ScalarMultiRisk_Aphi
import Definitions.Def_ScalarMultiRisk_LinftyFull

open MeasureTheory

namespace ScalarMultiRisk

/-- **The stepped acceptance set `A^φ_{t,s}`.** arXiv:1807.10694v5, proof of Corollary 4.11, p.23:
`A^φ_{t,s} := A^φ_t ∩ L∞_s(ℝ)`, the acceptance set of the restriction `φ^S_{t,s}` of `φ^S_t` to
`L∞_s(ℝ)`.

**Formalization Note.** The definition makes sense for `t ≤ s`, including `t = s`, as used by
Lemma 4.18. -/
def AphiStep {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} [NeZero d] (A : Market Ω T d)
    (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ) (S : Fin (T + 1) → Ω → Fin d → ℝ)
    (t s : Fin (T + 1)) : Set (Ω → ℝ) :=
  Aphi A ρ S t ∩ LinftyFull A.toFilteredSpace s

end ScalarMultiRisk


