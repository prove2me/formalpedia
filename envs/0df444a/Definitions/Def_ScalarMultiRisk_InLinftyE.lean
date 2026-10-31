-- Prove2me | Definitions.Def_ScalarMultiRisk_InLinftyE
-- name    : ScalarMultiRisk_InLinftyE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:27.752305+00:00
-- url     : https://prove2.me/theorems/f30fd891-3c2e-4a29-bd96-f9c28be1d558
-- title:
--   Membership of an extended random variable in $L^\infty_t(\mathbb R)$
-- statement:
--   An extended random variable is in $L^\infty_t(\mathbb R)$ when it is a.s. equal to a bounded $\mathcal F_t$-measurable real random variable. In particular it is a.s. finite.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, pp.18–20

import Mathlib
import Definitions.Def_ScalarMultiRisk_LinftyFull

open MeasureTheory

namespace ScalarMultiRisk

/-- **`L∞_t(ℝ)` membership for an extended random variable.** arXiv:1807.10694v5, p.18–20: the
condition "`π^S_t(X) ∈ L∞_t(ℝ)`" for the extended-valued `π^S_t(X)`: it is a.s. finite and
a.s. equal to a bounded `F_t`-measurable real random variable. -/
def InLinftyE {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} (B : FilteredSpace Ω T)
    (t : Fin (T + 1)) (f : Ω → EReal) : Prop :=
  ∃ g ∈ (LinftyFull B t : Set (Ω → ℝ)), f =ᵐ[B.P] fun ω => (g ω : EReal)

end ScalarMultiRisk


