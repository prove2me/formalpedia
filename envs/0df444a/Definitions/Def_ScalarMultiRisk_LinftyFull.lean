-- Prove2me | Definitions.Def_ScalarMultiRisk_LinftyFull
-- name    : ScalarMultiRisk_LinftyFull
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:06.336163+00:00
-- url     : https://prove2.me/theorems/606fc406-5406-4234-99c2-7931c906c4ac
-- title:
--   $L^\infty_t(E)$, and $L^\infty(E)=L^\infty_T(E)$
-- statement:
--   $L^\infty_t(E)$ is the set of $\mathcal F_t$-measurable essentially bounded $E$-valued random vectors, that is, $L^\infty_t(D)$ with $D=E$. The paper's $L^\infty(E)$ is $L^\infty_T(E)$.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, §2, p.5

import Mathlib
import Definitions.Def_ScalarMultiRisk_Linfty

open MeasureTheory

namespace ScalarMultiRisk

/-- **`L∞_t(ℝⁿ)`.** arXiv:1807.10694v5, §2, p.5: `L∞_t(E)`, i.e. `L∞_t(D)` with `D` the whole
space. `L∞(E)` of the paper is `LinftyFull B (Fin.last T)` (`L^p(D) := L^p_T(D)`, p.5). -/
def LinftyFull {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} {E : Type*} [NormedAddCommGroup E]
    (B : FilteredSpace Ω T) (t : Fin (T + 1)) : Set (Ω → E) :=
  Linfty B t fun _ => Set.univ

end ScalarMultiRisk


