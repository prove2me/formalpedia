-- Prove2me | Definitions.Def_GeoSemialgCSP_dWeight
-- name    : GeoSemialgCSP_dWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:50:00.593192+00:00
-- url     : https://prove2.me/theorems/7b6c4234-d6cd-4d1e-8b33-00d415d4c5ca
-- title:
--   The dictatorship test $D_R$
-- statement:
--   For $0<\eta<1$, the test $D_R$ is the $\eta$-noisy copy of $J_R$: sample a constraint $(Z_1,\dots,Z_k)$ of $J_R$ and independently replace each entry $Z^j_r$, with probability $\eta$, by a fresh uniform element of $[M]$. The weight of a $k$-tuple $(\tilde Z_1,\dots,\tilde Z_k)$ is the probability that it is output.
--
--   **Formalization Note** Each row passes through the noise kernel with keep probability $1-\eta$.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.3, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_GeoSemialgCSP_Wd
import Definitions.Def_GeoSemialgCSP_jWeight
import Definitions.Def_GeoSemialgCSP_noiseK

namespace GeoSemialgCSP

/-- **The dictatorship test `D_R`.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.3, printed p.12 (PDF p.13): for
`0 < η < 1`, `D_R` is the `η`-noisy copy of `J_R`: sample `(Z₁, …, Z_k)` from `J_R` and
independently replace each entry, with probability `η`, by a fresh uniform element of `[M]`.

**Formalization Note.** The noise keeps each entry with probability `1 − η`, i.e. kernel
`noiseK (1 − η)` row by row. -/
noncomputable def dWeight {k h H : ℕ} (L : PMF ((Fin h → Fin k) → Wd k H)) (R : ℕ) (η : ℝ)
    (Z' : Fin k → (Fin R → Wd k H)) : ℝ :=
  ∑ Z : Fin k → (Fin R → Wd k H), jWeight L R Z * ∏ j, noiseK (1 - η) (Z j) (Z' j)

end GeoSemialgCSP


