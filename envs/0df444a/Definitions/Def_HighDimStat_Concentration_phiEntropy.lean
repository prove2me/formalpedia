-- Prove2me | Definitions.Def_HighDimStat_Concentration_phiEntropy
-- name    : HighDimStat_Concentration_phiEntropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:22:58.068004+00:00
-- url     : https://prove2.me/theorems/103723a0-78f6-43cf-9278-22f7c76ffa90
-- title:
--   The phi-entropy of a nonnegative random variable
-- statement:
--   **Eqs. (3.1)-(3.2).** For $\varphi(u):=u\log u$ ($u>0$), $\varphi(0):=0$, the
--   **$\varphi$-entropy** of a nonnegative random variable $Z$ is
--
--   $$
--   H(Z) \;:=\; \mathbb E[Z\log Z] - \mathbb E[Z]\log\mathbb E[Z].
--   $$
--
--   This is the entropy functional the Herbst argument (Proposition 3.2) and its Bernstein
--   extension (Proposition 3.3) both bound in order to derive tail behavior.
--
--   **Formalization Note** $\varphi(0)=0$ holds automatically in Lean, since `Real.log 0 = 0` by
--   Mathlib's convention, so `Z * Real.log Z = 0` at `Z=0` without a case split.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 59 (PDF p. 79), Eqs. (3.1)-(3.2)

import Mathlib

open MeasureTheory

namespace HighDimStat.Concentration

/-- **Eqs. (3.1)-(3.2)**, Wainwright, *High-Dimensional Statistics* (2019), p. 59. The
`φ`-entropy of a nonnegative random variable `Z`, for `φ(u) := u log u` (`u>0`), `φ(0):=0`:

`H(Z) := E[Z log Z] - E[Z] log E[Z]`.

**Formalization Note** `φ(0)=0` holds automatically in Lean, since `Real.log 0 = 0` by
Mathlib's convention, so `Z * Real.log Z = 0` at `Z=0` without needing a case split. -/
noncomputable def phiEntropy {Ω : Type*} [MeasurableSpace Ω] (Z : Ω → ℝ) (Prob : Measure Ω) : ℝ :=
  (∫ ω, Z ω * Real.log (Z ω) ∂Prob) - (∫ ω, Z ω ∂Prob) * Real.log (∫ ω, Z ω ∂Prob)

end HighDimStat.Concentration


