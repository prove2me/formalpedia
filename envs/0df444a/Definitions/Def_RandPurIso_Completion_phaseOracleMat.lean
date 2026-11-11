-- Prove2me | Definitions.Def_RandPurIso_Completion_phaseOracleMat
-- name    : RandPurIso_Completion_phaseOracleMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:27:15.211893+00:00
-- url     : https://prove2.me/theorems/99890de7-7b37-4ace-9d3c-cba98c0c6c1c
-- title:
--   Phase oracle $S^f$ (Definition 3.16)
-- statement:
--   For $f:A\to[t]$ and $\omega_t=e^{2\pi i/t}$, $S^f$ is the unitary on $\mathcal H(A)$ with $S^f|x\rangle=\omega_t^{f(x)}|x\rangle$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definition 3.16, p. 24

import Mathlib
open Matrix

namespace RandPurIso.Completion

/-- **Phase oracle `S^f`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.16, p. 24): for `f : A → [t]` and
`ω_t = e^{2πi/t}`, the unitary `S^f|x⟩ = ω_t^{f(x)} |x⟩` on `H(A)`.

**Formalization Note.** `[t] = {0, …, t−1}` is `Fin t`; the exponent is `f(x)` as a natural number. -/
noncomputable def phaseOracleMat {A : Type} [DecidableEq A] (t : ℕ) (f : A → Fin t) : Matrix A A ℂ :=
  Matrix.diagonal fun x => Complex.exp (2 * Real.pi * Complex.I / t) ^ (f x).val

end RandPurIso.Completion


