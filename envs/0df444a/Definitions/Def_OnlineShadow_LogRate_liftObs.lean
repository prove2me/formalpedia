-- Prove2me | Definitions.Def_OnlineShadow_LogRate_liftObs
-- name    : OnlineShadow_LogRate_liftObs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:07:12.734671+00:00
-- url     : https://prove2.me/theorems/d9b26dd7-f48e-4b61-8c28-29dd292e6501
-- title:
--   Lifted observable $\overline A=\frac1n\sum_j A_j$
-- statement:
--   Given a number of copies $n$ and a single-copy matrix $A$, the **lifted observable** is
--   $$\overline A=\frac1n\sum_{j=1}^nA_j,\qquad A_j=1^{\otimes(j-1)}\otimes A\otimes1^{\otimes(n-j)} .$$
--   For an effect $A$ it measures the empirical average of $A$ over the $n$ copies; all soft measurements of the protocol are measurements of lifted observables.
--
--
--   **Formalization Note** $A_j$ is the published `OptimalSpectrum.Entangled.copyOp j A` (slots numbered from $0$). Defined for a matrix over any finite index type. The paper's $\overline A$ is the lift of $A$ on $(\mathbb C^d)^{\otimes n}$, and in the purified picture the lift of $A\otimes 1_{\mathcal R}$ on $(\mathcal H\otimes\mathcal R)^{\otimes n}$. At $n=0$ the value is $0$.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 3.3, p. 9

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_copyOp

namespace OnlineShadow.LogRate

/-- The **lifted observable** `Ā = (1/n) ∑ⱼ Aⱼ` on `n` copies (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 3.3, p.9), the average
of `M` acting on each slot. `Aⱼ = 1^{⊗(j−1)} ⊗ A ⊗ 1^{⊗(n−j)}` is the published
`OptimalSpectrum.Entangled.copyOp j A` (slots numbered from `0`).

**Formalization Note** Defined for any single-copy matrix over any finite index type `ι`. The paper's
`Ā` is `liftObs n A` on `(ℂ^d)^{⊗n}` (`ι = Fin d`), and in the purified picture
`liftObs n (A ⊗ₖ 1_R)` on `(H ⊗ R)^{⊗n}` (`ι = Fin d × Fin r`). At `n = 0` it is `0`. -/
noncomputable def liftObs {ι : Type} [DecidableEq ι] (n : ℕ) (M : Matrix ι ι ℂ) :
    Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  (1 / (n : ℂ)) • ∑ j : Fin n, OptimalSpectrum.Entangled.copyOp j M

end OnlineShadow.LogRate


