-- Prove2me | Definitions.Def_SybilClinch_AdmissibleAMM_Crev
-- name    : SybilClinch_AdmissibleAMM_Crev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:39:03.765577+00:00
-- url     : https://prove2.me/theorems/b1e1b09f-d0fa-4a65-8509-e50a13ad7d8d
-- title:
--   Reverse pool cost $C^{\rm rev}(w)=-C^{-1}(-w)$
-- statement:
--   For $0\le w<y_0$, the reverse one-sided pool cost is $C^{\rm rev}(w):=-C^{-1}(-w)$, the units of $X$ the pool must receive to release $w$ units of $Y$.
--
--   **Formalization Note** Written as $\varphi^{-1}(y_0-w)-x_0$, which equals $-C^{-1}(-w)$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.2, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_SybilClinch_AdmissibleAMM_phiInv
import Definitions.Def_SybilClinch_AdmissibleAMM_y0

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.2, printed p.26 (PDF p.28): the reverse one-sided pool cost
`C^rev(w) := −C⁻¹(−w)`, `0 ≤ w < y₀`: the units of `X` the pool must receive to release `w` units of
`Y`.

**Formalization Note.** Written as `φ⁻¹(y₀ − w) − x₀`, which equals `−C⁻¹(−w)` since
`C(z) = −w ⇔ x₀ − z = φ⁻¹(y₀ − w)`. -/
noncomputable def AdmissibleAMM.Crev (A : AdmissibleAMM) (w : ℝ) : ℝ :=
  A.phiInv (A.y0 - w) - A.x0

end SybilClinch


