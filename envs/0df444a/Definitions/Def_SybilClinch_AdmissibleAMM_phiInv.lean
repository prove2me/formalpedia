-- Prove2me | Definitions.Def_SybilClinch_AdmissibleAMM_phiInv
-- name    : SybilClinch_AdmissibleAMM_phiInv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:55.538907+00:00
-- url     : https://prove2.me/theorems/cb2493bf-734c-4270-87fa-3e041f84f406
-- title:
--   Inverse reserve curve $\varphi^{-1}$
-- statement:
--   For $y>0$, $\varphi^{-1}(y)$ is the unique $x>0$ with $\varphi(x)=y$; it is the reserve curve in exchanged coordinates.
--
--   **Formalization Note** Defined as $\inf\{x>0:\varphi(x)\le y\}$, which equals $\varphi^{-1}(y)$ for $y>0$ because $\varphi$ is continuous and strictly decreasing from $+\infty$ to $0$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.2, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_SybilClinch_AdmissibleAMM

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.2, printed p.26 (PDF p.28): the inverse of the reserve curve, `φ⁻¹(y)` for `y > 0`
(the reserve curve in exchanged coordinates is `φ⁻¹`).

**Formalization Note.** `sInf {x > 0 : φ x ≤ y}`; for `y > 0` this set is `[φ⁻¹(y), ∞)` because
`φ` is continuous and strictly decreasing from `+∞` to `0`, so the infimum is `φ⁻¹(y)`. -/
noncomputable def AdmissibleAMM.phiInv (A : AdmissibleAMM) (y : ℝ) : ℝ :=
  sInf {x : ℝ | 0 < x ∧ A.φ x ≤ y}

end SybilClinch


