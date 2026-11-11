-- Prove2me | Definitions.Def_RandPurIso_Completion_legalProj
-- name    : RandPurIso_Completion_legalProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:28:27.602104+00:00
-- url     : https://prove2.me/theorems/4dbb2f7a-1a62-420d-aeba-37fd159c3a7d
-- title:
--   Legal-path projector $\Omega_t=\frac1{t!}\sum_\pi P_\pi\otimes\overline{P_\pi}$
-- statement:
--   The **projector onto legal path states** is
--   $$\Omega_t=\frac1{t!}\sum_{\pi\in S_t}P_\pi\otimes\overline{P_\pi}$$
--   on $\mathcal R_t$, where $P_\pi$ permutes the tensor factors of $\mathcal H^{\otimes t}$; $\Omega_0=I$.
--
--   **Formalization Note** $P_\pi$ is the published `QAlgorithms.Schur.tensorPermutation`; the conjugate is entrywise.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, §3.4, p. 23

import Mathlib
import Definitions.Def_RandPurIso_Completion_PRSt
import Definitions.Def_QAlgorithms_Defs_TensorPermutationRepresentations
open Matrix

namespace RandPurIso.Completion

/-- **Projector onto legal path states** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §3.4, p. 23):
`Ω_t = (1/t!) Σ_{π ∈ S_t} P_π ⊗ conj(P_π)` on `R_t` (so `Ω_0 = I`), where `P_π` permutes the
tensor factors of `H^{⊗t}` (`QAlgorithms.Schur.tensorPermutation`). -/
noncomputable def legalProj (N t : ℕ) : Matrix (Rt N t) (Rt N t) ℂ :=
  ((t.factorial : ℂ)⁻¹) • ∑ π : Equiv.Perm (Fin t),
    Matrix.kronecker (QAlgorithms.Schur.tensorPermutation N t π)
      ((QAlgorithms.Schur.tensorPermutation N t π).map (starRingEnd ℂ))

end RandPurIso.Completion


