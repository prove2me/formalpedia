-- Prove2me | Definitions.Def_MaxCompForest_slowResp
-- name    : MaxCompForest_slowResp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:53.003488+00:00
-- url     : https://prove2.me/theorems/9a735707-3b3b-40c2-b0fa-6dc966dea4c7
-- title:
--   Slow response $R$ at a cutoff $c$
-- statement:
--   For a connected graph with normalized Laplacian $N$, orthonormal eigenvectors $u_a$ with eigenvalues $\lambda_a$, and a cutoff $c$,
--   $$
--   R=D^{-1/2}\Big[\sum_{0<\lambda_a<c}(\lambda_a^{-1}-1)\,u_au_a^{\top}\Big]D^{-1/2}.
--   $$
--   It retains only the positive eigenvalues below the cutoff. For $c\le 1$ it is positive semidefinite, and it does not depend on the choice of eigenbasis.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (F.1), p.42

import Mathlib
import Definitions.Def_MaxCompForest_normLap
import Definitions.Def_MaxCompForest_deg
import Definitions.Def_MaxCompForest_massInvSqrt
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The slow response** at cutoff `c`:
`R = D^{-1/2} [∑_{0 < λ_a < c} (λ_a⁻¹ − 1) u_a u_aᵀ] D^{-1/2}`, over an orthonormal eigenbasis of `N`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (F.1), p.42.

**Formalization Note.** Mathlib's `eigenvectorBasis` is one fixed eigenbasis; the paper notes that the
matrix is basis-independent. The strict `0 < λ_a` excludes the zero modes. -/
noncomputable def slowResp (G : WGraph V E) (c : ℝ) : Matrix V V ℝ :=
  massInvSqrt (deg G) *
    (∑ a, if 0 < (normLap_isHermitian G (deg G)).eigenvalues a ∧
          (normLap_isHermitian G (deg G)).eigenvalues a < c then
        (((normLap_isHermitian G (deg G)).eigenvalues a)⁻¹ - 1) •
          Matrix.vecMulVec (⇑((normLap_isHermitian G (deg G)).eigenvectorBasis a))
            (⇑((normLap_isHermitian G (deg G)).eigenvectorBasis a))
      else 0) *
    massInvSqrt (deg G)

end MaxCompForest


