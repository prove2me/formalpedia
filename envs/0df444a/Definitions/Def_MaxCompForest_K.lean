-- Prove2me | Definitions.Def_MaxCompForest_K
-- name    : MaxCompForest_K
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:30.475468+00:00
-- url     : https://prove2.me/theorems/6bf94fa4-41de-478d-a077-b4430bdd19be
-- title:
--   Transfer-current kernel $K=C_E^{1/2}B^{\top}L_G^{+}BC_E^{1/2}$
-- statement:
--   The edge-indexed matrix
--   $$
--   K=C_E^{1/2}B^{\top}L_G^{+}BC_E^{1/2},
--   $$
--   where $L_G^{+}$ is the Moore–Penrose pseudoinverse of the Laplacian $L_G=BC_EB^{\top}$. Its diagonal entries are the marginals $K_{ee}=P(e\in T)$, and its principal minors are the inclusion probabilities of the weighted spanning-tree law.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (3.2) p.14

import Mathlib
import Definitions.Def_MaxCompForest_edgeMat
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The transfer-current kernel** `K = C_E^{1/2} Bᵀ L_G⁺ B C_E^{1/2}`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (3.2) p.14.

**Formalization Note.** `G.lapPinv` is the published Moore–Penrose pseudoinverse of the Laplacian. -/
noncomputable def K (G : WGraph V E) : Matrix E E ℝ := edgeMat G G.lapPinv

end MaxCompForest


