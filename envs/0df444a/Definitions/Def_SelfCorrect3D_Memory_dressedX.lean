-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_dressedX
-- name    : SelfCorrect3D_Memory_dressedX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:16.373319+00:00
-- url     : https://prove2.me/theorems/153788c6-d832-4a4f-a050-d15690d59a37
-- title:
--   Dressed observable $\widetilde X_L$, eq. (46)
-- statement:
--   Given a memory frame, the **dressed logical $X$ observable** is
--
--   $$\widetilde X_L=\sum_{\sigma_Z}\Pi_{\sigma_Z}\,\mathcal O_Z(\sigma_Z)\,X_L\,\mathcal O_Z(\sigma_Z)\,\Pi_{\sigma_Z},$$
--
--   the logical $X$ conjugated, on each $X$-check syndrome sector, by the decoder's correction for that sector (Definition 2.3).
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, eq. (46) and Definition 2.3, p. 20

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_MemoryFrame

namespace SelfCorrect3D.Memory

/-- **Dressed observable** `X̃_L = Σ_{σ_Z} Π_{σ_Z} O_Z(σ_Z) X_L O_Z(σ_Z) Π_{σ_Z}`. Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943,
eq. (46) and Definition 2.3, p. 20, with `O_Z(σ_Z) = Z^{f_Z(σ_Z)}`.

**Formalization Note.** The sum runs over all `σ_Z ∈ 𝔽₂^{m_x}`, as printed; `Π_{σ_Z} = 0` for a
non-achievable `σ_Z`. -/
noncomputable def dressedX {n mX mZ : ℕ} (C : CSSCode n mX mZ) (F : MemoryFrame C) : Op n :=
  ∑ σZ, C.syndProjX σZ * pauliZ (F.fZ σZ) * pauliX F.xL * pauliZ (F.fZ σZ) * C.syndProjX σZ

end SelfCorrect3D.Memory


