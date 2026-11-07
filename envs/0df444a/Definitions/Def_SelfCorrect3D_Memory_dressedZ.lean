-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_dressedZ
-- name    : SelfCorrect3D_Memory_dressedZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:00.905382+00:00
-- url     : https://prove2.me/theorems/384cd960-8210-4f7d-b426-443417204990
-- title:
--   Dressed observable $\widetilde Z_L$, eq. (46)
-- statement:
--   Given a memory frame, the **dressed logical $Z$ observable** is
--
--   $$\widetilde Z_L=\sum_{\sigma_X}\Pi_{\sigma_X}\,\mathcal O_X(\sigma_X)\,Z_L\,\mathcal O_X(\sigma_X)\,\Pi_{\sigma_X}$$
--
--   (Definition 2.3).
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, eq. (46) and Definition 2.3, p. 20

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_MemoryFrame

namespace SelfCorrect3D.Memory

/-- **Dressed observable** `Z̃_L = Σ_{σ_X} Π_{σ_X} O_X(σ_X) Z_L O_X(σ_X) Π_{σ_X}`. Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943,
eq. (46) and Definition 2.3, p. 20, with `O_X(σ_X) = X^{f_X(σ_X)}`.

**Formalization Note.** The sum runs over all `σ_X ∈ 𝔽₂^{m_z}`, as printed. -/
noncomputable def dressedZ {n mX mZ : ℕ} (C : CSSCode n mX mZ) (F : MemoryFrame C) : Op n :=
  ∑ σX, C.syndProjZ σX * pauliX (F.fX σX) * pauliZ F.zL * pauliX (F.fX σX) * C.syndProjZ σX

end SelfCorrect3D.Memory


