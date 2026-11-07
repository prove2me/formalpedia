-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_CSSCode_syndProjZ
-- name    : SelfCorrect3D_Memory_CSSCode_syndProjZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:07.587409+00:00
-- url     : https://prove2.me/theorems/79c9e2f1-88ba-4425-a258-4e3d27dd54ce
-- title:
--   Syndrome projector $\Pi_{\sigma_X}$
-- statement:
--   For $\sigma_X\in\mathbb F_2^{m_z}$, the **syndrome projector**
--
--   $$\Pi_{\sigma_X}=\prod_{b=1}^{m_z}\frac{1+(-1)^{\sigma_X(b)}S^Z_b}{2}$$
--
--   projects onto the states with $Z$-check syndrome $\sigma_X$ (violated $Z$-checks, caused by $X$ errors). The full syndrome projector is $\Pi_\sigma=\Pi_{\sigma_Z}\Pi_{\sigma_X}$.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, §2.5, p. 20 (below eq. (46))

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_CSSCode

namespace SelfCorrect3D.Memory

/-- **Syndrome projector `Π_{σ_X}`** onto the states whose Z-check pattern is `σ_X ∈ 𝔽₂^{m_z}`.
Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, §2.5, p. 20 (below eq. (46)).
`Π_{σ_X} = ∏_b (1 + (−1)^{σ_X(b)} S^Z_b)/2`.

**Formalization Note.** Paper's naming: `σ_X ∈ 𝔽₂^{r_Z}` records the violated **Z**-checks (caused
by X errors). List product in the order `b = 0, 1, …` (the factors commute). -/
noncomputable def CSSCode.syndProjZ {n mX mZ : ℕ} (C : CSSCode n mX mZ)
    (σX : Fin mZ → ZMod 2) : Op n :=
  ((List.finRange mZ).map fun b =>
    (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ (σX b).val • C.stabZ b)).prod

end SelfCorrect3D.Memory


