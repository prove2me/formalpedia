-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_CSSCode_syndProjX
-- name    : SelfCorrect3D_Memory_CSSCode_syndProjX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:03.9368+00:00
-- url     : https://prove2.me/theorems/e5547141-ce82-4646-8f6e-7c5b8de91c12
-- title:
--   Syndrome projector $\Pi_{\sigma_Z}$
-- statement:
--   For $\sigma_Z\in\mathbb F_2^{m_x}$, the **syndrome projector**
--
--   $$\Pi_{\sigma_Z}=\prod_{a=1}^{m_x}\frac{1+(-1)^{\sigma_Z(a)}S^X_a}{2}$$
--
--   projects onto the states on which every $X$-type stabilizer $S^X_a$ has eigenvalue $(-1)^{\sigma_Z(a)}$, i.e. onto the states with $X$-check syndrome $\sigma_Z$. It vanishes unless $\sigma_Z$ is achievable.
--
--   **Formalization Note** The paper's naming is kept: $\sigma_Z$ records violated $X$-checks (caused by $Z$ errors). The commuting factors are multiplied in the order $a=1,2,\dots$.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, §2.5, p. 20 (below eq. (46))

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_CSSCode

namespace SelfCorrect3D.Memory

/-- **Syndrome projector `Π_{σ_Z}`** onto the states whose X-check pattern is `σ_Z ∈ 𝔽₂^{m_x}`.
Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, §2.5, p. 20 (below eq. (46)): "Π_{σ_X} and Π_{σ_Z} project
onto the subspace of states with syndrome σ_X and σ_Z, respectively".
`Π_{σ_Z} = ∏_a (1 + (−1)^{σ_Z(a)} S^X_a)/2`.

**Formalization Note.** The paper's naming is kept: `σ_Z ∈ 𝔽₂^{r_X}` records the violated
**X**-checks (caused by Z errors), `σ_Z(a) = 1` meaning `S^X_a` has eigenvalue `−1`. The
factors commute; the product is taken in the order `a = 0, 1, …` as a list product because the
matrix ring is not commutative. -/
noncomputable def CSSCode.syndProjX {n mX mZ : ℕ} (C : CSSCode n mX mZ)
    (σZ : Fin mX → ZMod 2) : Op n :=
  ((List.finRange mX).map fun a =>
    (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ (σZ a).val • C.stabX a)).prod

end SelfCorrect3D.Memory


