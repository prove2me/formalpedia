-- Prove2me | Definitions.Def_RandPurIso_Completion_pathRecording
-- name    : RandPurIso_Completion_pathRecording
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:31:01.019215+00:00
-- url     : https://prove2.me/theorems/83accb1e-438a-417d-a4c5-c1fdbdfefc81
-- title:
--   Exact path recording oracle $PR_{[N],T}$ (Definition 3.13)
-- statement:
--   For $N,T\in\mathbb N$, with $\mathsf{In}=\mathcal H([N])$ and $\mathbf{St}=\bigoplus_{t=0}^T\mathcal R_t$, the **exact path recording oracle** $PR_{[N],T}$ is the operator on $\mathsf{In}\otimes\mathbf{St}$ whose restriction to $\mathsf{In}\otimes\mathcal R_t$, $t<T$, is
--   $$PR_{[N],T}\big|_{\mathsf{In}\otimes\mathcal R_t}=\sum_{x,y\in[N]}|y\rangle\langle x|\otimes\Lambda_{t+1}\Omega_{t+1}\,\mathrm{App}^{(t)}_{x,y}\,\Lambda_t^+\Omega_t ,$$
--   and which is zero on $\mathsf{In}\otimes\mathcal R_T$. The recording register starts in $|\varnothing\rangle$. It simulates queries to a Haar-random unitary (Theorem 3.14).
--
--   **Formalization Note** $PR$ is defined by the formula; that it is a partial isometry (the paper's wording) is a consequence, not part of the definition.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definition 3.13, p. 24

import Mathlib
import Definitions.Def_RandPurIso_Completion_PRSt
import Definitions.Def_RandPurIso_Completion_legalProj
import Definitions.Def_RandPurIso_Completion_lam
import Definitions.Def_RandPurIso_Completion_appendMap
open Matrix

namespace RandPurIso.Completion

/-- The block `Λ_{t+1} Ω_{t+1} App^{(t)}_{x,y} Λ⁺_t Ω_t : R_t → R_{t+1}` of Definition 3.13. -/
noncomputable def prBlock (N t : ℕ) (x y : Fin N) : Matrix (Rt N (t + 1)) (Rt N t) ℂ :=
  lam N (t + 1) * legalProj N (t + 1) * appendMap N t x y * lamPlus N t * legalProj N t

/-- **Exact path recording oracle `PR_{[N],T}`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.13, p. 24): on `In ⊗ R_t`,
`t < T`, `PR_{[N],T} = Σ_{x,y∈[N]} |y⟩⟨x| ⊗ Λ_{t+1} Ω_{t+1} App^{(t)}_{x,y} Λ⁺_t Ω_t`; it is zero on
`In ⊗ R_T`. Here `In = H([N])` and `St = ⊕_{t=0}^{T} R_t`.

**Formalization Note.** `PR` is defined as the linear map given by the formula; that it is a
partial isometry (the paper's wording) is a consequence, not part of the definition. -/
noncomputable def pathRecording (N T : ℕ) : Matrix (Fin N × PRSt N T) (Fin N × PRSt N T) ℂ :=
  recordOp fun t y x => prBlock N t x y

end RandPurIso.Completion


