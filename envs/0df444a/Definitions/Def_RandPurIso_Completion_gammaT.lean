-- Prove2me | Definitions.Def_RandPurIso_Completion_gammaT
-- name    : RandPurIso_Completion_gammaT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:54.944204+00:00
-- url     : https://prove2.me/theorems/248cb064-2222-4991-b414-8025dcd3d03e
-- title:
--   Projectors $\Gamma_t$ and $\Gamma$
-- statement:
--   For $t\le T$, the projector on $\mathbf{St}$
--   $$\Gamma_t=\Omega_t\Big(\Pi_{M_1}^{\otimes t}\otimes\overline{\big(\Pi^{D^V}_{M_1}\big)^{\otimes t}}\Big)$$
--   acts on $\mathcal R_t$ (zero on the other summands), and $\Gamma=\bigoplus_{t=0}^{T-1}\Gamma_t$. It characterizes the internal recording state reached by $\widetilde{PR}$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, §5.1, p. 32

import Mathlib
import Definitions.Def_RandPurIso_Completion_PRSt
import Definitions.Def_RandPurIso_Completion_legalProj
import Definitions.Def_RandPurIso_Completion_projM0
open Matrix

namespace RandPurIso.Completion

/-- The tensor power `P^{⊗t}` of an operator on `H([M])`. -/
def tensorPow {M : ℕ} (t : ℕ) (P : Matrix (Fin M) (Fin M) ℂ) :
    Matrix (Fin t → Fin M) (Fin t → Fin M) ℂ :=
  fun xs' xs => ∏ i, P (xs' i) (xs i)

/-- **`Γ_t`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §5.1, p. 32): for `t ≤ T`, the projector on `St`
`Γ_t = Ω_t (Π_{M1}^{⊗t} ⊗ conj((Π^{D^V}_{M1})^{⊗t}))`, acting on `R_t` and zero on the other summands.
The conjugate applies entrywise to the output-slot factor. -/
noncomputable def gammaT (N : ℕ) {M : ℕ} (T : ℕ) (D : Matrix.unitaryGroup (Fin M) ℂ) (t : ℕ) :
    Matrix (PRSt M T) (PRSt M T) ℂ :=
  blockAt t (legalProj M t *
    Matrix.kronecker (tensorPow t (projM1 N M))
      ((tensorPow t (rotProj D (projM1 N M))).map (starRingEnd ℂ)))

/-- **`Γ = ⊕_{t=0}^{T−1} Γ_t`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §5.1, p. 32). -/
noncomputable def gammaAll (N : ℕ) {M : ℕ} (T : ℕ) (D : Matrix.unitaryGroup (Fin M) ℂ) :
    Matrix (PRSt M T) (PRSt M T) ℂ :=
  ∑ t ∈ Finset.range T, gammaT N T D t

end RandPurIso.Completion


