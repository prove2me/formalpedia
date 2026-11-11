-- Prove2me | Definitions.Def_RandPurIso_Completion_lam
-- name    : RandPurIso_Completion_lam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:02.284924+00:00
-- url     : https://prove2.me/theorems/a96909f5-b03e-404c-9f14-fa7fced33821
-- title:
--   Reweightings $\Lambda_t$, $\Lambda_t^+$
-- statement:
--   On the input slots of $\mathcal R_t$,
--   $$\Lambda_t=\sum_{|\lambda|=t,\ \ell(\lambda)\le N}\sqrt{\frac{f_\lambda}{d_{\lambda,N}}}\,(\Pi_{\lambda,t}\otimes I),\qquad \Lambda_t^+=\sum_{|\lambda|=t,\ \ell(\lambda)\le N}\sqrt{\frac{d_{\lambda,N}}{f_\lambda}}\,(\Pi_{\lambda,t}\otimes I),$$
--   with $\Lambda_0=\Lambda_0^+=I$, where $\Pi_{\lambda,t}$ is the orthogonal projector onto $\mathcal Q_{\lambda,N}\otimes\mathcal P_\lambda$ in the Schur–Weyl decomposition of $\mathcal H([N])^{\otimes t}$ and $I$ acts on the conjugate output slots.
--
--   **Formalization Note** $\Pi_{\lambda,t}$ is the published `QAlgorithms.Schur.isotypicProjector` (the full $\lambda$-isotypic projector of the permutation action) and the diagrams with $t$ boxes and at most $N$ rows are `QAlgorithms.Schur.Partition N t`.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, §3.4, pp. 23–24

import Mathlib
import Definitions.Def_RandPurIso_Completion_PRSt
import Definitions.Def_RandPurIso_Completion_hookLength
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
open Matrix

namespace RandPurIso.Completion

/-- A reweighting `Σ_{|λ|=t, ℓ(λ)≤N} c_λ Π_{λ,t}` on `H([N])^{⊗t}`, and `I` for `t = 0`
(Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §3.4, pp. 23–24). `Π_{λ,t}` is the projector onto `Q_{λ,N} ⊗ P_λ`
(`QAlgorithms.Schur.isotypicProjector`); `QAlgorithms.Schur.Partition N t` is the set of Young
diagrams with `t` boxes and at most `N` rows. -/
noncomputable def reweightIn (N t : ℕ) (coef : QAlgorithms.Schur.Partition N t → ℝ) :
    Matrix (Fin t → Fin N) (Fin t → Fin N) ℂ :=
  if t = 0 then 1 else ∑ μ, ((coef μ : ℝ) : ℂ) • QAlgorithms.Schur.isotypicProjector μ

/-- Input-slot part of `Λ_t`: `Σ_λ √(f_λ / d_{λ,N}) Π_{λ,t}`. -/
noncomputable def lamIn (N t : ℕ) : Matrix (Fin t → Fin N) (Fin t → Fin N) ℂ :=
  reweightIn N t fun μ => Real.sqrt (spechtDim t μ.1 / weylDim N μ.1)

/-- Input-slot part of `Λ⁺_t`: `Σ_λ √(d_{λ,N} / f_λ) Π_{λ,t}`. -/
noncomputable def lamPlusIn (N t : ℕ) : Matrix (Fin t → Fin N) (Fin t → Fin N) ℂ :=
  reweightIn N t fun μ => Real.sqrt (weylDim N μ.1 / spechtDim t μ.1)

/-- **Reweighting `Λ_t`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §3.4, p. 23): `Λ_t = Σ_{|λ|=t, ℓ(λ)≤N} √(f_λ/d_{λ,N}) (Π_{λ,t} ⊗ I)`
on `R_t`, acting only on the input slots; `Λ_0 = I`. -/
noncomputable def lam (N t : ℕ) : Matrix (Rt N t) (Rt N t) ℂ := Matrix.kronecker (lamIn N t) 1

/-- **Reweighting `Λ⁺_t`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §3.4, p. 23): `Σ √(d_{λ,N}/f_λ) (Π_{λ,t} ⊗ I)`; `Λ⁺_0 = I`. -/
noncomputable def lamPlus (N t : ℕ) : Matrix (Rt N t) (Rt N t) ℂ := Matrix.kronecker (lamPlusIn N t) 1

end RandPurIso.Completion


