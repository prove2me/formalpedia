-- Prove2me | Definitions.Def_ScholtesStab_MPCC_CI
-- name    : ScholtesStab_MPCC_CI
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:14.06912+00:00
-- url     : https://prove2.me/theorems/4501ba6f-363e-430d-8750-5f6766b585ac
-- title:
--   Quadratic index QI, biactive index BI and C-index CI
-- statement:
--   Let $\bar x\in M$ be a nondegenerate C-stationary point of MPCC with multipliers $(\bar\sigma,\bar\varrho)$. Its **quadratic index** QI is the number of negative eigenvalues of $D^2L(\bar x)\restriction_{\mathcal T_{\bar x}}$; its **biactive index** BI is the number of indices $j\in a_{00}(\bar x)$ with $\bar\varrho_{1,j},\bar\varrho_{2,j}<0$, i.e. $|a^{-}_{00}(\bar x)|$; and its **C-index** is
--
--   $$
--   CI=QI+BI.
--   $$
--
--   The C-index is the topological invariant of a nondegenerate C-stationary point in the Morse theory of MPCC: it is the dimension of the cell attached when passing the point.
--
--   **Formalization Note** QI is `negIndex` of the Hessian of $L$ on $\mathcal T_{\bar x}$. The three functions are defined for every point and multiplier tuple; the theorems assume nondegeneracy.
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, p.6, Definition 4

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_MPCC_IsCStationary
import Definitions.Def_ScholtesStab_MPCC_lagrangian
import Definitions.Def_ScholtesStab_MPCC_a01neg
import Definitions.Def_ScholtesStab_negIndex

namespace ScholtesStab

namespace MPCC

variable {n κ : ℕ}

/-- **Definition 4 (C-index): quadratic index QI.** Lämmel–Shikhman, arXiv:2501.07383v2, p.6:
"The number of negative eigenvalues of the matrix D²L(x̄)↾𝒯_x̄ is called its quadratic index
(QI)." Computed as `negIndex` of `fderiv ℝ (fderiv ℝ L) x̄` on `𝒯_x̄`. -/
noncomputable def QI (P : MPCC n κ) (xbar : E n) (m : MPCCMult κ) : ℕ :=
  negIndex (fderiv ℝ (fderiv ℝ (P.lagrangian xbar m)) xbar) (P.tangentSpace xbar)

/-- **Definition 4: biactive index BI** (p.6): "The number of negative pairs ϱ̄₁,ⱼ, ϱ̄₂,ⱼ,
j ∈ a₀₀(x̄) with ϱ̄₁,ⱼ, ϱ̄₂,ⱼ < 0 is called the biactive index (BI) of x̄", i.e. `|a⁻₀₀(x̄)|`. -/
noncomputable def BI (P : MPCC n κ) (xbar : E n) (m : MPCCMult κ) : ℕ :=
  (P.a00neg xbar m).card

/-- **Definition 4: C-index** (p.6): "We define the C-index (CI) as the sum of both, i. e.
CI = QI + BI."

**Formalization Note.** The paper defines CI for a nondegenerate C-stationary point with its
unique multipliers; the function is defined for every `(x̄, m)` and the theorems assume
nondegeneracy. -/
noncomputable def CI (P : MPCC n κ) (xbar : E n) (m : MPCCMult κ) : ℕ :=
  P.QI xbar m + P.BI xbar m

end MPCC

end ScholtesStab


