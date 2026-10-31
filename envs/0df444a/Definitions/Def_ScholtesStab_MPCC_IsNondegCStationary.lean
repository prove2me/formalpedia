-- Prove2me | Definitions.Def_ScholtesStab_MPCC_IsNondegCStationary
-- name    : ScholtesStab_MPCC_IsNondegCStationary
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:08.240996+00:00
-- url     : https://prove2.me/theorems/0a91ceb5-4d09-429a-bebd-2c5245eaf9a8
-- title:
--   Nondegenerate C-stationary point (NDC1–NDC3) and condition NDC4
-- statement:
--   A C-stationary point $\bar x\in M$ of MPCC with multipliers $(\bar\sigma,\bar\varrho)$ is **nondegenerate** if
--
--   1. NDC1: MPCC-LICQ holds at $\bar x$;
--   2. NDC2: $\bar\varrho_{1,j}\cdot\bar\varrho_{2,j}>0$ for all $j\in a_{00}(\bar x)$;
--   3. NDC3: the restricted Hessian $D^2L(\bar x)\restriction_{\mathcal T_{\bar x}}$ is nonsingular.
--
--   For a nondegenerate C-stationary point the paper uses the additional condition
--
--   $$
--   \text{NDC4:}\quad \bar\sigma_{1,j}\neq 0 \ \text{ for all } j\in a_{01}(\bar x)\quad\text{and}\quad \bar\sigma_{2,j}\neq 0\ \text{ for all } j\in a_{10}(\bar x).
--   $$
--
--   **Formalization Note** $D^2L(\bar x)$ is the second Fréchet derivative of the Lagrange function $L$ at $\bar x$, as a bilinear form; NDC3 is `NonsingularOn` on $\mathcal T_{\bar x}$.
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, p.6, Definition 3

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_MPCC_a01
import Definitions.Def_ScholtesStab_MPCC_MPCCLICQ
import Definitions.Def_ScholtesStab_MPCC_IsCStationary
import Definitions.Def_ScholtesStab_MPCC_lagrangian
import Definitions.Def_ScholtesStab_negIndex

namespace ScholtesStab

namespace MPCC

variable {n κ : ℕ}

/-- **Definition 3 (Nondegenerate C-stationarity)**, Lämmel–Shikhman, arXiv:2501.07383v2, p.6:
"A C-stationary point x̄ ∈ M of MPCC with multipliers (σ̄, ϱ̄) is called nondegenerate if
NDC1: MPCC-LICQ holds at x̄,
NDC2: multipliers for biactive constraints do not vanish, i.e. ϱ̄₁,ⱼ · ϱ̄₂,ⱼ > 0, j ∈ a₀₀(x̄),
NDC3: the restricted Hessian matrix D²L(x̄)↾𝒯_x̄ is nonsingular."

**Formalization Note.** `D²L(x̄)` is the second Fréchet derivative
`fderiv ℝ (fderiv ℝ L) x̄`, a bilinear form on `ℝⁿ`; NDC3 is `NonsingularOn` on `𝒯_x̄`. -/
def IsNondegCStationary (P : MPCC n κ) (xbar : E n) (m : MPCCMult κ) : Prop :=
  P.IsCStationary xbar m ∧ P.MPCCLICQ xbar ∧
    (∀ j ∈ P.a00 xbar, 0 < m.ϱ₁ j * m.ϱ₂ j) ∧
    NonsingularOn (fderiv ℝ (fderiv ℝ (P.lagrangian xbar m)) xbar) (P.tangentSpace xbar)

/-- **NDC4** (p.6): "σ̄₁,ⱼ ≠ 0 for all j ∈ a₀₁(x̄) and σ̄₂,ⱼ ≠ 0 for all j ∈ a₁₀(x̄)." -/
def NDC4 (P : MPCC n κ) (xbar : E n) (m : MPCCMult κ) : Prop :=
  (∀ j ∈ P.a01 xbar, m.σ₁ j ≠ 0) ∧ ∀ j ∈ P.a10 xbar, m.σ₂ j ≠ 0

end MPCC

end ScholtesStab


