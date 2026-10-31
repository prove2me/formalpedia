-- Prove2me | Definitions.Def_ScholtesStab_MPCC_IsNondegKKT
-- name    : ScholtesStab_MPCC_IsNondegKKT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:29.302519+00:00
-- url     : https://prove2.me/theorems/ccdf800c-ddd7-4005-b45f-141802e6dc24
-- title:
--   Nondegenerate KKT point of $\mathcal S$ (ND1–ND3) and its quadratic index
-- statement:
--   A Karush–Kuhn–Tucker point $x\in M^{\mathcal S}$ of $\mathcal S$ with multipliers $(\eta,\nu)$ is **nondegenerate** if
--
--   1. ND1: LICQ holds at $x$;
--   2. ND2: $\eta_j>0$ for $j\in\mathcal H(x)$, $\nu_{1,j}>0$ for $j\in\mathcal N_1(x)$, and $\nu_{2,j}>0$ for $j\in\mathcal N_2(x)$;
--   3. ND3: the restricted Hessian $D^2L^{\mathcal S}(x)\restriction_{\mathcal T^{\mathcal S}_x}$ is nonsingular.
--
--   The **quadratic index** of a nondegenerate KKT point is the number of negative eigenvalues of $D^2L^{\mathcal S}(x)\restriction_{\mathcal T^{\mathcal S}_x}$ (`QIS`).
--
--   **Formalization Note** $D^2L^{\mathcal S}(x)$ is the second Fréchet derivative of $L^{\mathcal S}$; the quadratic index is `negIndex` on $\mathcal T^{\mathcal S}_x$. `QIS` is defined for every point and multiplier tuple; the theorems assume nondegeneracy.
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, p.8, Definitions 7 and 8

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_MPCC_H
import Definitions.Def_ScholtesStab_MPCC_LICQ
import Definitions.Def_ScholtesStab_MPCC_IsKKT
import Definitions.Def_ScholtesStab_MPCC_lagrangianS
import Definitions.Def_ScholtesStab_negIndex

namespace ScholtesStab

namespace MPCC

variable {n κ : ℕ}

/-- **Definition 7 (Nondegenerate Karush–Kuhn–Tucker point)**, Lämmel–Shikhman,
arXiv:2501.07383v2, p.8: "A Karush-Kuhn-Tucker point x ∈ Mˢ of S with multipliers (η, ν) is
called nondegenerate if
ND1: LICQ holds at x,
ND2: the multipliers for active inequality constraints do not vanish, i.e. ηⱼ > 0, j ∈ ℋ(x),
ν₁,ⱼ > 0, j ∈ 𝒩₁(x), and ν₂,ⱼ > 0, j ∈ 𝒩₂(x),
ND3: the restricted Hessian matrix D²Lˢ(x)↾𝒯ˢ_x is nonsingular."

**Formalization Note.** `D²Lˢ(x)` is `fderiv ℝ (fderiv ℝ Lˢ) x`; ND3 is `NonsingularOn` on
`𝒯ˢ_x`. -/
def IsNondegKKT (P : MPCC n κ) (t : ℝ) (x : E n) (μ : SMult κ) : Prop :=
  P.IsKKT t x μ ∧ P.LICQ t x ∧
    ((∀ j ∈ P.H t x, 0 < μ.η j) ∧ (∀ j ∈ P.N1 x, 0 < μ.ν₁ j) ∧ ∀ j ∈ P.N2 x, 0 < μ.ν₂ j) ∧
    NonsingularOn (fderiv ℝ (fderiv ℝ (P.lagrangianS t μ)) x) (P.tangentSpaceS t x)

/-- **Definition 8 (Quadratic index)** (p.8): "Let x ∈ Mˢ be a nondegenerate Karush-Kuhn-Tucker
point of S with unique multipliers (η, ν). The number of negative eigenvalues of the matrix
D²Lˢ(x)↾𝒯ˢ_x is called its quadratic index (QI)."

**Formalization Note.** Defined for every `(t, x, μ)`; theorems assume `IsNondegKKT`. -/
noncomputable def QIS (P : MPCC n κ) (t : ℝ) (x : E n) (μ : SMult κ) : ℕ :=
  negIndex (fderiv ℝ (fderiv ℝ (P.lagrangianS t μ)) x) (P.tangentSpaceS t x)

end MPCC

end ScholtesStab


