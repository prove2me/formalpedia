-- Prove2me | Definitions.Def_ScholtesStab_MPCC_MPCCLICQ
-- name    : ScholtesStab_MPCC_MPCCLICQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:02.244335+00:00
-- url     : https://prove2.me/theorems/9caa68c4-6839-49bb-9cfa-71641317e949
-- title:
--   MPCC-LICQ
-- statement:
--   A feasible point $\bar x\in M$ satisfies the **MPCC-tailored linear independence constraint qualification (MPCC-LICQ)** if the vectors
--
--   $$
--   DF_{1,j}(\bar x),\ j\in a_{01}(\bar x)\cup a_{00}(\bar x),\qquad DF_{2,j}(\bar x),\ j\in a_{10}(\bar x)\cup a_{00}(\bar x),
--   $$
--
--   are linearly independent. For a biactive index $j\in a_{00}(\bar x)$ both $DF_{1,j}(\bar x)$ and $DF_{2,j}(\bar x)$ belong to the family.
--
--   **Formalization Note** The family is indexed by the disjoint union of the two index sets, so a vector listed twice makes it dependent. Differentials are Fréchet derivatives $\mathbb R^n\to\mathbb R$; their linear independence is that of the gradients. Feasibility $\bar x\in M$ is a separate hypothesis in the theorems.
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, p.5, Definition 1

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_MPCC_a01

namespace ScholtesStab

namespace MPCC

variable {n κ : ℕ}

/-- **Definition 1 (MPCC-LICQ).** Lämmel–Shikhman, arXiv:2501.07383v2, p.5: "We say that a
feasible point x̄ ∈ M satisfies the MPCC-tailored linear independence constraint qualification
(MPCC-LICQ) if the following vectors are linearly independent:
DF₁,ⱼ(x̄), j ∈ a₀₁(x̄) ∪ a₀₀(x̄),   DF₂,ⱼ(x̄), j ∈ a₁₀(x̄) ∪ a₀₀(x̄)."

**Formalization Note.** The vectors form an *indexed* family on the disjoint union of the two
index sets, so for `j ∈ a₀₀(x̄)` both `DF₁,ⱼ(x̄)` and `DF₂,ⱼ(x̄)` are members, and a repeated
vector makes the family dependent. The differentials `DF(x̄)` are the Fréchet derivatives
`fderiv ℝ F x̄ : ℝⁿ →L[ℝ] ℝ` (row vectors); their linear independence is that of the gradients.
Feasibility `x̄ ∈ M` is a separate hypothesis wherever the paper assumes it. -/
def MPCCLICQ (P : MPCC n κ) (x : E n) : Prop :=
  LinearIndependent ℝ
    (Sum.elim (fun j : ↥(P.a01 x ∪ P.a00 x) => fderiv ℝ (P.F₁ j) x)
      (fun j : ↥(P.a10 x ∪ P.a00 x) => fderiv ℝ (P.F₂ j) x))

end MPCC

end ScholtesStab


