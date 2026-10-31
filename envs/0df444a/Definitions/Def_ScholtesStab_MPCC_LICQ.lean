-- Prove2me | Definitions.Def_ScholtesStab_MPCC_LICQ
-- name    : ScholtesStab_MPCC_LICQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:37.969478+00:00
-- url     : https://prove2.me/theorems/b744eb38-d1b3-4ce1-85fc-5b02e6ba5f0e
-- title:
--   LICQ for the Scholtes regularization $\mathcal S$
-- statement:
--   A feasible point $x\in M^{\mathcal S}$ of $\mathcal S$ satisfies the **linear independence constraint qualification (LICQ)** if the vectors
--
--   $$
--   F_{2,j}(x)DF_{1,j}(x)+F_{1,j}(x)DF_{2,j}(x),\ j\in\mathcal H(x),\qquad DF_{1,j}(x),\ j\in\mathcal N_1(x),\qquad DF_{2,j}(x),\ j\in\mathcal N_2(x),
--   $$
--
--   are linearly independent. The first group are the differentials of the active product constraints $F_{1,j}F_{2,j}\le t$.
--
--   **Formalization Note** The family is indexed by the disjoint union $\mathcal H(x)\sqcup\mathcal N_1(x)\sqcup\mathcal N_2(x)$. Feasibility is a separate hypothesis in the theorems.
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, p.7, Definition 5

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_MPCC_H

namespace ScholtesStab

namespace MPCC

variable {n κ : ℕ}

/-- **Definition 5 (LICQ)**, Lämmel–Shikhman, arXiv:2501.07383v2, p.7: "We say that a feasible
point x ∈ Mˢ of S satisfies the linear independence constraint qualification (LICQ) if the
following vectors are linearly independent:
F₂,ⱼ(x)DF₁,ⱼ(x) + F₁,ⱼ(x)DF₂,ⱼ(x), j ∈ ℋ(x),   DF₁,ⱼ(x), j ∈ 𝒩₁(x),   DF₂,ⱼ(x), j ∈ 𝒩₂(x)."

**Formalization Note.** An *indexed* family on the disjoint union `ℋ(x) ⊕ 𝒩₁(x) ⊕ 𝒩₂(x)`, so
repeated vectors count separately. Differentials are `fderiv ℝ · x : ℝⁿ →L[ℝ] ℝ`. Feasibility
`x ∈ Mˢ` is a separate hypothesis wherever the paper assumes it. -/
def LICQ (P : MPCC n κ) (t : ℝ) (x : E n) : Prop :=
  LinearIndependent ℝ
    (Sum.elim
      (fun j : ↥(P.H t x) => P.F₂ j x • fderiv ℝ (P.F₁ j) x + P.F₁ j x • fderiv ℝ (P.F₂ j) x)
      (Sum.elim (fun j : ↥(P.N1 x) => fderiv ℝ (P.F₁ j) x)
        (fun j : ↥(P.N2 x) => fderiv ℝ (P.F₂ j) x)))

end MPCC

end ScholtesStab


