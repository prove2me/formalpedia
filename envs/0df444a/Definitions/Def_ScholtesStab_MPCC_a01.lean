-- Prove2me | Definitions.Def_ScholtesStab_MPCC_a01
-- name    : ScholtesStab_MPCC_a01
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:10.250519+00:00
-- url     : https://prove2.me/theorems/eac72c9b-9ff9-42ef-bc92-060fd5b47365
-- title:
--   Active index sets $a_{01}(\bar x)$, $a_{10}(\bar x)$, $a_{00}(\bar x)$ of MPCC
-- statement:
--   For $\bar x\in\mathbb R^n$ the index sets of active constraints of MPCC are
--
--   $$
--   a_{01}(\bar x)=\{j \mid F_{1,j}(\bar x)=0,\ F_{2,j}(\bar x)>0\},\quad
--   a_{10}(\bar x)=\{j \mid F_{1,j}(\bar x)>0,\ F_{2,j}(\bar x)=0\},\quad
--   a_{00}(\bar x)=\{j \mid F_{1,j}(\bar x)=0,\ F_{2,j}(\bar x)=0\}.
--   $$
--
--   For a feasible point $\bar x\in M$ every index $j$ lies in exactly one of the three sets; $a_{00}(\bar x)$ collects the **biactive** indices.
--
--   **Formalization Note** The sets are finite sets of 0-based indices (`Finset (Fin κ)`), so their cardinalities are `Finset.card`.
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, §2.1, p.5

import Mathlib
import Definitions.Def_ScholtesStab_MPCC

namespace ScholtesStab

namespace MPCC

variable {n κ : ℕ}

/-- **Index sets of active constraints of MPCC.**
Lämmel–Shikhman, arXiv:2501.07383v2, §2.1, p.5:
`a₀₁(x̄) = {j | F₁,ⱼ(x̄) = 0, F₂,ⱼ(x̄) > 0}`. -/
noncomputable def a01 (P : MPCC n κ) (x : E n) : Finset (Fin κ) :=
  Finset.univ.filter fun j => P.F₁ j x = 0 ∧ 0 < P.F₂ j x

/-- `a₁₀(x̄) = {j | F₁,ⱼ(x̄) > 0, F₂,ⱼ(x̄) = 0}` (p.5). -/
noncomputable def a10 (P : MPCC n κ) (x : E n) : Finset (Fin κ) :=
  Finset.univ.filter fun j => 0 < P.F₁ j x ∧ P.F₂ j x = 0

/-- `a₀₀(x̄) = {j | F₁,ⱼ(x̄) = 0, F₂,ⱼ(x̄) = 0}` (p.5), the biactive indices.

**Formalization Note.** The sets are `Finset`s of 0-based indices `Fin κ`, so that their
cardinalities are `Finset.card`. -/
noncomputable def a00 (P : MPCC n κ) (x : E n) : Finset (Fin κ) :=
  Finset.univ.filter fun j => P.F₁ j x = 0 ∧ P.F₂ j x = 0

end MPCC

end ScholtesStab


