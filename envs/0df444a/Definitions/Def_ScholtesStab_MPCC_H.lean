-- Prove2me | Definitions.Def_ScholtesStab_MPCC_H
-- name    : ScholtesStab_MPCC_H
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:22.194758+00:00
-- url     : https://prove2.me/theorems/94f3d9df-2cff-42cb-8cc1-011dca778fa0
-- title:
--   Active index sets $\mathcal H(x)$, $\mathcal N_1(x)$, $\mathcal N_2(x)$ of $\mathcal S$
-- statement:
--   For a point $x\in M^{\mathcal S}$ of the Scholtes regularization with parameter $t$, the index sets of active constraints are
--
--   $$
--   \mathcal H(x)=\{j\mid F_{1,j}(x)\cdot F_{2,j}(x)=t\},\qquad \mathcal N_1(x)=\{j\mid F_{1,j}(x)=0\},\qquad \mathcal N_2(x)=\{j\mid F_{2,j}(x)=0\}.
--   $$
--
--   For $t>0$, $\mathcal H(x)$ is disjoint from $\mathcal N_1(x)\cup\mathcal N_2(x)$.
--
--   **Formalization Note** The parameter $t$, suppressed in the paper's notation, is an explicit argument of `H`.
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, §2.2, p.7

import Mathlib
import Definitions.Def_ScholtesStab_MPCC

namespace ScholtesStab

namespace MPCC

variable {n κ : ℕ}

/-- **Active index sets of the Scholtes regularization S.**
Lämmel–Shikhman, arXiv:2501.07383v2, §2.2, p.7: `ℋ(x) = {j | F₁,ⱼ(x) · F₂,ⱼ(x) = t}`.

**Formalization Note.** The parameter `t`, suppressed in the paper's notation, is explicit. -/
noncomputable def H (P : MPCC n κ) (t : ℝ) (x : E n) : Finset (Fin κ) :=
  Finset.univ.filter fun j => P.F₁ j x * P.F₂ j x = t

/-- `𝒩₁(x) = {j | F₁,ⱼ(x) = 0}` (p.7). -/
noncomputable def N1 (P : MPCC n κ) (x : E n) : Finset (Fin κ) :=
  Finset.univ.filter fun j => P.F₁ j x = 0

/-- `𝒩₂(x) = {j | F₂,ⱼ(x) = 0}` (p.7). -/
noncomputable def N2 (P : MPCC n κ) (x : E n) : Finset (Fin κ) :=
  Finset.univ.filter fun j => P.F₂ j x = 0

end MPCC

end ScholtesStab


