-- Prove2me | Definitions.Def_SelfDualLP_Regularity_LPData
-- name    : SelfDualLP_Regularity_LPData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:34.29236+00:00
-- url     : https://prove2.me/theorems/4cf4f0eb-73c8-4f7a-9364-f5bc78a1e34b
-- title:
--   Standard-form (LP) and (LD): feasibility and coordinatewise interior
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, and $c\in\mathbb R^n$. The paper's primal and dual linear programs are
--   $$
--   \text{(LP)}\quad \min\{c^Tx:Ax=b,\ x\ge0\},\qquad
--   \text{(LD)}\quad \max\{b^Ty:A^Ty\le c\}.
--   $$
--   The primal interior condition means $Ax=b$ and $x_j>0$ for every coordinate $j$. The dual interior condition means the slack $s=c-A^Ty$ has $s_j>0$ for every coordinate. Dual variables $y$ are unrestricted.
--
--   These predicates identify exactly the feasible and strictly feasible points used in Theorem 9. The standard-form LP and dual feasible sets come from the referenced published general-form LP definition; the coordinatewise interior predicates specialize the paper's notation $\mathcal F^0$.
--
--   **Formalization Note** When $n=0$, coordinatewise positivity is vacuous, while primal equality still has to hold.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 53, (LP), (LD), F and F⁰; DOI 10.1287/moor.19.1.53

import Definitions.Def_LinearOptimization_DualLP

open Matrix

namespace SelfDualLP.Regularity

/-- The paper's (LP), in the published standard-form representation. -/
def PrimalFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  x ∈ LinearOptimization.generalFeasibleSet (LinearOptimization.stdFormLP A b c)

/-- The paper's (LD), `max bᵀy` subject to `Aᵀy ≤ c`, with `y` free. -/
def DualFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (y : Fin m → ℝ) : Prop :=
  y ∈ LinearOptimization.dualFeasibleStd A c

/-- Interior feasibility of (LP): `Ax = b` and every `xⱼ > 0`. -/
def PrimalInterior {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ j, 0 < x j

/-- Interior feasibility of (LD): every slack `cⱼ - (Aᵀy)ⱼ > 0`. -/
def DualInterior {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (y : Fin m → ℝ) : Prop :=
  ∀ j, 0 < c j - (Aᵀ *ᵥ y) j

end SelfDualLP.Regularity


