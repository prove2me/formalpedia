-- Prove2me | Definitions.Def_MatMulDS_fiveTensor
-- name    : MatMulDS_fiveTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:40.623202+00:00
-- url     : https://prove2.me/theorems/5ffdb58c-a056-4901-8283-a2c3e3648514
-- title:
--   The five-term tensor and identity
-- statement:
--   The **five-term tensor** is $T_5=\sum_{i,j\in\{1,2\}}x_iy_jz_{ij}+(p_1y_1+p_2q)z_0$, a block tensor with a short block and a central block whose right variables share $y_1$. Its **five-term identity** has products
--   $$P_{11}=(x_1+\varepsilon^2p_1)y_1,\ P_{21}=x_2(y_1-\varepsilon q),\ P_{12}=(x_1-\varepsilon p_2)y_2,\ P_{22}=(x_2+\varepsilon p_2)(y_2+\varepsilon q),\ P_0=(-x_1-x_2)(y_1+y_2).$$
--   Each $z_{ij}$ is $\varepsilon^2P_{ij}$, and $z_0$ is the sum of all five products, so $h=2$.
--
--   The private map sends $z_{ij}\mapsto P_{ij}$ and $z_0\mapsto P_0$, and the weight gives $P_0$ weight $1$ and the others $0$. All identities of the mission are built from this one.
--
--   **Formalization Note** Indices are 0-based: $x_i=x_{i-1,0}$, $p_1=x_{2,0}$, $p_2=x_{2,1}$, $y_j=y_{0,j-1}$, $q=y_{1,0}$, $z_{ij}=z_{i-1,j-1}$, $z_0=z_{2,0}$.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), (5.1), (5.2), (F3), (F4), p.26 (PDF p.28); p.28 (PDF p.30)

import Mathlib
import Definitions.Def_MatMulDS_IdentityData

set_option autoImplicit false

open Polynomial

namespace MatMulDS

/-- **The five-term tensor** `T5 = Σ_{i,j∈{1,2}} x_i y_j z_ij + (p1 y1 + p2 q) z0`, (5.1), p.26 (STOC 2027
submission, held file sha256 6c5a1c16…), as the block tensor of p.28: a short block (index `0`) with rows `{1,2}`,
middle index `{1}` and columns `{1,2}`, and a central block (index `1`) with row `{3}`, middle indices `{1,2}` and
column `{1}`.

**Formalization Note** Indices are 0-based: `x_i = x_(i-1, 0)`, `p1 = x_(2,0)`, `p2 = x_(2,1)`, `y_j = y_(0, j-1)`,
`q = y_(1,0)`, `z_ij = z_(i-1, j-1)`, `z0 = z_(2,0)`. -/
def fiveTensor : BlockTensor (Fin 3) (Fin 2) (Fin 2) (Fin 2) where
  rows β := if β = 0 then {0, 1} else {2}
  mids β := if β = 0 then {0} else {0, 1}
  cols β := if β = 0 then {0, 1} else {0}
  rows_nonempty := by decide
  mids_nonempty := by decide
  cols_nonempty := by decide
  rows_disjoint := by decide

/-- **The five-term identity** (5.2), p.26. The products are `P11, P21, P12, P22, P0`, with indices `0, 1, 2, 3, 4`:
`(x1 + ε²p1) y1`, `x2 (y1 − εq)`, `(x1 − εp2) y2`, `(x2 + εp2)(y2 + εq)`, `(−x1 − x2)(y1 + y2)`. The output
`z_ij` is `ε²` times the product `P_ij`, and `z0` is the sum of all five products, so `h = 2`. -/
noncomputable def fiveData : IdentityData (Fin 3) (Fin 2) (Fin 2) (Fin 5) where
  U p a := match p, a with
    | 0, (0, 0) => 1
    | 0, (2, 0) => X ^ 2
    | 1, (1, 0) => 1
    | 2, (0, 0) => 1
    | 2, (2, 1) => -X
    | 3, (1, 0) => 1
    | 3, (2, 1) => X
    | 4, (0, 0) => -1
    | 4, (1, 0) => -1
    | _, _ => 0
  V p b := match p, b with
    | 0, (0, 0) => 1
    | 1, (0, 0) => 1
    | 1, (1, 0) => -X
    | 2, (0, 1) => 1
    | 3, (0, 1) => 1
    | 3, (1, 0) => X
    | 4, (0, 0) => 1
    | 4, (0, 1) => 1
    | _, _ => 0
  C o p := match o, p with
    | (0, 0), 0 => X ^ 2
    | (1, 0), 1 => X ^ 2
    | (0, 1), 2 => X ^ 2
    | (1, 1), 3 => X ^ 2
    | (2, 0), _ => 1
    | _, _ => 0
  h := 2

/-- The private map of Item (F3) on index pairs: `z_ij ↦ P_ij` and `z0 ↦ P0`. -/
def fivePrivateFn : Fin 3 × Fin 2 → Fin 5
  | (0, 0) => 0
  | (1, 0) => 1
  | (0, 1) => 2
  | (1, 1) => 3
  | _ => 4

/-- The private map of Item (F3), p.26, as a map on outputs. -/
def fivePrivate (o : fiveTensor.Out) : Fin 5 := fivePrivateFn o.1

/-- The weight of Item (F4), p.26: `P0` has weight `1` and the four products `P_ij` have weight `0`. -/
noncomputable def fiveWeight (p : Fin 5) : ℝ := if p = 4 then 1 else 0

end MatMulDS


