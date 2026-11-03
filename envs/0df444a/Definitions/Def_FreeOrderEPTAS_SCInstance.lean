-- Prove2me | Definitions.Def_FreeOrderEPTAS_SCInstance
-- name    : FreeOrderEPTAS_SCInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:37.193171+00:00
-- url     : https://prove2.me/theorems/28b5bd96-ded0-4aad-a964-e21c698ecbc6
-- title:
--   Multi-Dimensional Santa Claus instances
-- statement:
--   An instance of **Multi-Dimensional Santa Claus** in normal form has $m$ machines, $D$ dimensions and $n$ jobs. Machine $i$ accepts at most $k_i$ jobs and has a set $A_i\subseteq[D]$ of active dimensions, and assigning job $j$ to machine $i$ incurs the load $\ell_{ijd}\in[0,1]$ along dimension $d$.
--
--   The paper reaches this form without loss of generality by scaling the lower bounds $L_i$ to binary vectors, with $A_i=\{d:L_{id}=1\}$, and truncating loads at $1$.
--
--   **Formalization Note** `Assignment m n` is a binary matrix, which builds in constraint (I) of (IP). `bit` is the real value of a binary variable.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §2.1, p.8

import Mathlib

namespace FreeOrderEPTAS

/-- An instance of Multi-Dimensional Santa Claus in the normal form of §2.1 (arXiv:2007.13121v3,
p.8): `m` machines with capacities `k_i`, `D` dimensions, `n` jobs, the active dimensions
`A_i = {d : L_id = 1}` (the lower bounds are binary after scaling), and loads `ℓ_ijd ∈ [0, 1]`. -/
structure SCInstance (m D n : ℕ) where
  /-- The bound `k_i` on the number of jobs of machine `i`. -/
  k : Fin m → ℕ
  /-- The active dimensions `A_i` of machine `i`. -/
  A : Fin m → Finset (Fin D)
  /-- The load `ℓ_ijd`. -/
  ℓ : Fin m → Fin n → Fin D → ℝ
  /-- `ℓ_ijd ∈ [0, 1]`. -/
  ℓ_mem : ∀ i j d, ℓ i j d ∈ Set.Icc (0 : ℝ) 1

/-- A binary matrix `x ∈ {0, 1}^{m × n}`, which builds in constraint (I) of (IP). -/
abbrev Assignment (m n : ℕ) : Type := Fin m → Fin n → Bool

/-- The real value of a binary variable. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

end FreeOrderEPTAS


