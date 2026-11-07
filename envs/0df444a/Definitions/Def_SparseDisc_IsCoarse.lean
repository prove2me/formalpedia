-- Prove2me | Definitions.Def_SparseDisc_IsCoarse
-- name    : SparseDisc_IsCoarse
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:53:27.130639+00:00
-- url     : https://prove2.me/theorems/84fc2644-ccc4-43b2-b136-a400592a0e12
-- title:
--   $c$-coarse subset of the cube
-- statement:
--   Let $c \ge 1$. A set $Z \subseteq \{\pm1\}^U$ is **$c$-coarse** if it is symmetric ($Z = -Z$) and
--   $$
--   Z \supseteq \{ z : |\varphi(z)| \le c \}
--   $$
--   for some odd 2-Lipschitz function $\varphi$ on $\{\pm1\}^U$. Coarse sets are the local constraints of the paper's constraint systems.
--
--   **Formalization Note** The predicate is written for every real $c$; every statement that uses it assumes $c \ge 1$ (or levels $\ell \ge 1$) explicitly, as Definition 8.2 does.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Definition 8.2, p.29

import Mathlib
import Definitions.Def_SparseDisc_IsOdd
import Definitions.Def_SparseDisc_IsLip

namespace SparseDisc

/-- `IsCoarse c Z`: `Z ⊆ {±1}^U` is **`c`-coarse** — symmetric, and `Z ⊇ {z : |φ(z)| ≤ c}` for some
odd 2-Lipschitz `φ` on `{±1}^U` (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive
Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), Definition 8.2, p.29).

**Formalization Note** Definition 8.2 is made for `c ≥ 1`; the predicate is written for every real
`c`, and every statement that uses it assumes `1 ≤ c` (or levels `ℓ ≥ 1`) explicitly. -/
def IsCoarse {U : Type} [Fintype U] (c : ℝ) (Z : Set (Cube U)) : Prop :=
  (∀ z, z ∈ Z ↔ -z ∈ Z) ∧ ∃ φ : Cube U → ℝ, IsOdd φ ∧ IsLip 2 φ ∧ {z | |φ z| ≤ c} ⊆ Z

end SparseDisc


