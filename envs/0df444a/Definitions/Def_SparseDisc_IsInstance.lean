-- Prove2me | Definitions.Def_SparseDisc_IsInstance
-- name    : SparseDisc_IsInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:53:27.853482+00:00
-- url     : https://prove2.me/theorems/cf4ba210-d200-4924-b88a-a83c4450453b
-- title:
--   Instance $(g_v, U_v)_{v \in V}$
-- statement:
--   An **instance** on a finite item set $\iota$ is a family $(g_v, U_v)_{v \in V}$ in which every $g_v : \{\pm1\}^{\iota} \to \mathbb R$ is odd and 2-Lipschitz and depends only on the coordinates in its support $U_v \subseteq \iota$: if $x$ and $y$ agree on $U_v$ then $g_v(x) = g_v(y)$.
--
--   Instances are the reformulation in which all upper bounds are proved; a family of 1-Lipschitz set functions yields the instance $(g_f, R(f))_{f \in F}$ (Lemma 2.1).
--
--   **Formalization Note** Sparsity of the supports is the separate predicate `SparseDisc.IsTwoSparseSupp`.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Definition 2.2, pp.11–12

import Mathlib
import Definitions.Def_SparseDisc_IsOdd
import Definitions.Def_SparseDisc_IsLip

namespace SparseDisc

/-- `IsInstance g U`: `(g_v, U_v)_{v ∈ V}` is an **instance** on the items `ι` — every
`g_v : {±1}^ι → ℝ` is odd and 2-Lipschitz and depends only on the coordinates in its support
`U_v ⊆ ι` (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027
submission manuscript (sha256 0f09ec60…25b81), Definition 2.2, pp.11–12).

**Formalization Note** The item set `[m]` is a finite type `ι` and the index set `V` a type.
"Depends only on `U_v`" is: `x` and `y` agreeing on `U_v` give the same value. Sparsity is the
separate predicate `IsTwoSparseSupp`. -/
def IsInstance {V ι : Type} [Fintype ι] (g : V → Cube ι → ℝ) (U : V → Finset ι) : Prop :=
  ∀ v, IsOdd (g v) ∧ IsLip 2 (g v) ∧ ∀ x y : Cube ι, (∀ j ∈ U v, x j = y j) → g v x = g v y

end SparseDisc


