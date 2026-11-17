-- Prove2me | Definitions.Def_AnchoredEP_Supplement_methodIterate
-- name    : AnchoredEP_Supplement_methodIterate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:12:31.540403+00:00
-- url     : https://prove2.me/theorems/bca92a23-0133-41d5-827e-7901485e4af2
-- title:
--   Points produced by a deterministic $p$th-order method
-- statement:
--   Running a deterministic $p$th-order method $M$ from $z_0$ on the oracle of an operator $F:\mathbb R^n\to\mathbb R^n$ produces the points
--   $$
--   z_0,\qquad z_{t}=M_{t}\big(\{D^jF(z_s)\}_{0\le j\le p-1,\ 0\le s<t}\big)\quad(t\ge1).
--   $$
--   The output of the method after $N$ oracle queries (at $z_0,\dots,z_{N-1}$) is $z_N$. The method sees $F$ only through the oracle outputs at its previous points.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Section 6, p.12

import Mathlib
import Definitions.Def_AnchoredEP_Supplement_OracleOutput
import Definitions.Def_AnchoredEP_Supplement_oracleResponse
import Definitions.Def_AnchoredEP_Supplement_PthOrderMethod

namespace AnchoredEP.Supplement

/-- **The points produced by a deterministic `p`th-order method on an operator.** Jiang–Yoon,
arXiv:2609.30212, Section 6, p.12: `z₀` is the given starting point and, for `t ≥ 1`, `z_t` is the
method's function of the oracle outputs at `z_0, …, z_{t−1}`.

`methodIterate M z0 F t` is `z_t` when the method `M` is run on the oracle of `F` (for a
fixed-point problem, of `T`). The output after `N` oracle queries (the queries `z_0, …, z_{N−1}`)
is `methodIterate M z0 F N`.

**Formalization Note.** The method sees `F` only through `oracleResponse p F` at its previous
points. -/
noncomputable def methodIterate {p n : ℕ} (M : PthOrderMethod p n) (z0 : EuclideanSpace ℝ (Fin n))
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => z0
  | t + 1 => M (t + 1) (fun s : Fin (t + 1) => oracleResponse p F (methodIterate M z0 F s))
termination_by t => t
decreasing_by exact s.isLt

end AnchoredEP.Supplement


