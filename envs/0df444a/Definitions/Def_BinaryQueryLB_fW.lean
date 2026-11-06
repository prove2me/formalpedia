-- Prove2me | Definitions.Def_BinaryQueryLB_fW
-- name    : BinaryQueryLB_fW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:44.856855+00:00
-- url     : https://prove2.me/theorems/168631a5-da21-4b9f-a197-94f6270b7451
-- title:
--   The max-affine function $f_W$
-- statement:
--   For an $m\times m$ matrix $W$ with rows $w_i$ and $q=(x,z)\in\mathbb R^{2m}$,
--   $$
--   f_W(q)=\max_{i\in[m]}\big\{a x_i+\langle w_i,z\rangle\big\}=\max_{i\in[m]}\langle v_i(W),q\rangle .
--   $$
--
--   **Formalization Note** The maximum is a real supremum over the finite index set, a genuine maximum for $m\ge1$, which all theorems assume.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.4, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_xPart
import Definitions.Def_BinaryQueryLB_zPart
import Definitions.Def_BinaryQueryLB_aConst

namespace BinaryQueryLB

/-- **The max-affine function `f_W` (Definition 2.4).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.4, p.12:
"`f_W(q) = max_{i∈[m]} {a x_i + ⟨w_i, z⟩} = max_{i∈[m]} ⟨v_i(W), q⟩`".

**Formalization Note.** The maximum over the finite index set `Fin m` is a real supremum; it is a
genuine maximum whenever `m ≥ 1`, which every theorem assumes (for `m = 0` the value is `0`). -/
noncomputable def fW {m : ℕ} (W : Fin m → EuclideanSpace ℝ (Fin m)) (q : PtSpace m) : ℝ :=
  ⨆ i, aConst * xPart q i + inner ℝ (W i) (zPart q)

end BinaryQueryLB


