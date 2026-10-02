-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_PolarCone
-- name    : DiscreteConvex_ConjugacyDualityB_PolarCone
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:28:11.72715+00:00
-- url     : https://prove2.me/theorems/89663fb5-3956-4f5c-a6af-5cde7f212bf8
-- title:
--   PolarCone
-- statement:
--   The polar cone $C^\circ=\{y:\langle y,x\rangle\le 0\ \forall x\in C\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.210, Eq. (3.34).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.210, Eq. (3.34)

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The polar cone `C° = {y : ⟨y,x⟩ ≤ 0 ∀x∈C}`. -/
def PolarCone (C : Set (V → ℝ)) : Set (V → ℝ) := {y | ∀ x ∈ C, ∑ v, y v * x v ≤ 0}

end DiscreteConvex.ConjugacyDualityB


