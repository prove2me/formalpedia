-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_FVal
-- name    : DiscreteConvex_CombinatorialC_FVal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:44:23.954797+00:00
-- url     : https://prove2.me/theorems/fdbcb900-277c-4c0e-9088-eac4694a3328
-- title:
--   Maximum weight circulation value F(w,c)
-- statement:
--   $F(w,c)=\max\{\langle w,\xi\rangle : \xi\text{ a feasible circulation for }c\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsFeasibleCirc

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.83, citing the maximum weight circulation
value, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- `FVal src dst w c` is the maximum weight `F(w,c) = max\{⟨w,ξ⟩ : ξ\text{ a feasible
circulation for } c\}` of a feasible circulation, taken as a real supremum. -/
noncomputable def FVal {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] (src dst : A → V)
    (w c : A → ℝ) : ℝ :=
  sSup {t : ℝ | ∃ xi : A → ℝ, IsFeasibleCirc src dst c xi ∧ t = dotProduct w xi}

end DiscreteConvex.CombinatorialC


