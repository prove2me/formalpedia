-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_ConvexConjE
-- name    : DiscreteConvex_ConjugacyDualityD_ConvexConjE
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:56:21.234049+00:00
-- url     : https://prove2.me/theorems/381613d2-1b5d-4355-9fed-a60619096ad6
-- title:
--   ConvexConjE
-- statement:
--   The `EReal`-valued convex Legendre-Fenchel transform.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.235, Eq. (8.57)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.235, Eq. (8.57)-adjacent

import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `EReal`-valued convex Legendre-Fenchel transform. -/
noncomputable def ConvexConjE (F : (V → ℤ) → EReal) (y : V → ℤ) : EReal :=
  sSup {t : EReal | ∃ x : V → ℤ, t = ((∑ i, (y i : ℝ) * (x i : ℝ) : ℝ) : EReal) - F x}

end DiscreteConvex.ConjugacyDualityD


