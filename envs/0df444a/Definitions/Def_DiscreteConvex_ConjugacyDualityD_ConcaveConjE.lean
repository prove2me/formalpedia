-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_ConcaveConjE
-- name    : DiscreteConvex_ConjugacyDualityD_ConcaveConjE
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:56:16.583983+00:00
-- url     : https://prove2.me/theorems/5f7a4b4f-b6ac-45d2-90a1-e3a2955679cb
-- title:
--   ConcaveConjE
-- statement:
--   The `EReal`-valued concave Legendre-Fenchel transform.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.241, Eq. (8.66)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.241, Eq. (8.66)-adjacent

import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `EReal`-valued concave Legendre-Fenchel transform. -/
noncomputable def ConcaveConjE (F : (V → ℤ) → EReal) (y : V → ℤ) : EReal :=
  sInf {t : EReal | ∃ x : V → ℤ, t = ((∑ i, (y i : ℝ) * (x i : ℝ) : ℝ) : EReal) - F x}

end DiscreteConvex.ConjugacyDualityD


