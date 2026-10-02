-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_K1
-- name    : DiscreteConvex_AlgorithmsC_K1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:25:33.967311+00:00
-- url     : https://prove2.me/theorems/7329c009-cbfe-432d-aaf2-ce3405366335
-- title:
--   K1
-- statement:
--   $K_1$: the $\ell^1$-size of $\operatorname{dom}g$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.307, Eq. (10.37).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.307, Eq. (10.37)

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_DomZ
import Definitions.Def_DiscreteConvex_AlgorithmsC_L1Norm

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `K₁`, Eq. (10.37): the `ℓ¹`-size of `dom g`. -/
noncomputable def K1 {W : Type*} [Fintype W] [DecidableEq W] (g : (W → ℤ) → WithTop ℝ) : ℤ :=
  sSup {k : ℤ | ∃ p q : W → ℤ, p ∈ DomZ g ∧ q ∈ DomZ g ∧ k = L1Norm (fun v => p v - q v)}

end DiscreteConvex.AlgorithmsC


