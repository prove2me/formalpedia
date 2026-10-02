-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_KInfty
-- name    : DiscreteConvex_AlgorithmsC_KInfty
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:25:28.586007+00:00
-- url     : https://prove2.me/theorems/27a34152-33b3-4ff5-9eb2-3ab0e98b3f77
-- title:
--   KInfty
-- statement:
--   $K_\infty$: the $\ell^\infty$-size of $\operatorname{dom}g$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.307, Eq. (10.38).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.307, Eq. (10.38)

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_DomZ
import Definitions.Def_DiscreteConvex_AlgorithmsC_LInftyNorm

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `K∞`, Eq. (10.38): the `ℓ∞`-size of `dom g`. -/
noncomputable def KInfty {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (g : (W → ℤ) → WithTop ℝ) : ℤ :=
  sSup {k : ℤ | ∃ p q : W → ℤ, p ∈ DomZ g ∧ q ∈ DomZ g ∧ k = LInftyNorm (fun v => p v - q v)}

-- ===== Conjugate scaling (§10.4.5) =====

end DiscreteConvex.AlgorithmsC


