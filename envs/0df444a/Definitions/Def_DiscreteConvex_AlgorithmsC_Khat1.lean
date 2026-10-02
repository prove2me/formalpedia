-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_Khat1
-- name    : DiscreteConvex_AlgorithmsC_Khat1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:25:16.617082+00:00
-- url     : https://prove2.me/theorems/6cbb03be-0fd4-487a-85a9-0995bcfb4cb2
-- title:
--   Khat1
-- statement:
--   $\hat K_1$: the $\ell^1$-size of $\operatorname{dom}g$ restricted to pairs sharing a coordinate.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.306, Eq. (10.34).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.306, Eq. (10.34)

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_DomZ
import Definitions.Def_DiscreteConvex_AlgorithmsC_L1Norm

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `K̂₁`, Eq. (10.34): the `ℓ¹`-size of `dom g` restricted to pairs sharing a coordinate. -/
noncomputable def Khat1 {W : Type*} [Fintype W] [DecidableEq W] (g : (W → ℤ) → WithTop ℝ) : ℤ :=
  sSup {k : ℤ | ∃ p q : W → ℤ, p ∈ DomZ g ∧ q ∈ DomZ g ∧ (∃ v, p v = q v) ∧
    k = L1Norm (fun v => p v - q v)}

end DiscreteConvex.AlgorithmsC


