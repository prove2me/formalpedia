-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_ExchangeAxiomB
-- name    : DiscreteConvex_MConvexFunctionsB_ExchangeAxiomB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:08:02.269899+00:00
-- url     : https://prove2.me/theorems/765ba283-11b9-40d5-893d-a200181d56d7
-- title:
--   ExchangeAxiomB
-- statement:
--   Axiom **(B-EXC[Z])**: $B \subseteq \mathbb Z^V$ is an **M-convex set**.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z])

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppNeg

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101, axiom (B-EXC[Z]), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Axiom **(B-EXC[Z])**: `B ⊆ Zⱽ` is an **M-convex set**. -/
def ExchangeAxiomB {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - CharVec u w + CharVec v w) ∈ B ∧
    (fun w => y w + CharVec u w - CharVec v w) ∈ B

end DiscreteConvex.MConvexFunctionsB


