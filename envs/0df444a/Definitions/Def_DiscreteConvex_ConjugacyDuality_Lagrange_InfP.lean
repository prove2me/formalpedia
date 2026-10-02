-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_InfP
-- name    : DiscreteConvex_ConjugacyDuality_Lagrange_InfP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:13:22.933421+00:00
-- url     : https://prove2.me/theorems/e60d3064-010f-4508-85d7-627772941c39
-- title:
--   Primal optimal value
-- statement:
--   $\inf(P) = \inf\{f(x) : x \in \mathbb Z^V\}$, the optimal value of the primal problem $P$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.237.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.237

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_PrimalValue

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.237: the primal optimal value, in
`DiscreteConvex.ConjugacyDuality.Lagrange`.
-/

open DiscreteConvex.ConjugacyDuality

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- `inf(P) = inf\{f(x) : x ∈ Zⱽ\}`, the optimal value of the primal problem `P`. -/
noncomputable def InfP {V U : Type*} [Zero (U → ℤ)] (F : (V → ℤ) → (U → ℤ) → WithTop ℝ) :
    EReal :=
  sInf {v : EReal | ∃ x : V → ℤ, v = ToEReal (PrimalValue F x)}

end DiscreteConvex.ConjugacyDuality.Lagrange


