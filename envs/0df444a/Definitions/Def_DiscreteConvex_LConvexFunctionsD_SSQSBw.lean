-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_SSQSBw
-- name    : DiscreteConvex_LConvexFunctionsD_SSQSBw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:02:46.151984+00:00
-- url     : https://prove2.me/theorems/abb21f84-cc14-4b49-9878-b6fb358e123d
-- title:
--   SSQSBw
-- statement:
--   Axiom (SSQSBw), the weaker variant of (SSQSB).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, axiom (SSQSBw).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, axiom (SSQSBw)

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomZ

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SSQSBw), the weaker variant of (SSQSB). -/
def SSQSBw (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p ∈ DomZ g, ∀ q ∈ DomZ g,
    max (g p) (g q) > min (g (p ⊓ q)) (g (p ⊔ q)) ∨
      (g p = g q ∧ g p = g (p ⊓ q) ∧ g p = g (p ⊔ q))

end DiscreteConvex.LConvexFunctionsD


