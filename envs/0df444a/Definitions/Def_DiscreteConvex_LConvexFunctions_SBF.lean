-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_SBF
-- name    : DiscreteConvex_LConvexFunctions_SBF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:13:34.051114+00:00
-- url     : https://prove2.me/theorems/56edc2eb-764b-4d3c-93fd-e5c6df3d25d7
-- title:
--   Submodularity on the integer lattice (SBF[Z])
-- statement:
--   Axiom **(SBF[Z])**: $g(p)+g(q) \ge g(p \vee q) + g(p \wedge q)$ for all $p,q \in \mathbb Z^V$ ($\vee,\wedge$ componentwise max/min).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (SBF[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (SBF[Z])

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.177, axiom (SBF[Z]): submodularity on the
integer lattice, in `DiscreteConvex.LConvexFunctions`.
-/

namespace DiscreteConvex.LConvexFunctions

/-- Axiom **(SBF[Z])**: `g(p) + g(q) ≥ g(p ∨ q) + g(p ∧ q)` for all `p, q ∈ Zⱽ`
(`∨`, `∧` componentwise max/min). -/
def SBF {V : Type*} (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℤ, g p + g q ≥ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.LConvexFunctions


