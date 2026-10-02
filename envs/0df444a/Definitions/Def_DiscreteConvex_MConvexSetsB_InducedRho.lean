-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSetsB_InducedRho
-- name    : DiscreteConvex_MConvexSetsB_InducedRho
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:26:38.333038+00:00
-- url     : https://prove2.me/theorems/ff9d90b1-bc26-4722-af72-e76c2f0a94dd
-- title:
--   InducedRho
-- statement:
--   The set function $\rho(X) = \sup\{x(X) : x \in B\}$ induced by a set $B \subseteq \mathbb Z^V$ of integer vectors, Eq. (4.25); used in Proposition 4.13 to recover the submodular function associated with an M-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.108-109, Eq. (4.25).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.108-109, Eq. (4.25)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.108-109, Eq. (4.25): the submodular set
function induced by an M-convex set, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- The set function `ρ(X) = sup\{x(X) : x ∈ B\}` induced by a set `B ⊆ Zⱽ` of integer
vectors, Eq. (4.25); used in Proposition 4.13 to recover the submodular function associated
with an M-convex set. -/
noncomputable def InducedRho {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ)) :
    Finset V → WithTop ℝ :=
  fun X => sSup ((fun x : V → ℤ => (((∑ v ∈ X, x v : ℤ) : ℝ) : WithTop ℝ)) '' B)

end DiscreteConvex.MConvexSetsB


