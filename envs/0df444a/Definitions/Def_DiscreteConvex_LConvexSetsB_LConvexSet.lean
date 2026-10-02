-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_LConvexSet
-- name    : DiscreteConvex_LConvexSetsB_LConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:41:54.251539+00:00
-- url     : https://prove2.me/theorems/b3186641-c4f5-48e1-b7ce-2bf75fe247a0
-- title:
--   LConvexSet
-- statement:
--   Axioms **(SBS[Z])** and **(TRS[Z])**: a nonempty set $D \subseteq \mathbb Z^V$ closed under coordinatewise $\vee$/$\wedge$ and under adding/subtracting the all-ones vector $\mathbf 1$. This is an **L-convex set**.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.121, axioms (SBS[Z]) and (TRS[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.121, axioms (SBS[Z]) and (TRS[Z])

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.121, axioms (SBS[Z]) and (TRS[Z]): the
definition of an L-convex set, in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- Axioms **(SBS[Z])** and **(TRS[Z])**: a nonempty set `D ⊆ Zⱽ` closed under
coordinatewise `∨`/`∧` and under adding/subtracting the all-ones vector `1`. -/
def LConvexSet {V : Type*} (D : Set (V → ℤ)) : Prop :=
  D.Nonempty ∧
  (∀ p ∈ D, ∀ q ∈ D, (fun v => max (p v) (q v)) ∈ D ∧ (fun v => min (p v) (q v)) ∈ D) ∧
  (∀ p ∈ D, (fun v => p v + 1) ∈ D ∧ (fun v => p v - 1) ∈ D)

end DiscreteConvex.LConvexSetsB


