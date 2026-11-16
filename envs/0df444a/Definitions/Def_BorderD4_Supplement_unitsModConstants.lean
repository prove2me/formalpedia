-- Prove2me | Definitions.Def_BorderD4_Supplement_unitsModConstants
-- name    : BorderD4_Supplement_unitsModConstants
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:01:16.779458+00:00
-- url     : https://prove2.me/theorems/cbfc5892-b1db-4d66-a336-fe61377e51fa
-- title:
--   The group $A^\times/F^\times$ of units modulo constants
-- statement:
--   For an algebra $A$ over a field $F$, the group of **units modulo constants** is the quotient
--   $$A^\times/F^\times$$
--   of the unit group of $A$ by the image of the nonzero constants. For the coordinate ring $A=F[W_0]$ of an irreducible affine variety it is the group $F[W_0]^\times/F^\times$ of Theorem 7.4, the analogue of Dirichlet's unit group used in the exact impossibility proof.
--
--   **Formalization Note** $F^\times$ maps into $A^\times$ by `algebraMap`; the quotient carries the quotient commutative group structure, written multiplicatively.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §1.4.3, p.21; Theorem 7.4, p.81

import Mathlib
set_option autoImplicit false

namespace BorderD4.Supplement

/-- The group `A^×/F^×` of units modulo constants of an `F`-algebra `A`: the unit group of `A` modulo the image of
the nonzero constants `F^×`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §1.4.3, p.21, and Theorem 7.4, p.81 (the group `F[W_0]^×/F^×`).

**Formalization Note** `F^×` is embedded in `A^×` by `algebraMap`; for `A = F[W_0] = F[x]/p` with `p` a proper
ideal this map is injective. The quotient of the commutative group `Aˣ` by this subgroup is a commutative group,
written multiplicatively; `unitsModConstants` is a `def` carrying that instance. -/
def unitsModConstants (F A : Type*) [Field F] [CommRing A] [Algebra F A] : Type _ :=
  Aˣ ⧸ (Units.map (algebraMap F A).toMonoidHom).range

/-- The commutative group structure of `A^×/F^×`, the quotient group structure. -/
noncomputable instance unitsModConstants.instCommGroup (F A : Type*) [Field F] [CommRing A] [Algebra F A] :
    CommGroup (unitsModConstants F A) :=
  QuotientGroup.Quotient.commGroup _

end BorderD4.Supplement


