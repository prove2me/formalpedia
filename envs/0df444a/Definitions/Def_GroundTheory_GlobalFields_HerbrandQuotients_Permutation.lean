-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
-- name    : GroundTheory_GlobalFields_HerbrandQuotients_Permutation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:54.455836+00:00
-- url     : https://prove2.me/theorems/87bbf8dc-b833-4cb0-9f47-e1d619e5ba9d
-- title:
--   Permutation
-- statement:
--   Definitions and structural lemmas for Permutation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open GroundTheory.GroupCoh MulAction
section Orbits
variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
noncomputable def orbitPoint (x : X) : X :=
  Quotient.out (Quotient.mk (orbitRel G X) x)
variable {G}
variable [Fintype G]
end Orbits
section Permutation
variable {G X : Type*} [Group G] [Fintype G] [MulAction G X]
noncomputable def permOfFun [Finite X] (F : X → ℤ) : MonoidAlgebra ℤ X :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm F)
end Permutation
section Cohomology
variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] {σ : G}
end Cohomology
section Quotient
variable {G : Type*} [Group G] [Fintype G]
end Quotient
end GroundTheory.Global


