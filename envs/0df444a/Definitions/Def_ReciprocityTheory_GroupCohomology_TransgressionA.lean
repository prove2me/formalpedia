-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA
-- name    : ReciprocityTheory_GroupCohomology_TransgressionA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:59.756693+00:00
-- url     : https://prove2.me/theorems/06688f7b-986c-476f-beb2-39b9f972c7e2
-- title:
--   Transgression A
-- statement:
--   Definitions and structural lemmas for Transgression A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/TransgressionA.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_Section
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh.InflationTransgression
open ReciprocityTheory.Gal ReciprocityTheory.Coh
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def cj (N : Subgroup G) [N.Normal] (s : G) (n : N) : N :=
  ⟨s⁻¹ * n * s, by simpa using (inferInstance : N.Normal).conj_mem n n.2 s⁻¹⟩
def D1 (M : TRep R G) (y : G → M.V) (a b : G) : M.V := M.rho a (y b) - y (a * b) + y a
structure InflD (M : TRep R G) (N : Subgroup G) (D : G → G → M.V) : Prop where
  right : ∀ a b (n : N), D a (b * n) = D a b
  left : ∀ a b (n : N), D (a * n) b = D a b
  inv : ∀ a b (n : N), M.rho n (D a b) = D a b
section
variable (M : TRep R G) (N : Subgroup G) [N.Normal] (y : G → M.V) (hy1 : y 1 = 0)
  (hD : InflD M N (D1 M y))
include hy1 hD
end
end
end ReciprocityTheory.Coh.InflationTransgression


