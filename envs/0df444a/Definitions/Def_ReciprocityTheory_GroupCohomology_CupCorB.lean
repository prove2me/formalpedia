-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB
-- name    : ReciprocityTheory_GroupCohomology_CupCorB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:09:14.054346+00:00
-- url     : https://prove2.me/theorems/bbc9bce1-7a1a-46a2-bbbe-dd1372f613fd
-- title:
--   Cup Cor B
-- statement:
--   Definitions and structural lemmas for Cup Cor B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
section Leibniz
variable {R : Type u} [CommRing R] {X V W Z : Type u} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]
def hcup (β : V →ₗ[R] W →ₗ[R] Z) (p q : ℕ) (F : (Fin (p + 1) → X) → V) (F' : (Fin (q + 1) → X) → W)
    (x : Fin (p + q + 1) → X) : Z :=
  β (F fun i => x ⟨i, by omega⟩) (F' fun j => x ⟨p + j, by omega⟩)
end Leibniz
section PartialProd
end PartialProd
section Homz
variable {R : Type u} [CommRing R]
def homz {K V : Type u} [Group K] [AddCommGroup V] [Module R V] (ρ : Representation R K V) (n : ℕ)
    (f : (Fin n → K) → V) (x : Fin (n + 1) → K) : V :=
  ρ (x 0) (f fun i => (x i.castSucc)⁻¹ * x i.succ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {M N P : TRep R G}
  (U : Subgroup G) [U.FiniteIndex]
end Homz
section SlopeTestRemainingChoices
variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
variable [U.FiniteIndex]
end SlopeTestRemainingChoices
end
end ReciprocityTheory.Coh.CCA


