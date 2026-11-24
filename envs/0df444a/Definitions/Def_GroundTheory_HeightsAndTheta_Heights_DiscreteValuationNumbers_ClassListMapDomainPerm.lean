-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:18.932499+00:00
-- url     : https://prove2.me/theorems/0c445e6c-136b-41df-8ce0-85fe40550417
-- title:
--   Class List Map Domain Perm
-- statement:
--   Definitions and structural lemmas for Class List Map Domain Perm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomogIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
set_option linter.unusedSectionVars false
universe u
section Coord
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end Coord
section Model
variable (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
end Model
section Generic
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
end Generic
section Cycles
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
end Cycles
section PairNumbers
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
end PairNumbers
section DualGens
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end DualGens
section ProjBundle
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def optIdx (M : ℕ) :
    (Σ o : Option K, bundleIdx ι M o) → (Σ k : K ⊕ Unit, Sum.elim ι (fun _ : Unit => Fin M) k)
  | ⟨none, l⟩ => ⟨Sum.inr (), l⟩
  | ⟨some k, i⟩ => ⟨Sum.inl k, i⟩
end ProjBundle
section Joins
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
variable [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
end Joins
section Degenerate
variable (O : Type*) [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
def zeroPt : (Σ _ : Unit, Fin 1) → Ω := fun _ => 0
end Degenerate
end GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples


