-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportDefs
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:46:02.59818+00:00
-- url     : https://prove2.me/theorems/31c8dc2d-c734-407c-8d6a-ad62984b53a4
-- title:
--   Transport Defs
-- statement:
--   Definitions and structural lemmas for Transport Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/TransportDefs.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ValuativeRel
structure Model (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (p : ℕ) [Fact p.Prime] where
  K' : IntermediateField ℚ_[p] (PadicAlgCl p)
  fin : FiniteDimensional ℚ_[p] K'
  e : K ≃+* K'
  E : AlgebraicClosure K ≃+* PadicAlgCl p
  comm : ∀ x, E (algebraMap K (AlgebraicClosure K) x) = (e x : PadicAlgCl p)
  homeo : IsHomeomorph e
  int : ∀ x, x ∈ 𝒪[K] ↔ ‖(e x : PadicAlgCl p)‖ ≤ 1
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {p : ℕ} [Fact p.Prime]
def Model.IsGalIso (m : Model K p) (φ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≃* GK p m.K') : Prop :=
  ∀ σ x, φ σ (m.E x) = m.E (σ x)
def Model.Corr (m : Model K p) (L : IntermediateField K (AlgebraicClosure K))
    (L' : IntermediateField ℚ_[p] (PadicAlgCl p)) : Prop := ∀ x, m.E x ∈ L' ↔ x ∈ L
noncomputable def Model.eU (m : Model K p) : Kˣ ≃* (m.K')ˣ := Units.mapEquiv m.e.toMulEquiv
end ReciprocityTheory.DiscreteGroups.LocalClassField


