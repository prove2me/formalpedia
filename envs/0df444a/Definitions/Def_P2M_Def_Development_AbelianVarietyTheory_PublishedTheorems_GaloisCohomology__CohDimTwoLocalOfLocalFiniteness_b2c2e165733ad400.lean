-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__CohDimTwoLocalOfLocalFiniteness_b2c2e165733ad400
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__CohDimTwoLocalOfLocalFiniteness_b2c2e165733ad400
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:14.268791+00:00
-- url     : https://prove2.me/theorems/216c25f3-9475-470f-9e3a-ef45e14e61bb
-- title:
--   Coh Dim Two Local Of Local Finiteness
-- statement:
--   Definitions and structural lemmas for Coh Dim Two Local Of Local Finiteness, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/CohDimTwoLocalOfLocalFiniteness.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual
namespace GlobalTheory.Published
def CohDimTwoGlobal : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
    ContainsAbove S l → ContAction rhoS → ∀ n, 3 ≤ n → Subsingleton (Hn rhoS n)
def CohDimTwoLocal : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω)
    (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M),
    IsPlaceOver A v → ContAction rho → ∀ n, 3 ≤ n → Subsingleton (Hn rho n)
def CohDimTwo : Prop := CohDimTwoGlobal ∧ CohDimTwoLocal
section Scalars
variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {M : Type*} [AddCommGroup M]
  [TopologicalSpace M] [IsTopologicalAddGroup M]
omit [TopologicalSpace Γ] [TopologicalSpace M] [IsTopologicalAddGroup M] in

def zmodRep {R : Type*} [CommRing R] [Module R M] (N : ℕ) [Module (ZMod N) M]
    (rho : Representation R Γ M) : Representation (ZMod N) Γ M where
  toFun g := (rho g).toAddMonoidHom.toZModLinearMap N
  map_one' := by ext m; simp
  map_mul' g h := by ext m; simp
end Scalars
section Consequences
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime] {R : Type*} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Finite M] [TopologicalSpace M] [DiscreteTopology M]
end Consequences
end GlobalTheory.Published


