-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:34.778589+00:00
-- url     : https://prove2.me/theorems/93415ff3-56b6-42aa-8838-a56901cd48f5
-- title:
--   Cm Curve Good Outside Prime Premises
-- statement:
--   Definitions and structural lemmas for Cm Curve Good Outside Prime Premises, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WeierstrassCurve
open scoped nonZeroDivisors IntermediateField
namespace GlobalTheory.Published
noncomputable def sqrtNegNat (p : ℕ) : ℂ := (Real.sqrt p : ℂ) * Complex.I
def IsIntegersLattice (p : ℕ) (L : PeriodPair) : Prop :=
  ∀ z : ℂ, z ∈ L.lattice ↔ z ∈ ℚ⟮sqrtNegNat p⟯ ∧ IsIntegral ℤ z
section Reduction
variable {F : Type} [Field F] [NumberField F]
def HasGoodReductionOutside (p : ℕ) (A : WeierstrassCurve F) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), (p : 𝓞 F) ∉ v.asIdeal →
    ∃ C : VariableChange F, (C • A).HasGoodReduction (v.valuationSubringAtPrime F)
def HasMinimalDiscriminant (A : WeierstrassCurve F) (D : F) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F),
    ∃ (C : VariableChange F) (u : (v.valuationSubringAtPrime F)ˣ),
      (C • A).IsMinimal (v.valuationSubringAtPrime F) ∧
        (C • A).Δ = ((u : v.valuationSubringAtPrime F) : F) * D
end Reduction
def IsGoodCMCurve (p : ℕ) (F : IntermediateField ℚ ℂ) (A : WeierstrassCurve F) : Prop :=
  ∃ (_ : NumberField F) (_ : A.IsElliptic) (L : PeriodPair), IsIntegersLattice p L ∧
    F = ℚ⟮(latticeCurve L).j⟯ ∧ (A.j : ℂ) = (latticeCurve L).j ∧ HasGoodReductionOutside p A
def CMCurveGoodOutsidePrimeSt : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 3 → 3 < p →
    ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F) (A : WeierstrassCurve F),
      IsGoodCMCurve p F A ∧ HasMinimalDiscriminant A (-(p : F) ^ 3)
section Lattice
variable {p : ℕ} {K : Type} [Field K] [NumberField K]
variable [Algebra K ℂ]
end Lattice
section Consequences
variable {p : ℕ}
variable {F : IntermediateField ℚ ℂ} {A : WeierstrassCurve F}
end Consequences
section Model
end Model
end GlobalTheory.Published


