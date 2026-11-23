-- Prove2me | Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
-- name    : Formalism_GaloisCohomology_LocalTateDualityK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:58.441794+00:00
-- url     : https://prove2.me/theorems/606f0275-a4e9-4de3-b381-cf9d2d1d7e01
-- title:
--   Local Tate Duality K
-- statement:
--   Definitions and structural lemmas for Local Tate Duality K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisCohomology/LocalTateDualityK.lean

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Formalism_GaloisCohomology_StatementLoc
import Theorems.Thm_P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd
import Theorems.Thm_ReciprocityTheory_Gal_continuous_toGS

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
namespace Formalism.GaloisCohomology
def SelAllLeInf : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))) (R : Type) [CommRing R] (M : Type)
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [T2Space M] (rhoS : Representation R (GS Ω S) M), ContAction rhoS →
  ∀ (A : Places F Ω) (L : ∀ v, Submodule R (H1 ((rhoS.comp (toGS Ω S)).comp (Dec (F := F) (A.1 v)).subtype))),
  (∀ v ∉ S, L v ≤ unrAt (rhoS.comp (toGS Ω S)) (A.1 v)) →
    SelAll (rhoS.comp (toGS Ω S)) A L ≤ LinearMap.range (resH1 rhoS (toGS Ω S) (continuous_toGS Ω S))
def SelAllLen : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))) (R : Type) [CommRing R] (M : Type)
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [T2Space M] (rhoS : Representation R (GS Ω S) M), ContAction rhoS →
  ∀ (A : Places F Ω) (L : ∀ v, Submodule R (H1 ((rhoS.comp (toGS Ω S)).comp (Dec (F := F) (A.1 v)).subtype))),
  (∀ v ∉ S, L v ≤ unrAt (rhoS.comp (toGS Ω S)) (A.1 v)) →
    Module.length R (SelAll (rhoS.comp (toGS Ω S)) A L) =
      Module.length R ((SelAll (rhoS.comp (toGS Ω S)) A L).comap
        (resH1 rhoS (toGS Ω S) (continuous_toGS Ω S)))
section Local
variable (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
def cycK (r : ℕ) : GK l K →* (ZMod (l ^ r))ˣ :=
  (Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp
    ((cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (GK l K) (PadicAlgCl l)))
def CycKSpec : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  (r : ℕ) (σ : GK l K) (ζ : PadicAlgCl l), ζ ^ (l ^ r) = 1 →
    σ ζ = ζ ^ ((cycK l K r σ : ZMod (l ^ r)).val)
def LocalFinitenessK : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
  FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M]
  [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod (l ^ r)) (GK l K) M), 0 < r → ContAction rho →
    Finite (H0 rho) ∧ Finite (H1 rho) ∧ Finite (H2 rho) ∧ ∀ n, 3 ≤ n → Subsingleton (Hn rho n)
def LocalTateDualityK : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
  FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M]
  [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod (l ^ r)) (GK l K) M), 0 < r → ∀ hrho : ContAction rho,
    Nonempty (H2 (charRep (cycK l K r)) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) ∧
    Function.Bijective (cupH0H2TwistedDual (cycK l K r) rho (MonoidHom.id _)) ∧
    Function.Bijective (cupH1H1TwistedDual (cycK l K r) rho (MonoidHom.id _) (hrho.comp' continuous_id)) ∧
    Function.Bijective (cupH1H1TwistedDual (cycK l K r) rho (MonoidHom.id _) (hrho.comp' continuous_id)).flip ∧
    Function.Bijective (cup20 (cycK l K r) rho (MonoidHom.id _))
def LocalEulerCharK : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
  FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M]
  [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod (l ^ r)) (GK l K) M), 0 < r → ContAction rho →
    Nat.card (H1 rho) = Nat.card (H0 rho) * Nat.card (H2 rho) * Nat.card M ^ Module.finrank ℚ_[l] K
end Local
end Formalism.GaloisCohomology


