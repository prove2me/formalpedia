-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
-- name    : Formalism_GL3MeanSquares_CongruenceTorsion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:17.888935+00:00
-- url     : https://prove2.me/theorems/993a333d-8326-4b0d-b67b-086db5f5faf3
-- title:
--   Congruence Torsion
-- statement:
--   Definitions and structural lemmas for Congruence Torsion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/CongruenceTorsion.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal IsDedekindDomain
open scoped Pointwise TensorProduct
noncomputable section
namespace Formalism.HermitianLattices.StabilizerLevels
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.HermitianLattices.FiltrationBoundaryCriterion
def HostEOverF : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ x : hostE ζ a b,
    (∃ u ∈ hostF ζ a b, ∃ v ∈ hostF ζ a b, x = u + v * bE ζ a b) ∧
    (∃ u ∈ hostF ζ a b, ∃ v ∈ hostF ζ a b, x = u + v * aE ζ a b)
def HostQuadSub : Prop :=
  ∀ (e q d : ℕ), 1 ≤ e → HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ m : ℤ, Squarefree m →
    ((∃ x : hostE ζ a b, x ^ 2 = (m : hostE ζ a b)) ↔
      (m = 1 ∨ m = 2 ∨ m = -(q : ℤ) ∨ m = -(d : ℤ) ∨ m = (q : ℤ) * d ∨ m = -2 * (q : ℤ) ∨
        m = -2 * (d : ℤ) ∨ m = 2 * (q : ℤ) * d))
def CongruenceTorsion : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (g k : ℕ), g.Prime → (g : R) ∈ I →
    (⨅ m : ℕ, I ^ m) = ⊥ →
  ∀ A : Matrix (Fin k) (Fin k) R, (∀ i j, (A - 1) i j ∈ I) →
  ∀ N : ℕ, 0 < N → A ^ N = 1 → ∃ m : ℕ, A ^ (g ^ m) = 1
def UnipotentPowers : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (g k : ℕ), g.Prime → (g : R) ∈ I →
  ∀ A : Matrix (Fin k) (Fin k) R, (∀ i j, j ≤ i → (A - 1) i j ∈ I) →
  ∀ s : ℕ, k ≤ g ^ s → ∀ i j, (A ^ (g ^ s) - 1) i j ∈ I
def NilpotentPowers : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (g k : ℕ), g.Prime → (g : R) ∈ I →
  ∀ (A : Matrix (Fin k) (Fin k) R) (N : ℕ), (∀ i j, ((A - 1) ^ N) i j ∈ I) →
  ∀ s : ℕ, N ≤ g ^ s → ∀ i j, (A ^ (g ^ s) - 1) i j ∈ I
def StabLevelG : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (k : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E),
    (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    Formalism.UG.IsHerm (σ : E →+* E) J → IsUnit J.det → Formalism.UG.IsTotDef σ J →
  ∀ U : Subgroup (Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    U ≤ Formalism.UG.levelAf σ J →
  ∀ (w : HeightOneSpectrum (𝓞 F)) (g : ℕ), g.Prime → (g : 𝓞 F) ∈ w.asIdeal →
    Module.finrank ℚ E * k < g - 1 →
    (∀ x ∈ U, ∀ i j : Fin k,
      ∃ r ∈ Formalism.UG.tensInt (F := F) (w.adicCompletion F) (Formalism.UG.intOE E)
        (w.adicCompletionIntegers F).toSubring,
      ((Formalism.UG.bc (Formalism.UG.prV (E := E) w) x :
          Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin k) (Fin k) (E ⊗[F] w.adicCompletion F)) i j -
        (1 : Matrix (Fin k) (Fin k) (E ⊗[F] w.adicCompletion F)) i j =
          (g : E ⊗[F] w.adicCompletion F) * r) →
    Formalism.UG.IsNeat
      ((Formalism.UG.ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf
        (Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)))
      (U.subgroupOf (Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)))
def StabLevelProG : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (k : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E),
    (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    Formalism.UG.IsHerm (σ : E →+* E) J → IsUnit J.det → Formalism.UG.IsTotDef σ J →
  ∀ U : Subgroup (Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    U ≤ Formalism.UG.levelAf σ J →
  ∀ (w : HeightOneSpectrum (𝓞 F)) (g : ℕ), g.Prime → (g : 𝓞 F) ∈ w.asIdeal →
    Module.finrank ℚ E * k < g - 1 →
    (∀ x ∈ U, ∃ s : ℕ, ∀ i j : Fin k,
      ∃ r ∈ Formalism.UG.tensInt (F := F) (w.adicCompletion F) (Formalism.UG.intOE E)
        (w.adicCompletionIntegers F).toSubring,
      (((Formalism.UG.bc (Formalism.UG.prV (E := E) w) x :
          Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin k) (Fin k) (E ⊗[F] w.adicCompletion F)) ^ (g ^ s)) i j -
        (1 : Matrix (Fin k) (Fin k) (E ⊗[F] w.adicCompletion F)) i j =
          (g : E ⊗[F] w.adicCompletion F) * r) →
    Formalism.UG.IsNeat
      ((Formalism.UG.ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf
        (Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)))
      (U.subgroupOf (Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)))
def IsForm {G W : Type} [Group G] (Γ U : Subgroup G) [MulAction U W] (f : G → W) : Prop :=
  ∀ γ ∈ Γ, ∀ (u : U) (g : G), f (γ * g * (u : G)) = u⁻¹ • f g
def FormsExact : Prop :=
  ∀ (G : Type) [Group G] (Γ U : Subgroup G),
    (∀ y : G, ∀ γ ∈ Γ, y⁻¹ * γ * y ∈ U → γ = 1) →
  ∀ (W₁ W₂ W₃ : Type) [AddCommGroup W₁] [AddCommGroup W₂] [AddCommGroup W₃]
    [DistribMulAction U W₁] [DistribMulAction U W₂] [DistribMulAction U W₃]
    (a : W₁ →+ W₂) (b : W₂ →+ W₃),
    (∀ (u : U) (x : W₁), a (u • x) = u • a x) → (∀ (u : U) (x : W₂), b (u • x) = u • b x) →
    (∀ y : W₂, b y = 0 ↔ ∃ x : W₁, a x = y) →
    (∀ f : G → W₂, IsForm Γ U f → (∀ g, b (f g) = 0) →
      ∃ f' : G → W₁, IsForm Γ U f' ∧ ∀ g, a (f' g) = f g) ∧
    (Function.Surjective b → ∀ f'' : G → W₃, IsForm Γ U f'' →
      ∃ f : G → W₂, IsForm Γ U f ∧ ∀ g, b (f g) = f'' g)
def PrincipalRiemann : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ = cc e →
  ∀ 𝔟 : Ideal (𝓞 (hostE ζ a b)),
    differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟 * (σ • 𝔟) →
  ∀ 𝔠 : Ideal (𝓞 (KinE ζ a b)), 𝔠 ≠ ⊥ →
  ∀ ξ : hostE ζ a b, ξ * (((Ideal.absNorm 𝔠 : ℕ) : hostE ζ a b) * bE ζ a b) = -1 →
    σ ξ = -ξ ∧
    (∀ φ ∈ cmType ζ a b d, 0 < (φ ξ).im) ∧
    ∀ x : hostE ζ a b,
      x ∈ (((𝔠.map (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) : Ideal (𝓞 (hostE ζ a b))) :
            FractionalIdeal (nonZeroDivisors (𝓞 (hostE ζ a b))) (hostE ζ a b)) *
          ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 (hostE ζ a b))) (hostE ζ a b))⁻¹)) ↔
        ∀ y ∈ (((𝔠.map (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) :
              Ideal (𝓞 (hostE ζ a b))) :
            FractionalIdeal (nonZeroDivisors (𝓞 (hostE ζ a b))) (hostE ζ a b)) *
          ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 (hostE ζ a b))) (hostE ζ a b))⁻¹)),
          Algebra.trace ℚ (hostE ζ a b) (ξ * x * σ y) ∈ (algebraMap ℤ ℚ).range
end Formalism.HermitianLattices.StabilizerLevels


