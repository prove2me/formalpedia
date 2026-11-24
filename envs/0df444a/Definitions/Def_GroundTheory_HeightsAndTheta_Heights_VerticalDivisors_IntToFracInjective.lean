-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:01.909644+00:00
-- url     : https://prove2.me/theorems/b09e454c-2783-43a4-b03a-4381c6246d28
-- title:
--   Int To Frac Injective
-- statement:
--   Definitions and structural lemmas for Int To Frac Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/IntToFracInjective.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
section NumberField
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
def parPrime (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : Ideal (MvPolynomial (Par e n) (𝓞 K)) :=
  Ideal.map C v.asIdeal
instance parPrime_isPrime (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : (parPrime e n v).IsPrime := by
  have h : parPrime e n v = RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk v.asIdeal) :
      MvPolynomial (Par e n) (𝓞 K) →+* MvPolynomial (Par e n) (𝓞 K ⧸ v.asIdeal)) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
    rfl
  rw [h]
  exact RingHom.ker_isPrime _
abbrev ParDVR (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : Type _ :=
  Localization.AtPrime (parPrime e n v)
instance parDVR_isDomain (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : IsDomain (ParDVR e n v) :=
  IsLocalization.isDomain_of_atPrime _ (parPrime e n v)
def parY (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : Par e n → ParDVR e n v :=
  fun p => algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (X p)
def modelR (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) :
    Ideal (MvPolynomial (Fin n) (ParDVR e n v)) :=
  (integralModel I).map (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)))
abbrev SecB (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) : Type _ :=
  SecAlg (modelR e I v) (parY e n v)
abbrev ParFrac (K : Type*) [Field K] [NumberField K] (e n : ℕ) : Type _ :=
  FractionRing (MvPolynomial (Par e n) (𝓞 K))
def parToFrac (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : ParDVR e n v →+* ParFrac K e n :=
  IsLocalization.lift (M := (parPrime e n v).primeCompl) (g := algebraMap _ (ParFrac K e n))
    fun s => IsUnit.mk0 _ fun h => (s.2 : (s : MvPolynomial (Par e n) (𝓞 K)) ∉ parPrime e n v)
      (by rw [(IsFractionRing.injective _ (ParFrac K e n)) (h.trans (map_zero _).symm)]
          exact Ideal.zero_mem _)
theorem intToFrac_injective (K : Type*) [Field K] [NumberField K] (e n : ℕ) :
    Function.Injective ((algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n)).comp C) := by
  simp only [RingHom.coe_comp]
  exact (IsFractionRing.injective _ _).comp (MvPolynomial.C_injective _ _)
def kToFrac (K : Type*) [Field K] [NumberField K] (e n : ℕ) : K →+* ParFrac K e n :=
  IsFractionRing.lift (intToFrac_injective K e n)
def parYF (K : Type*) [Field K] [NumberField K] (e n : ℕ) : Par e n → ParFrac K e n :=
  fun p => algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (X p)
def idealF (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) :
    Ideal (MvPolynomial (Fin n) (ParFrac K e n)) :=
  I.map (MvPolynomial.map (kToFrac K e n))
def specComps (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) :
    Set (Ideal (MvPolynomial (Fin n) (𝓞 K))) :=
  relComps (integralModel I ⊔ Ideal.map C v.asIdeal)
def secIdealOf (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K))
    (W : Ideal (MvPolynomial (Fin n) (𝓞 K))) : Ideal (SecB e I v) :=
  (W.map (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)))).map (Ideal.Quotient.mk _)
def vertDeg (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (u : Fin n → 𝓞 K)
    (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  ∑ᶠ W ∈ vertComps I u v,
    localMult (integralModel I ⊔ Ideal.span {linForm u}) W * chowDegree (reduceMod v W) (e + 1)
end NumberField
def ParDVRIsDVR.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)),
    IsDiscreteValuationRing (ParDVR e n v)
def ParAlgIndep.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ),
    letI := (kToFrac K e n).toAlgebra
    AlgebraicIndependent K (parYF K e n)
def GaussDVR.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (g : MvPolynomial (Par e n) (𝓞 K)), g ≠ 0 →
      gaussNorm v (g.map (algebraMap (𝓞 K) K)) *
          (Ideal.absNorm v.asIdeal : ℝ) ^ (Ring.ord (ParDVR e n v) (algebraMap _ _ g)).toNat = 1
def PrimitiveScale.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (σ : Type)
    (f : MvPolynomial σ K), f ≠ 0 →
      ∃ (c : K) (g : MvPolynomial σ (𝓞 K)), c ≠ 0 ∧ g.map (algebraMap (𝓞 K) K) = C c * f ∧
        ∃ m, g.coeff m ∉ v.asIdeal
def SecBFinite.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → Module.Finite (ParDVR e n v) (SecB e I v)
def SecBTorsionFree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)), IsProjPrime I →
      ∀ (r : ParDVR e n v) (b : SecB e I v), r ≠ 0 → r • b = 0 → b = 0
def SecBGeneric.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)), IsProjPrime I →
      ∃ φ : SecB e I v →+* SecAlg (idealF e I) (parYF K e n),
        (∀ j, φ (secCoord _ _ j) = secCoord _ _ j) ∧
        (∀ r : ParDVR e n v, φ (algebraMap _ _ r) = algebraMap _ _ (parToFrac e n v r)) ∧
        letI := φ.toAlgebra
        IsLocalization (Algebra.algebraMapSubmonoid (SecB e I v) (nonZeroDivisors (ParDVR e n v)))
          (SecAlg (idealF e I) (parYF K e n))
def SecBLinInj.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm (fun j => (u j : K)) ∉ I →
      Function.Injective fun b : SecB e I v =>
        secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)) * b
def SpecMax.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f →
      (∀ W ∈ specComps I v, (secIdealOf e I v W).IsMaximal) ∧
        ∀ 𝔫 : Ideal (SecB e I v), 𝔫.IsMaximal → ∃! W, W ∈ specComps I v ∧ secIdealOf e I v W = 𝔫
open Classical in

def SpecLength.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm (fun j => (u j : K)) ∉ I →
      ∀ 𝔫 : MaximalSpectrum (SecB e I v), ∀ W ∈ specComps I v, secIdealOf e I v W = 𝔫.asIdeal →
        Ring.ord (Localization.AtPrime 𝔫.asIdeal)
            (algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)
              (secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)))) =
          if linForm u ∈ W then (localMult (integralModel I ⊔ Ideal.span {linForm u}) W : ℕ∞) else 0
def SpecResidue.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → ∀ W ∈ specComps I v,
      Module.length (ParDVR e n v) (SecB e I v ⧸ secIdealOf e I v W) = chowDegree (reduceMod v W) (e + 1)
def VertSpec.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm (fun j => (u j : K)) ∉ I →
      vertComps I u v = {W | W ∈ specComps I v ∧ linForm u ∈ W}
def NormIdentity.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) (g.map (algebraMap (𝓞 K) K)) →
    linForm (fun j => (u j : K)) ∉ I → (∃ m, g.coeff m ∉ v.asIdeal) →
      ∃ w : (ParDVR e n v)ˣ,
        algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename Sum.inl (specFirst g u)) =
          w * Algebra.norm (ParDVR e n v)
            (secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)))
def OrdEq.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) (g.map (algebraMap (𝓞 K) K)) →
    linForm (fun j => (u j : K)) ∉ I → (∃ m, g.coeff m ∉ v.asIdeal) →
      Ring.ord (ParDVR e n v)
          (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename Sum.inl (specFirst g u))) =
        vertDeg e I u v
def VertTermEq.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
      vertTermAt I (e + 1) u v = vertDeg e I u v * Real.log (Ideal.absNorm v.asIdeal)
def GaussEq.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) (g.map (algebraMap (𝓞 K) K)) →
    linForm (fun j => (u j : K)) ∉ I → (∃ m, g.coeff m ∉ v.asIdeal) →
      gaussNorm v (specFirst (g.map (algebraMap (𝓞 K) K)) fun j => (u j : K)) *
          (Ideal.absNorm v.asIdeal : ℝ) ^ vertDeg e I u v = 1 ∧
        gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1
end
end GroundTheory.Heights₂.Heights.Vertical


