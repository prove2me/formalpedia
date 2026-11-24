-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:26:46.32591+00:00
-- url     : https://prove2.me/theorems/f0eb26fb-1da3-4418-8492-e9130490a3c6
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
section Forms
variable {R : Type*} [CommSemiring R] {k n : ℕ}
def groupWeight (k n : ℕ) : Fin k × Fin n → (Fin k → ℕ) := fun ij => Pi.single ij.1 1
def IsMultiHomog (δ : ℕ) (f : MvPolynomial (Fin k × Fin n) R) : Prop :=
  IsWeightedHomogeneous (groupWeight k n) f (fun _ => δ)
def linForm (u : Fin n → R) : MvPolynomial (Fin n) R := ∑ j, C (u j) * X j
def specFirstVar (u : Fin n → R) (ij : Fin (k + 1) × Fin n) : MvPolynomial (Fin k × Fin n) R :=
  Fin.cases (motive := fun _ => MvPolynomial (Fin k × Fin n) R) (C (u ij.2))
    (fun i => X (i, ij.2)) ij.1
def specFirst (f : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    MvPolynomial (Fin k × Fin n) R :=
  bind₁ (specFirstVar u) f
end Forms
section Proj
variable {R : Type*} [CommRing R] {n : ℕ}
def IsHomogIdeal (I : Ideal (MvPolynomial (Fin n) R)) : Prop :=
  ∀ f ∈ I, ∀ d, homogeneousComponent d f ∈ I
def IsRelevant (I : Ideal (MvPolynomial (Fin n) R)) : Prop :=
  ∃ j, X j ∉ I
structure IsProjPrime (I : Ideal (MvPolynomial (Fin n) R)) : Prop where
  isPrime : I.IsPrime
  isHomog : IsHomogIdeal I
  isRelevant : IsRelevant I
abbrev ProjCycle (R : Type*) [CommRing R] (n : ℕ) := Ideal (MvPolynomial (Fin n) R) →₀ ℕ
open Classical in

def localMult {A : Type*} [CommRing A] (J W : Ideal A) : ℕ :=
  if h : W.IsPrime then
    haveI := h
    (Module.length (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W)))).toNat
  else 0
def relComps (J : Ideal (MvPolynomial (Fin n) R)) : Set (Ideal (MvPolynomial (Fin n) R)) :=
  {W | W ∈ J.minimalPrimes ∧ IsRelevant W}
open Classical in

def fundCycle [IsNoetherianRing R] (J : Ideal (MvPolynomial (Fin n) R)) : ProjCycle R n :=
  Finsupp.onFinset (J.finite_minimalPrimes_of_isNoetherianRing _).toFinset
    (fun W => if W ∈ relComps J then localMult J W else 0)
    (fun W hW => by
      rw [Set.Finite.mem_toFinset]
      by_contra h
      exact hW (if_neg fun h' => h h'.1))
def divCycle [IsNoetherianRing R] (I : Ideal (MvPolynomial (Fin n) R)) (u : Fin n → R) :
    ProjCycle R n :=
  fundCycle (I ⊔ Ideal.span {linForm u})
end Proj
section ChowForm
variable {F : Type*} [Field F] {n : ℕ}
def incidence (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ) :
    Set (Fin k × Fin n → AlgebraicClosure F) :=
  {u | ∃ x : Fin n → AlgebraicClosure F, x ≠ 0 ∧ (∀ g ∈ I, aeval x g = 0) ∧
    ∀ i, ∑ j, u (i, j) * x j = 0}
def IsChowForm (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ)
    (f : MvPolynomial (Fin k × Fin n) F) : Prop :=
  f ≠ 0 ∧ ∀ g : MvPolynomial (Fin k × Fin n) F,
    (∀ u ∈ incidence I k, aeval u g = 0) ↔ f ∣ g
def chowDegree (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ) : ℕ :=
  sInf {δ | ∃ f, IsChowForm I k f ∧ IsMultiHomog δ f}
def IsChowFormCycle (Z : ProjCycle F n) (k : ℕ) (f : MvPolynomial (Fin k × Fin n) F) : Prop :=
  ∃ c : F, c ≠ 0 ∧ ∃ g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F,
    (∀ W ∈ Z.support, IsChowForm W k (g W)) ∧ f = C c * ∏ W ∈ Z.support, g W ^ Z W
end ChowForm
section Finite
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
def gaussNorm (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    (f : MvPolynomial ι K) : ℝ :=
  let s : NNReal := f.support.sup fun m =>
    ⟨NumberField.HeightOneSpectrum.adicAbv K v (f.coeff m), AbsoluteValue.nonneg _ _⟩
  (s : ℝ)
def integralModel (I : Ideal (MvPolynomial (Fin n) K)) : Ideal (MvPolynomial (Fin n) (𝓞 K)) :=
  I.comap (MvPolynomial.map (algebraMap (𝓞 K) K))
def vertComps (I : Ideal (MvPolynomial (Fin n) K)) (u : Fin n → 𝓞 K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Set (Ideal (MvPolynomial (Fin n) (𝓞 K))) :=
  {W | W ∈ relComps (integralModel I ⊔ Ideal.span {linForm u}) ∧
    W.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) = v.asIdeal}
def reduceMod (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (W : Ideal (MvPolynomial (Fin n) (𝓞 K))) :
    Ideal (MvPolynomial (Fin n) v.asIdeal.ResidueField) :=
  W.map (MvPolynomial.map (algebraMap (𝓞 K) v.asIdeal.ResidueField))
def vertTermAt (I : Ideal (MvPolynomial (Fin n) K)) (k : ℕ) (u : Fin n → 𝓞 K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ᶠ W ∈ vertComps I u v,
    (localMult (integralModel I ⊔ Ideal.span {linForm u}) W : ℝ) *
      chowDegree (reduceMod v W) k * Real.log (Ideal.absNorm v.asIdeal)
def vertTerm (I : Ideal (MvPolynomial (Fin n) K)) (k : ℕ) (u : Fin n → 𝓞 K) : ℝ :=
  ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), vertTermAt I k u v
end Finite
section Arch
open Matrix
variable {n : ℕ}
structure HermNorm (n : ℕ) where

  mat : Matrix (Fin n) (Fin n) ℂ

  isUnit_det : IsUnit mat.det
namespace HermNorm
def std (n : ℕ) : HermNorm n := ⟨1, by simp⟩
def norm (h : HermNorm n) (u : Fin n → ℂ) : ℝ :=
  √(∑ i, ‖(h.mat *ᵥ u) i‖ ^ 2)
def dualNorm (h : HermNorm n) (y : Fin n → ℂ) : ℝ :=
  √(∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2)
def pointOf (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) : Fin n → ℂ :=
  h.matᵀ *ᵥ fun i => y i
end HermNorm
def sphereMean (h : HermNorm n) (k : ℕ) (g : (Fin k × Fin n → ℂ) → ℝ) : ℝ :=
  ⨍ u in {u : Fin k × Fin n → ℂ | ∀ i, h.norm (fun j => u (i, j)) < 1},
    g (fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij)
def mahler (h : HermNorm n) (k : ℕ) (f : MvPolynomial (Fin k × Fin n) ℂ) : ℝ :=
  sphereMean h k fun u => Real.log ‖eval u f‖
def fsLog (h : HermNorm n) (u : Fin n → ℂ) (y : Fin n → ℂ) : ℝ :=
  Real.log (‖∑ j, u j * y j‖ / h.dualNorm y)
def coneIntegral (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (e : ℕ)
    (g : (Fin n → ℂ) → ℝ) : ℝ :=
  (∫ y in {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf y) q = 0},
      g (h.pointOf y) ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))) /
    (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}).toReal
def cycleIntegral (h : HermNorm n) (Z : ProjCycle ℂ n) (e : ℕ) (g : (Fin n → ℂ) → ℝ) : ℝ :=
  ∑ W ∈ Z.support, (Z W : ℝ) * coneIntegral h W e g
end Arch
section Height
structure ArchData (K : Type*) [Field K] [NumberField K] (n : ℕ) where

  normAt : (K →+* ℂ) → HermNorm n

  conj_norm : ∀ σ u, (normAt (ComplexEmbedding.conjugate σ)).norm (star u) = (normAt σ).norm u
def ArchData.std (K : Type*) [Field K] [NumberField K] (n : ℕ) : ArchData K n where
  normAt _ := HermNorm.std n
  conj_norm _ u := by simp [HermNorm.std, HermNorm.norm]
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
def chowHt (H : ArchData K n) (k δ : ℕ) (f : MvPolynomial (Fin k × Fin n) K) : ℝ :=
  (1 / Module.finrank ℚ K : ℝ) *
    ((∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f)) +
      ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f.map σ) + k * δ * (harmonic (n - 1) : ℝ) / 2))
end Height
def SphereMeanLinear.Statement : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℂ), ∑ j, ‖p j‖ ^ 2 = 1 →
    sphereMean (HermNorm.std n) 1 (fun z => Real.log ‖∑ j, z (0, j) * star (p j)‖) =
      -(harmonic (n - 1) : ℝ) / 2
def ChowFormSection.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I →
      IsChowFormCycle (divCycle I u) e (specFirst f u)
def ChowFormSectionVertical.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (u : Fin n → 𝓞 K),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm (fun j => (u j : K)) ∉ I →
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        Real.log (gaussNorm v f) - Real.log (gaussNorm v (specFirst f fun j => (u j : K))) =
          vertTermAt I (e + 1) u v
def ChowFormSwap.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin k × Fin n) F), IsChowForm I k f →
      ∀ τ : Equiv.Perm (Fin k), ∃ c : F, c ^ 2 = 1 ∧ rename (Prod.map τ id) f = C c * f
def MahlerSection.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (u : Fin n → ℂ),
    (∀ W ∈ Z.support, IsProjPrime W) → IsChowFormCycle Z (e + 1) f → IsMultiHomog δ f →
    (∀ W ∈ Z.support, linForm u ∉ W) →
      mahler h e (specFirst f u) =
        mahler h (e + 1) f + δ * (harmonic (n - 1) : ℝ) / 2 + cycleIntegral h Z e (fsLog h u)
def GaussLemma.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ι : Type) (f g : MvPolynomial ι K), gaussNorm v (f * g) = gaussNorm v f * gaussNorm v g
def MahlerMul.Statement : Prop :=
  ∀ (n k : ℕ) (h : HermNorm n) (f g : MvPolynomial (Fin k × Fin n) ℂ), f ≠ 0 → g ≠ 0 →
    mahler h k (f * g) = mahler h k f + mahler h k g
def ChowHeightMul.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (H : ArchData K n) (k δ₁ δ₂ : ℕ)
    (f₁ f₂ : MvPolynomial (Fin k × Fin n) K), f₁ ≠ 0 → f₂ ≠ 0 →
      chowHt H k (δ₁ + δ₂) (f₁ * f₂) = chowHt H k δ₁ f₁ + chowHt H k δ₂ f₂
def ChowHeightRecursion.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e δ : ℕ) (H : ArchData K n)
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (e + 1) × Fin n) K)
    (u : Fin n → 𝓞 K),
    IsProjPrime I → IsChowForm I (e + 1) f → IsMultiHomog δ f →
    linForm (fun j => (u j : K)) ∉ I →
      chowHt H (e + 1) δ f =
        chowHt H e δ (specFirst f fun j => (u j : K)) +
          (1 / Module.finrank ℚ K : ℝ) *
            (vertTerm I (e + 1) u -
              ∑ σ : K →+* ℂ, cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
                (fsLog (H.normAt σ) fun j => σ (u j)))
def ChowHeightLowerBound.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e δ : ℕ) (H : ArchData K n)
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (e + 1) × Fin n) K)
    (S : Set (Fin n → 𝓞 K)) (Λ : (K →+* ℂ) → ℝ),
    IsProjPrime I → IsChowForm I (e + 1) f → IsMultiHomog δ f →
    Submodule.span (𝓞 K) S = ⊤ → (∀ s ∈ S, ∀ σ, (H.normAt σ).norm (fun j => σ (s j)) ≤ Λ σ) →
      -(((e + 1) * δ : ℕ) : ℝ) * ((1 / Module.finrank ℚ K : ℝ) * ∑ σ : K →+* ℂ, Real.log (Λ σ)) ≤
        chowHt H (e + 1) δ f
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


