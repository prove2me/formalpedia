-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
-- name    : Formalism_UnipotentAdelicQuotients_ThmBInHecke
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:16.064293+00:00
-- url     : https://prove2.me/theorems/209e39bb-59ba-4bb7-b472-82850d880705
-- title:
--   Thm BIn Hecke
-- statement:
--   Definitions and structural lemmas for Thm BIn Hecke, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/ThmBInHecke.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain
namespace HeckeCharacterZeroLocus.ThmBIn
section Adeles
variable (F : Type) [Field F] [NumberField F]
abbrev AF := AdeleRing (𝓞 F) F
abbrev Ainf := InfiniteAdeleRing F
abbrev Af := FiniteAdeleRing (𝓞 F) F
abbrev Fv (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F
def pairA (x : Ainf F) (y : Af F) : AF F := (x, y)
def sndA : AF F →ₐ[F] Af F := AlgHom.snd F (Ainf F) (Af F)
def evalV (v : HeightOneSpectrum (𝓞 F)) : Af F →ₐ[F] Fv F v :=
  { RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v with
    commutes' := fun _ => rfl }
def intAf : Set (Af F) :=
  {a | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v a ∈ v.adicCompletionIntegers F}
end Adeles
section Tens
variable {F E : Type} [Field F] [Field E] [Algebra F E]
scoped instance topTens (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (R ⊗[F] E) := moduleTopology R (R ⊗[F] E)
variable (R : Type) [CommRing R] [Algebra F R]
def sigR (σ : E →ₐ[F] E) : R ⊗[F] E →+* R ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom
def inclR : E →+* R ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).toRingHom
end Tens
def IsCMExt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) : Prop :=
  NumberField.IsTotallyReal F ∧ NumberField.IsTotallyComplex E ∧ Module.finrank F E = 2 ∧
    ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)
section Hecke
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
abbrev AE : Type := AF F ⊗[F] E
abbrev incA : E →+* AF F ⊗[F] E := inclR (F := F) (AF F)
def finPart : AE F E →+* Af F ⊗[F] E :=
  (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
def intAE : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}
def idF : (AF F)ˣ →* (AE F E)ˣ :=
  Units.map (algebraMap (AF F) (AE F E)).toMonoidHom
open HeckeCharacterZeroLocus.ThmBIn in

def IsHeckeChar (χ : (AE F E)ˣ →* Circle) : Prop :=
  Continuous χ ∧ ∀ x : Eˣ, χ (Units.map (incA F E).toMonoidHom x) = 1
def IsPlaceIdem (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) : Prop :=
  ∃ α : Af F, ε = pairA F 0 α ∧ evalV F v α = 1 ∧ ∀ v', v' ≠ v → evalV F v' α = 0
variable {F E}
abbrev cA (σ : E →ₐ[F] E) : AE F E →+* AE F E := sigR (AF F) σ
def IsSplitIdem (σ : E →ₐ[F] E) (e : AE F E) : Prop :=
  e * e = e ∧ e * cA σ e = 0 ∧ ∃ v ε, IsPlaceIdem F v ε ∧ e + cA σ e = algebraMap (AF F) (AE F E) ε
def IsIdemAt (σ : E →ₐ[F] E) (e : AE F E) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  IsSplitIdem σ e ∧ ∀ x : 𝓞 E, x ≠ 0 →
    (x ∈ P.asIdeal ↔ finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E)
def IsPrimeIdem (σ : E →ₐ[F] E) (P : HeightOneSpectrum (𝓞 E)) (e f : AE F E) : Prop :=
  (IsIdemAt σ e P ∧ f = e + cA σ e) ∨
  (f = e ∧ (∃ v ε, IsPlaceIdem F v ε ∧ e = algebraMap (AF F) (AE F E) ε) ∧
    ∀ x : 𝓞 E, x ≠ 0 →
      (x ∈ P.asIdeal ↔ finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E))
def IsUnifIdele (σ : E →ₐ[F] E) (P : HeightOneSpectrum (𝓞 E)) (x : (AE F E)ˣ) : Prop :=
  ∃ (e f : AE F E) (ϖ : 𝓞 E), IsPrimeIdem σ P e f ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧
    (x : AE F E) = e * incA F E (ϖ : E) + (1 - e)
def IsUnramAt (σ : E →ₐ[F] E) (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ e f : AE F E, IsPrimeIdem σ P e f ∧ ∀ x : (AE F E)ˣ, (x : AE F E) = e * (x : AE F E) + (1 - e) →
    finPart F E (x : AE F E) ∈ intAE F E → finPart F E ((x⁻¹ : (AE F E)ˣ) : AE F E) ∈ intAE F E → χ x = 1
open Classical in

def chiAt (σ : E →ₐ[F] E) (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)) : ℂ :=
  if h : IsUnramAt σ χ P ∧ ∃ x, IsUnifIdele σ P x then ((χ h.2.choose : Circle) : ℂ) else 0
def normP (P : HeightOneSpectrum (𝓞 E)) : ℕ := Ideal.absNorm P.asIdeal
def lfac (σ : E →ₐ[F] E) (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)) (s : ℂ) : ℂ :=
  (1 - chiAt σ χ P * (normP P : ℂ) ^ (-s))⁻¹
def lEuler (σ : E →ₐ[F] E) (χ : (AE F E)ˣ →* Circle) (s : ℂ) : ℂ :=
  ∏' P : HeightOneSpectrum (𝓞 E), lfac σ χ P s
end Hecke
def HeckeLNonvanish : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ →
    ∀ χ : (AE F E)ˣ →* Circle, IsHeckeChar F E χ → (∀ a : (AF F)ˣ, χ (idF F E a) = 1) → χ ≠ 1 →
      (∀ s : ℂ, 1 < s.re → Multipliable (fun P : HeightOneSpectrum (𝓞 E) => lfac σ χ P s)) ∧
      ∃ (L : ℂ → ℂ) (ε : ℝ), 0 < ε ∧ DifferentiableOn ℂ L {s | 1 - ε < s.re} ∧
        (∀ s : ℂ, 1 < s.re → L s = lEuler σ χ s) ∧ L 1 ≠ 0
def LfinHol : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ →
    ∀ χ : (AE F E)ˣ →* Circle, IsHeckeChar F E χ → (∀ a : (AF F)ˣ, χ (idF F E a) = 1) → χ ≠ 1 →
      ∃ (L : ℂ → ℂ) (ε : ℝ), 0 < ε ∧ DifferentiableOn ℂ L {s | 1 - ε < s.re} ∧
        (∀ s : ℂ, 1 < s.re → Multipliable (fun P : HeightOneSpectrum (𝓞 E) => lfac σ χ P s) ∧
          L s = lEuler σ χ s) ∧
        ∀ n : ℕ, 1 ≤ n → (L n).im = 0 ∧ 0 < (L n).re
end HeckeCharacterZeroLocus.ThmBIn
end


