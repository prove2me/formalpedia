-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DatumF
-- name    : Formalism_LocalToGlobal_IndefiniteReal_DatumF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:58:37.355513+00:00
-- url     : https://prove2.me/theorems/ad958c84-30d8-4c13-9d93-c7e55cf12c81
-- title:
--   Datum F
-- statement:
--   Definitions and structural lemmas for Datum F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DatumF.lean

import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct ContDiff
namespace Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
section Base
variable (F E)
abbrev AEF : Type := AF F ⊗[F] E
abbrev incAF : E →+* AF F ⊗[F] E := inclR (F := F) (AF F)
variable {F E}
abbrev cAF (σ : E →ₐ[F] E) : AEF F E →+* AEF F E := sigR (AF F) σ
abbrev GAF (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Type := HA (AF F) σ J
def GQF (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Subgroup (GAF σ J) := HFinIn (AF F) σ J
def matHomF (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : GAF σ J →* GL (Fin n) (AF F ⊗[F] E) :=
  (HR (AF F) σ J).subtype
def mtF (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) : Matrix (Fin n) (Fin n) (AEF F E) :=
  (matHomF σ J g).1
variable (F E) in

def infPartF : AEF F E →+* Ainf F ⊗[F] E :=
  (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
variable (F E) in

def finPartF : AEF F E →+* Af F ⊗[F] E :=
  (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
end Base
section Real
def IsInfEmbF (τ : E →+* ℂ) (θ : Ainf F ⊗[F] E →+* ℂ) : Prop :=
  (∀ x : E, θ ((1 : Ainf F) ⊗ₜ[F] x) = τ x) ∧ Continuous fun a : Ainf F => θ (a ⊗ₜ[F] (1 : E))
def IsInfFamF {Tau : Type} (tauE : Tau → (E →+* ℂ)) (θ : Tau → (Ainf F ⊗[F] E →+* ℂ)) : Prop :=
  ∀ ρ, IsInfEmbF (tauE ρ) (θ ρ)
def IsStdCharF {Tau : Type} [Fintype Tau] (tauE : Tau → (E →+* ℂ)) (ψ : AddChar (AF F) ℂ) (s : ℤ) : Prop :=
  IsCharAF F ψ ∧ AllSome (IsInfFamF (F := F) tauE) fun θ =>
    ∀ x : Ainf F, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * s * ∑ ρ, θ ρ (x ⊗ₜ[F] (1 : E)))
variable (F E) in

def idFF : (AF F)ˣ →* (AEF F E)ˣ := Units.map (algebraMap (AF F) (AEF F E)).toMonoidHom
def IsHeckeCharF (χ : (AEF F E)ˣ →* Circle) : Prop :=
  Continuous χ ∧ ∀ x : Eˣ, χ (Units.map (incAF F E).toMonoidHom x) = 1
variable (E) in

def IsEtaF (η : (AF F)ˣ →* Circle) : Prop :=
  Continuous η ∧ (∀ a : Fˣ, η (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1) ∧
    (∀ x : (AEF F E)ˣ, η (Units.map (Algebra.norm (AF F) : AEF F E →* AF F) x) = 1) ∧ η ≠ 1
def ResEtaF (χ : (AEF F E)ˣ →* Circle) (n : ℕ) : Prop :=
  AllSome (IsEtaF E) fun η => ∀ a, χ (idFF F E a) = η a ^ n
variable (F) in

def IsPlaceIdemF (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) : Prop :=
  ∃ α : Af F, ε = pairA F 0 α ∧ evalV F v α = 1 ∧ ∀ v', v' ≠ v → evalV F v' α = 0
def IsSplitIdemF (σ : E →ₐ[F] E) (e : AEF F E) : Prop :=
  e * e = e ∧ e * cAF σ e = 0 ∧ ∃ v ε, IsPlaceIdemF F v ε ∧ e + cAF σ e = algebraMap (AF F) (AEF F E) ε
def SuppAtF (σ : E →ₐ[F] E) (e : AEF F E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) : Prop :=
  ∀ i j, (e + cAF σ e) * (mtF σ J g - 1) i j = (mtF σ J g - 1) i j
def IsDetAtF (σ : E →ₐ[F] E) (e : AEF F E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) (x : (AEF F E)ˣ) :
    Prop :=
  (x : AEF F E) = e * (mtF σ J g).det + (1 - e)
end Real
section Orient
variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
abbrev WOF (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ) : Type :=
  Matrix (Fin nT) (Fin nS) (AEF F E)
scoped instance measWOF (nS nT : ℕ) : MeasurableSpace (WOF F E nS nT) := borel _
def ratWF (γ : Matrix (Fin nT) (Fin nS) E) : WOF F E nS nT := γ.map (incAF F E)
variable (F E nS nT) in

def ratLF : AddSubgroup (WOF F E nS nT) :=
  ((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS)).range
def hOF (x y : WOF F E nS nT) : AEF F E :=
  ∑ a, ∑ b, ∑ c, ∑ d, incAF F E (JS⁻¹ a b) * cAF σ (y c b) * incAF F E (JT c d) * x d a
def symplOF (xi0 : E) (x y : WOF F E nS nT) : AF F :=
  Algebra.trace (AF F) (AEF F E) (incAF F E xi0 * hOF σ JS JT x y)
def symplOHF (xi0 : E) (x y : WOF F E nS nT) : AF F :=
  algebraMap F (AF F) (1 / 2) * symplOF σ JS JT xi0 x y
def heisOF (xi0 : E) (ψ : AddChar (AF F) ℂ) (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ) : WOF F E nS nT → ℂ :=
  fun w => ψ (symplOHF σ JS JT xi0 w w₀) * f (w + w₀)
def actOF (g : GAF σ JS) (h : GAF σ JT) (x : WOF F E nS nT) : WOF F E nS nT :=
  HMul.hMul (HMul.hMul (mtF σ JT h) (x : Matrix (Fin nT) (Fin nS) (AEF F E))) (mtF σ JS g⁻¹)
structure IsThetaFunOF (xi0 : E) (ψ : AddChar (AF F) ℂ) (f : WOF F E nS nT → ℂ) : Prop where
  quasi : ∀ γ w, f (ratWF γ + w) = ψ (-(symplOHF σ JS JT xi0 (ratWF γ) w)) * f w
  level : ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
    ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT xi0 ψ u f = f
  cont : Continuous f
  smooth : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L → (∀ t, (L t).map (finPartF F E) = 0) →
    ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)
def splitFacOF (χS χT : (AEF F E)ˣ →* Circle) (x y : (AEF F E)ˣ) : Circle := (χT x)⁻¹ * χS y
structure IsWeilDatumOF {Tau : Type} [Fintype Tau] (tauE : Tau → (E →+* ℂ)) (xi0 : E) (ψ : AddChar (AF F) ℂ)
    (χS χT : (AEF F E)ˣ →* Circle)
    (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop where
  std : IsStdCharF tauE ψ (-1)
  hecS : IsHeckeCharF χS
  hecT : IsHeckeCharF χT
  resS : ResEtaF χS nS
  resT : ResEtaF χT nT
  om_pres : ∀ p f, IsThetaFunOF σ JS JT xi0 ψ f → IsThetaFunOF σ JS JT xi0 ψ (om p f)
  om_heis : ∀ g h w₀ f, IsThetaFunOF σ JS JT xi0 ψ f →
    om (g, h) (heisOF σ JS JT xi0 ψ w₀ f) = heisOF σ JS JT xi0 ψ (actOF σ JS JT g h w₀) (om (g, h) f)
  om_aut : ∀ γ ∈ GQF σ JS, ∀ γ' ∈ GQF σ JT, ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → om (γ, γ') f 0 = f 0
  om_cont : ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → ∀ w, Continuous fun p : GAF σ JS × GAF σ JT => om p f w
  om_unit : ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f, IsThetaFunOF σ JS JT xi0 ψ f →
      ∫⁻ w in 𝓕, ‖om p f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ
  om_split : ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h → ∀ x y,
    IsDetAtF σ e JS g x → IsDetAtF σ e JT h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT xi0 ψ f →
        ℓ (heisOF σ JS JT xi0 ψ u f) = ℓ f) →
      ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → ℓ (om (g, h) f) = (r : ℂ) * (splitFacOF χS χT x y : ℂ) * ℓ f
variable {σ JS JT}
def thetaKOF (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) (g : GAF σ JS) (h : GAF σ JT)
    (f : WOF F E nS nT → ℂ) : ℂ :=
  om (g, h) f 0
end Orient
end Formalism.IndefR.DatumF
end


