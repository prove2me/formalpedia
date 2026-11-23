-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
-- name    : Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:30.355856+00:00
-- url     : https://prove2.me/theorems/8601be06-4433-44fc-9fc2-84bae96156fd
-- title:
--   Inv Transpose GLInv Transpose GL
-- statement:
--   Definitions and structural lemmas for Inv Transpose GLInv Transpose GL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Polynomial
open scoped ENNReal
namespace PositivityTheory.Rg.Tf.Loc
noncomputable section
section Abstract
variable {G : Type*} [Group G]
def twConj (θ : Monoid.End G) (g δ : G) : G := g⁻¹ * δ * θ g
def TwConjugate (θ : Monoid.End G) (δ δ' : G) : Prop := ∃ g : G, δ' = twConj θ g δ
def twNorm (θ : Monoid.End G) (m : ℕ) (δ : G) : G :=
  ((List.range m).map fun i => (θ ^ i) δ).prod
@[simp] theorem twNorm_zero (θ : Monoid.End G) (δ : G) : twNorm θ 0 δ = 1 := by
  simp [twNorm]
def twCent (θ : Monoid.End G) (δ : G) : Subgroup G where
  carrier := {g | twConj θ g δ = δ}
  one_mem' := by simp [twConj]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, twConj] at *
    rw [map_mul, show (a * b)⁻¹ * δ * (θ a * θ b) = b⁻¹ * (a⁻¹ * δ * θ a) * θ b by group, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, twConj] at *
    calc a⁻¹⁻¹ * δ * θ a⁻¹ = a * (a⁻¹ * δ * θ a) * (θ a)⁻¹ := by rw [ha, map_inv, inv_inv]
      _ = δ := by group
variable [MeasurableSpace G]
def IsQuotNormaliser (H : Subgroup G) (μH : Measure H) (ρ : G → ℝ≥0∞) : Prop :=
  Measurable ρ ∧ ∀ g : G, ∫⁻ h, ρ ((h : G) * g) ∂μH = 1
open Classical in

def quotLIntegral (μG : Measure G) (H : Subgroup G) (μH : Measure H) (F : G → ℝ≥0∞) : ℝ≥0∞ :=
  if hρ : ∃ ρ, IsQuotNormaliser H μH ρ then ∫⁻ g, F g * hρ.choose g ∂μG else 0
def twOrbIntegral (θ : Monoid.End G) (μG : Measure G) (δ : G) (μδ : Measure (twCent θ δ))
    (f : G → ℝ≥0∞) : ℝ≥0∞ :=
  quotLIntegral μG (twCent θ δ) μδ (fun g => f (twConj θ g δ))
def orbIntegral (μG : Measure G) (γ : G) (μγ : Measure (Subgroup.centralizer {γ}))
    (f : G → ℝ≥0∞) : ℝ≥0∞ :=
  quotLIntegral μG (Subgroup.centralizer {γ}) μγ (fun g => f (g⁻¹ * γ * g))
end Abstract
section Galois
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {k E : Type*} [Field k] [Field E] [Algebra k E]
def sigmaGL (τ : E ≃ₐ[k] E) : Monoid.End (GL n E) :=
  Matrix.GeneralLinearGroup.map (τ.toAlgHom.toRingHom)
def incl : GL n k →* GL n E := Matrix.GeneralLinearGroup.map (algebraMap k E)
def normGL (σ : E ≃ₐ[k] E) (δ : GL n E) : GL n E :=
  twNorm (sigmaGL σ) (Module.finrank k E) δ
def IsTwRegSemisimple (σ : E ≃ₐ[k] E) (δ : GL n E) : Prop :=
  ((normGL σ δ : GL n E) : Matrix n n E).charpoly.Separable
def IsRegSemisimple (γ : GL n k) : Prop := ((γ : GL n k) : Matrix n n k).charpoly.Separable
def IsNormOf (σ : E ≃ₐ[k] E) (δ : GL n E) (γ : GL n k) : Prop :=
  ∃ h : GL n E, normGL σ δ = h * incl γ * h⁻¹
end Galois
section Units
variable {n : Type*} [Fintype n] [DecidableEq n]
def unitGL (F : Type*) [Field F] [ValuativeRel F] : Subgroup (GL n F) :=
  (Matrix.GeneralLinearGroup.map (Valuation.integer (ValuativeRel.valuation F)).subtype).range
def unitFn (F : Type*) [Field F] [ValuativeRel F] : GL n F → ℝ≥0∞ :=
  Set.indicator ((unitGL (n := n) F : Subgroup (GL n F)) : Set (GL n F)) 1
end Units
def IsUnramifiedLoc (k E : Type*) [Field k] [Field E] [Algebra k E] [ValuativeRel E] : Prop :=
  ∃ π : k, ValuativeRel.valuation E (algebraMap k E π) < 1 ∧
    ∀ x : E, ValuativeRel.valuation E x < 1 →
      ValuativeRel.valuation E x ≤ ValuativeRel.valuation E (algebraMap k E π)
def BCFLUnit : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
      (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)),
      μE.IsHaarMeasure → μk.IsHaarMeasure →
      μE (unitGL (n := Fin n) E : Set (GL (Fin n) E)) = 1 →
      μk (unitGL (n := Fin n) k : Set (GL (Fin n) k)) = 1 →
      (∀ (δ : GL (Fin n) E) (γ : GL (Fin n) k) (h : GL (Fin n) E)
          (μδ : Measure (twCent (sigmaGL σ) δ)) (μγ : Measure (Subgroup.centralizer {γ})),
          IsTwRegSemisimple σ δ → normGL σ δ = h * incl γ * h⁻¹ →
          μδ.IsHaarMeasure → μγ.IsHaarMeasure →
          Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ =
            Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ →
          twOrbIntegral (sigmaGL σ) μE δ μδ (unitFn E) = orbIntegral μk γ μγ (unitFn k)) ∧
      (∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})),
          IsRegSemisimple γ → (¬ ∃ δ : GL (Fin n) E, IsNormOf σ δ γ) →
          μγ.IsHaarMeasure → orbIntegral μk γ μγ (unitFn k) = 0)
section Unitary
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {k E : Type*} [Field k] [Field E] [Algebra k E]
def invTransposeGL : Monoid.End (GL n E) where
  toFun g := ⟨Matrix.transpose ((g⁻¹ : GL n E) : Matrix n n E), Matrix.transpose (g : Matrix n n E),
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := Units.ext (by
    show Matrix.transpose (((1 : GL n E)⁻¹ : GL n E) : Matrix n n E) = 1
    simp)
  map_mul' := fun a b => Units.ext (by
    show Matrix.transpose (((a * b)⁻¹ : GL n E) : Matrix n n E) =
      Matrix.transpose ((a⁻¹ : GL n E) : Matrix n n E) * Matrix.transpose ((b⁻¹ : GL n E) : Matrix n n E)
    rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul])
def thetaGL (σ : E ≃ₐ[k] E) (J : GL n E) : Monoid.End (GL n E) :=
  (MulAut.conj J).toMonoidHom.comp (invTransposeGL.comp (sigmaGL σ))
def unitaryGL (σ : E ≃ₐ[k] E) (J : GL n E) : Subgroup (GL n E) :=
  MonoidHom.eqLocus (thetaGL σ J) (MonoidHom.id _)
def normU (σ : E ≃ₐ[k] E) (J δ : GL n E) : GL n E := twNorm (thetaGL σ J) 2 δ
def unitFnU [ValuativeRel E] (σ : E ≃ₐ[k] E) (J : GL n E) : unitaryGL σ J → ℝ≥0∞ :=
  Set.indicator {u | (u : GL n E) ∈ unitGL (n := n) E} 1
variable [TopologicalSpace E] [MeasurableSpace (GL n E)]
structure StableData (σ : E ≃ₐ[k] E) (J : GL n E) (γ : unitaryGL σ J)
    (μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ J)))) where
  reps : Finset (unitaryGL σ J)
  conj : unitaryGL σ J → GL n E
  meas : (γ' : unitaryGL σ J) → Measure (Subgroup.centralizer ({γ'} : Set (unitaryGL σ J)))
  conj_spec : ∀ γ' ∈ reps, ((γ' : GL n E)) = (conj γ')⁻¹ * (γ : GL n E) * conj γ'
  distinct : ∀ γ₁ ∈ reps, ∀ γ₂ ∈ reps, (∃ u : unitaryGL σ J, γ₂ = u⁻¹ * γ₁ * u) → γ₁ = γ₂
  exhaust : ∀ γ'' : unitaryGL σ J, (∃ g : GL n E, (γ'' : GL n E) = g⁻¹ * (γ : GL n E) * g) →
    ∃ γ' ∈ reps, ∃ u : unitaryGL σ J, γ'' = u⁻¹ * γ' * u
  haar : ∀ γ' ∈ reps, (meas γ').IsHaarMeasure
  compat : ∀ γ' ∈ reps,
    Measure.map (fun t : Subgroup.centralizer ({γ'} : Set (unitaryGL σ J)) =>
        conj γ' * ((t : unitaryGL σ J) : GL n E) * (conj γ')⁻¹) (meas γ') =
      Measure.map (fun t : Subgroup.centralizer ({γ} : Set (unitaryGL σ J)) =>
        ((t : unitaryGL σ J) : GL n E)) μγ
def stableOrbIntegralU (σ : E ≃ₐ[k] E) (J : GL n E) (μU : Measure (unitaryGL σ J))
    {γ : unitaryGL σ J} {μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ J)))}
    (D : StableData σ J γ μγ) (f : unitaryGL σ J → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ γ' ∈ D.reps, orbIntegral μU γ' (D.meas γ') f
structure TwStableData (σ : E ≃ₐ[k] E) (J : GL n E) (γ : unitaryGL σ J)
    (μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ J)))) where
  reps : Finset (GL n E)
  conj : GL n E → GL n E
  meas : (δ : GL n E) → Measure (twCent (thetaGL σ J) δ)
  norm_spec : ∀ δ ∈ reps, normU σ J δ = conj δ * (γ : GL n E) * (conj δ)⁻¹
  distinct : ∀ δ₁ ∈ reps, ∀ δ₂ ∈ reps, TwConjugate (thetaGL σ J) δ₁ δ₂ → δ₁ = δ₂
  exhaust : ∀ δ : GL n E, (∃ g : GL n E, normU σ J δ = g * (γ : GL n E) * g⁻¹) →
    ∃ δ' ∈ reps, TwConjugate (thetaGL σ J) δ' δ
  haar : ∀ δ ∈ reps, (meas δ).IsHaarMeasure
  compat : ∀ δ ∈ reps,
    Measure.map (fun x : twCent (thetaGL σ J) δ => (conj δ)⁻¹ * (x : GL n E) * conj δ) (meas δ) =
      Measure.map (fun t : Subgroup.centralizer ({γ} : Set (unitaryGL σ J)) =>
        ((t : unitaryGL σ J) : GL n E)) μγ
def twStableOrbIntegralU (σ : E ≃ₐ[k] E) (J : GL n E) (μE : Measure (GL n E))
    {γ : unitaryGL σ J} {μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ J)))}
    (T : TwStableData σ J γ μγ) (f : GL n E → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ δ ∈ T.reps, twOrbIntegral (thetaGL σ J) μE δ (T.meas δ) f
end Unitary
def BCFLUnitU : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    Module.finrank k E = 2 → IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, σ ≠ 1 →
    ∀ (n : ℕ) (J : GL (Fin n) E), J ∈ unitGL (n := Fin n) E → thetaGL σ J ^ 2 = 1 →
    ∀ [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      (μE : Measure (GL (Fin n) E)) (μU : Measure (unitaryGL σ J)),
      μE.IsHaarMeasure → μU.IsHaarMeasure →
      μE (unitGL (n := Fin n) E : Set (GL (Fin n) E)) = 1 →
      μU {u | (u : GL (Fin n) E) ∈ unitGL (n := Fin n) E} = 1 →
      ∀ (γ : unitaryGL σ J) (μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ J))))
        (D : StableData σ J γ μγ) (T : TwStableData σ J γ μγ),
        (((γ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E).charpoly.Separable →
        μγ.IsHaarMeasure →
        twStableOrbIntegralU σ J μE T (unitFn E) = stableOrbIntegralU σ J μU D (unitFnU σ J)
section ComplexValued
variable {G : Type*} [Group G] [MeasurableSpace G]
open Classical in

def quotIntegral (μG : Measure G) (H : Subgroup G) (μH : Measure H) (F : G → ℂ) : ℂ :=
  if hρ : ∃ ρ, IsQuotNormaliser H μH ρ then ∫ g, F g * ((hρ.choose g).toReal : ℂ) ∂μG else 0
def twOrbIntegralC (θ : Monoid.End G) (μG : Measure G) (δ : G) (μδ : Measure (twCent θ δ))
    (f : G → ℂ) : ℂ :=
  quotIntegral μG (twCent θ δ) μδ (fun g => f (twConj θ g δ))
def orbIntegralC (μG : Measure G) (γ : G) (μγ : Measure (Subgroup.centralizer {γ}))
    (f : G → ℂ) : ℂ :=
  quotIntegral μG (Subgroup.centralizer {γ}) μγ (fun g => f (g⁻¹ * γ * g))
end ComplexValued
section Iwahori
variable {m : ℕ}
def IsUniformiser {F : Type*} [Field F] [ValuativeRel F] (ϖ : F) : Prop :=
  ValuativeRel.valuation F ϖ < 1 ∧ ϖ ≠ 0 ∧
    ∀ x : F, ValuativeRel.valuation F x < 1 → ValuativeRel.valuation F x ≤ ValuativeRel.valuation F ϖ
def iwahori (F : Type*) [Field F] [ValuativeRel F] : Set (GL (Fin m) F) :=
  {g | g ∈ unitGL (n := Fin m) F ∧
    ∀ i j : Fin m, j < i → ValuativeRel.valuation F ((g : Matrix (Fin m) (Fin m) F) i j) < 1}
def diagPow {F : Type*} [Field F] (ϖ : Fˣ) (a : Fin m → ℤ) : GL (Fin m) F :=
  ⟨Matrix.diagonal fun i => ((ϖ ^ a i : Fˣ) : F), Matrix.diagonal fun i => (((ϖ ^ a i)⁻¹ : Fˣ) : F),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact Units.mul_inv _,
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact Units.inv_mul _⟩
def StrictlyDominant (a : Fin m → ℤ) : Prop := StrictAnti a
def iwahoriFn (F : Type*) [Field F] [ValuativeRel F] (x : GL (Fin m) F) : GL (Fin m) F → ℂ :=
  Set.indicator {g | ∃ a ∈ iwahori (m := m) F, ∃ b ∈ iwahori (m := m) F, g = a * x * b} 1
end Iwahori
section UnitaryKappa
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {k E : Type*} [Field k] [Field E] [Algebra k E]
def theta1 (σ : E ≃ₐ[k] E) : Monoid.End (GL n E) := thetaGL σ 1
def unitFnC (F : Type*) [Field F] [ValuativeRel F] : GL n F → ℂ :=
  Set.indicator ((unitGL (n := n) F : Subgroup (GL n F)) : Set (GL n F)) 1
def unitFnUC [ValuativeRel E] (σ : E ≃ₐ[k] E) (J : GL n E) : unitaryGL σ J → ℂ :=
  Set.indicator {u | (u : GL n E) ∈ unitGL (n := n) E} 1
variable [TopologicalSpace E] [MeasurableSpace (GL n E)]
structure KappaData (σ : E ≃ₐ[k] E) (γ₀ : GL n E) (ν : Measure (GL n E)) where
  forms : Finset (GL n E)
  herm : ∀ J ∈ forms, thetaGL σ J ^ 2 = 1
  ι : Type
  fin : Fintype ι
  form : ι → GL n E
  form_mem : ∀ x, form x ∈ forms
  rep : (x : ι) → unitaryGL σ (form x)
  conj : ι → GL n E
  meas : (x : ι) → Measure (Subgroup.centralizer ({rep x} : Set (unitaryGL σ (form x))))
  sign : ι → ℤ
  conj_spec : ∀ x, ((rep x : unitaryGL σ (form x)) : GL n E) = (conj x)⁻¹ * γ₀ * conj x
  distinct : ∀ x y, form x = form y →
    (∃ u ∈ unitaryGL σ (form x), ((rep y : unitaryGL σ (form y)) : GL n E) =
      u⁻¹ * ((rep x : unitaryGL σ (form x)) : GL n E) * u) → x = y
  exhaust : ∀ J ∈ forms, ∀ γ'' ∈ unitaryGL σ J, (∃ g : GL n E, γ'' = g⁻¹ * γ₀ * g) →
    ∃ x, form x = J ∧ ∃ u ∈ unitaryGL σ J,
      γ'' = u⁻¹ * ((rep x : unitaryGL σ (form x)) : GL n E) * u
  sign_spec : ∀ x, sign x = 1 ∨ sign x = -1
  haar : ∀ x, (meas x).IsHaarMeasure
  compat : ∀ x,
    Measure.map (fun t : Subgroup.centralizer ({rep x} : Set (unitaryGL σ (form x))) =>
      conj x * ((t : unitaryGL σ (form x)) : GL n E) * (conj x)⁻¹) (meas x) = ν
def kappaOrbIntegral (σ : E ≃ₐ[k] E) {γ₀ : GL n E} {ν : Measure (GL n E)}
    (D : KappaData σ γ₀ ν) (μU : (x : D.ι) → Measure (unitaryGL σ (D.form x)))
    (f : (x : D.ι) → unitaryGL σ (D.form x) → ℂ) : ℂ :=
  haveI := D.fin
  ∑ x, (D.sign x : ℂ) * orbIntegralC (μU x) (D.rep x) (D.meas x) (f x)
end UnitaryKappa
end
end PositivityTheory.Rg.Tf.Loc


