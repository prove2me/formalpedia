-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- name    : Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:43.671834+00:00
-- url     : https://prove2.me/theorems/82b3f00e-e327-4391-b554-57d8efd7a311
-- title:
--   Genus Mass Volumes
-- statement:
--   Definitions and structural lemmas for Genus Mass Volumes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/GenusMassVolumes.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
def AllSome {α : Sort*} (P : α → Prop) (Q : α → Prop) : Prop := (∃ a, P a) ∧ ∀ a, P a → Q a
def IsCMExt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) : Prop :=
  NumberField.IsTotallyReal F ∧ NumberField.IsTotallyComplex E ∧ Module.finrank F E = 2 ∧
    ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)
section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
def IsHermND (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Prop :=
  (∀ i j, σ (J j i) = J i j) ∧ J.det ≠ 0
def hE (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) : E :=
  Formalism.UG.hform (σ : E →+* E) J x y
def gramE (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → E) :
    Matrix (Fin n) (Fin n) E := fun a b => hE σ J (X a) (X b)
variable (R : Type) [CommRing R] [Algebra F R]
def sigR (σ : E →ₐ[F] E) : R ⊗[F] E →+* R ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom
def inclR : E →+* R ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).toRingHom
def JR {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  J.map (inclR R)
def HR (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Subgroup (GL (Fin M) (R ⊗[F] E)) :=
  Formalism.UG.UJ (sigR R σ) (JR R J)
def HFin (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Subgroup (GL (Fin M) (R ⊗[F] E)) :=
  (Formalism.UG.UJ (σ : E →+* E) J).map (Formalism.UG.bc (inclR R))
def HFinIn (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HR R σ J) :=
  (HFin R σ J).subgroupOf (HR R σ J)
def hR (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → R ⊗[F] E) :
    R ⊗[F] E :=
  Formalism.UG.hform (sigR R σ) (JR R J) x y
def BR (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y : Fin n → Fin M → R ⊗[F] E) : R :=
  ∑ a, Algebra.trace R (R ⊗[F] E) (hR R σ J (X a) (Y a))
def qR (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin M → R ⊗[F] E) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (hR R σ J x x)
def gramR (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  fun a b => hR R σ J (X a) (X b)
def HermR (σ : E →ₐ[F] E) (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) (R ⊗[F] E)) where
  carrier := {S | ∀ a b, sigR R σ (S b a) = S a b}
  zero_mem' := by intro a b; simp
  add_mem' := by
    intro S T hS hT a b
    simp only [Set.mem_setOf_eq] at *
    simp [map_add, hS a b, hT a b]
  neg_mem' := by
    intro S hS a b
    simp only [Set.mem_setOf_eq] at *
    simp [map_neg, hS a b]
def pairHerm (σ : E →ₐ[F] E) (n : ℕ) (S T : HermR R σ n) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
    (∑ a, ∑ b, (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a b * (T : Matrix (Fin n) (Fin n) _) b a)
def ratTup {M n : ℕ} (X : Fin n → Fin M → E) : Fin n → Fin M → R ⊗[F] E :=
  fun a i => inclR R (X a i)
def actTup {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    Fin n → Fin M → R ⊗[F] E :=
  fun a => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec (X a)
end Alg
end Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
section Top
variable {F E : Type} [Field F] [Field E] [Algebra F E]
scoped instance topTens (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (R ⊗[F] E) := moduleTopology R (R ⊗[F] E)
scoped instance measTens (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    MeasurableSpace (R ⊗[F] E) := borel (R ⊗[F] E)
def HA (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Type := HR R σ J
variable (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)
instance : Group (HA R σ J) := inferInstanceAs (Group (HR R σ J))
instance [TopologicalSpace R] : TopologicalSpace (HA R σ J) :=
  inferInstanceAs (TopologicalSpace (HR R σ J))
instance [TopologicalSpace R] : MeasurableSpace (HA R σ J) := borel (HA R σ J)
instance : MulAction (HFinIn R σ J) (HA R σ J) := inferInstanceAs (MulAction (HFinIn R σ J) (HR R σ J))
def HA.mat (h : HA R σ J) : GL (Fin M) (R ⊗[F] E) := let h' : HR R σ J := h; h'.1
end Top
def meanC {G : Type} [MeasurableSpace G] (μ : Measure G) (𝓕 : Set G) (f : G → ℂ) : ℂ :=
  ((μ 𝓕).toReal)⁻¹ • ∫ h in 𝓕, f h ∂μ
def meanL {G : Type} [MeasurableSpace G] (μ : Measure G) (𝓕 : Set G) (f : G → ENNReal) : ENNReal :=
  (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, f h ∂μ
def SelfDual {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (μ : Measure V)
    (χ : V → V → ℂ) : Prop :=
  μ.IsAddHaarMeasure ∧
  ∀ Φ : V → ℂ, Continuous Φ → HasCompactSupport Φ →
    Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ →
      ∀ z, ∫ y, (∫ x, Φ x * χ x y ∂μ) * χ y z ∂μ = Φ (-z)
def IsContDensity {V X Y : Type} [MeasurableSpace V] [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (Φ : V → ℂ) (g : X → ℂ) : Prop :=
  Continuous g ∧ ∀ S : Set X, IsCompact S →
    ∫ v in f ⁻¹' (ι '' S), Φ v ∂μ = ∫ b in S, g b ∂ν
def IsContDensityOn {V X Y : Type} [MeasurableSpace V] [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (B : Set X) (Φ : V → ℂ) (g : X → ℂ) :
    Prop :=
  ContinuousOn g B ∧ ∀ S : Set X, IsCompact S → S ⊆ B →
    ∫ v in f ⁻¹' (ι '' S), Φ v ∂μ = ∫ b in S, g b ∂ν
def IsFibreFamily {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure V) (f : V → Y) (ι : X → Y) (U : Set V) (ν : Measure X)
    (B : Set X) (fib : X → Measure V) : Prop :=
  (∀ b, fib b (f ⁻¹' {ι b} ∩ U)ᶜ = 0) ∧
  (∀ φ : V → ENNReal, Measurable φ → ∫⁻ v in U, φ v ∂μ = ∫⁻ b, ∫⁻ v, φ v ∂(fib b) ∂ν) ∧
  (∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∀ b ∈ B, Integrable φ (fib b)) ∧ ContinuousOn (fun b => ∫ v, φ v ∂(fib b)) B)
section Adeles
variable (F : Type) [Field F] [NumberField F]
abbrev AF := AdeleRing (𝓞 F) F
abbrev Ainf := InfiniteAdeleRing F
abbrev Af := FiniteAdeleRing (𝓞 F) F
abbrev Fv (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F
end Adeles
end Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
section AdeleAnalysis
variable {F : Type} [Field F] [NumberField F]
scoped instance measAF : MeasurableSpace (AF F) := borel _
scoped instance measAinf : MeasurableSpace (Ainf F) := borel _
scoped instance measAf : MeasurableSpace (Af F) := borel _
scoped instance measFv (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (Fv F v) := borel _
variable (F)
def pairA (x : Ainf F) (y : Af F) : AF F := (x, y)
def fstA : AF F →ₐ[F] Ainf F := AlgHom.fst F (Ainf F) (Af F)
def sndA : AF F →ₐ[F] Af F := AlgHom.snd F (Ainf F) (Af F)
def evalV (v : HeightOneSpectrum (𝓞 F)) : Af F →ₐ[F] Fv F v :=
  { RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v with
    commutes' := fun _ => rfl }
open Classical in

def singleV (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : Af F :=
  RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y
def IsCharAF (ψ : AddChar (AF F) ℂ) : Prop :=
  Continuous ψ ∧ (∀ x, ‖ψ x‖ = 1) ∧ (∀ a : F, ψ (algebraMap F (AF F) a) = 1) ∧ ∃ x, ψ x ≠ 1
def psiInf (ψ : AddChar (AF F) ℂ) (x : Ainf F) : ℂ := ψ (pairA F x 0)
def psiV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : ℂ :=
  ψ (pairA F 0 (singleV F v y))
end AdeleAnalysis
section Tuples
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
def projInf {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) : Fin n → Fin M → Ainf F ⊗[F] E :=
  fun a i => Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (X a i)
def projFin {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) : Fin n → Fin M → Af F ⊗[F] E :=
  fun a i => Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (X a i)
def projV (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (X : Fin n → Fin M → Af F ⊗[F] E) :
    Fin n → Fin M → Fv F v ⊗[F] E :=
  fun a i => Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (X a i)
def sizeInf {d : ℕ} (b : Module.Basis (Fin d) F E) (y : Ainf F ⊗[F] E) : ℝ :=
  ∑ k, ∑ v : InfinitePlace F, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y k v‖
def sizeTup {d M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → Ainf F ⊗[F] E) : ℝ :=
  ∑ a, ∑ i, sizeInf b (X a i)
def RapidDecay {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ X, ‖Φ X‖ * (1 + sizeTup b X) ^ N ≤ C
def latV {d M n : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
  {Y | ∀ a i k, (Algebra.TensorProduct.basis (Fv F v) b).repr (Y a i) k ∈ v.adicCompletionIntegers F}
def IsSB {V : Type} [TopologicalSpace V] (Φ : V → ℂ) : Prop :=
  IsLocallyConstant Φ ∧ HasCompactSupport Φ
def IsProdInfFin {M n : ℕ} (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ)
    (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) : Prop :=
  ∀ X, Φ X = Φinf (projInf X) * Φf (projFin X)
def IsPureFin {d M n : ℕ} (b : Module.Basis (Fin d) F E) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ) : Prop :=
  (∀ v, IsSB (Φv v)) ∧ (∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) ∧
    ∀ X, Φf X = ∏ᶠ v, Φv v (projV v X)
end Tuples
end Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
section More
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
theorem map_mem_HermR (σ : E →ₐ[F] E) {n : ℕ} (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a b, σ (T b a) = T a b) : T.map (inclR R) ∈ HermR R σ n := by
  intro a b
  simp [sigR, inclR, Matrix.map_apply, hT a b]
def hermOf (σ : E →ₐ[F] E) {n : ℕ} (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a b, σ (T b a) = T a b) : HermR R σ n :=
  ⟨T.map (inclR R), map_mem_HermR R σ T hT⟩
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
instance instMulActionTup (n : ℕ) : MulAction (HA R σ J) (Fin n → Fin M → R ⊗[F] E) where
  smul h X := actTup R (HA.mat R σ J h) X
  one_smul X := by
    funext a
    show ((1 : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec (X a) = X a
    simp
  mul_smul g h X := by
    funext a
    show (((HA.mat R σ J g) * (HA.mat R σ J h) : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _).mulVec (X a) =
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec
        (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec (X a))
    rw [Units.val_mul, Matrix.mulVec_mulVec]
def Hstab (x : Fin 1 → Fin M → E) : Subgroup (HA R σ J) :=
  MulAction.stabilizer (HA R σ J) (ratTup (F := F) R x)
def HstabFin (x : Fin 1 → Fin M → E) : Subgroup (Hstab R σ J x) :=
  ((HFinIn R σ J) ⊓ Hstab R σ J x).subgroupOf (Hstab R σ J x)
instance measHerm [TopologicalSpace R] (n : ℕ) : MeasurableSpace (HermR R σ n) := borel _
end More
end Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
section HMeasures
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
def IsHaarH (μ : Measure (HA (AF F) σ J)) : Prop := μ.IsHaarMeasure
def IsFDH (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) : Prop :=
  IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ
def SdW (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (ψR : R → ℂ) (n : ℕ)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) : Prop :=
  SelfDual μ (fun X Y => ψR (BR R σ J X Y))
def SdR (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ψR : R → ℂ)
    (ν : Measure R) : Prop :=
  SelfDual ν (fun s t => ψR (s * t))
def SdHerm (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (ψR : R → ℂ) (n : ℕ)
    (ν : Measure (HermR R σ n)) : Prop :=
  SelfDual ν (fun S T => ψR (pairHerm R σ n S T))
def IsXbetaMeasure (ψ : AddChar (AF F) ℂ) (β : F)
    (νX : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) : Prop :=
  νX {X | qR (AF F) σ J (X 0) ≠ algebraMap F (AF F) β} = 0 ∧
  AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) 1) fun μinf =>
  AllSome (SdR (Ainf F) (psiInf F ψ)) fun νinf =>
  AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) =>
    ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) 1 (μv v)) fun μv =>
  AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v) =>
    ∀ v, SdR (Fv F v) (psiV F ψ v) (νv v)) fun νv =>
  AllSome (fun fibInf : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E) =>
    IsFibreFamily μinf (fun X => qR (Ainf F) σ J (X 0)) id Set.univ νinf
      {c : Ainf F | ∀ w, c w ≠ 0} fibInf) fun fibInf =>
  AllSome (fun fibV : ∀ v : HeightOneSpectrum (𝓞 F),
      Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) =>
    ∀ v, IsFibreFamily (μv v) (fun X => qR (Fv F v) σ J (X 0)) id Set.univ (νv v)
      {c | c ≠ 0} (fibV v)) fun fibV =>
  ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ)
    (Φinf : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin 1 → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    Integrable Φ νX ∧
    Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (algebraMap F (Fv F v) β))) ∧
    ∫ X, Φ X ∂νX = (∫ X, Φinf X ∂(fibInf (algebraMap F (Ainf F) β))) *
      ∏' v, ∫ X, Φv v X ∂(fibV v (algebraMap F (Fv F v) β))
def IsCompatible (x : Fin 1 → Fin M → E) (μ : Measure (HA (AF F) σ J))
    (μ' : Measure (Hstab (AF F) σ J x)) (νX : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) : Prop :=
  ∀ f : HA (AF F) σ J → ENNReal, Measurable f →
    ∀ s : (Fin 1 → Fin M → AF F ⊗[F] E) → HA (AF F) σ J,
      (∀ y, (∃ g : HA (AF F) σ J, g • ratTup (AF F) x = y) → s y • ratTup (AF F) x = y) →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (AF F) σ J)) ∂μ' ∂νX
end HMeasures
end Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes


