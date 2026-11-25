-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_InstTopologicalSpaceHA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_InstTopologicalSpaceHA
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:40.589128+00:00
-- url     : https://prove2.me/theorems/113008f7-d888-4e36-8dcc-f37071c05017
-- title:
--   Inst Topological Space HA
-- statement:
--   Definitions and structural lemmas for Inst Topological Space HA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/InstTopologicalSpaceHA.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_OmegaDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
def sigR (σ : E →ₐ[F] E) : R ⊗[F] E →+* R ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom
def inclR : E →+* R ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).toRingHom
def JR {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  J.map (inclR R)
def HR (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Subgroup (GL (Fin M) (R ⊗[F] E)) :=
  HcS.UG.UJ (sigR R σ) (JR R J)
end Alg
end HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes
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
def HA.mat (h : HA R σ J) : GL (Fin M) (R ⊗[F] E) := let h' : HR R σ J := h; h'.1
end Top
def SelfDual {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (μ : Measure V)
    (χ : V → V → ℂ) : Prop :=
  μ.IsAddHaarMeasure ∧
  ∀ Φ : V → ℂ, Continuous Φ → HasCompactSupport Φ →
    Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ →
      ∀ z, ∫ y, (∫ x, Φ x * χ x y ∂μ) * χ y z ∂μ = Φ (-z)
section Adeles
variable (F : Type) [Field F] [NumberField F]
abbrev AF := AdeleRing (𝓞 F) F
abbrev Ainf := InfiniteAdeleRing F
abbrev Af := FiniteAdeleRing (𝓞 F) F
end Adeles
end HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
section AdeleAnalysis
variable {F : Type} [Field F] [NumberField F]
scoped instance measAF : MeasurableSpace (AF F) := borel _
scoped instance measAinf : MeasurableSpace (Ainf F) := borel _
scoped instance measAf : MeasurableSpace (Af F) := borel _
variable (F)
def pairA (x : Ainf F) (y : Af F) : AF F := (x, y)
def fstA : AF F →ₐ[F] Ainf F := AlgHom.fst F (Ainf F) (Af F)
def IsCharAF (ψ : AddChar (AF F) ℂ) : Prop :=
  Continuous ψ ∧ (∀ x, ‖ψ x‖ = 1) ∧ (∀ a : F, ψ (algebraMap F (AF F) a) = 1) ∧ ∃ x, ψ x ≠ 1
def psiInf (ψ : AddChar (AF F) ℂ) (x : Ainf F) : ℂ := ψ (pairA F x 0)
end AdeleAnalysis
section Tuples
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
end Tuples
end HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
section More
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
end More
end HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
section HMeasures
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
end HMeasures
end HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes


