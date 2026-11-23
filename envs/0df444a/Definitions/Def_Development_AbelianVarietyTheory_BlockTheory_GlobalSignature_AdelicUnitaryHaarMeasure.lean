-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_AdelicUnitaryHaarMeasure
-- name    : Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_AdelicUnitaryHaarMeasure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:31.999208+00:00
-- url     : https://prove2.me/theorems/0a667180-7d25-4500-80b9-f1769cf0d371
-- title:
--   Adelic Unitary Haar Measure
-- statement:
--   Definitions and structural lemmas for Adelic Unitary Haar Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/AdelicUnitaryHaarMeasure.lean

import Mathlib
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
def IsUnimodularLC (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] : Prop :=
  IsTopologicalGroup G ∧ T2Space G ∧ LocallyCompactSpace G ∧ SecondCountableTopology G ∧
    BorelSpace G ∧ (∃ μ : Measure G, μ.IsHaarMeasure) ∧
    ∀ μ : Measure G, μ.IsHaarMeasure → μ.IsMulRightInvariant
def IsDiscreteWithDomains {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (Γ : Subgroup G) : Prop :=
  Countable Γ ∧ DiscreteTopology Γ ∧
    ∀ μ : Measure G, μ.IsHaarMeasure →
      ∃ 𝓕 : Set G, MeasurableSet 𝓕 ∧ IsFundamentalDomain Γ 𝓕 μ
section Points
variable {F E : Type} [Field F] [Field E] [Algebra F E]
def ratPts (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA R σ J) := HFinIn R σ J
def UnimodularOver (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E)
    {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Prop :=
  IsUnimodularLC (HA R σ J) ∧
    ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → IsUnimodularLC (Hstab R σ J x)
end Points
def AdelicUnitaryHaar : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      UnimodularOver (AF F) σ J ∧ UnimodularOver (Ainf F) σ J ∧ UnimodularOver (Af F) σ J ∧
      (∀ v : HeightOneSpectrum (𝓞 F), UnimodularOver (Fv F v) σ J) ∧
      IsDiscreteWithDomains (ratPts (AF F) σ J) ∧
      ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 →
        IsDiscreteWithDomains (HstabFin (AF F) σ J x)
theorem isUnimodularLC_of_commGroup (G : Type) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] : IsUnimodularLC G :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Measure.haar, inferInstance⟩, fun _ _ => inferInstance⟩
example : @IsUnimodularLC Circle _ _ (borel Circle) :=
  @isUnimodularLC_of_commGroup Circle _ _ _ _ _ _ (borel Circle) (@BorelSpace.mk _ _ (borel Circle) rfl)
example (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] :
    IsDiscreteWithDomains (⊥ : Subgroup G) := by
  refine ⟨inferInstance, inferInstance, fun μ _ => ⟨Set.univ, MeasurableSet.univ, ?_⟩⟩
  exact IsFundamentalDomain.mk' MeasurableSet.univ.nullMeasurableSet fun x =>
    ⟨1, Set.mem_univ _, fun _ _ => Subsingleton.elim _ _⟩
end GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure


