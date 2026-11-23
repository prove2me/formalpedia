-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAF
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:02.504317+00:00
-- url     : https://prove2.me/theorems/4cbc6860-568d-47e9-98b9-20a8ec569654
-- title:
--   Topo AF
-- statement:
--   Definitions and structural lemmas for Topo AF, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/TopoAF.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW.TopoAF
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology TopologicalSpace Filter
open scoped RestrictedProduct
variable (F : Type) [Field F] [NumberField F]
instance countable_field : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
instance countable_ringOfIntegers : Countable (𝓞 F) := Finsupp.Countable.of_moduleFinite (R := ℤ)
theorem countable_ideal : Countable (Ideal (𝓞 F)) := by
  have hs : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    exact ⟨s, hs⟩
  exact hs.countable
instance countable_spectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  have := countable_ideal F
  have hi : Function.Injective (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) :=
    fun v w h => HeightOneSpectrum.ext h
  exact hi.countable
variable {F} in
instance separable_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    SeparableSpace (v.adicCompletion F) := by
  let h := (HeightOneSpectrum.adicCompletion.equivCompletion F v).toHomeomorphOfIsInducing
    (HeightOneSpectrum.adicCompletion.isUniformInducing_toCompletion F v).isInducing
  have : Countable (WithVal (v.valuation F)) := (WithVal.equiv (v.valuation F)).injective.countable
  exact h.symm.surjective.denseRange.separableSpace h.symm.continuous
variable {F} in
instance secondCountable_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (v.adicCompletion F) :=
  UniformSpace.secondCountable_of_separable _
theorem isOpen_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  Valued.isOpen_integer _
instance secondCountable_finiteAdeleRing : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hS : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), cofinite ≤ 𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := fun S => by
    rw [le_principal_iff]; exact S.finite_toSet.compl_mem_cofinite
  let U : Finset (HeightOneSpectrum (𝓞 F)) → Set (Πʳ v, [R v, A v]) := fun S =>
    Set.range (RestrictedProduct.inclusion R A (hS S))
  have hemb : ∀ S, IsOpenEmbedding (RestrictedProduct.inclusion R A (hS S)) := fun S =>
    RestrictedProduct.isOpenEmbedding_inclusion_principal (isOpen_integers F) (hS S)
  have hsc : ∀ S, SecondCountableTopology (U S) := fun S => by
    have h1 : SecondCountableTopology (Πʳ v, [R v, A v]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)]) :=
      RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
    exact (hemb S).toIsEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have hcov : ⋃ S, U S = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : {v | x v ∉ A v}.Finite := x.eventually
    refine Set.mem_iUnion.2 ⟨hx.toFinset, ?_⟩
    show x ∈ Set.range (RestrictedProduct.inclusion R A (hS hx.toFinset))
    rw [RestrictedProduct.range_inclusion]
    simp only [Set.mem_ofPred_eq, eventually_principal, Set.mem_compl_iff, Finset.mem_coe,
      Set.Finite.mem_toFinset, not_not]
    exact fun v hv => hv
  exact @secondCountableTopology_of_countable_cover _ _ _ _ U hsc (fun S => (hemb S).isOpen_range) hcov
instance secondCountable_adeleRing : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
section HA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F} {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E]
instance secondCountable_tensAF : SecondCountableTopology (AF F ⊗[F] E) := inferInstance
theorem secondCountable_HA_of (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [SecondCountableTopology R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : SecondCountableTopology (HA R σ J) := by
  haveI : SecondCountableTopology (R ⊗[F] E) := inferInstance
  haveI hm : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → R ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin M) (Fin M) (R ⊗[F] E))).symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin M) (R ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  exact (Topology.IsInducing.subtypeVal (t := (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))))).secondCountableTopology
instance secondCountable_HA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    SecondCountableTopology (HA (AF F) σ J) :=
  secondCountable_HA_of (AF F) σ J
end HA
end PI.VolStabSW.TopoAF


