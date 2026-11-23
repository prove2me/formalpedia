-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SmulMemHermR
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SmulMemHermR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:31:00.532922+00:00
-- url     : https://prove2.me/theorems/f1fa88ae-a8d3-4fa4-ae37-19f35a613e64
-- title:
--   Smul Mem Herm R
-- statement:
--   Definitions and structural lemmas for Smul Mem Herm R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SmulMemHermR.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DetAdmA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.OmFibreUniq.W.Sd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.VolStabSW PI.VolStabSW.SdUniqW PI.AdicCompletionValuation
open scoped TensorProduct
section HermMod
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) (a : ℕ)
theorem sigR_algebraMap (c : R) : sigR R σ (algebraMap R (R ⊗[F] E) c) = algebraMap R _ c := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]
theorem smul_mem_HermR (c : R) (S : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (hS : S ∈ HermR R σ a) :
    c • S ∈ HermR R σ a := by
  intro i j
  have h := hS i j
  simp only [Matrix.smul_apply]
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, h, sigR_algebraMap]
instance hermSMul : SMul R (HermR R σ a) :=
  ⟨fun c S => ⟨c • (S : Matrix (Fin a) (Fin a) (R ⊗[F] E)), smul_mem_HermR R σ a c S S.2⟩⟩
instance hermModule : Module R (HermR R σ a) :=
  Function.Injective.module R (HermR R σ a).subtype Subtype.val_injective (fun _ _ => rfl)
instance hermContSMul [TopologicalSpace R] [IsTopologicalRing R] :
    ContinuousSMul R (HermR R σ a) :=
  ⟨by
    apply Continuous.subtype_mk
    exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)⟩
instance hermSC [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
    [FiniteDimensional F E] : SecondCountableTopology (HermR R σ a) := by
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → R ⊗[F] E))
  exact TopologicalSpace.Subtype.secondCountableTopology _
end HermMod
def PsiNT : Prop :=
  ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)),
    IsCharAF F ψ → IsStdChar ψ → NumberField.IsTotallyReal F → ∃ y, psiV F ψ v y ≠ 1
def AbsSd : Prop :=
  ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ψ0 : Fv F v → ℂ),
    Continuous ψ0 → (∀ r s, ψ0 (r + s) = ψ0 r * ψ0 s) → (∀ r, ‖ψ0 r‖ = 1) → (∃ y, ψ0 y ≠ 1) →
    ∀ {V : Type} [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V]
      [IsTopologicalAddGroup V] [ContinuousSMul (Fv F v) V] [T2Space V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (B : V → V → Fv F v),
      (∀ x x' y, B (x + x') y = B x y + B x' y) → (∀ (c : Fv F v) x y, B (c • x) y = c * B x y) →
      (∀ x y, B x y = B y x) → (∀ x, Continuous (B x)) →
      ∀ {ι : Type} [Fintype ι] (β β' : ι → V),
        (∀ x, x = ∑ j, B x (β' j) • β j) → (∀ y, y = ∑ j, B (β j) y • β' j) →
        ∃ μ : Measure V, SelfDual μ (fun x y => ψ0 (B x y))
def BRFacts : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ),
    IsCMExt F E σ → IsHermND σ J →
    (∀ x x' y : TupV (E := E) v n a,
      BR (Fv F v) σ J (x + x') y = BR (Fv F v) σ J x y + BR (Fv F v) σ J x' y) ∧
    (∀ (c : Fv F v) (x y : TupV (E := E) v n a), BR (Fv F v) σ J (c • x) y = c * BR (Fv F v) σ J x y) ∧
    (∀ x y : TupV (E := E) v n a, BR (Fv F v) σ J x y = BR (Fv F v) σ J y x) ∧
    (∀ x : TupV (E := E) v n a, Continuous (BR (Fv F v) σ J x))
def FrameW : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ),
    IsCMExt F E σ → IsHermND σ J →
    ∃ (ι : Type) (_ : Fintype ι) (β β' : ι → TupV (E := E) v n a),
      (∀ x, x = ∑ j, BR (Fv F v) σ J x (β' j) • β j) ∧
      (∀ y, y = ∑ j, BR (Fv F v) σ J (β j) y • β' j)
def HermFacts : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ), IsCMExt F E σ →
    (∀ x x' y : HermR (Fv F v) σ a,
      pairHerm (Fv F v) σ a (x + x') y = pairHerm (Fv F v) σ a x y + pairHerm (Fv F v) σ a x' y) ∧
    (∀ (c : Fv F v) (x y : HermR (Fv F v) σ a),
      pairHerm (Fv F v) σ a (c • x) y = c * pairHerm (Fv F v) σ a x y) ∧
    (∀ x y : HermR (Fv F v) σ a, pairHerm (Fv F v) σ a x y = pairHerm (Fv F v) σ a y x) ∧
    (∀ x : HermR (Fv F v) σ a, Continuous (pairHerm (Fv F v) σ a x))
def FrameH : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ), IsCMExt F E σ →
    ∃ (ι : Type) (_ : Fintype ι) (β β' : ι → HermR (Fv F v) σ a),
      (∀ x, x = ∑ j, pairHerm (Fv F v) σ a x (β' j) • β j) ∧
      (∀ y, y = ∑ j, pairHerm (Fv F v) σ a (β j) y • β' j)
end PI.OmFibreUniq.W.Sd


