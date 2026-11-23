-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:34.773249+00:00
-- url     : https://prove2.me/theorems/c05e4ace-b2f4-48bc-b3af-65ad25ea0f56
-- title:
--   Has Finite Length Of Is Irreducible
-- statement:
--   Definitions and structural lemmas for Has Finite Length Of Is Irreducible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HasFiniteLengthOfIsIrreducible.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Theorems.Thm_GlobalTheory_SmGL_isIrreducible_ofChar
import Theorems.Thm_GlobalTheory_SmGL_isSmoothChar_deltaHalf
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_ofChar_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
namespace GlobalTheory
namespace SmGL
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def IrreducibleAdmissible : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π
def JacquetFiniteLength : Prop :=
  ∀ (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V),
    IsSmooth π → HasFiniteLength π → HasFiniteLength (jac e π)
def InductionFiniteLength : Prop :=
  ∀ (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W),
    IsSmooth ρ → HasFiniteLength ρ → HasFiniteLength (parInd e ρ)
def InductionContragredient : Prop :=
  ∀ (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    [MeasurableSpace (GL n k)] [BorelSpace (GL n k)] (μ : Measure (GL n k)) [μ.IsHaarMeasure]
    (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W),
    IsSmooth ρ → ∃ Φ : (parInd e (contra ρ)).Equiv (contra (parInd e ρ)),
      ∀ (f' : IndSp e (contra ρ)) (f : IndSp e ρ),
        (Φ f' : Module.Dual ℂ (IndSp e ρ)) f =
          ∫ x in (KO k n : Set (GL n k)), (f'.1.1 x : Module.Dual ℂ W) (f.1.1 x) ∂μ
end SmGL
namespace Published
def BernsteinZelevinskyFiniteness : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    IrreducibleAdmissible k ∧ JacquetFiniteLength k ∧ InductionFiniteLength k ∧
      InductionContragredient k
end Published
namespace SmGL
section Transport
variable {F G H V : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
theorem hasFiniteLength_iff_wellFounded (ρ : Representation F G V) :
    HasFiniteLength ρ ↔
      WellFoundedGT (Subrepresentation ρ) ∧ WellFoundedLT (Subrepresentation ρ) := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  rw [HasFiniteLength, isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_iff', isArtinian_iff]
  refine and_congr ⟨fun _ => φ.toOrderEmbedding.wellFoundedGT,
    fun _ => φ.symm.toOrderEmbedding.wellFoundedGT⟩ ⟨fun h => ?_, fun _ => ?_⟩
  · haveI : WellFoundedLT (Submodule (MonoidAlgebra F G) ρ.asModule) := ⟨h⟩
    exact φ.toOrderEmbedding.wellFoundedLT
  · exact φ.symm.toOrderEmbedding.wellFoundedLT.wf
theorem hasFiniteLength_of_isIrreducible {ρ : Representation F G V} (h : ρ.IsIrreducible) :
    HasFiniteLength ρ := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  haveI : Finite (Subrepresentation ρ) := IsSimpleOrder.instFinite
  exact (hasFiniteLength_iff_wellFounded ρ).2 ⟨Finite.to_wellFoundedGT, Finite.to_wellFoundedLT⟩
end Transport
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
section Two
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
end Two
example {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsSmooth (detRep n χ) ∧ (detRep n χ).IsIrreducible ∧ HasFiniteLength (detRep n χ) ∧
      IsAdmissible (detRep n χ) :=
  have h := (isSmooth_ofChar_iff _).2 (hχ.detChar (n := n))
  ⟨h, isIrreducible_ofChar _, hasFiniteLength_of_isIrreducible (isIrreducible_ofChar _), h,
    fun _ _ _ => inferInstance⟩
example : IsSmooth (ofChar (deltaHalf k m)) ∧ HasFiniteLength (ofChar (deltaHalf k m)) :=
  ⟨(isSmooth_ofChar_iff _).2 (isSmoothChar_deltaHalf k),
    hasFiniteLength_of_isIrreducible (isIrreducible_ofChar _)⟩
end SmGL
end GlobalTheory


