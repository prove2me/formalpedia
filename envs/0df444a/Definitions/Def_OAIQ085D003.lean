-- Prove2me | Definitions.Def_OAIQ085D003
-- name    : OAIQ085D003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T15:52:19.017325+00:00
-- url     : https://prove2.me/theorems/98e36631-9e94-4a7a-bb7b-f9b4ef0b5199
-- title:
--   Definitions bundle OAIQ085D003 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 333 declarations of OpenAI's Lean: 199 definitions, 4 inductive types or structures, 8 instances and 122 theorems. The definitions and types are `OAI.DFVSGames.Gadget.Descent.childDomain`, `OAI.DFVSGames.Gadget.Descent.childLift`, `OAI.DFVSGames.Gadget.Descent.childSection`, `OAI.DFVSGames.Gadget.Descent.commonGamma`, `OAI.DFVSGames.Gadget.Descent.leafRank`, `OAI.DFVSGames.Gadget.DetectionBridge.IsFullLift`, `OAI.DFVSGames.Gadget.Enlargement.LinearInjection`, `OAI.DFVSGames.Gadget.Enlargement.enlargedOutput`, `OAI.DFVSGames.Gadget.Enlargement.postcompose`, `OAI.DFVSGames.Gadget.Enlargement.probability`, `OAI.DFVSGames.Gadget.Enlargement.productShift`, `OAI.DFVSGames.Gadget.EnlargementConstruction.Copies`, `OAI.DFVSGames.Gadget.EnlargementConstruction.copiesFintype`, `OAI.DFVSGames.Gadget.EnlargementConstruction.copyObserver`, `OAI.DFVSGames.Gadget.EnlargementConstruction.enlargementCopiesFintype`, `OAI.DFVSGames.Gadget.EnlargementConstruction.productEmbed`, `OAI.DFVSGames.Gadget.EnlargementConstruction.productStage`, `OAI.DFVSGames.Gadget.FreshGenericity.linearEquivFintype`, `OAI.DFVSGames.Gadget.FreshGenericity.linearMapFintype`, `OAI.DFVSGames.Gadget.FreshGenericity.rankSpaceEquiv`, `OAI.DFVSGames.Gadget.FreshGenericity.rankSpaceFintype`, `OAI.DFVSGames.Gadget.FreshGenericity.submoduleFintype`, `OAI.DFVSGames.Gadget.Harmonic.badRankCoefficient`, `OAI.DFVSGames.Gadget.Harmonic.depth`, `OAI.DFVSGames.Gadget.Harmonic.harmonic`, `OAI.DFVSGames.Gadget.Lift`, `OAI.DFVSGames.Gadget.Lift.restrict`, `OAI.DFVSGames.Gadget.NonlinearRecurrence.change`, `OAI.DFVSGames.Gadget.Orientation.RankSpace`, `OAI.DFVSGames.Gadget.Orientation.dualOrientationEquiv`, `OAI.DFVSGames.Gadget.Orientation.orientationEquiv`, `OAI.DFVSGames.Gadget.Parameters.genericityError`, `OAI.DFVSGames.Gadget.Parameters.initialRank`, `OAI.DFVSGames.Gadget.Parameters.rankFor`, `OAI.DFVSGames.Gadget.QuadraticStageNoise.rate`, `OAI.DFVSGames.Gadget.Quotient.Equivariant`, `OAI.DFVSGames.Gadget.Quotient.Space`, `OAI.DFVSGames.Gadget.Quotient.conditionedFiberEquiv`, `OAI.DFVSGames.Gadget.Quotient.conditionedProductEquiv`, `OAI.DFVSGames.Gadget.Quotient.conditionedShiftEquiv` and 163 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DirectedFeedback_Analysis_KMSMomentScalar`, `DirectedFeedback_Encoding_ActualGoodRows`, `DirectedFeedback_Games_ActualAdviceSampling`, `DirectedFeedback_Games_BlockOrientations`, `DirectedFeedback_Games_ChildLifts`, `DirectedFeedback_Games_EqualityFiber`, `DirectedFeedback_Games_Genericity`, `DirectedFeedback_Games_Harmonic`, `DirectedFeedback_Games_KMSAnalyticCodomainTransport`, `DirectedFeedback_Games_KMSAnalyticHybridEnergyFiber`, `DirectedFeedback_Games_KMSAnalyticHybridEnergyImageSplit`, `DirectedFeedback_Games_KMSAnalyticSmallTransport`, `DirectedFeedback_Games_KMSBasisComparisonFibers`, `DirectedFeedback_Games_KMSBasisComparisonPseudorandom`, `DirectedFeedback_Games_KMSBasisComparisonRetention`, `DirectedFeedback_Games_KMSKernelFiberDefs`, `DirectedFeedback_Games_MatrixChartDegreeNeighbors`, `DirectedFeedback_Games_NonlinearRecurrence`, `DirectedFeedback_Probability_DescentProbability`, `DirectedFeedback_Probability_Enlargement`, `DirectedFeedback_Probability_KMSFourthMomentZoomTransport`, `DirectedFeedback_Probability_KMSMomentConstants`, `DirectedFeedback_Probability_PolynomialProbability`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ085D009` and `OAIQ085D010`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ActualGoodRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.RowErasure.SelectionPartition

open scoped BigOperators Classical

noncomputable section

variable {X S : Type*} [Fintype X] [Fintype S]

def event (observe : X → S) (good : S → Prop) (chosen : S → Finset X)
    (x : X) : Prop :=
  good (observe x) ∧ x ∈ chosen (observe x)

end
end DFVSGames.Inverse.RowErasure.SelectionPartition

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ActualAdviceSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Gadget

open scoped BigOperators

section Parent

variable {k I P R X B : Type*} [CommRing k] [Fintype I]
variable [AddCommGroup P] [Module k P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup B] [Module k B]

def aggregate (J : I → B →ₗ[k] X × B) : (I → B) →ₗ[k] X × B where
  toFun v := ∑ i, J i (v i)
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum]

def shiftAggregate (J : I → B →ₗ[k] X × B) (lam : R →ₗ[k] B) :
    (I → R) →ₗ[k] X × B where
  toFun h := aggregate J (fun i => lam (h i))
  map_add' u v := by simp [aggregate, Finset.sum_add_distrib]
  map_smul' c v := by simp [aggregate, Finset.smul_sum]

def parentShifts (J : I → B →ₗ[k] X × B) (lam : R →ₗ[k] B) :
    Submodule k (I → R) :=
  LinearMap.ker ((LinearMap.fst k X B).comp (shiftAggregate J lam))

def parentLogical (J : I → B →ₗ[k] X × B) (lam : R →ₗ[k] B) :
    parentShifts J lam →ₗ[k] B :=
  ((LinearMap.snd k X B).comp (shiftAggregate J lam)).comp
    (parentShifts J lam).subtype

def parentEmbed (J : I → B →ₗ[k] X × B) (lam : R →ₗ[k] B)
    (e : R →ₗ[k] P) : parentShifts J lam →ₗ[k] (I → P) where
  toFun h i := e (h.val i)
  map_add' u v := by ext; simp
  map_smul' c v := by ext; simp

theorem parentEmbed_injective (J : I → B →ₗ[k] X × B) (lam : R →ₗ[k] B)
    (e : R →ₗ[k] P) (he : Function.Injective e) :
    Function.Injective (parentEmbed J lam e) := by
  intro u v huv
  apply Subtype.ext
  funext i
  exact he (congrFun huv i)

theorem shiftAggregate_surjective (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) : Function.Surjective (shiftAggregate J lam) := by
  classical
  intro v
  obtain ⟨u, hu⟩ := hJ v
  choose h hh using fun i => hlam (u i)
  refine ⟨h, ?_⟩
  have heq : (fun i => lam (h i)) = u := funext hh
  change aggregate J (fun i => lam (h i)) = v
  rw [heq, hu]

theorem parentLogical_surjective (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) : Function.Surjective (parentLogical J lam) := by
  intro b
  obtain ⟨h, hh⟩ := shiftAggregate_surjective J hJ lam hlam (0, b)
  have hm : h ∈ parentShifts J lam := by
    change (shiftAggregate J lam h).1 = 0
    rw [hh]
  refine ⟨⟨h, hm⟩, ?_⟩
  change (shiftAggregate J lam h).2 = b
  rw [hh]

def parentOutput (J : I → B →ₗ[k] X × B) (C : P → B) (Q : X → B)
    (u : I → P) : B :=
  let v := aggregate J (fun i => C (u i))
  v.2 + Q v.1

theorem aggregate_output_shift (J : I → B →ₗ[k] X × B)
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h)
    (u : I → P) (h : I → R) :
    aggregate J (fun i => C (u i + e (h i))) =
      aggregate J (fun i => C (u i)) + shiftAggregate J lam h := by
  simp only [hC]
  change aggregate J ((fun i => C (u i)) + (fun i => lam (h i))) = _
  exact (aggregate J).map_add _ _

theorem parentOutput_equivariant (J : I → B →ₗ[k] X × B)
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (C : P → B) (Q : X → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h)
    (u : I → P) (h : parentShifts J lam) :
    parentOutput J C Q (u + parentEmbed J lam e h) =
      parentOutput J C Q u + parentLogical J lam h := by
  have hzero : (shiftAggregate J lam h.val).1 = 0 := h.property
  unfold parentOutput
  change (aggregate J (fun i => C (u i + e (h.val i)))).2 +
    Q (aggregate J (fun i => C (u i + e (h.val i)))).1 = _
  rw [aggregate_output_shift J e lam C hC]
  simp only [Prod.fst_add, Prod.snd_add, hzero, add_zero]
  change _ = _ + (shiftAggregate J lam h.val).2
  abel

end Parent

end DFVSGames.Gadget

namespace DFVSGames.Gadget

universe u v

structure Stage (k : Type u) (B : Type v) [CommRing k]
    [AddCommGroup B] [Module k B] where
  Input : Type v
  Shift : Type v
  Noise : Type v
  [inputAdd : AddCommGroup Input]
  [inputModule : Module k Input]
  [shiftAdd : AddCommGroup Shift]
  [shiftModule : Module k Shift]
  [inputFinite : Finite Input]
  [shiftFinite : Finite Shift]
  [noiseFinite : Finite Noise]
  [noiseNonempty : Nonempty Noise]
  embed : Shift →ₗ[k] Input
  embed_injective : Function.Injective embed
  logical : Shift →ₗ[k] B
  logical_surjective : Function.Surjective logical
  output : Input → B
  equivariant : ∀ u h, output (u + embed h) = output u + logical h
  noise : Noise → Input

attribute [instance] Stage.inputAdd Stage.inputModule Stage.shiftAdd Stage.shiftModule
  Stage.inputFinite Stage.shiftFinite Stage.noiseFinite Stage.noiseNonempty

namespace Stage

variable {k : Type u} {B : Type v} [CommRing k]
variable [AddCommGroup B] [Module k B] [Finite B]

def base : Stage k B where
  Input := B
  Shift := B
  Noise := B
  embed := LinearMap.id
  embed_injective := Function.injective_id
  logical := LinearMap.id
  logical_surjective := Function.surjective_id
  output := id
  equivariant := by intros; rfl
  noise := id

variable {I X : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

noncomputable def next (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B)
    (s : Stage k B) : Stage k B where
  Input := I → s.Input
  Shift := parentShifts J s.logical
  Noise := I × s.Noise
  embed := parentEmbed J s.logical s.embed
  embed_injective := parentEmbed_injective J s.logical s.embed s.embed_injective
  logical := parentLogical J s.logical
  logical_surjective := parentLogical_surjective J hJ s.logical s.logical_surjective
  output := parentOutput J s.output Q
  equivariant := parentOutput_equivariant J s.embed s.logical s.output Q s.equivariant
  noise := fun t => Pi.single t.1 (s.noise t.2)

noncomputable def iterate (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) : ℕ → Stage k B
  | 0 => base
  | n + 1 => next J hJ Q (iterate J hJ Q n)

@[simp] theorem iterate_zero (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) :
    iterate J hJ Q 0 = base := rfl

@[simp] theorem iterate_succ (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) (n : ℕ) :
    iterate J hJ Q (n + 1) = next J hJ Q (iterate J hJ Q n) := rfl

end Stage

end DFVSGames.Gadget

namespace DFVSGames.Gadget

variable {k S T X B : Type*} [Field k]
variable [AddCommGroup S] [Module k S]
variable [AddCommGroup T] [Module k T]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup B] [Module k B]

theorem family_factors_of_ker
    (f : T →ₗ[k] X) (hf : Function.Surjective f)
    (ψ : S →ₗ[k] (T →ₗ[k] k))
    (hker : ∀ z t, f t = 0 → ψ z t = 0) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k), ∀ z t, ψ z t = γ z (f t) := by
  obtain ⟨σ, hσ⟩ := f.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hf)
  have hσ_apply (x : X) : f (σ x) = x := congrArg (fun g : X →ₗ[k] X => g x) hσ
  let γ : S →ₗ[k] (X →ₗ[k] k) :=
    { toFun := fun z => (ψ z).comp σ
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  refine ⟨γ, fun z t => ?_⟩
  have hz := hker z (t - σ (f t)) (by rw [map_sub, hσ_apply, sub_self])
  have heq : ψ z t - ψ z (σ (f t)) = 0 := by simpa only [map_sub] using hz
  exact sub_eq_zero.mp heq

theorem common_parent_factorization
    (a : T →ₗ[k] X) (b : T →ₗ[k] B) (ha : Function.Surjective a)
    (ψ : S →ₗ[k] (T →ₗ[k] k)) (ζ : S →ₗ[k] (B →ₗ[k] k))
    (hlift : ∀ z t, a t = 0 → ψ z t = ζ z (b t)) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k),
      ∀ z t, ψ z t = γ z (a t) + ζ z (b t) := by
  let η : S →ₗ[k] (T →ₗ[k] k) :=
    { toFun := fun z => ψ z - (ζ z).comp b
      map_add' := by intros; ext; simp; abel
      map_smul' := by intros; ext; simp [smul_sub] }
  obtain ⟨γ, hγ⟩ := family_factors_of_ker a ha η (by
    intro z t ht
    change ψ z t - ζ z (b t) = 0
    rw [hlift z t ht, sub_self])
  refine ⟨γ, fun z t => ?_⟩
  have h := hγ z t
  change ψ z t - ζ z (b t) = γ z (a t) at h
  exact (sub_eq_iff_eq_add).mp h

theorem aggregate_fst_surjective (A : T →ₗ[k] X × B)
    (hA : Function.Surjective A) :
    Function.Surjective ((LinearMap.fst k X B).comp A) := by
  intro x
  obtain ⟨t, ht⟩ := hA (x, 0)
  exact ⟨t, congrArg Prod.fst ht⟩

end DFVSGames.Gadget

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ChildLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Gadget

open scoped BigOperators

variable {k I P R X B S : Type*} [Field k] [Fintype I] [DecidableEq I]
variable [AddCommGroup P] [Module k P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup B] [Module k B]
variable [AddCommGroup S] [Module k S]

def tupleEmbed (e : R →ₗ[k] P) : (I → R) →ₗ[k] (I → P) where
  toFun h i := e (h i)
  map_add' u v := by ext; simp
  map_smul' c v := by ext; simp

omit [Fintype I] in
theorem tupleEmbed_single (e : R →ₗ[k] P) (i : I) (h : R) :
    tupleEmbed e (Pi.single i h) = Pi.single i (e h) := by
  ext j
  by_cases hij : i = j
  · subst j; simp [tupleEmbed]
  · simp [tupleEmbed, hij]

theorem shiftAggregate_single (J : I → B →ₗ[k] X × B)
    (lam : R →ₗ[k] B) (i : I) (h : R) :
    shiftAggregate J lam (Pi.single i h) = J i (lam h) := by
  classical
  simp [shiftAggregate, aggregate, Pi.single_apply, apply_ite, map_zero]

theorem parent_lift_common_child
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (hlam : Function.Surjective lam)
    (ψ : S →ₗ[k] ((I → P) →ₗ[k] k)) (ζ : S →ₗ[k] (B →ₗ[k] k))
    (hlift : ∀ z (h : parentShifts J lam),
      ψ z (parentEmbed J lam e h) = ζ z (parentLogical J lam h)) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k), ∀ i z h,
      ψ z (Pi.single i (e h)) =
        γ z (J i (lam h)).1 + ζ z (J i (lam h)).2 := by
  let a := (LinearMap.fst k X B).comp (shiftAggregate J lam)
  let b := (LinearMap.snd k X B).comp (shiftAggregate J lam)
  let Ψ : S →ₗ[k] ((I → R) →ₗ[k] k) :=
    { toFun := fun z => (ψ z).comp (tupleEmbed e)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have ha : Function.Surjective a :=
    aggregate_fst_surjective _ (shiftAggregate_surjective J hJ lam hlam)
  obtain ⟨γ, hγ⟩ := common_parent_factorization a b ha Ψ ζ (by
    intro z h hh
    exact hlift z ⟨h, hh⟩)
  refine ⟨γ, fun i z h => ?_⟩
  have heq := hγ z (Pi.single i h)
  change ψ z (tupleEmbed e (Pi.single i h)) =
    γ z (shiftAggregate J lam (Pi.single i h)).1 +
      ζ z (shiftAggregate J lam (Pi.single i h)).2 at heq
  simpa only [tupleEmbed_single, shiftAggregate_single] using heq

end DFVSGames.Gadget

namespace DFVSGames.Gadget

universe u v

variable {k : Type u} {B : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B]

structure Lift (s : Stage k B) (S : Submodule k (B →ₗ[k] k)) where
  family : S →ₗ[k] (s.Input →ₗ[k] k)
  agrees : ∀ z h, family z (s.embed h) = z.val (s.logical h)

def Lift.restrict {s : Stage k B} {S T : Submodule k (B →ₗ[k] k)}
    (L : Lift s T) (hST : S ≤ T) : Lift s S where
  family := L.family.comp (Submodule.inclusion hST)
  agrees := by intro z h; exact L.agrees _ h

variable {I X : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

def singleInput (i : I) (P : Type v) [AddCommGroup P] [Module k P] :
    P →ₗ[k] (I → P) where
  toFun p := Pi.single i p
  map_add' a b := by ext j; by_cases h : i = j <;> simp [h]
  map_smul' c p := by ext j; by_cases h : i = j <;> simp [h]

def childCharacter (J : I → B →ₗ[k] X × B)
    {S : Submodule k (B →ₗ[k] k)} (γ : S →ₗ[k] (X →ₗ[k] k)) (i : I) :
    S →ₗ[k] (B →ₗ[k] k) where
  toFun z := (γ z).comp ((LinearMap.fst k X B).comp (J i)) +
    z.val.comp ((LinearMap.snd k X B).comp (J i))
  map_add' a b := by ext; simp; abel
  map_smul' c z := by ext; simp [smul_add]

omit [Finite B] in
theorem exists_common_child_character
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (Q : X → B) (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k), ∀ i z h,
      L.family z (Pi.single i (s.embed h)) = childCharacter J γ i z (s.logical h) := by
  have hlift : ∀ z (h : parentShifts J s.logical),
      L.family z (parentEmbed J s.logical s.embed h) =
        z.val (parentLogical J s.logical h) := by
    intro z h
    exact L.agrees z h
  have hcommon := parent_lift_common_child (S := S) J hJ s.embed s.logical
    s.logical_surjective
  obtain ⟨γ, hγ⟩ := hcommon L.family S.subtype hlift
  exact ⟨γ, fun i z h => hγ i z h⟩

def descendantFamily {s : Stage k B} {S : Submodule k (B →ₗ[k] k)}
    (ψ : S →ₗ[k] ((I → s.Input) →ₗ[k] k)) (i : I)
    (φ : S →ₗ[k] (B →ₗ[k] k))
    (sectionMap : LinearMap.range φ →ₗ[k] S) :
    LinearMap.range φ →ₗ[k] (s.Input →ₗ[k] k) where
  toFun z := (ψ (sectionMap z)).comp (singleInput i s.Input)
  map_add' a b := by ext; simp
  map_smul' c z := by ext; simp

omit [Finite B] in

theorem exists_descendant_lift
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (Q : X → B) (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S)
    (γ : S →ₗ[k] (X →ₗ[k] k))
    (hγ : ∀ i z h, L.family z (Pi.single i (s.embed h)) =
      childCharacter J γ i z (s.logical h)) (i : I) :
    ∃ (L' : Lift s (LinearMap.range (childCharacter J γ i)))
      (sectionMap : LinearMap.range (childCharacter J γ i) →ₗ[k] S),
      (∀ z, childCharacter J γ i (sectionMap z) = z.val) ∧
      (∀ z p, L'.family z p = L.family (sectionMap z) (Pi.single i p)) := by
  let φ : S →ₗ[k] (B →ₗ[k] k) := childCharacter J γ i
  let : Module.Free k (LinearMap.range φ) :=
    Module.Free.of_divisionRing k (LinearMap.range φ)
  let : Module.Projective k (LinearMap.range φ) := Module.Projective.of_free
  obtain ⟨σ, hσ⟩ := φ.rangeRestrict.exists_rightInverse_of_surjective
    φ.range_rangeRestrict
  have hσ' (z : LinearMap.range φ) : φ (σ z) = z.val :=
    congrArg Subtype.val (congrArg (fun f => f z) hσ)
  let L' : Lift s (LinearMap.range φ) :=
    { family := descendantFamily L.family i φ σ
      agrees := by
        intro z h
        change L.family (σ z) (Pi.single i (s.embed h)) = z.val (s.logical h)
        rw [hγ, hσ'] }
  exact ⟨L', σ, hσ', fun z p => rfl⟩

end DFVSGames.Gadget

noncomputable section

open scoped BigOperators
open Module

namespace DFVSGames.Gadget.Orientation

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]

def RankSpace (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (r : ℕ) :=
  {E : Submodule K V // finrank K E = r}

instance rankSpaceAction (r : ℕ) : MulAction (V ≃ₗ[K] V) (RankSpace K V r) where
  smul a E := ⟨E.val.map a.toLinearMap, (a.finrank_map_eq E.val).trans E.property⟩
  one_smul E := by
    apply Subtype.ext
    exact E.val.map_id
  mul_smul a b E := by
    apply Subtype.ext
    exact E.val.map_comp b.toLinearMap a.toLinearMap

variable {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U]

def orientationEquiv (J₀ : B ≃ₗ[K] U) : (B ≃ₗ[K] U) ≃ (U ≃ₗ[K] U) where
  toFun J := J₀.symm.trans J
  invFun a := J₀.trans a
  left_inv J := by ext x; simp
  right_inv a := by ext x; simp

def dualOrientationEquiv [FiniteDimensional K B] [FiniteDimensional K U] :
    (B ≃ₗ[K] U) ≃ (Module.Dual K U ≃ₗ[K] Module.Dual K B) where
  toFun J := J.dualMap
  invFun e := ((Module.evalEquiv K B).trans e.dualMap).trans (Module.evalEquiv K U).symm
  left_inv J := by
    ext b
    apply (Module.evalEquiv K U).injective
    ext φ
    simp
  right_inv e := by
    ext φ b
    simp

end DFVSGames.Gadget.Orientation
end

noncomputable section

open scoped BigOperators

namespace DFVSGames.Gadget.OrientationVectors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem equiv_apply_ne_zero {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] (J : B ≃ₗ[K] U) {b : B} (hb : b ≠ 0) :
    J b ≠ 0 := by
  intro h
  apply hb
  exact J.injective (h.trans (map_zero J).symm)

instance nonzeroAction : MulAction (V ≃ₗ[K] V) {x : V // x ≠ 0} where
  smul a x := ⟨a x.val, equiv_apply_ne_zero a x.property⟩
  one_smul x := by apply Subtype.ext; rfl
  mul_smul a b x := by apply Subtype.ext; rfl

end DFVSGames.Gadget.OrientationVectors
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_BlockOrientations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem squareMap_injective : Function.Injective (fun x : F => x ^ 2) := by
  intro x y h
  change x ^ 2 = y ^ 2 at h
  have hs : (x + y) ^ 2 = 0 := by
    rw [CharTwo.add_sq, h, CharTwo.add_self_eq_zero]
  have hz : x + y = 0 := (sq_eq_zero_iff).mp hs
  exact (add_eq_zero_iff_eq_neg.mp hz).trans (CharTwo.neg_eq y)

noncomputable def squareRoot (c : F) : F :=
  Classical.choose (Finite.surjective_of_injective squareMap_injective c)

@[simp] theorem squareRoot_sq (c : F) : squareRoot c ^ 2 = c :=
  Classical.choose_spec (Finite.surjective_of_injective squareMap_injective c)

@[simp] theorem squareRoot_of_sq (c : F) : squareRoot (c ^ 2) = c := by
  apply squareMap_injective
  exact squareRoot_sq _

end DFVSGames.Quadratic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Genericity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Quadratic

open Module
open scoped BigOperators

noncomputable section

section AlignmentEvents

variable {R F V ι n : Type*}
variable [Field R] [Field F] [Algebra R F]
variable [AddCommGroup V] [Module R V]
variable [Fintype V] [Fintype ι] [Fintype n]

def alignmentEvent (z : V → n → F) (g : V →ₗ[R] (n → F)) (c : V → F) :
    Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ≠ 0 ∧ (∑ i, z v i * g v i) = c v)

end AlignmentEvents

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

def alignmentRightHandSide (z : Fin 3 → F) : F := squareRoot (z 0 * z 1 * z 2)

def IsGeneric (S : Submodule (ZMod 2) (Fin 3 → F)) : Prop := by
  classical
  exact
    (∀ z w : S, z ≠ 0 → w ≠ 0 →
      (∃ t : F, (z : Fin 3 → F) = t • (w : Fin 3 → F)) → z = w) ∧
    (∀ g : S →ₗ[ZMod 2] (Fin 3 → F),
      (alignmentEvent (R := ZMod 2) (fun z : S => (z : Fin 3 → F)) g
        (fun z : S => alignmentRightHandSide (z : Fin 3 → F))).card ≤
          3 * Module.finrank (ZMod 2) S)

end

end DFVSGames.Quadratic

namespace DFVSGames.Gadget.Descent

universe u v

variable {k : Type u} {B I X : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B] [FiniteDimensional k B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

variable (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B)

noncomputable def commonGamma (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) : S →ₗ[k] (X →ₗ[k] k) :=
  Classical.choose (exists_common_child_character J hJ Q s S L)

omit [FiniteDimensional k B] in
omit [Finite B] in
theorem commonGamma_spec (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) (z : S) (h : s.Shift) :
    L.family z (Pi.single i (s.embed h)) =
      childCharacter J (commonGamma J hJ Q s S L) i z (s.logical h) :=
  Classical.choose_spec (exists_common_child_character J hJ Q s S L) i z h

noncomputable def childDomain (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) : Submodule k (B →ₗ[k] k) :=
  LinearMap.range (childCharacter J (commonGamma J hJ Q s S L) i)

noncomputable def childLift (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) :
    Lift s (childDomain J hJ Q s S L i) :=
  Classical.choose (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i)

noncomputable def childSection (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) :
    childDomain J hJ Q s S L i →ₗ[k] S :=
  Classical.choose (Classical.choose_spec (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i))

noncomputable def leafRank
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B) :
    (n : ℕ) → (S : Submodule k (B →ₗ[k] k)) →
    Lift (Stage.iterate J hJ Q n) S → (Stage.iterate J hJ Q n).Noise → ℕ
  | 0, S, _, _ => Module.finrank k S
  | n + 1, S, L, t => leafRank J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L t.1)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L t.1) t.2

end DFVSGames.Gadget.Descent

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Harmonic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Gadget.Harmonic

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

def harmonic : ℕ → ℚ
  | 0 => 0
  | r + 1 => harmonic r + (↑(r + 1))⁻¹

@[simp] theorem harmonic_zero : harmonic 0 = 0 := rfl

@[simp] theorem harmonic_succ (r : ℕ) :
    harmonic (r + 1) = harmonic r + (↑(r + 1))⁻¹ := rfl

def badRankCoefficient (r₀ : ℕ) : ℚ := harmonic r₀ * 2 ^ r₀

def depth (r₀ : ℕ) (θ : ℚ) : ℕ := ⌊harmonic r₀ / (8 * θ)⌋₊

end DFVSGames.Gadget.Harmonic

noncomputable section

open scoped BigOperators Classical
open Module

namespace DFVSGames.Gadget.FreshGenericity

open _root_.OAI.DFVSGames.Gadget.Orientation Quadratic

section RankTransport

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

def rankSpaceEquiv (e : V ≃ₗ[K] W) (r : ℕ) : RankSpace K V r ≃ RankSpace K W r :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (fun S => by
    change finrank K S = r ↔ finrank K (S.map e.toLinearMap) = r
    rw [e.finrank_map_eq])

@[simp] theorem rankSpaceEquiv_apply (e : V ≃ₗ[K] W) (r : ℕ)
    (S : RankSpace K V r) :
    (rankSpaceEquiv e r S).val = S.val.map e.toLinearMap := rfl

local instance linearMapFintype [Fintype V] [Fintype W] : Fintype (V →ₗ[K] W) :=
  Fintype.ofInjective (fun f : V →ₗ[K] W => (f : V → W)) DFunLike.coe_injective

local instance linearEquivFintype [Fintype V] [Fintype W] : Fintype (V ≃ₗ[K] W) :=
  Fintype.ofInjective (fun e : V ≃ₗ[K] W => (e : V → W)) DFunLike.coe_injective

local instance submoduleFintype [Fintype V] : Fintype (Submodule K V) :=
  Fintype.ofInjective (fun S : Submodule K V => (S : Set V)) SetLike.coe_injective

local instance rankSpaceFintype [Fintype V] (r : ℕ) : Fintype (RankSpace K V r) :=
  inferInstanceAs (Fintype {S : Submodule K V // finrank K S = r})

end RankTransport

attribute [local instance] linearMapFintype linearEquivFintype submoduleFintype rankSpaceFintype

end DFVSGames.Gadget.FreshGenericity
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_DescentProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Gadget.DescentProbability

open Harmonic Descent

universe u v

variable {k : Type u} {B I X : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B] [FiniteDimensional k B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

variable (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B)

noncomputable instance noiseFintype (n : ℕ) : Fintype (Stage.iterate J hJ Q n).Noise := by
  induction n with
  | zero => exact Fintype.ofFinite B
  | succ n ih =>
    exact inferInstanceAs (Fintype (I × (Stage.iterate J hJ Q n).Noise))

end DFVSGames.Gadget.DescentProbability

namespace DFVSGames.Gadget.Quotient

variable {𝕜 P B : Type*} [Ring 𝕜]
variable [AddCommGroup P] [Module 𝕜 P] [AddCommGroup B] [Module 𝕜 B]

def shiftKernel (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) : Submodule 𝕜 P :=
  (LinearMap.ker lam).map R.subtype

abbrev Space (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) := P ⧸ shiftKernel R lam

def projection (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) :
    P →ₗ[𝕜] Space R lam := (shiftKernel R lam).mkQ

theorem projection_surjective (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) :
    Function.Surjective (projection R lam) := (shiftKernel R lam).mkQ_surjective

theorem mem_shiftKernel (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (x : P) :
    x ∈ shiftKernel R lam ↔ ∃ h : R, lam h = 0 ∧ (h : P) = x := Iff.rfl

theorem projection_eq_zero (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (h : R) :
    projection R lam (h : P) = 0 ↔ lam h = 0 := by
  change (Submodule.Quotient.mk (h : P) : Space R lam) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, mem_shiftKernel]
  constructor
  · rintro ⟨k, hk, hkh⟩
    have : k = h := Subtype.ext hkh
    simpa [this] using hk
  · intro hh
    exact ⟨h, hh, rfl⟩

def quotientShift (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) :
    (R ⧸ LinearMap.ker lam) →ₗ[𝕜] Space R lam :=
  (LinearMap.ker lam).liftQ ((projection R lam).comp R.subtype) (by
    intro h hh
    exact (projection_eq_zero R lam h).mpr hh)

@[simp] theorem quotientShift_mk (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (h : R) :
    quotientShift R lam (Submodule.Quotient.mk h) = projection R lam (h : P) := rfl

noncomputable def logicalShift (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) : B →ₗ[𝕜] Space R lam :=
  (quotientShift R lam).comp (lam.quotKerEquivOfSurjective hlam).symm.toLinearMap

@[simp] theorem logicalShift_lambda (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (h : R) :
    logicalShift R lam hlam (lam h) = projection R lam (h : P) := by
  simp [logicalShift, LinearMap.quotKerEquivOfSurjective_symm_apply]

theorem logicalShift_injective (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) : Function.Injective (logicalShift R lam hlam) := by
  intro a b hab
  obtain ⟨h, rfl⟩ := hlam a
  obtain ⟨k, rfl⟩ := hlam b
  rw [logicalShift_lambda, logicalShift_lambda] at hab
  have hz : projection R lam ((h - k : R) : P) = 0 := by
    change projection R lam ((h : P) - (k : P)) = 0
    rw [map_sub, hab, sub_self]
  have := (projection_eq_zero R lam (h - k)).mp hz
  exact sub_eq_zero.mp (by simpa only [map_sub] using this)

def Equivariant (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (C : P → B) : Prop :=
  ∀ (u : P) (h : R), C (u + (h : P)) = C u + lam h

def conditionedShiftEquiv (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (D : P → Prop)
    (hD : ∀ (u : P) (h : R), D (u + (h : P)) ↔ D u) (b : B) (h : R) :
    {u : P // C u = b ∧ D u} ≃ {u : P // C u = b + lam h ∧ D u} where
  toFun u := ⟨u.val + (h : P), by
    exact ⟨(hC u.val h).trans (congrArg (fun x => x + lam h) u.property.1),
      (hD u.val h).mpr u.property.2⟩⟩
  invFun u := ⟨u.val + ((-h : R) : P), by
    constructor
    · rw [hC u.val (-h), u.property.1, map_neg, add_neg_cancel_right]
    · exact (hD u.val (-h)).mpr u.property.2⟩
  left_inv u := Subtype.ext (by simp)
  right_inv u := Subtype.ext (by simp)

noncomputable def conditionedFiberEquiv (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (D : P → Prop) (hD : ∀ (u : P) (h : R), D (u + (h : P)) ↔ D u)
    (b c : B) : {u : P // C u = b ∧ D u} ≃ {u : P // C u = c ∧ D u} := by
  classical
  let h : R := Classical.choose (hlam (c - b))
  have hh : lam h = c - b := Classical.choose_spec (hlam (c - b))
  have he : b + lam h = c := by rw [hh, add_comm, sub_add_cancel]
  simpa only [he] using conditionedShiftEquiv R lam C hC D hD b h

def conditionedSigmaEquiv (C : P → B) (D : P → Prop) :
    {u : P // D u} ≃ Σ b : B, {u : P // C u = b ∧ D u} where
  toFun u := ⟨C u.val, ⟨u.val, rfl, u.property⟩⟩
  invFun u := ⟨u.2.val, u.2.property.2⟩
  left_inv _ := rfl
  right_inv := by rintro ⟨b, u, hu, hD⟩; cases hu; rfl

noncomputable def conditionedProductEquiv (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (D : P → Prop) (hD : ∀ (u : P) (h : R), D (u + (h : P)) ↔ D u) (b : B) :
    {u : P // D u} ≃ B × {u : P // C u = b ∧ D u} :=
  ((conditionedSigmaEquiv C D).trans
    (Equiv.sigmaCongrRight (fun c => conditionedFiberEquiv R lam hlam C hC D hD c b))).trans
    (Equiv.sigmaEquivProd _ _)

@[simp] theorem conditionedProductEquiv_fst (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (D : P → Prop) (hD : ∀ (u : P) (h : R), D (u + (h : P)) ↔ D u) (b : B)
    (u : {u : P // D u}) :
    (conditionedProductEquiv R lam hlam C hC D hD b u).1 = C u.val := rfl

theorem output_constant_on_fibers (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (x y : P)
    (hxy : projection R lam x = projection R lam y) : C x = C y := by
  have hm : x - y ∈ shiftKernel R lam := (Submodule.Quotient.eq _).mp hxy
  obtain ⟨h, hh, hval⟩ := (mem_shiftKernel R lam _).mp hm
  have he : y + (h : P) = x := by rw [hval, add_comm, sub_add_cancel]
  simpa only [he, hh, add_zero] using hC y h

def output (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) : Space R lam → B :=
  _root_.Quotient.lift C (fun _ _ h =>
    output_constant_on_fibers R lam C hC _ _ (_root_.Quotient.sound h))

@[simp] theorem output_projection (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (u : P) :
    output R lam C hC (projection R lam u) = C u := rfl

theorem output_equivariant (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (x : Space R lam) (b : B) :
    output R lam C hC (x + logicalShift R lam hlam b) = output R lam C hC x + b := by
  obtain ⟨u, rfl⟩ := projection_surjective R lam x
  obtain ⟨h, rfl⟩ := hlam b
  rw [logicalShift_lambda, ← map_add, output_projection, output_projection]
  exact hC u h

def fiberMap (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (a : P) :
    shiftKernel R lam → {u : P // projection R lam u = projection R lam a} :=
  fun h => ⟨a + (h : P), by
    have hh : projection R lam (h : P) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr h.property
    rw [map_add, hh, add_zero]⟩

end DFVSGames.Gadget.Quotient

namespace DFVSGames.Gadget.StageQuotient

universe u v

variable {k : Type u} {B : Type v} [CommRing k]
variable [AddCommGroup B] [Module k B]

def shifts (s : Stage k B) : Submodule k s.Input := LinearMap.range s.embed

noncomputable def shiftEquiv (s : Stage k B) : s.Shift ≃ₗ[k] shifts s :=
  LinearEquiv.ofInjective s.embed s.embed_injective

@[simp] theorem shiftEquiv_coe (s : Stage k B) (h : s.Shift) :
    ((shiftEquiv s h : shifts s) : s.Input) = s.embed h := rfl

@[simp] theorem embed_shiftEquiv_symm (s : Stage k B) (h : shifts s) :
    s.embed ((shiftEquiv s).symm h) = (h : s.Input) :=
  LinearEquiv.ofInjective_symm_apply s.embed h

noncomputable def logical (s : Stage k B) : shifts s →ₗ[k] B :=
  s.logical.comp (shiftEquiv s).symm.toLinearMap

@[simp] theorem logical_shiftEquiv (s : Stage k B) (h : s.Shift) :
    logical s (shiftEquiv s h) = s.logical h := by
  simp [logical]

theorem logical_surjective (s : Stage k B) : Function.Surjective (logical s) := by
  intro b
  obtain ⟨h, hh⟩ := s.logical_surjective b
  exact ⟨shiftEquiv s h, (logical_shiftEquiv s h).trans hh⟩

theorem equivariant (s : Stage k B) :
    Quotient.Equivariant (shifts s) (logical s) s.output := by
  intro u h
  have he := s.equivariant u ((shiftEquiv s).symm h)
  simpa only [embed_shiftEquiv_symm, logical, LinearMap.comp_apply,
    LinearEquiv.coe_coe] using he

abbrev Space (s : Stage k B) := Quotient.Space (shifts s) (logical s)

noncomputable def projection (s : Stage k B) : s.Input →ₗ[k] Space s :=
  Quotient.projection (shifts s) (logical s)

theorem projection_surjective (s : Stage k B) : Function.Surjective (projection s) :=
  Quotient.projection_surjective (shifts s) (logical s)

instance spaceFinite (s : Stage k B) : Finite (Space s) :=
  Finite.of_surjective (projection s) (projection_surjective s)

noncomputable def shift (s : Stage k B) : B →ₗ[k] Space s :=
  Quotient.logicalShift (shifts s) (logical s) (logical_surjective s)

theorem shift_injective (s : Stage k B) : Function.Injective (shift s) :=
  Quotient.logicalShift_injective (shifts s) (logical s) (logical_surjective s)

@[simp] theorem shift_logical (s : Stage k B) (h : s.Shift) :
    shift s (s.logical h) = projection s (s.embed h) := by
  rw [← logical_shiftEquiv s h]
  exact Quotient.logicalShift_lambda (shifts s) (logical s) (logical_surjective s)
    (shiftEquiv s h)

noncomputable def output (s : Stage k B) : Space s → B :=
  Quotient.output (shifts s) (logical s) s.output (equivariant s)

@[simp] theorem output_projection (s : Stage k B) (u : s.Input) :
    output s (projection s u) = s.output u := rfl

theorem output_equivariant (s : Stage k B) (x : Space s) (b : B) :
    output s (x + shift s b) = output s x + b :=
  Quotient.output_equivariant (shifts s) (logical s) (logical_surjective s)
    s.output (equivariant s) x b

noncomputable def noise (s : Stage k B) : s.Noise → Space s :=
  fun t => projection s (s.noise t)

noncomputable def toStage [Finite B] (s : Stage k B) : Stage k B where
  Input := Space s
  Shift := B
  Noise := s.Noise
  embed := shift s
  embed_injective := shift_injective s
  logical := LinearMap.id
  logical_surjective := Function.surjective_id
  output := output s
  equivariant := output_equivariant s
  noise := noise s

end DFVSGames.Gadget.StageQuotient

namespace DFVSGames.Gadget.DetectionBridge

open Harmonic

variable {K B V E Ω : Type*} [Field K]
variable [AddCommGroup B] [Module K B] [AddCommGroup V] [Module K V]
variable [AddCommGroup E] [Module K E] [Fintype Ω]

def IsFullLift (ι : B →ₗ[K] V)
    (ψ : Module.Dual K B →ₗ[K] Module.Dual K V) : Prop :=
  ∀ (z : Module.Dual K B) (b : B), ψ z (ι b) = z b

end DFVSGames.Gadget.DetectionBridge

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_Enlargement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Gadget.Enlargement

open scoped BigOperators Classical

noncomputable section

def probability {Ω : Type*} [Fintype Ω] (p : Ω → Prop) : ℚ :=
  (Nat.card {x : Ω // p x} : ℚ) / (Nat.card Ω : ℚ)

theorem exists_equiv_map_nonzero {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ e : V ≃ₗ[F] V, e x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton F V x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton F V y hy
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨e, ?_⟩
  have h := (he (ex 1)).symm
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h

abbrev LinearInjection (F B K : Type*) [Field F] [AddCommGroup B]
    [Module F B] [AddCommGroup K] [Module F K] :=
  {L : B →ₗ[F] K // Function.Injective L}

theorem linearInjection_nonempty_of_finrank_le {F B K : Type*} [Field F]
    [AddCommGroup B] [Module F B] [FiniteDimensional F B]
    [AddCommGroup K] [Module F K] [FiniteDimensional F K]
    (h : Module.finrank F B ≤ Module.finrank F K) :
    Nonempty (LinearInjection F B K) := by
  obtain ⟨L, hL⟩ := finrank_le_iff_exists_linearMap.mp h
  exact ⟨⟨L, hL⟩⟩

def postcompose {F B K : Type*} [Field F] [AddCommGroup B] [Module F B]
    [AddCommGroup K] [Module F K] (e : K ≃ₗ[F] K) :
    LinearInjection F B K ≃ LinearInjection F B K where
  toFun L := ⟨e.toLinearMap.comp L.1, e.injective.comp L.2⟩
  invFun L := ⟨e.symm.toLinearMap.comp L.1, e.symm.injective.comp L.2⟩
  left_inv L := by
    apply Subtype.ext
    ext x
    exact e.symm_apply_apply (L.1 x)
  right_inv L := by
    apply Subtype.ext
    ext x
    exact e.apply_symm_apply (L.1 x)

theorem injection_eval_ne_zero {F B K : Type*} [Field F] [AddCommGroup B]
    [Module F B] [AddCommGroup K] [Module F K]
    (L : LinearInjection F B K) {b : B} (hb : b ≠ 0) : L.1 b ≠ 0 := by
  intro h
  apply hb
  apply L.2
  simpa using h

theorem exists_injection_hitting_nonzero {F B K : Type*} [Field F]
    [AddCommGroup B] [Module F B] [FiniteDimensional F B]
    [AddCommGroup K] [Module F K] [FiniteDimensional F K]
    (h : Module.finrank F B ≤ Module.finrank F K)
    (b : B) (hb : b ≠ 0) (x : K) (hx : x ≠ 0) :
    ∃ L : LinearInjection F B K, L.1 b = x := by
  obtain ⟨L⟩ := linearInjection_nonempty_of_finrank_le h
  obtain ⟨e, he⟩ := exists_equiv_map_nonzero (F := F) (L.1 b) x
    (injection_eval_ne_zero L hb) hx
  exact ⟨postcompose e L, he⟩

def productShift {F B K : Type*} [Field F] [AddCommGroup B] [Module F B]
    [AddCommGroup K] [Module F K] [Fintype (LinearInjection F B K)] :
    (LinearInjection F B K → B) →ₗ[F] K where
  toFun b := ∑ L : LinearInjection F B K, L.1 (b L)
  map_add' b c := by simp [map_add, Finset.sum_add_distrib]
  map_smul' t b := by simp [map_smul, Finset.smul_sum]

theorem productShift_surjective {F B K : Type*} [Field F]
    [AddCommGroup B] [Module F B] [FiniteDimensional F B]
    [AddCommGroup K] [Module F K] [FiniteDimensional F K]
    [Fintype (LinearInjection F B K)]
    (h : Module.finrank F B ≤ Module.finrank F K)
    (b : B) (hb : b ≠ 0) :
    Function.Surjective (productShift (F := F) (B := B) (K := K)) := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact ⟨0, map_zero _⟩
  · obtain ⟨L, hL⟩ := exists_injection_hitting_nonzero h b hb x hx
    refine ⟨fun L' => if L' = L then b else 0, ?_⟩
    simpa [productShift, apply_ite] using hL

def enlargedOutput {F B K V : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [Fintype (LinearInjection F B K)] (C : V → B)
    (x : LinearInjection F B K → V) : K := ∑ L : LinearInjection F B K, L.1 (C (x L))

theorem enlargedOutput_shift {F B K V : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [AddCommGroup V] [Module F V] [Fintype (LinearInjection F B K)]
    (C : V → B) (i : B →ₗ[F] V)
    (hC : ∀ x b, C (x + i b) = C x + b)
    (x : LinearInjection F B K → V) (b : LinearInjection F B K → B) :
    enlargedOutput C (fun L => x L + i (b L)) =
      enlargedOutput C x + productShift b := by
  simp [enlargedOutput, productShift, hC, map_add, Finset.sum_add_distrib]

end

end DFVSGames.Gadget.Enlargement

noncomputable section

namespace DFVSGames.Gadget.EnlargementConstruction

open scoped BigOperators Classical
open Enlargement

universe u

variable {B K V N : Type u}
variable [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
variable [FiniteDimensional (ZMod 2) B]
variable [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
variable [FiniteDimensional (ZMod 2) K]
variable [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype N] [Nonempty N]

abbrev Copies (B K : Type u) [AddCommGroup B] [Module (ZMod 2) B]
    [AddCommGroup K] [Module (ZMod 2) K] := LinearInjection (ZMod 2) B K

@[instance_reducible]
noncomputable def copiesFintype : Fintype (Copies B K) :=
  Fintype.ofInjective (fun L : Copies B K => (L.1 : B → K)) (by
    intro L M h
    apply Subtype.ext
    exact LinearMap.ext (congrFun h))

local instance enlargementCopiesFintype : Fintype (Copies B K) := copiesFintype

def productEmbed (i : B →ₗ[ZMod 2] V) :
    (Copies B K → B) →ₗ[ZMod 2] (Copies B K → V) where
  toFun b L := i (b L)
  map_add' b c := by ext L; exact map_add i (b L) (c L)
  map_smul' t b := by ext L; exact map_smul i t (b L)

omit [Fintype B] [FiniteDimensional (ZMod 2) B] [Fintype K] [FiniteDimensional (ZMod 2) K] [Fintype V] in
theorem productEmbed_injective (i : B →ₗ[ZMod 2] V)
    (hi : Function.Injective i) : Function.Injective (productEmbed (K := K) i) := by
  intro b c h
  funext L
  apply hi
  exact congrFun h L

def productStage (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) : Stage (ZMod 2) K := by
  letI : Nonempty (Copies B K) := linearInjection_nonempty_of_finrank_le hdim
  exact
    { Input := Copies B K → V
      Shift := Copies B K → B
      Noise := Copies B K × N
      embed := productEmbed i
      embed_injective := productEmbed_injective i hi
      logical := productShift
      logical_surjective := productShift_surjective hdim b₀ hb₀
      output := enlargedOutput C
      equivariant := enlargedOutput_shift C i hC
      noise := fun t => Pi.single t.1 (noise t.2) }

def copyObserver {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    (T : StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀) →ₗ[ZMod 2] E)
    (L : Copies B K) : V →ₗ[ZMod 2] E :=
  T.comp ((StageQuotient.projection (productStage i hi C hC noise hdim b₀ hb₀)).comp
    (LinearMap.single (R := ZMod 2) (φ := fun _ : Copies B K => V) L))

end DFVSGames.Gadget.EnlargementConstruction
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_NonlinearRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Gadget.NonlinearRecurrence

open scoped BigOperators

variable {k I P R X B : Type*} [CommRing k]
variable [Fintype I] [DecidableEq I]
variable [AddCommGroup P] [Module k P] [Fintype P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X] [Fintype X]
variable [AddCommGroup B] [Module k B] [Fintype B] [DecidableEq B]

def change (F : X × B → B) (p d : X × B) : ℚ :=
  if F (p + d) ≠ F p then 1 else 0

omit [Fintype X] [Fintype B] in
@[simp] theorem change_zero (F : X × B → B) (p : X × B) : change F p 0 = 0 := by
  simp [change]

end DFVSGames.Gadget.NonlinearRecurrence

namespace DFVSGames.Gadget.StageNoiseRecurrence

open scoped BigOperators

noncomputable def average {A : Type*} [Finite A] (f : A → ℚ) : ℚ :=
  letI := Fintype.ofFinite A
  𝔼 a, f a

universe u v

variable {k : Type u} {B : Type v} [CommRing k] [AddCommGroup B] [Module k B]

noncomputable def error (s : Stage k B) : ℚ := by
  classical
  exact average (fun n : s.Noise => average (fun u : s.Input =>
    if s.output (u + s.noise n) ≠ s.output u then 1 else 0))

end DFVSGames.Gadget.StageNoiseRecurrence

noncomputable section

namespace DFVSGames.Gadget.QuadraticStageNoise

open scoped BigOperators Classical
open Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

def rate (F : Type*) [Fintype F] : ℚ :=
  1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1)

end DFVSGames.Gadget.QuadraticStageNoise
end

namespace DFVSGames.Gadget.Parameters

open Harmonic
open scoped BigOperators

def rankFor (level : ℚ) : ℕ := 2 ^ ⌈2 * level⌉₊

def genericityError (r₀ : ℕ) : ℚ := 1 / (2 * (badRankCoefficient r₀ + 1))

def initialRank (p : ℚ) : ℕ := rankFor (8 * (p⁻¹ + 1))

end DFVSGames.Gadget.Parameters

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_PolynomialProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Quadratic

abbrev BinaryField (d : ℕ) := GaloisField 2 d

end DFVSGames.Quadratic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticHybridEnergyImageSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical

variable {R B U : Type*} [Ring R]
  [AddCommGroup B] [Module R B] [AddCommGroup U] [Module R U]

theorem range_subtype_comp_of_surjective (W : Submodule R U)
    (z : B →ₗ[R] W) (hz : Function.Surjective z) :
    (W.subtype.comp z).range = W := by
  ext u
  constructor
  · rintro ⟨b, rfl⟩
    exact (z b).property
  · intro hu
    obtain ⟨b, hb⟩ := hz ⟨u, hu⟩
    exact ⟨b, congrArg Subtype.val hb⟩

def fixedImageEquivSurjection (W : Submodule R U) :
    {z : B →ₗ[R] U // z.range = W} ≃
      {z : B →ₗ[R] W // Function.Surjective z} where
  toFun z := ⟨z.val.codRestrict W (fun b => z.property.le (LinearMap.mem_range_self z.val b)), by
    intro w
    have hw : w.val ∈ z.val.range := z.property.symm ▸ w.property
    obtain ⟨b, hb⟩ := hw
    exact ⟨b, Subtype.ext hb⟩⟩
  invFun z := ⟨W.subtype.comp z.val, range_subtype_comp_of_surjective W z.val z.property⟩
  left_inv z := by
    apply Subtype.ext
    apply LinearMap.ext
    intro b
    rfl
  right_inv z := by
    apply Subtype.ext
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    rfl

@[simp] theorem fixedImageEquivSurjection_symm_val (W : Submodule R U)
    (z : {z : B →ₗ[R] W // Function.Surjective z}) :
    ((fixedImageEquivSurjection W).symm z).val = W.subtype.comp z.val := rfl

@[simp] theorem fixedImageEquivSurjection_apply_coe (W : Submodule R U)
    (z : {z : B →ₗ[R] U // z.range = W}) (b : B) :
    ((fixedImageEquivSurjection W z).val b : U) = z.val b := rfl

abbrev ImageRankFrequency (q : ℕ) :=
  {z : B →ₗ[R] U // Module.finrank R z.range = q}

abbrev RankImage (R U : Type*) [Ring R] [AddCommGroup U] [Module R U] (q : ℕ) :=
  {W : Submodule R U // Module.finrank R W = q}

def frequencyImage (q : ℕ) (z : ImageRankFrequency (R := R) (B := B) (U := U) q) :
    RankImage R U q := ⟨z.val.range, z.property⟩

def frequencyImageFiberEquiv (q : ℕ) (W : RankImage R U q) :
    {z : ImageRankFrequency (R := R) (B := B) (U := U) q // frequencyImage q z = W} ≃
      {z : B →ₗ[R] U // z.range = W.val} where
  toFun z := ⟨z.val.val, congrArg Subtype.val z.property⟩
  invFun z := ⟨⟨z.val, by rw [z.property]; exact W.property⟩, Subtype.ext z.property⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

def rankFrequencyImageEquiv (q : ℕ) :
    ImageRankFrequency (R := R) (B := B) (U := U) q ≃
      Σ W : RankImage R U q, {z : B →ₗ[R] W.val // Function.Surjective z} :=
  (Equiv.sigmaFiberEquiv (frequencyImage (R := R) (B := B) (U := U) q)).symm.trans
    (Equiv.sigmaCongrRight fun W =>
      (frequencyImageFiberEquiv q W).trans (fixedImageEquivSurjection W.val))

@[simp] theorem rankFrequencyImageEquiv_symm_val (q : ℕ)
    (p : Σ W : RankImage R U q, {z : B →ₗ[R] W.val // Function.Surjective z}) :
    ((rankFrequencyImageEquiv q).symm p).val = p.1.val.subtype.comp p.2.val := rfl

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def imageCoordinates (W D : Submodule K V) (h : IsCompl W D) : V ≃ₗ[K] (W × D) :=
  (Submodule.prodEquivOfIsCompl W D h).symm

@[simp] theorem imageCoordinates_subtype (W D : Submodule K V) (h : IsCompl W D)
    (w : W) : imageCoordinates W D h (w : V) = (w, 0) :=
  Submodule.prodEquivOfIsCompl_symm_apply_left W D h w

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

namespace DFVSGames.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

def compressBlock (S : (B × C) →ₗ[R] (A × (W × D))) : B →ₗ[R] (W × D) :=
  (LinearMap.snd R A (W × D)).comp (S.comp (LinearMap.inl R B C))

@[simp] theorem compressBlock_apply
    (S : (B × C) →ₗ[R] (A × (W × D))) (b : B) :
    compressBlock S b = (S (b, 0)).2 := rfl

structure Coordinates (z : B →ₗ[R] W) where
  alpha : (B × C) →ₗ[R] A
  psi : (B × C) →ₗ[R] W
  psi_left : psi.comp (LinearMap.inl R B C) = z
  v : C →ₗ[R] D

@[ext] theorem Coordinates.ext {z : B →ₗ[R] W} {p q : Coordinates (A := A) (D := D)
    (C := C) z} (ha : p.alpha = q.alpha) (hp : p.psi = q.psi) (hv : p.v = q.v) : p = q := by
  cases p
  cases q
  cases ha
  cases hp
  cases hv
  rfl

def assemble {z : B →ₗ[R] W} (p : Coordinates (A := A) (D := D) (C := C) z) :
    (B × C) →ₗ[R] (A × (W × D)) :=
  p.alpha.prod (p.psi.prod (p.v.comp (LinearMap.snd R B C)))

@[simp] theorem assemble_apply {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) (x : B × C) :
    assemble p x = (p.alpha x, p.psi x, p.v x.2) := rfl

@[simp] theorem compressBlock_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    compressBlock (assemble p) = z.prod (0 : B →ₗ[R] D) := by
  apply LinearMap.ext
  intro b
  have hp : p.psi (b, 0) = z b :=
    congrArg (fun L : (B →ₗ[R] W) => L b) p.psi_left
  simp [compressBlock, assemble, hp]

def extract (z : B →ₗ[R] W)
    (S : {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)}) :
    Coordinates (A := A) (D := D) (C := C) z where
  alpha := (LinearMap.fst R A (W × D)).comp S.val
  psi := (LinearMap.fst R W D).comp ((LinearMap.snd R A (W × D)).comp S.val)
  psi_left := by
    apply LinearMap.ext
    intro b
    exact congrArg (fun L : B →ₗ[R] (W × D) => (L b).1) S.property
  v := (LinearMap.snd R W D).comp
    ((LinearMap.snd R A (W × D)).comp (S.val.comp (LinearMap.inr R B C)))

@[simp] theorem assemble_extract (z : B →ₗ[R] W)
    (S : {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)}) :
    assemble (extract z S) = S.val := by
  apply LinearMap.ext
  rintro ⟨b, c⟩
  have hzero : (S.val (b, 0)).2.2 = 0 :=
    congrArg (fun L : B →ₗ[R] (W × D) => (L b).2) S.property
  have hlast : (S.val (b, c)).2.2 = (S.val (0, c)).2.2 := by
    calc
      _ = (S.val ((b, 0) + (0, c))).2.2 := by simp
      _ = (S.val (b, 0)).2.2 + (S.val (0, c)).2.2 := by rw [map_add]; rfl
      _ = _ := by rw [hzero, zero_add]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact hlast.symm

@[simp] theorem extract_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    extract z ⟨assemble p, compressBlock_assemble p⟩ = p := by
  apply Coordinates.ext
  · apply LinearMap.ext
    intro x
    rfl
  · apply LinearMap.ext
    intro x
    rfl
  · apply LinearMap.ext
    intro c
    rfl

def compressedFiberEquiv (z : B →ₗ[R] W) :
    {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)} ≃
      Coordinates (A := A) (D := D) (C := C) z where
  toFun := extract z
  invFun p := ⟨assemble p, compressBlock_assemble p⟩
  left_inv S := Subtype.ext (assemble_extract z S)
  right_inv := extract_assemble

end DFVSGames.Inverse.KMSAnalyticHybridCoordinates

namespace DFVSGames.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

def fullCoordinates {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    (B × C) →ₗ[R] (A × (W × C)) :=
  p.alpha.prod (p.psi.prod (LinearMap.snd R B C))

def embedLast (v : C →ₗ[R] D) : (A × (W × C)) →ₗ[R] (A × (W × D)) :=
  (LinearMap.id : A →ₗ[R] A).prodMap ((LinearMap.id : W →ₗ[R] W).prodMap v)

@[simp] theorem embedLast_apply (v : C →ₗ[R] D) (x : A × (W × C)) :
    embedLast v x = (x.1, x.2.1, v x.2.2) := rfl

end DFVSGames.Inverse.KMSAnalyticHybridCoordinates

namespace DFVSGames.Inverse.KMSKernelOrbits

noncomputable section

variable {K E F : Type*} [DivisionRing K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

def rangeEquivOfKerEq (S T : F →ₗ[K] E) (hker : S.ker = T.ker) :
    S.range ≃ₗ[K] T.range :=
  S.quotKerEquivRange.symm ≪≫ₗ
    Submodule.quotEquivOfEq S.ker T.ker hker ≪≫ₗ T.quotKerEquivRange

end
end DFVSGames.Inverse.KMSKernelOrbits

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticHybridEnergyFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

abbrev Extension (z : B →ₗ[R] W) :=
  {ψ : (B × C) →ₗ[R] W // ψ.comp (LinearMap.inl R B C) = z}

def coordinatesDataEquiv (z : B →ₗ[R] W) :
    Coordinates (A := A) (D := D) (C := C) z ≃
      ((B × C) →ₗ[R] A) × (Extension (C := C) z) × (C →ₗ[R] D) where
  toFun p := (p.alpha, ⟨p.psi, p.psi_left⟩, p.v)
  invFun p := ⟨p.1, p.2.1.val, p.2.1.property, p.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨a, ⟨ψ, hψ⟩, v⟩; rfl

def compressedFiberDataEquiv (z : B →ₗ[R] W) :
    {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)} ≃
      ((B × C) →ₗ[R] A) × (Extension (C := C) z) × (C →ₗ[R] D) :=
  (compressedFiberEquiv z).trans (coordinatesDataEquiv z)

def extensionEquiv (z : B →ₗ[R] W) : Extension (C := C) z ≃ (C →ₗ[R] W) where
  toFun ψ := ψ.val.comp (LinearMap.inr R B C)
  invFun u := ⟨z.coprod u, by ext b; simp⟩
  left_inv ψ := by
    apply Subtype.ext
    apply LinearMap.ext
    rintro ⟨b, c⟩
    have hb : ψ.val (b, 0) = z b :=
      congrArg (fun t : B →ₗ[R] W => t b) ψ.property
    change z b + ψ.val (0, c) = ψ.val (b, c)
    rw [← hb, ← map_add]
    simp
  right_inv u := by ext c; simp

end
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_KMSFourthMomentZoomTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical

local instance (priority := 2000) classicalSurjective {X Y : Type*} :
    DecidablePred (Function.Surjective : (X → Y) → Prop) :=
  fun g => Classical.propDecidable (Function.Surjective g)

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticSmallTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSFourthMoment

def mixedStepFactor (R : ℕ) : ℝ := 2 ^ (2 * R + 2)

end DFVSGames.Inverse.KMSFourthMoment

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSKernelFiberDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSKernelFiberCard

noncomputable section

abbrev F2 := ZMod 2

variable (F E I : Type*)
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]

abbrev KernelClass :=
  {K : Submodule F2 F // Module.finrank F2 (F ⧸ K) = Module.finrank F2 I}

abbrev RankFrequency :=
  {S : F →ₗ[F2] E // Module.finrank F2 S.range = Module.finrank F2 I}

abbrev FullFrequency := {T : F →ₗ[F2] I // Function.Surjective T}

variable {F E I}

def rankKernel (S : RankFrequency F E I) : KernelClass F I :=
  ⟨S.val.ker, S.val.quotKerEquivRange.finrank_eq.trans S.property⟩

def fullKernel (T : FullFrequency F I) : KernelClass F I :=
  ⟨T.val.ker, (T.val.quotKerEquivOfSurjective T.property).finrank_eq⟩

@[simp] theorem rankKernel_val (S : RankFrequency F E I) :
    (rankKernel S).val = S.val.ker := rfl

@[simp] theorem fullKernel_val (T : FullFrequency F I) :
    (fullKernel T).val = T.val.ker := rfl

end
end DFVSGames.Inverse.KMSKernelFiberCard

namespace DFVSGames.Inverse.KMSAnalyticKernelCount

noncomputable section

variable {R E F : Type*} [Ring R]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

theorem ker_comp_mkQ (K : Submodule R F) (J : (F ⧸ K) →ₗ[R] E)
    (hJ : Function.Injective J) : (J.comp K.mkQ).ker = K := by
  rw [LinearMap.ker_comp_of_ker_eq_bot K.mkQ (LinearMap.ker_eq_bot.mpr hJ),
    Submodule.ker_mkQ]

def fixedKernelEquivQuotientInjection (K : Submodule R F) :
    {S : F →ₗ[R] E // S.ker = K} ≃
      {J : (F ⧸ K) →ₗ[R] E // Function.Injective J} where
  toFun S := ⟨K.liftQ S.val S.property.symm.le,
    LinearMap.ker_eq_bot.mp (K.ker_liftQ_eq_bot S.val _ S.property.le)⟩
  invFun J := ⟨J.val.comp K.mkQ, ker_comp_mkQ K J.val J.property⟩
  left_inv S := by
    apply Subtype.ext
    exact K.liftQ_mkQ S.val _
  right_inv J := by
    apply Subtype.ext
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    rfl

@[simp]
theorem fixedKernelEquiv_apply_mkQ (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) (x : F) :
    (fixedKernelEquivQuotientInjection K S).val (K.mkQ x) = S.val x := rfl

@[simp]
theorem fixedKernelEquiv_symm_apply (K : Submodule R F)
    (J : {J : (F ⧸ K) →ₗ[R] E // Function.Injective J}) :
    ((fixedKernelEquivQuotientInjection K).symm J).val = J.val.comp K.mkQ := rfl

theorem range_forward (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) :
    (fixedKernelEquivQuotientInjection K S).val.range = S.val.range :=
  K.range_liftQ S.val _

theorem fixedKernel_finrank_eq_quotient (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) :
    Module.finrank R S.val.range = Module.finrank R (F ⧸ K) := by
  rw [← range_forward K S]
  exact LinearMap.finrank_range_of_inj (fixedKernelEquivQuotientInjection K S).property

end
end DFVSGames.Inverse.KMSAnalyticKernelCount

namespace DFVSGames.Inverse.KMSKernelFiberCard

open KMSAnalyticKernelCount

noncomputable section

variable {F E I : Type*}
  [AddCommGroup F] [Module F2 F] [FiniteDimensional F2 F]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup I] [Module F2 I] [FiniteDimensional F2 I]

def quotientEquiv (K : KernelClass F I) : (F ⧸ K.val) ≃ₗ[F2] I :=
  Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq K.property)

end
end DFVSGames.Inverse.KMSKernelFiberCard

namespace DFVSGames.Inverse.KMSInjectionCount

open scoped BigOperators

noncomputable section

abbrev F2 := ZMod 2

variable (I E : Type*) [AddCommGroup I] [Module F2 I]
  [AddCommGroup E] [Module F2 E]

def beta : ℕ := Nat.card {J : I →ₗ[F2] E // Function.Injective J}

def injectiveEquivIndependent {ι : Type*} (b : Module.Basis ι F2 I) :
    {J : I →ₗ[F2] E // Function.Injective J} ≃
      {s : ι → E // LinearIndependent F2 s} where
  toFun J := ⟨J.val ∘ b, b.linearIndependent.map' J.val (LinearMap.ker_eq_bot.mpr J.property)⟩
  invFun s := ⟨b.constr F2 s.val, b.injective_constr_of_linearIndependent s.property⟩
  left_inv J := by
    apply Subtype.ext
    exact b.constr_self F2 J.val
  right_inv s := by
    apply Subtype.ext
    funext i
    exact b.constr_basis F2 s.val i

end
end DFVSGames.Inverse.KMSInjectionCount

namespace DFVSGames.Inverse.KMSKernelFiberCard

open KMSAnalyticKernelCount KMSInjectionCount
open scoped Classical

noncomputable section

variable {F E I J : Type*}
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J]

def injectionEquivOfDomainEquiv (e : J ≃ₗ[F2] I) :
    {u : J →ₗ[F2] E // Function.Injective u} ≃
      {u : I →ₗ[F2] E // Function.Injective u} where
  toFun u := ⟨u.val.comp e.symm.toLinearMap, u.property.comp e.symm.injective⟩
  invFun u := ⟨u.val.comp e.toLinearMap, u.property.comp e.injective⟩
  left_inv u := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change u.val (e.symm (e x)) = u.val x
    rw [e.symm_apply_apply]
  right_inv u := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change u.val (e (e.symm x)) = u.val x
    rw [e.apply_symm_apply]

variable [FiniteDimensional F2 F] [FiniteDimensional F2 I]

def fixedKernelEquivInjection (K : KernelClass F I) :
    {S : F →ₗ[F2] E // S.ker = K.val} ≃
      {J : I →ₗ[F2] E // Function.Injective J} :=
  (fixedKernelEquivQuotientInjection K.val).trans
    (injectionEquivOfDomainEquiv (quotientEquiv K))

def rankFiberEquivFixedKernel (K : KernelClass F I) :
    {S : RankFrequency F E I // rankKernel S = K} ≃
      {S : F →ₗ[F2] E // S.ker = K.val} where
  toFun S := ⟨S.val.val, congrArg Subtype.val S.property⟩
  invFun S := ⟨⟨S.val,
    (fixedKernel_finrank_eq_quotient K.val S).trans K.property⟩,
    Subtype.ext S.property⟩
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv S := by
    apply Subtype.ext
    rfl

omit [FiniteDimensional F2 F] in

theorem surjective_of_kernel_class (K : KernelClass F I)
    (T : F →ₗ[F2] I) (hT : T.ker = K.val) : Function.Surjective T := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  exact (fixedKernel_finrank_eq_quotient K.val ⟨T, hT⟩).trans K.property

def fullFiberEquivFixedKernel (K : KernelClass F I) :
    {T : FullFrequency F I // fullKernel T = K} ≃
      {T : F →ₗ[F2] I // T.ker = K.val} where
  toFun T := ⟨T.val.val, congrArg Subtype.val T.property⟩
  invFun T := ⟨⟨T.val, surjective_of_kernel_class K T.val T.property⟩,
    Subtype.ext T.property⟩
  left_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv T := by
    apply Subtype.ext
    rfl

end
end DFVSGames.Inverse.KMSKernelFiberCard

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticCodomainTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalyticCompatibleSplitting

noncomputable section

abbrev F2 := ZMod 2

variable {I F K : Type*}
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup K] [Module F2 K]

structure CompatibleSplitting (π : I →ₗ[F2] K) (A : F →ₗ[F2] K) where
  functional : K →ₗ[F2] F2
  targetVector : K
  functional_targetVector : functional targetVector = 1
  leftVector : I
  leftVector_image : π leftVector = targetVector
  rightVector : F
  rightVector_image : A rightVector = targetVector
  left_surjective : Function.Surjective π
  right_surjective : Function.Surjective A

namespace CompatibleSplitting

variable {π : I →ₗ[F2] K} {A : F →ₗ[F2] K}

abbrev K0 (s : CompatibleSplitting π A) := s.functional.ker
abbrev J (s : CompatibleSplitting π A) := (s.functional.comp π).ker
abbrev B (s : CompatibleSplitting π A) := (s.functional.comp A).ker

def leftMap (s : CompatibleSplitting π A) : s.J →ₗ[F2] s.K0 :=
  (π.comp (s.functional.comp π).ker.subtype).codRestrict s.functional.ker
    (fun x => x.property)

def rightMap (s : CompatibleSplitting π A) : s.B →ₗ[F2] s.K0 :=
  (A.comp (s.functional.comp A).ker.subtype).codRestrict s.functional.ker
    (fun x => x.property)

end CompatibleSplitting

end
end DFVSGames.Inverse.KMSAnalyticCompatibleSplitting

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical

universe u v

variable {E A I J : Type u}
  {F : Type v}
  [AddCommGroup E]
  [AddCommGroup A]
  [AddCommGroup I]
  [AddCommGroup J]
  [AddCommGroup F]
  [Fintype E]
  [Fintype A]
  [Fintype I]
  [Fintype J]
  [Fintype F]

def mixedRankConstant (R : ℕ) : ℝ := (2 : ℝ) ^ (4 * R * R) * mixedStepFactor R ^ R

end
end DFVSGames.Inverse.KMSFourthMoment

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_KMSMomentConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSMomentConstants
noncomputable section
open KMSFourthMoment

def fourthMomentConstant (r : ℕ) : ℝ := 2 ^ (109 * r * r + 2 * r)

end
end DFVSGames.Inverse.KMSMomentConstants

namespace DFVSGames.Inverse.KMS

noncomputable section
open scoped BigOperators Classical

section FiniteDensity

variable {Ω : Type*} [DecidableEq Ω]

def relativeDensity (S I : Finset Ω) : ℝ :=
  ((S ∩ I).card : ℝ) / I.card

end FiniteDensity

abbrev F2 := ZMod 2
abbrev Ambient (n : ℕ) := Fin n → F2

def Vertex (n ell : ℕ) :=
  {L : Submodule F2 (Ambient n) // Module.finrank F2 L = ell}

instance vertexFinite (n ell : ℕ) : Finite (Vertex n ell) := by
  let : Finite (Submodule F2 (Ambient n)) :=
    Finite.of_injective (fun L : Submodule F2 (Ambient n) => (L : Set (Ambient n)))
      SetLike.coe_injective
  exact inferInstanceAs (Finite {L : Submodule F2 (Ambient n) //
    Module.finrank F2 L = ell})

instance vertexFintype (n ell : ℕ) : Fintype (Vertex n ell) := Fintype.ofFinite _

def Adjacent {n ell : ℕ} (L M : Vertex n ell) : Prop :=
  L ≠ M ∧ Module.finrank F2 ↥(L.val ⊓ M.val : Submodule F2 (Ambient n)) + 1 = ell

def neighbors {n ell : ℕ} (L : Vertex n ell) : Finset (Vertex n ell) :=
  Finset.univ.filter (Adjacent L)

def retention {n ell : ℕ} (S : Finset (Vertex n ell)) : ℝ :=
  (∑ L ∈ S, relativeDensity S (neighbors L)) / S.card

def interval {n ell : ℕ} (A B : Submodule F2 (Ambient n)) :
    Finset (Vertex n ell) :=
  Finset.univ.filter fun L => A ≤ L.val ∧ L.val ≤ B

def ExpansionPrinciple : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      ∃ r : ℕ, 1 ≤ r ∧ ∃ ell₀ : ℕ, ∀ ell : ℕ, ell₀ ≤ ell →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∀ S : Finset (Vertex n ell), S.Nonempty → ζ ≤ retention S →
            ∃ A B : Submodule F2 (Ambient n),
              A ≤ B ∧ Module.finrank F2 A + (n - Module.finrank F2 B) ≤ r ∧
                (S ∩ interval A B).Nonempty ∧ α ≤ relativeDensity S (interval A B)

end
end DFVSGames.Inverse.KMS

namespace DFVSGames.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical

abbrev BasisMap (n ell : ℕ) := KMS.Ambient ell →ₗ[KMS.F2] KMS.Ambient n

instance basisMapFinite (n ell : ℕ) : Finite (BasisMap n ell) :=
  Finite.of_injective (fun X : BasisMap n ell => (X : KMS.Ambient ell → KMS.Ambient n))
    DFunLike.coe_injective

instance basisMapFintype (n ell : ℕ) : Fintype (BasisMap n ell) := Fintype.ofFinite _

def InLift {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) (X : BasisMap n ell) : Prop :=
  ∃ L ∈ S, LinearMap.range X = L.val

def lift {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) : Finset (BasisMap n ell) :=
  Finset.univ.filter (InLift S)

@[simp] theorem mem_lift {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : X ∈ lift S ↔ InLift S X := by
  simp [lift]

def liftedIndicator {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : ℝ := if InLift S X then 1 else 0

theorem injective_of_inLift {n ell : ℕ} {S : Finset (KMS.Vertex n ell)}
    {X : BasisMap n ell} (h : InLift S X) : Function.Injective X := by
  obtain ⟨L, _, hL⟩ := h
  have hr : Module.finrank KMS.F2 (LinearMap.range X) = ell := by
    rw [hL]
    exact L.property
  have hd := X.finrank_range_add_finrank_ker
  have he : Module.finrank KMS.F2 (KMS.Ambient ell) = ell := by
    simp [KMS.Ambient]
  have hk : Module.finrank KMS.F2 (LinearMap.ker X) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

def rangeVertex {n ell : ℕ} (X : BasisMap n ell) (hX : Function.Injective X) :
    KMS.Vertex n ell :=
  ⟨LinearMap.range X, by
    rw [LinearMap.finrank_range_of_inj hX]
    simp [KMS.Ambient]⟩

theorem inLift_iff_rangeVertex_mem {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    InLift S X ↔ rangeVertex X hX ∈ S := by
  constructor
  · rintro ⟨L, hL, hXL⟩
    have he : rangeVertex X hX = L := Subtype.ext hXL
    simpa only [he] using hL
  · intro h
    exact ⟨rangeVertex X hX, h, rfl⟩

end
end DFVSGames.Inverse.KMSBasisComparison

namespace DFVSGames.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {q t : ℕ}

def RestrictedCompletion (Q : Fin q → V) (W L : Submodule K V) :=
  {z : Fin t → W //
    LinearIndependent K (Sum.elim Q (fun i => (z i : V))) ∧
      Submodule.span K (Set.range (Sum.elim Q (fun i => (z i : V)))) = L}

variable {Q : Fin q → V} {W L M N : Submodule K V}

def completionBasis (z : RestrictedCompletion (t := t) Q W L) :
    Module.Basis (Fin q ⊕ Fin t) K L :=
  (Module.Basis.span z.property.1).map (LinearEquiv.ofEq _ _ z.property.2)

@[simp] theorem completionBasis_coe
    (z : RestrictedCompletion (t := t) Q W L) (i : Fin q ⊕ Fin t) :
    (completionBasis z i : V) = Sum.elim Q (fun j => (z.val j : V)) i := by
  simp [completionBasis]

def completionOfBasis (b : Module.Basis (Fin q ⊕ Fin t) K L)
    (hQ : ∀ i, (b (Sum.inl i) : V) = Q i)
    (hW : ∀ i, (b (Sum.inr i) : V) ∈ W) :
    RestrictedCompletion (t := t) Q W L := by
  have hb : Sum.elim Q (fun i => ((⟨b (Sum.inr i), hW i⟩ : W) : V)) =
      fun i => (b i : V) := by
    funext i
    cases i with
    | inl i => exact (hQ i).symm
    | inr i => rfl
  refine ⟨fun i => ⟨b (Sum.inr i), hW i⟩, ?_, ?_⟩
  · rw [hb]
    exact b.linearIndependent.map' L.subtype (by simp)
  · rw [hb]
    calc
      Submodule.span K (Set.range fun i => (b i : V)) =
          (Submodule.span K (Set.range b)).map L.subtype := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      _ = L := by rw [b.span_eq]; simp

def completionSpanEquiv
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) : L ≃ₗ[K] M :=
  (completionBasis x).equiv (completionBasis y) (Equiv.refl _)

@[simp] theorem completionSpanEquiv_basis
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (i : Fin q ⊕ Fin t) :
    completionSpanEquiv x y (completionBasis x i) = completionBasis y i := by
  simp [completionSpanEquiv]

@[simp] theorem completionSpanEquiv_symm
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    (completionSpanEquiv x y).symm = completionSpanEquiv y x := by
  simp [completionSpanEquiv]

theorem completionSpanEquiv_sub_mem
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (v : L) :
    (completionSpanEquiv x y v : V) - (v : V) ∈ W := by
  let d : L →ₗ[K] V := M.subtype.comp (completionSpanEquiv x y).toLinearMap - L.subtype
  have hd : (⊤ : Submodule K L) ≤ W.comap d := by
    rw [← (completionBasis x).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change d (completionBasis x i) ∈ W
    change (completionSpanEquiv x y (completionBasis x i) : V) -
      (completionBasis x i : V) ∈ W
    rw [completionSpanEquiv_basis]
    cases i with
    | inl i => simp
    | inr i =>
      simpa only [completionBasis_coe, Sum.elim_inr] using
        W.sub_mem (y.val i).property (x.val i).property
  exact hd (Submodule.mem_top : v ∈ (⊤ : Submodule K L))

theorem completionSpanEquiv_mem_iff
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (v : L) :
    (completionSpanEquiv x y v : V) ∈ W ↔ (v : V) ∈ W := by
  have hd := completionSpanEquiv_sub_mem x y v
  constructor
  · intro hv
    exact (W.sub_mem_iff_right hv).mp hd
  · intro hv
    exact (W.sub_mem_iff_left hv).mp hd

def transportCompletion
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) :
    RestrictedCompletion (t := t) Q W M :=
  completionOfBasis ((completionBasis z).map (completionSpanEquiv x y))
    (by
      intro i
      have h : completionBasis z (Sum.inl i) = completionBasis x (Sum.inl i) := by
        apply Subtype.ext
        simp
      simp [Module.Basis.map_apply, h])
    (by
      intro i
      change (completionSpanEquiv x y (completionBasis z (Sum.inr i)) : V) ∈ W
      apply (completionSpanEquiv_mem_iff x y _).mpr
      simp)

@[simp] theorem transportCompletion_coe
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) (i : Fin t) :
    ((transportCompletion x y z).val i : V) =
      (completionSpanEquiv x y (completionBasis z (Sum.inr i)) : V) := rfl

theorem transportCompletion_inverse
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) :
    transportCompletion y x (transportCompletion x y z) = z := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  rw [transportCompletion_coe]
  have hb : completionBasis (transportCompletion x y z) (Sum.inr i) =
      completionSpanEquiv x y (completionBasis z (Sum.inr i)) := by
    apply Subtype.ext
    simp
  rw [hb, ← completionSpanEquiv_symm, LinearEquiv.symm_apply_apply]
  simp

def restrictedCompletionEquiv
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    RestrictedCompletion (t := t) Q W L ≃ RestrictedCompletion (t := t) Q W M where
  toFun := transportCompletion x y
  invFun := transportCompletion y x
  left_inv := transportCompletion_inverse x y
  right_inv := transportCompletion_inverse y x

end
end DFVSGames.Inverse.KMSBasisComparisonPseudorandom

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSBasisComparisonPseudorandom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped BigOperators Classical
open KMS

variable {n q t : ℕ}

def prefixSpan (Q : Fin q → Ambient n) : Submodule F2 (Ambient n) :=
  Submodule.span F2 (Set.range Q)

def joinedTuple (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : Fin t → W) : (Fin q ⊕ Fin t) → Ambient n :=
  Sum.elim Q (fun i => (z i : Ambient n))

abbrev IndependentCompletion (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :=
  {z : Fin t → W // LinearIndependent F2 (joinedTuple Q W z)}

def completionVertex (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) : Vertex n (q + t) :=
  ⟨Submodule.span F2 (Set.range (joinedTuple Q W z.val)), by
    simpa using finrank_span_eq_card z.property⟩

theorem prefix_le_completion (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) :
    prefixSpan Q ≤ (completionVertex Q W z).val := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨Sum.inl i, rfl⟩

theorem completion_le_sup (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) :
    (completionVertex Q W z).val ≤ prefixSpan Q ⊔ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  cases i with
  | inl i =>
      exact (le_sup_left : prefixSpan Q ≤ prefixSpan Q ⊔ W)
        (Submodule.subset_span ⟨i, rfl⟩)
  | inr i =>
      exact (le_sup_right : W ≤ prefixSpan Q ⊔ W) (z.val i).property

theorem completion_mem_interval (Q : Fin q → Ambient n)
    (W : Submodule F2 (Ambient n)) (z : IndependentCompletion (t := t) Q W) :
    completionVertex Q W z ∈ interval (prefixSpan Q) (prefixSpan Q ⊔ W) := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    prefix_le_completion Q W z, completion_le_sup Q W z⟩

def GrassmannPseudorandom {ell : ℕ} (S : Finset (Vertex n ell))
    (r : ℕ) (ε : ℝ) : Prop :=
  ∀ A B : Submodule F2 (Ambient n), A ≤ B →
    Module.finrank F2 A + (n - Module.finrank F2 B) ≤ r →
      relativeDensity S (interval A B) ≤ ε

def completionEvent (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) (z : Fin t → W) : Prop :=
  ∃ h : LinearIndependent F2 (joinedTuple Q W z), completionVertex Q W ⟨z, h⟩ ∈ S

def restrictedLiftDensity (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) : ℝ :=
  (Nat.card {z : Fin t → W // completionEvent S Q W z} : ℝ) /
    Nat.card (Fin t → W)

def TuplePseudorandom {ell : ℕ} (S : Finset (Vertex n ell))
    (r : ℕ) (ε : ℝ) : Prop :=
  ∀ q t : ℕ, ∀ h : q + t = ell, ∀ Q : Fin q → Ambient n,
    ∀ W : Submodule F2 (Ambient n), q + (n - Module.finrank F2 W) ≤ r →
      restrictedLiftDensity (h.symm ▸ S) Q W ≤ ε

abbrev IntervalVertex (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :=
  ↥(interval (ell := q + t) (prefixSpan Q) (prefixSpan Q ⊔ W))

def completionIntervalVertex (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) : IntervalVertex (t := t) Q W :=
  ⟨completionVertex Q W z, completion_mem_interval Q W z⟩

def completionFiberEquiv (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (L : IntervalVertex (t := t) Q W) :
    {z : IndependentCompletion (t := t) Q W // completionIntervalVertex Q W z = L} ≃
      RestrictedCompletion (t := t) Q W L.val.val where
  toFun z := ⟨z.val.val, z.val.property,
    congrArg (fun M => M.val.val) z.property⟩
  invFun z := ⟨⟨z.val, z.property.1⟩, Subtype.ext (Subtype.ext z.property.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def completionEventEquiv (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :
    {z : Fin t → W // completionEvent S Q W z} ≃
      {z : IndependentCompletion (t := t) Q W // completionVertex Q W z ∈ S} where
  toFun z := ⟨⟨z.val, z.property.choose⟩, z.property.choose_spec⟩
  invFun z := ⟨z.val.val, z.val.property, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def intervalEventEquiv (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :
    {L : IntervalVertex (t := t) Q W // L.val ∈ S} ≃
      ↥(S ∩ interval (prefixSpan Q) (prefixSpan Q ⊔ W)) where
  toFun L := ⟨L.val.val, Finset.mem_inter.mpr ⟨L.property, L.val.property⟩⟩
  invFun L := ⟨⟨L.val, (Finset.mem_inter.mp L.property).2⟩,
    (Finset.mem_inter.mp L.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

end
end DFVSGames.Inverse.KMSBasisComparisonPseudorandom

namespace DFVSGames.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison

variable {n q t : ℕ}

def tupleBasis (q t : ℕ) : Module.Basis (Fin q ⊕ Fin t) F2 (Ambient (q + t)) :=
  (Pi.basisFun F2 (Fin (q + t))).reindex finSumFinEquiv.symm

def tupleMap (x : (Fin q ⊕ Fin t) → Ambient n) : BasisMap n (q + t) :=
  (tupleBasis q t).constr F2 x

@[simp] theorem tupleMap_basis (x : (Fin q ⊕ Fin t) → Ambient n)
    (i : Fin q ⊕ Fin t) : tupleMap x (tupleBasis q t i) = x i :=
  (tupleBasis q t).constr_basis F2 x i

end
end DFVSGames.Inverse.KMSBasisComparisonPseudorandom

namespace DFVSGames.Inverse.KMSAffineRestriction
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom

variable {n ell q t r : ℕ} {ε : ℝ}

def affineCoordinates {E W : Type*}
    [AddCommGroup E] [Module F2 E] [AddCommGroup W] [Module F2 W]
    (b : Module.Basis (Fin t) F2 E) (T : E →ₗ[F2] W) :
    (E →ₗ[F2] W) ≃ (Fin t → W) :=
  ((b.constr F2).toEquiv).symm.trans (Equiv.addLeft (fun i => T (b i)))

@[simp] theorem affineCoordinates_apply {E W : Type*}
    [AddCommGroup E] [Module F2 E] [AddCommGroup W] [Module F2 W]
    (b : Module.Basis (Fin t) F2 E) (T H : E →ₗ[F2] W) (i : Fin t) :
    affineCoordinates b T H i = T (b i) + H (b i) := rfl

end
end DFVSGames.Inverse.KMSAffineRestriction

namespace DFVSGames.Inverse.KMSAffineRestriction
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom

variable {n ell q t : ℕ}

def complementBasis (U E0 : Submodule F2 (Ambient ell)) (hc : IsCompl U E0)
    (bU : Module.Basis (Fin q) F2 U) (b0 : Module.Basis (Fin t) F2 E0) :
    Module.Basis (Fin q ⊕ Fin t) F2 (Ambient ell) :=
  (bU.prod b0).map (Submodule.prodEquivOfIsCompl U E0 hc)

end
end DFVSGames.Inverse.KMSAffineRestriction

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_KMSMomentScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSMomentScalar

noncomputable section
open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

def IsBoolean (f : X → ℝ) : Prop := ∀ x, f x = 0 ∨ f x = 1

end
end DFVSGames.Inverse.KMSMomentScalar

namespace DFVSGames.Inverse.KMSLowLevel
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Inverse.KMSMomentScalar

section FiniteCutoff
variable {I : Type*} [Fintype I]

def rankEnergy (rank : I → ℕ) (a : I → ℝ) (i : ℕ) : ℝ :=
  ∑ s, if rank s = i then a s ^ 2 else 0

end FiniteCutoff

end
end DFVSGames.Inverse.KMSLowLevel

namespace DFVSGames.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

abbrev Lines (K E : Type*) [Field K] [AddCommGroup E] [Module K E] :=
  {L : Submodule K E // finrank K L = 1}

abbrev Hyperplanes (K E : Type*) [Field K] [AddCommGroup E] [Module K E] :=
  {H : Submodule K E // finrank K H + 1 = finrank K E}

theorem finrank_map_mkQ_add [FiniteDimensional K E]
    (H W : Submodule K E) (hHW : H ≤ W) :
    finrank K (W.map H.mkQ) + finrank K H = finrank K W := by
  have h := LinearMap.finrank_range_add_finrank_ker (H.mkQ.comp W.subtype)
  have hr : LinearMap.range (H.mkQ.comp W.subtype) = W.map H.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker (H.mkQ.comp W.subtype) = H.comap W.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hHW).finrank_eq] at h
  exact h

abbrev Extensions (H : Submodule K E) :=
  {W : Submodule K E // H ≤ W ∧ finrank K W = finrank K H + 1}

noncomputable def extensionsEquivLines [FiniteDimensional K E]
    (H : Submodule K E) : Extensions H ≃ Lines K (E ⧸ H) where
  toFun W := ⟨W.val.map H.mkQ, by
    have h := finrank_map_mkQ_add H W.val W.property.1
    rw [W.property.2] at h
    omega⟩
  invFun L := ⟨L.val.comap H.mkQ, Submodule.le_comap_mkQ H L.val, by
    have h := finrank_map_mkQ_add H (L.val.comap H.mkQ)
      (Submodule.le_comap_mkQ H L.val)
    have heq : (L.val.comap H.mkQ).map H.mkQ = L.val :=
      Submodule.map_comap_eq_self (by simp)
    rw [heq, L.property] at h
    omega⟩
  left_inv W := by
    apply Subtype.ext
    simp [Submodule.comap_map_mkQ, sup_eq_right.mpr W.property.1]
  right_inv L := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by simp)

end DFVSGames.Inverse.MatrixChart

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_MatrixChartDegreeNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

abbrev HyperplanesBelow (L : Submodule K E) :=
  {H : Submodule K E // H ≤ L ∧ finrank K H + 1 = finrank K L}

abbrev GrassmannNeighbors (L : Submodule K E) :=
  {W : Submodule K E // finrank K W = finrank K L ∧
    finrank K (L ⊓ W : Submodule K E) + 1 = finrank K L}

noncomputable def hyperplanesBelowEquiv (L : Submodule K E) :
    HyperplanesBelow L ≃ Hyperplanes K L where
  toFun H := ⟨H.val.comap L.subtype, by
    rw [(Submodule.comapSubtypeEquivOfLe H.property.1).finrank_eq]
    exact H.property.2⟩
  invFun H := ⟨H.val.map L.subtype, Submodule.map_subtype_le L H.val, by
    rw [Submodule.finrank_map_subtype_eq]
    exact H.property⟩
  left_inv H := by
    apply Subtype.ext
    simp [Submodule.map_comap_subtype, inf_eq_right.mpr H.property.1]
  right_inv H := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective Subtype.val_injective H.val

abbrev NeighborExtensionData (L : Submodule K E) :=
  (H : HyperplanesBelow L) × {W : Extensions H.val // W.val ≠ L}

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.KMSBasisComparison

open Module

variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

def rankOneUpdate (X : E →ₗ[K] F) (a : E →ₗ[K] K) (y : F) : E →ₗ[K] F :=
  X + a.smulRight y

@[simp] theorem rankOneUpdate_apply (X : E →ₗ[K] F) (a : E →ₗ[K] K)
    (y : F) (x : E) : rankOneUpdate X a y x = X x + a x • y := rfl

theorem rankOneUpdate_mem_range_iff (X : E →ₗ[K] F) (a : E →ₗ[K] K)
    {y : F} (hy : y ∉ LinearMap.range X) (x : E) :
    rankOneUpdate X a y x ∈ LinearMap.range X ↔ a x = 0 := by
  constructor
  · intro h
    have hs : a x • y ∈ LinearMap.range X := by
      have hh := (LinearMap.range X).sub_mem h (LinearMap.mem_range_self X x)
      simpa only [rankOneUpdate_apply, add_sub_cancel_left] using hh
    by_contra ha
    exact hy (((LinearMap.range X).smul_mem_iff ha).mp hs)
  · intro ha
    simpa only [rankOneUpdate_apply, ha, zero_smul, add_zero] using
      LinearMap.mem_range_self X x

theorem injective_rankOneUpdate (X : E →ₗ[K] F) (hX : Function.Injective X)
    (a : E →ₗ[K] K) {y : F} (hy : y ∉ LinearMap.range X) :
    Function.Injective (rankOneUpdate X a y) := by
  apply (injective_iff_map_eq_zero (rankOneUpdate X a y)).mpr
  intro x hx
  have ha : a x = 0 := (rankOneUpdate_mem_range_iff X a hy x).mp
    (by rw [hx]; exact (LinearMap.range X).zero_mem)
  have hxx : X x = 0 := by simpa only [rankOneUpdate_apply, ha, zero_smul,
    add_zero] using hx
  exact hX (by simpa only [map_zero] using hxx)

theorem range_inf_rankOneUpdate (X : E →ₗ[K] F) (a : E →ₗ[K] K)
    {y : F} (hy : y ∉ LinearMap.range X) :
    LinearMap.range X ⊓ LinearMap.range (rankOneUpdate X a y) =
      (LinearMap.ker a).map X := by
  ext z
  constructor
  · rintro ⟨hz, x, hx⟩
    have ha : a x = 0 := (rankOneUpdate_mem_range_iff X a hy x).mp
      (by rw [hx]; exact hz)
    refine ⟨x, ha, ?_⟩
    simpa only [rankOneUpdate_apply, ha, zero_smul, add_zero] using hx
  · rintro ⟨x, hx, rfl⟩
    refine ⟨LinearMap.mem_range_self X x, x, ?_⟩
    have ha : a x = 0 := hx
    simp only [rankOneUpdate_apply, ha, zero_smul, add_zero]

noncomputable def rankOneUpdateNeighbor [FiniteDimensional K E]
    (X : E →ₗ[K] F) (hX : Function.Injective X)
    (a : E →ₗ[K] K) (ha : a ≠ 0)
    (y : F) (hy : y ∉ LinearMap.range X) :
    MatrixChart.GrassmannNeighbors (LinearMap.range X) :=
  ⟨LinearMap.range (rankOneUpdate X a y), by
    constructor
    · rw [LinearMap.finrank_range_of_inj (injective_rankOneUpdate X hX a hy),
        LinearMap.finrank_range_of_inj hX]
    · rw [range_inf_rankOneUpdate X a hy,
        ← (Submodule.equivMapOfInjective X hX (LinearMap.ker a)).finrank_eq,
        LinearMap.finrank_range_of_inj hX]
      exact Module.Dual.finrank_ker_add_one_of_ne_zero ha⟩

@[simp] theorem rankOneUpdateNeighbor_val [FiniteDimensional K E]
    (X : E →ₗ[K] F) (hX : Function.Injective X)
    (a : E →ₗ[K] K) (ha : a ≠ 0) (y : F) (hy : y ∉ LinearMap.range X) :
    (rankOneUpdateNeighbor X hX a ha y hy).val =
      LinearMap.range (rankOneUpdate X a y) := rfl

end DFVSGames.Inverse.KMSBasisComparison

namespace DFVSGames.Inverse.MatrixChart

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

def graphEquiv (T : X →ₗ[K] Y) : X ≃ₗ[K] T.graph where
  toFun x := ⟨(x, T x), rfl⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl x.property.symm
  map_add' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (map_add T _ _)
  map_smul' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (map_smul T _ _)

theorem graph_injective : Function.Injective (LinearMap.graph (R := K) (M := X) (M₂ := Y)) := by
  intro T U h
  apply LinearMap.ext
  intro x
  have hx : (x, T x) ∈ U.graph := h ▸ (show (x, T x) ∈ T.graph from rfl)
  exact hx

def intersectionEquiv (T U : X →ₗ[K] Y) :
    LinearMap.ker (T - U) ≃ₗ[K] (T.graph ⊓ U.graph : Submodule K (X × Y)) where
  toFun x := ⟨(x.val, T x.val), by
    refine ⟨rfl, ?_⟩
    have hx : T x.val - U x.val = 0 := x.property
    exact sub_eq_zero.mp hx⟩
  invFun x := ⟨x.val.1, by
    change T x.val.1 - U x.val.1 = 0
    exact sub_eq_zero.mpr (x.property.1.symm.trans x.property.2)⟩
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl x.property.1.symm
  map_add' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (map_add T _ _)
  map_smul' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (map_smul T _ _)

theorem finrank_graph [FiniteDimensional K X] (T : X →ₗ[K] Y) :
    Module.finrank K T.graph = Module.finrank K X :=
  (graphEquiv T).finrank_eq.symm

theorem finrank_intersection_add_rank [FiniteDimensional K X] (T U : X →ₗ[K] Y) :
    Module.finrank K (T.graph ⊓ U.graph : Submodule K (X × Y)) +
      Module.finrank K (LinearMap.range (T - U)) = Module.finrank K X := by
  rw [← (intersectionEquiv T U).finrank_eq, Nat.add_comm]
  exact LinearMap.finrank_range_add_finrank_ker (T - U)

theorem adjacent_iff_rank_one [FiniteDimensional K X] (T U : X →ₗ[K] Y) :
    Module.finrank K (T.graph ⊓ U.graph : Submodule K (X × Y)) + 1 =
        Module.finrank K X ↔
      Module.finrank K (LinearMap.range (T - U)) = 1 := by
  have h := finrank_intersection_add_rank T U
  omega

theorem adjacent_rank_one_step [FiniteDimensional K X]
    (T : X →ₗ[K] Y) (a : X →ₗ[K] K) (l : Y) (ha : a ≠ 0) (hl : l ≠ 0) :
    Module.finrank K (T.graph ⊓ (T + a.smulRight l).graph :
      Submodule K (X × Y)) + 1 = Module.finrank K X := by
  apply (adjacent_iff_rank_one T (T + a.smulRight l)).mpr
  have heq : T - (T + a.smulRight l) = (-a).smulRight l := by
    apply LinearMap.ext
    intro x
    simp []
  rw [heq, LinearMap.range_smulRight_apply (neg_ne_zero.mpr ha)]
  exact finrank_span_singleton hl

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

section ArbitraryField

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem exists_smulRight_of_rank_one (T : X →ₗ[K] Y)
    (hT : Module.finrank K T.range = 1) :
    ∃ (a : X →ₗ[K] K) (l : Y), a ≠ 0 ∧ l ≠ 0 ∧ T = a.smulRight l := by
  classical
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hT
  let a : X →ₗ[K] K := e.symm.toLinearMap.comp T.rangeRestrict
  have ha : a ≠ 0 := LinearMap.surjective_iff_ne_zero.mp
    (e.symm.surjective.comp T.surjective_rangeRestrict)
  have hl : (e 1 : Y) ≠ 0 := by
    intro h
    have he : e 1 = e 0 := by
      apply Subtype.ext
      simp at h
    exact one_ne_zero (e.injective he)
  refine ⟨a, (e 1 : Y), ha, hl, ?_⟩
  apply LinearMap.ext
  intro x
  have h : a x • e 1 = T.rangeRestrict x := by
    calc
      a x • e 1 = e (a x • (1 : K)) := (e.map_smul _ _).symm
      _ = e (a x) := by rw [smul_eq_mul, mul_one]
      _ = T.rangeRestrict x := e.apply_symm_apply _
  exact (congrArg Subtype.val h).symm

theorem rank_one_iff_exists_smulRight (T : X →ₗ[K] Y) :
    Module.finrank K T.range = 1 ↔
      ∃ (a : X →ₗ[K] K) (l : Y), a ≠ 0 ∧ l ≠ 0 ∧ T = a.smulRight l := by
  constructor
  · exact exists_smulRight_of_rank_one T
  · rintro ⟨a, l, ha, hl, rfl⟩
    rw [LinearMap.range_smulRight_apply ha]
    exact finrank_span_singleton hl

end ArbitraryField

variable {X Y : Type*}
  [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

theorem binary_smulRight_unique
    {a b : X →ₗ[ZMod 2] ZMod 2} {l k : Y}
    (ha : a ≠ 0) (hl : l ≠ 0)
    (h : a.smulRight l = b.smulRight k) : a = b ∧ l = k := by
  obtain ⟨x, hx⟩ := a.surjective ha 1
  have hx' : l = b x • k := by
    simpa only [LinearMap.smulRight_apply, hx, one_smul] using
      LinearMap.congr_fun h x
  have scalar_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hlk : l = k := by
    rcases scalar_cases (b x) with hb | hb
    · exact False.elim (hl (by simpa only [hb, zero_smul] using hx'))
    · simpa only [hb, one_smul] using hx'
  refine ⟨?_, hlk⟩
  apply LinearMap.ext
  intro y
  apply smul_left_injective (ZMod 2) hl
  have hy := LinearMap.congr_fun h y
  simpa only [LinearMap.smulRight_apply, ← hlk] using hy

abbrev BinaryRankOneFactors (X Y : Type*)
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] :=
  {a : X →ₗ[ZMod 2] ZMod 2 // a ≠ 0} × {l : Y // l ≠ 0}

abbrev BinaryRankOneMaps (X Y : Type*)
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] :=
  {T : X →ₗ[ZMod 2] Y // Module.finrank (ZMod 2) T.range = 1}

def binaryRankOneMap (p : BinaryRankOneFactors X Y) : BinaryRankOneMaps X Y :=
  ⟨p.1.val.smulRight p.2.val,
    (rank_one_iff_exists_smulRight _).mpr
      ⟨p.1.val, p.2.val, p.1.property, p.2.property, rfl⟩⟩

theorem binary_smulRight_injective :
    Function.Injective (binaryRankOneMap (X := X) (Y := Y)) := by
  intro p q h
  obtain ⟨ha, hl⟩ := binary_smulRight_unique p.1.property p.2.property
    (congrArg Subtype.val h)
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hl)

theorem binary_smulRight_surjective :
    Function.Surjective (binaryRankOneMap (X := X) (Y := Y)) := by
  intro T
  obtain ⟨a, l, ha, hl, h⟩ := exists_smulRight_of_rank_one T.val T.property
  exact ⟨(⟨a, ha⟩, ⟨l, hl⟩), Subtype.ext h.symm⟩

noncomputable def binaryRankOneEquiv :
    BinaryRankOneFactors X Y ≃ BinaryRankOneMaps X Y :=
  Equiv.ofBijective binaryRankOneMap
    ⟨binary_smulRight_injective, binary_smulRight_surjective⟩

@[simp] theorem binaryRankOneEquiv_apply (p : BinaryRankOneFactors X Y) :
    (binaryRankOneEquiv p).val = p.1.val.smulRight p.2.val := rfl

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.KMSBasisComparison

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

abbrev FixedFunctionalNeighborFiber (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (y₀ : F) :=
  {y : F // y ∉ X.range ∧
    (X + a.smulRight y).range = (X + a.smulRight y₀).range}

theorem add_image_not_mem_range (X : E →ₗ[ZMod 2] F)
    {y : F} (hy : y ∉ X.range) (z : E) : y + X z ∉ X.range := by
  intro h
  exact hy (by simpa using X.range.sub_mem h (X.mem_range_self z))

theorem range_update_add_kernel (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (y : F) (z : a.ker) :
    (X + a.smulRight (y + X z)).range = (X + a.smulRight y).range := by
  have hz : a z = 0 := z.property
  have hforward (x : E) :
      (X + a.smulRight (y + X z)) x =
        (X + a.smulRight y) (x + a x • z) := by
    simp [hz, smul_add] ; abel
  have hbackward (x : E) :
      (X + a.smulRight y) x =
        (X + a.smulRight (y + X z)) (x - a x • z) := by
    simp [hz, smul_add]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨x + a x • z, (hforward x).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨x - a x • z, (hbackward x).symm⟩

def fixedFunctionalFiberMap (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    a.ker → FixedFunctionalNeighborFiber X a y₀ :=
  fun z => ⟨y₀ + X z, add_image_not_mem_range X hy₀ z,
    range_update_add_kernel X a y₀ z⟩

theorem fixedFunctionalFiberMap_injective (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Function.Injective (fixedFunctionalFiberMap X a hy₀) := by
  intro z w h
  apply Subtype.ext
  apply hX
  exact add_left_cancel (congrArg Subtype.val h)

theorem fixedFunctionalFiberMap_surjective (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0)
    {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Function.Surjective (fixedFunctionalFiberMap X a hy₀) := by
  intro y
  obtain ⟨x, hx⟩ := a.surjective ha 1
  have hmem : X x + y.val ∈ (X + a.smulRight y₀).range := by
    exact y.property.2.le ⟨x, by simp [hx]⟩
  obtain ⟨t, ht⟩ := hmem
  have hbinary : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hat : a t = 1 := by
    rcases hbinary (a t) with hat | hat
    · have he : X t = X x + y.val := by simpa [hat] using ht
      have hy : y.val = X (t - x) := by
        rw [map_sub, he]
        abel
      exact False.elim (y.property.1 ⟨t - x, hy.symm⟩)
    · exact hat
  have hz : t - x ∈ a.ker := by
    change a (t - x) = 0
    simp [hat, hx]
  refine ⟨⟨t - x, hz⟩, ?_⟩
  apply Subtype.ext
  change y₀ + X (t - x) = y.val
  have he : X t + y₀ = X x + y.val := by simpa [hat] using ht
  calc
    y₀ + X (t - x) = (X t + y₀) - X x := by rw [map_sub]; abel
    _ = y.val := by rw [he]; abel

def fixedFunctionalNeighborFiberEquiv (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    a.ker ≃ FixedFunctionalNeighborFiber X a y₀ :=
  Equiv.ofBijective (fixedFunctionalFiberMap X a hy₀)
    ⟨fixedFunctionalFiberMap_injective X hX a hy₀,
      fixedFunctionalFiberMap_surjective X a ha hy₀⟩

end
end DFVSGames.Inverse.KMSBasisComparison

namespace DFVSGames.Inverse.KMSBasisComparison

variable {E F : Type*}
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

theorem binary_functional_eq_of_ker_eq
    {a b : E →ₗ[ZMod 2] ZMod 2} (h : a.ker = b.ker) : a = b := by
  have scalar_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  apply LinearMap.ext
  intro x
  have hzero : a x = 0 ↔ b x = 0 := by
    change x ∈ a.ker ↔ x ∈ b.ker
    rw [h]
  rcases scalar_cases (a x) with ha | ha
  · exact ha.trans (hzero.mp ha).symm
  · rcases scalar_cases (b x) with hb | hb
    · exact False.elim (zero_ne_one ((hzero.mpr hb).symm.trans ha))
    · exact ha.trans hb.symm

theorem binary_functional_eq_of_map_ker_eq
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    {a b : E →ₗ[ZMod 2] ZMod 2}
    (h : a.ker.map X = b.ker.map X) : a = b := by
  exact binary_functional_eq_of_ker_eq (Submodule.map_injective_of_injective hX h)

end DFVSGames.Inverse.KMSBasisComparison

namespace DFVSGames.Inverse.KMSBasisComparison

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

abbrev OutsideNeighborFactors (X : E →ₗ[ZMod 2] F) :=
  {a : E →ₗ[ZMod 2] ZMod 2 // a ≠ 0} × {y : F // y ∉ X.range}

abbrev OutsideNeighborPairFiber (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (y : F) :=
  {p : OutsideNeighborFactors X //
    (rankOneUpdate X p.1.val p.2.val).range = (rankOneUpdate X a y).range}

theorem functional_eq_of_update_range_eq (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) {a b : E →ₗ[ZMod 2] ZMod 2}
    {y z : F} (hy : y ∉ X.range) (hz : z ∉ X.range)
    (h : (rankOneUpdate X a y).range = (rankOneUpdate X b z).range) :
    a = b := by
  apply binary_functional_eq_of_map_ker_eq X hX
  rw [← range_inf_rankOneUpdate X a hy, ← range_inf_rankOneUpdate X b hz, h]

def fixedToPairFiber (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0) (y₀ : F) :
    FixedFunctionalNeighborFiber X a y₀ → OutsideNeighborPairFiber X a y₀ :=
  fun y => ⟨(⟨a, ha⟩, ⟨y.val, y.property.1⟩), y.property.2⟩

theorem fixedToPairFiber_injective (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0) (y₀ : F) :
    Function.Injective (fixedToPairFiber X a ha y₀) := by
  intro y z h
  apply Subtype.ext
  exact congrArg (fun p => p.val.2.val) h

theorem fixedToPairFiber_surjective (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Function.Surjective (fixedToPairFiber X a ha y₀) := by
  intro p
  have haeq : p.val.1.val = a :=
    functional_eq_of_update_range_eq X hX p.val.2.property hy₀ p.property
  have he : (X + a.smulRight p.val.2.val).range =
      (X + a.smulRight y₀).range := by
    simpa only [rankOneUpdate, haeq] using p.property
  refine ⟨⟨p.val.2.val, p.val.2.property, he⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext haeq.symm
  · rfl

def fixedFunctionalEquivPairFiber (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    FixedFunctionalNeighborFiber X a y₀ ≃ OutsideNeighborPairFiber X a y₀ :=
  Equiv.ofBijective (fixedToPairFiber X a ha y₀)
    ⟨fixedToPairFiber_injective X a ha y₀,
      fixedToPairFiber_surjective X hX a ha hy₀⟩

end
end DFVSGames.Inverse.KMSBasisComparison

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSBasisComparisonFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

section UniformFibers

variable {X Y G : Type*}

def fiberProductEquiv (f : X → Y) (e : ∀ y, {x : X // f x = y} ≃ G) : X ≃ Y × G :=
  (Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaEquivProdOfEquiv e)

@[simp] theorem fiberProductEquiv_fst (f : X → Y)
    (e : ∀ y, {x : X // f x = y} ≃ G) (x : X) :
    (fiberProductEquiv f e x).1 = f x := rfl

end UniformFibers

section LinearFibers

variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

def RangeFiber (L : Submodule K F) :=
  {X : E →ₗ[K] F // Function.Injective X ∧ LinearMap.range X = L}

def rangeFiberEquiv (L : Submodule K F) : RangeFiber (E := E) L ≃ (E ≃ₗ[K] L) where
  toFun X := LinearEquiv.ofBijective
    (X.val.codRestrict L (fun x =>
      X.property.2.le (LinearMap.mem_range_self X.val x)))
    ⟨fun _ _ h => X.property.1 (congrArg Subtype.val h), by
      intro y
      have hy : (y : F) ∈ LinearMap.range X.val := X.property.2.ge y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩
  invFun e := ⟨L.subtype.comp e.toLinearMap,
    (Submodule.subtype_injective L).comp e.injective, by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact (e x).property
      · intro hy
        obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
        exact ⟨x, congrArg Subtype.val hx⟩⟩
  left_inv X := by
    apply Subtype.ext
    ext x
    rfl
  right_inv e := by
    ext x
    rfl

def rangeFiberEquivAut {L : Submodule K F} (e : E ≃ₗ[K] L) :
    RangeFiber (E := E) L ≃ (E ≃ₗ[K] E) :=
  (rangeFiberEquiv L).trans
    { toFun := fun a => a.trans e.symm
      invFun := fun a => a.trans e
      left_inv := by intro a; ext x; simp
      right_inv := by intro a; ext x; simp }

end LinearFibers

end
end DFVSGames.Inverse.KMSBasisComparison

namespace DFVSGames.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

variable {E F : Type*}
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]
  [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) F]

def outsideNeighborSample (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    (p : OutsideNeighborFactors X) : MatrixChart.GrassmannNeighbors X.range :=
  rankOneUpdateNeighbor X hX p.1.val p.1.property p.2.val p.2.property

omit [FiniteDimensional (ZMod 2) F] in
@[simp] theorem outsideNeighborSample_val (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (p : OutsideNeighborFactors X) :
    (outsideNeighborSample X hX p).val =
      (rankOneUpdate X p.1.val p.2.val).range := rfl

end
end DFVSGames.Inverse.KMSBasisComparison

namespace DFVSGames.Inverse.MatrixChart

variable {X Y : Type*}
  [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]
  [FiniteDimensional (ZMod 2) X]

abbrev BinaryChartNeighbors (T : X →ₗ[ZMod 2] Y) :=
  {U : X →ₗ[ZMod 2] Y //
    Module.finrank (ZMod 2) (T.graph ⊓ U.graph : Submodule (ZMod 2) (X × Y)) + 1 =
      Module.finrank (ZMod 2) X}

abbrev BinaryGraphChartNeighbors (T : X →ₗ[ZMod 2] Y) :=
  {L : Submodule (ZMod 2) (X × Y) //
    (∃ U : X →ₗ[ZMod 2] Y, L = U.graph) ∧
      Module.finrank (ZMod 2) (T.graph ⊓ L : Submodule (ZMod 2) (X × Y)) + 1 =
        Module.finrank (ZMod 2) X}

def rankOneEquivChartNeighbors (T : X →ₗ[ZMod 2] Y) :
    BinaryRankOneMaps X Y ≃ BinaryChartNeighbors T where
  toFun D := ⟨T - D.val, (adjacent_iff_rank_one T (T - D.val)).mpr (by
    have he : T - (T - D.val) = D.val := by
      exact sub_sub_cancel T _
    rw [he]
    exact D.property)⟩
  invFun U := ⟨T - U.val, (adjacent_iff_rank_one T U.val).mp U.property⟩
  left_inv D := by
    apply Subtype.ext
    change T - (T - D.val) = D.val
    exact sub_sub_cancel T _
  right_inv U := by
    apply Subtype.ext
    change T - (T - U.val) = U.val
    exact sub_sub_cancel T _

def graphChartNeighbor (T : X →ₗ[ZMod 2] Y)
    (U : BinaryChartNeighbors T) : BinaryGraphChartNeighbors T :=
  ⟨U.val.graph, ⟨U.val, rfl⟩, U.property⟩

omit [FiniteDimensional (ZMod 2) X] in
theorem graphChartNeighbor_injective (T : X →ₗ[ZMod 2] Y) :
    Function.Injective (graphChartNeighbor T) := by
  intro U V h
  apply Subtype.ext
  exact graph_injective (congrArg Subtype.val h)

omit [FiniteDimensional (ZMod 2) X] in
theorem graphChartNeighbor_surjective (T : X →ₗ[ZMod 2] Y) :
    Function.Surjective (graphChartNeighbor T) := by
  intro L
  obtain ⟨U, hU⟩ := L.property.1
  have h :
      Module.finrank (ZMod 2) (T.graph ⊓ U.graph : Submodule (ZMod 2) (X × Y)) + 1 =
        Module.finrank (ZMod 2) X := by
    rw [← hU]
    exact L.property.2
  exact ⟨⟨U, h⟩, Subtype.ext hU.symm⟩

noncomputable def chartNeighborsEquivGraphNeighbors (T : X →ₗ[ZMod 2] Y) :
    BinaryChartNeighbors T ≃ BinaryGraphChartNeighbors T :=
  Equiv.ofBijective (graphChartNeighbor T)
    ⟨graphChartNeighbor_injective T, graphChartNeighbor_surjective T⟩

noncomputable def binaryFactorsEquivGraphNeighbors (T : X →ₗ[ZMod 2] Y) :
    BinaryRankOneFactors X Y ≃ BinaryGraphChartNeighbors T :=
  binaryRankOneEquiv.trans
    ((rankOneEquivChartNeighbors T).trans (chartNeighborsEquivGraphNeighbors T))

@[simp] theorem binaryFactorsEquivGraphNeighbors_apply (T : X →ₗ[ZMod 2] Y)
    (p : BinaryRankOneFactors X Y) :
    (binaryFactorsEquivGraphNeighbors T p).val =
      (T - p.1.val.smulRight p.2.val).graph := rfl

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

open Module

variable {ell m : ℕ}

abbrev CoordinateMatrix (ell m : ℕ) :=
  (Fin ell → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

open Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

abbrev matrixGraph (M : Matrix ι κ K) : Submodule K ((ι → K) × (κ → K)) :=
  M.vecMulLinear.graph

omit [Fintype κ] in
@[simp] theorem mem_matrixGraph (M : Matrix ι κ K) (x : ι → K) (y : κ → K) :
    (x, y) ∈ matrixGraph M ↔ y = M.transpose *ᵥ x := by
  rw [Matrix.mulVec_transpose]
  rfl

omit [Fintype κ] in
theorem matrixGraph_injective : Function.Injective (matrixGraph (K := K) (ι := ι) (κ := κ)) := by
  classical
  intro M N h
  have hh : M.vecMulLinear = N.vecMulLinear := graph_injective h
  exact (LinearMap.toMatrixRight' (R := K)).symm.injective hh

abbrev dotFunctional (x : ι → K) : (ι → K) →ₗ[K] K := dotProductBilin K K x

theorem dotFunctional_injective : Function.Injective (dotFunctional (K := K) (ι := ι)) := by
  intro x y h
  apply dotProduct_eq x y
  intro z
  exact congrArg (fun f : (ι → K) →ₗ[K] K => f z) h

omit [Fintype κ] in

theorem finrank_matrixGraph (M : Matrix ι κ K) :
    Module.finrank K (matrixGraph M) = Fintype.card ι := by
  rw [finrank_graph]
  simp

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

open Matrix

def coordinateJoin (K : Type*) [Field K] (ell m : Nat) :
    ((Fin ell → K) × (Fin m → K)) ≃ₗ[K] (Fin (ell + m) → K) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin ell) (Fin m) K K).symm.trans
    (LinearEquiv.funCongrLeft K K finSumFinEquiv.symm)

end DFVSGames.Inverse.MatrixChart

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSBasisComparisonRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.MatrixChart

open Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

theorem dotFunctional_surjective :
    Function.Surjective (dotFunctional (K := K) (ι := ι)) := by
  classical
  intro f
  refine ⟨fun i => f (Pi.single i 1), ?_⟩
  apply (Pi.basisFun K ι).ext
  intro i
  change (fun j => f (Pi.single j 1)) ⬝ᵥ (Pi.basisFun K ι i) =
    f (Pi.basisFun K ι i)
  simp

end DFVSGames.Inverse.MatrixChart

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_EqualityFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.EqualityFiber

noncomputable section

open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

def fiberMass (p : X → ℝ) (f : X → Y) (y : Y) : ℝ := by
  classical
  exact ∑ x, if f x = y then p x else 0

def fiberFlow (p : X → ℝ) (k : X → X → ℝ) (f : X → Y) (y : Y) : ℝ := by
  classical
  exact ∑ x, p x * ∑ x', k x x' * if f x = y ∧ f x' = y then 1 else 0

def equalityAcceptance (p : X → ℝ) (k : X → X → ℝ) (f : X → Y) : ℝ := by
  classical
  exact ∑ x, p x * ∑ x', k x x' * if f x = f x' then 1 else 0

end
end DFVSGames.Inverse.EqualityFiber

end OAI
end


