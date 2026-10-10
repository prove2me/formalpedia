-- Prove2me | Definitions.Def_OAIErdos3B134
-- name    : OAIErdos3B134
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T13:05:16.680369+00:00
-- url     : https://prove2.me/theorems/35434463-65ab-4989-a3a4-063aa80f7e83
-- title:
--   OpenAI Erdős-3 split, definitions bundle 135 of 136
-- statement:
--   Definitions bundle 135 of 136 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B133`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 135 available.
--
--   Modules: `OAI.Erdos3.ActiveProfileCoefficientIndex`, `OAI.Erdos3.PartitionedProfileNoiseIndex`, `OAI.Erdos3.SamplerCoefficientSlot`, `OAI.Erdos3.VectorPolynomial.AllocatedFrozenJetRows`, `OAI.Erdos3.VectorPolynomial.AllocatedFrozenSupported`, `OAI.Erdos3.VectorPolynomial.AllocatedLongJetRows`, `OAI.Erdos3.VectorPolynomial.AllocatedNonkernelCoefficient`, `OAI.Erdos3.VectorPolynomial.NonkernelCoefficient`, `OAI.Erdos3.VectorPolynomial.allocatedContinuousKernelDensity`, `OAI.Erdos3.VectorPolynomial.allocatedContinuousProfileCenters`, `OAI.Erdos3.VectorPolynomial.allocatedContinuousProfileScales`, `OAI.Erdos3.VectorPolynomial.allocatedContinuousProfileWidths`, `OAI.Erdos3.VectorPolynomial.allocatedFrozenBlockPMF`, `OAI.Erdos3.VectorPolynomial.allocatedFrozenJetMap`, `OAI.Erdos3.VectorPolynomial.allocatedFrozenJetReference`, `OAI.Erdos3.VectorPolynomial.allocatedFrozenJetReference_sigmaFinite`, `OAI.Erdos3.VectorPolynomial.allocatedGridJetDensity`, `OAI.Erdos3.VectorPolynomial.allocatedGridJetFactor`, `OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelDensity`, `OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelMask`, `OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelPMF`, `OAI.Erdos3.VectorPolynomial.allocatedKernelCoefficientEquiv`, `OAI.Erdos3.VectorPolynomial.allocatedLongJetDensity`, `OAI.Erdos3.VectorPolynomial.allocatedLongJetFactor`, `OAI.Erdos3.VectorPolynomial.allocatedLongJetMap`, `OAI.Erdos3.VectorPolynomial.allocatedLongJetReference`, `OAI.Erdos3.VectorPolynomial.allocatedLongJetReference_sigmaFinite`, `OAI.Erdos3.VectorPolynomial.allocatedNonkernelExponent`, `OAI.Erdos3.VectorPolynomial.allocatedNonkernelJetMatrix`, `OAI.Erdos3.VectorPolynomial.allocatedPartitionedJetMatrix`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalCubeDirections`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalCubeRoot`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalLongJetMap`, `OAI.Erdos3.VectorPolynomial.allocatedPrincipalSides_le_scale`, `OAI.Erdos3.VectorPolynomial.allocatedTranslatedPartitionedJetMatrix`, `OAI.Erdos3.VectorPolynomial.kernelCoefficientEquiv`, `OAI.Erdos3.VectorPolynomial.kernelExponentEmbedding`, `OAI.Erdos3.allocatedUnitProfileWidth`, `OAI.Erdos3.kernelCubeBox_site_le_exp`, `OAI.Erdos3.partitionedAllocatedProfileJet`, `OAI.Erdos3.partitionedIdealMap`, `OAI.Erdos3.partitionedProfileConstant`, `OAI.Erdos3.partitionedProfileInput`, `OAI.Erdos3.partitionedProfileJet`, `OAI.Erdos3.partitionedProfilePrincipal`, `OAI.Erdos3.partitionedProfileTerms`, `OAI.Erdos3.principalAxisResidueJoin`, `OAI.Erdos3.profileNoiseWithActive`, `OAI.Erdos3.translatedIntegerMappedJetMatrix`, `OAI.Erdos3.unitProfilePrincipalLowerBound`, `OAI.Erdos3.unitProfilePrincipalLowerBound_pos`, `OAI.Erdos3.unitProfilePrincipalSize`, `OAI.Erdos3.unitProfileTailSize`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B133

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveProfileNoise
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {D G : Type*} [Fintype D] [Fintype G] {B : D → Type*}
variable [∀ d, Fintype (B d)] (h : D → ℕ) (d : D)

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

abbrev SamplerCoefficientSlot {D : Type*} (G : Type*) (B : D → Type*)
    (h : D → ℕ) (d : D) := BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)

abbrev PartitionedProfileNoiseIndex {D : Type*} (G Z α : Type*) (B : D → Type*)
    (h : D → ℕ) (P : D → Prop) :=
  (Z ⊕ PrincipalAxisParameter (B := B) (h := h) (α := α) P) ⊕
    (Σ d, SamplerCoefficientSlot G B h d)

def partitionedProfileInput {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}
    (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
    (k : SamplerTupleIndex G B h) (a : Option α) :
    PartitionedProfileNoiseIndex G Z α B h P ⊕
      PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) :=
  Sum.map Sum.inl id (partitionedPrincipalInput P extra k a)

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
variable {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)

noncomputable def partitionedProfilePrincipal (γ : D → ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (d : {d // ¬P d}) (b : B d.val) : ℝ :=
  3 * γ d.val / 2 + γ d.val / 2 * y (.inr ⟨d.val, principalCoefficientSlot h d.val b⟩)

noncomputable def partitionedProfileConstant (ρ : D → ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ) (d : {d // ¬P d}) : ℝ :=
  ρ d.val * y (.inr ⟨d.val, constantCoefficientSlot _ _⟩)

noncomputable def partitionedProfileTerms (d : {d // ¬P d}) :
    Finset (SamplerCoefficientSlot G B h d.val) :=
  nonprincipalCoefficientSlots Subtype.val (canonicalPrincipalExponent h d.val)

noncomputable def partitionedProfileJet (ρ γ ε : D → ℝ) (t : ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (o : Σ d, O d) : ℝ :=
  booleanCoefficient (fun s => MvPolynomial.eval
    (normalizedCubeTuple (partitionedProfileInput P extra) y x s)
    (monomialArrayPolynomial Subtype.val (fun e : SamplerCoefficientSlot G B h o.1.val =>
      coefficientProfileCenter (principalCoefficientSlots h o.1.val) (γ o.1.val) e +
        coefficientProfileWidth (principalCoefficientSlots h o.1.val) (constantCoefficientSlot _ _)
          (ρ o.1.val) (γ o.1.val) (t * ε o.1.val) e * y (.inr ⟨o.1.val, e⟩)))) (sets o.1 o.2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
variable {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)

noncomputable def unitProfilePrincipalSize (d : D) : ℝ :=
  principalProfileSize 1 (Fintype.card (B d))

noncomputable def unitProfileTailSize (d : D) : ℝ :=
  tailProfileSize 1 1 (Fintype.card (SamplerCoefficientSlot G B h d))

noncomputable def partitionedAllocatedProfileJet (R : D → ℝ) (t : ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    (Σ d, O d) → ℝ :=
  partitionedProfileJet h P extra sets (fun d => R d / 4)
    (fun d => principalProfileSize (R d) (Fintype.card (B d)))
    (fun d => tailProfileSize (R d) 1 (Fintype.card (SamplerCoefficientSlot G B h d))) t y x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D : Type*} [Fintype D] (B : D → Type*) [∀ d, Fintype (B d)]

noncomputable def unitProfilePrincipalLowerBound : ℝ :=
  1 / (8 * (((∑ d, Fintype.card (B d) : ℕ) : ℝ) + 1))

theorem unitProfilePrincipalLowerBound_pos : 0 < unitProfilePrincipalLowerBound B := by
  unfold unitProfilePrincipalLowerBound
  positivity

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)]
  (sets : ∀ d, O d → Finset α)

noncomputable def partitionedIdealMap
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    (Σ d, O d) → ℝ :=
  booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) y) +
    jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
      (partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y) sets x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

abbrev ActiveProfileCoefficientIndex {D : Type*} (G : Type*) (B : D → Type*)
    (h : D → ℕ) (P : D → Prop) := Σ d : {d // ¬P d}, SamplerCoefficientSlot G B h d.val

def profileNoiseWithActive {D G Z α : Type*} {B : D → Type*}
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) :
    PartitionedProfileNoiseIndex G Z α B h P → ℝ
  | .inl j => z (.inl j)
  | .inr ⟨d, e⟩ => if hp : P d then z (.inr ⟨d, e⟩) else r ⟨⟨d, hp⟩, e⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalJoinedResidues
namespace OAI

section

namespace Erdos3

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}

def principalAxisResidueJoin (P : D → Prop) [DecidablePred P]
    {L : PrincipalTupleIndex B h → ℕ} (u : PrincipalAxisTuples (α := α) P L) (m : ℕ)
    (r : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) → Option α → ZMod m) :
    PrincipalTupleIndex B h → Option α → ZMod m :=
  fun j i => if hp : P j.1 then ((u ⟨⟨j.1, hp⟩, j.2⟩ i : ℤ) : ZMod m)
    else r ⟨⟨j.1, hp⟩, j.2⟩ i

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialChoiceEnvelope
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

namespace VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {D N : Type*} [Fintype D] [Fintype N]
variable (c : D → N → ℤ) (index : D → N → PrincipalTupleIndex B (layerSamplerDegree I n))

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable (x : G → IntegerScalarCubeBox α S.value) (root : G → ℤ)
variable (selection : α ↪ G)
variable (hP : (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection).det ≠ 0)
variable (H : D → ℝ) (Q : D → N → ℝ) (hH : ∀ d, 0 < H d) (hQ : ∀ d j, 0 < Q d j)

variable [DecidableEq G]

variable [DecidableEq N]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedPrincipalSides_le_scale (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
    allocatedPrincipalSides B U basis S j ≤ S.value :=
  layerSamplerSides_le (G := G) B U basis R S.positive (.inr j)

variable {D N : Type*} [Fintype D] [Fintype N]
variable (c : D → N → ℤ) (index : D → N → PrincipalTupleIndex B (layerSamplerDegree I n))

variable {α : Type*} [Fintype α] (selection : α ↪ G) (M : ℕ) (τ : ℝ)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

noncomputable def allocatedPhysicalCubeRoot : LayerSamplerVariables G I n B → ℤ :=
  fun k => c k + Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) k

noncomputable def allocatedPhysicalCubeDirections : Matrix α (LayerSamplerVariables G I n B) ℤ :=
  fun i => Sum.elim (fun g => (x g (some i) : ℤ)) (fun j => (y j (some i) : ℤ))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators

theorem kernelCubeBox_site_le_exp {G : Type*} {q L : ℕ}
    (c : G → ℤ) (x : G → IntegerScalarCubeBox (Fin q) L) {P : ℝ}
    (hc : ∀ g, |(c g : ℝ)| ≤ Real.exp P) (hL : (L : ℝ) ≤ Real.exp P)
    (s : Finset (Fin q)) (g : G) :
    |((BooleanCubeKernel.affineSite (fun g => c g + (x g none : ℤ))
      (fun i g => (x g (some i) : ℤ)) s (some g) : ℤ) : ℝ)| ≤ Real.exp (P + (q + 2 : ℕ)) := by
  have hx (i) : |((x g i : ℤ) : ℝ)| ≤ Real.exp P := by
    have hi := Finset.mem_Ico.mp (x g i).property
    have hl : |((x g i : ℤ) : ℝ)| ≤ L := by exact_mod_cast abs_le.mpr ⟨hi.1, hi.2.le⟩
    exact hl.trans hL
  have hs : (s.card : ℝ) ≤ q := by
    exact_mod_cast (show s.card ≤ q from by simpa only [Fintype.card_fin] using s.card_le_univ)
  have hsum : |∑ i ∈ s, ((x g (some i) : ℤ) : ℝ)| ≤ (q : ℝ) * Real.exp P := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i ∈ s, Real.exp P := Finset.sum_le_sum (fun i _ => hx (some i))
      _ = (s.card : ℝ) * Real.exp P := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hs (Real.exp_nonneg P)
  have hraw : |(c g : ℝ) + ((x g none : ℤ) : ℝ) + ∑ i ∈ s, ((x g (some i) : ℤ) : ℝ)| ≤
      ((q : ℝ) + 2) * Real.exp P := by
    have h := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (hc g) (hx none))) hsum)
    nlinarith
  calc
    _ = |(c g : ℝ) + ((x g none : ℤ) : ℝ) + ∑ i ∈ s, ((x g (some i) : ℤ) : ℝ)| := by
      simp only [BooleanCubeKernel.affineSite, Int.cast_add, Int.cast_sum]
    _ ≤ ((q : ℝ) + 2) * Real.exp P := hraw
    _ ≤ Real.exp ((q : ℝ) + 2) * Real.exp P := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg P)
      linarith [Real.add_one_le_exp ((q : ℝ) + 2)]
    _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

namespace VectorPolynomial

open BooleanCubeKernel Polynomial

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

noncomputable def kernelExponentEmbedding (G X : Type*) (h : ℕ) :
    BoundedIntegerExponent G h ↪ BoundedCoefficientExponent (G ⊕ X) h where
  toFun d := ⟨d.val.embDomain Function.Embedding.inl, by
    change (d.val.embDomain Function.Embedding.inl).sum (fun _ n => n) ≤ h
    rw [Finsupp.sum_embDomain]
    exact d.property⟩
  inj' := by
    intro d e hde
    exact Subtype.ext ((Finsupp.embDomain_injective Function.Embedding.inl) (congrArg Subtype.val hde))

abbrev NonkernelCoefficient (G X : Type*) (h : ℕ) :=
  UnselectedColumn (kernelExponentEmbedding G X h)

noncomputable def kernelCoefficientEquiv (G X : Type*) [Fintype G] (h : ℕ) :
    BoundedIntegerExponent G h ⊕ NonkernelCoefficient G X h ≃ BoundedCoefficientExponent (G ⊕ X) h :=
  selectedColumnEquiv (kernelExponentEmbedding G X h)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

abbrev AllocatedNonkernelCoefficient (j : Fin m) :=
  NonkernelCoefficient G (PrincipalTupleIndex B (layerSamplerDegree I n)) (j.val+1)

noncomputable def allocatedKernelCoefficientEquiv (j : Fin m) :
    BoundedIntegerExponent G (j.val+1) ⊕ AllocatedNonkernelCoefficient (G := G) B j ≃
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) :=
  kernelCoefficientEquiv G (PrincipalTupleIndex B (layerSamplerDegree I n)) (j.val+1)

def allocatedNonkernelExponent (j : Fin m) (d : AllocatedNonkernelCoefficient (G := G) B j) :
    LayerSamplerVariables G I n B →₀ ℕ := d.val.val

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "scales" => allocatedIntegerProfileScales B U basis S j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedContinuousProfileCenters (R : Fin m → ℝ) (j : Fin m) (i : I j) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  coefficientProfileCenter (layerContinuousPrincipalSlots B j i)
    (principalProfileSize (R j) (layerContinuousPrincipalSlots (G := G) B j i).card)

noncomputable def allocatedContinuousProfileWidths (R σ : Fin m → ℝ) (j : Fin m) (i : I j) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  coefficientProfileWidth (layerContinuousPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (R j/4) (principalProfileSize (R j) (layerContinuousPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def allocatedContinuousProfileScales (j : Fin m) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  fun d => 1 / monomialScale (layerSamplerBox B U basis S) d.val

variable (j : Fin m) (i : I j)

local notation "centers" => allocatedContinuousProfileCenters (G := G) B R j i
local notation "widths" => allocatedContinuousProfileWidths (G := G) B R σ j i
local notation "scales" => allocatedContinuousProfileScales B U basis S j
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) 1

noncomputable def allocatedContinuousKernelDensity
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (O → ℝ) → ℝ :=
  affineSelectedJetDensity s
    (normalizedPivotEquiv ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s) hA
      (fun o => kernelScale (s o)) (fun _ => 1)
      (fun o => kernelJetCoefficientScale_pos G (j.val+1) (by exact_mod_cast S.positive) zero_lt_one (s o))
      (fun _ => zero_lt_one))
    (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
      (fun d => kernelScale d.val) (fun _ => 1)))
    (allocatedNonkernelExponent B j) input fixedReal rows (centers ∘ reindex) (widths ∘ reindex) y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators Matrix Classical

noncomputable def allocatedUnitProfileWidth (R σ : ℝ) (a : ℕ) : ℝ :=
  allocatedWidthFloor R σ 1 0 a

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : I j)

local notation "unitWidth" => allocatedUnitProfileWidth (R j) (σ j)
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))

local notation "centers" => allocatedContinuousProfileCenters (G := G) B R j i
local notation "widths" => allocatedContinuousProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) 1
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => kernelScale (s o)) (fun _ => 1)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1)
    (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) zero_lt_one (s o))
  (fun _ => zero_lt_one)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => kernelScale (Subtype.val d)) (fun _ => 1))
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedIntegerKernelComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)

noncomputable def allocatedPartitionedJetMatrix (j : Fin m) :
    Matrix (O j) (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) ℤ :=
  integerMappedJetMatrix Subtype.val input fixedInteger (rows j) (principalTupleIntegers v)

noncomputable def allocatedIntegerKernelPMF (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
    (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i) : PMF (O j → ℤ) :=
  (allocatedEnormousProfilePMF B U basis hR hσ S j i hσ1 henormous).map
    (fun a => allocatedPartitionedJetMatrix B U basis S x u v rows j *ᵥ a)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "scales" => allocatedIntegerProfileScales B U basis S j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))

local notation "unitWidth" => allocatedUnitProfileWidth (R j) (σ j)
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "height" => (basisAxisScale (basis j) i : ℝ)
local notation "heightPos" => Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) height
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => kernelScale (s o)) (fun _ => height)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1)
    (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) heightPos (s o))
  (fun _ => heightPos)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => kernelScale (Subtype.val d)) (fun _ => height))
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))

noncomputable def allocatedIntegerKernelDensity
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (O → ℝ) → ℝ :=
  affineSelectedJetDensity s pivot free (allocatedNonkernelExponent B j) input fixedReal rows
    (centers ∘ reindex) (widths ∘ reindex) y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

end Erdos3

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α) (j : Fin m)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)

noncomputable def allocatedNonkernelJetMatrix
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) ℤ :=
  integerMappedJetMatrix (allocatedNonkernelExponent B j) input fixedInteger (rows j)
    (principalTupleIntegers v)

noncomputable def allocatedIntegerKernelMask (modulus : ℕ)
    (residue : Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)) :
    (O j → ℤ) → ℝ :=
  coefficientResidueMultiplier (scalarKernelIntegerJet x (j.val+1) (rows j)) residue

variable (i : Fin (n j)) (s : O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id s).det ≠ 0)
variable (hσ1 : σ j ≤ 1) (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "height" => (basisAxisScale (basis j) i : ℝ)
local notation "heightPos" => Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) height
local notation "nonkernelScale" => fun d => height / monomialScale (layerSamplerBox B U basis S)
  (allocatedNonkernelExponent B j d)
local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j
local notation "unitWidth" => allocatedUnitProfileWidth (R j) (σ j)
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable [DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedLongJetMixture
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

abbrev AllocatedLongJetRows (O : Fin m → Type*) :=
  ∀ a : {a // ¬grid a}, CoefficientJetAxisRow O a.val

noncomputable def allocatedLongJetReference (O : Fin m → Type*) [∀ j, Fintype (O j)] :
    Measure (AllocatedLongJetRows B U basis S O) :=
  Measure.pi (fun a : {a // ¬grid a} => coefficientJetAxisReference O a.val)

instance allocatedLongJetReference_sigmaFinite (O : Fin m → Type*) [∀ j, Fintype (O j)] :
    SigmaFinite (allocatedLongJetReference B U basis S O) := by
  unfold allocatedLongJetReference
  infer_instance

variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

noncomputable def allocatedLongJetMap (c : AllocatedLongCoefficients B U basis S) :
    AllocatedLongJetRows B U basis S O :=
  fun a => coefficientJetAxisMap (allocatedPartitionedJetMatrix B U basis S x u v rows) a.val (c a)

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

noncomputable def allocatedLongJetFactor :
    ∀ a : {a // ¬grid a}, CoefficientJetAxisRow O a.val → ℝ
  | ⟨⟨j, .inl i⟩, _⟩ =>
      allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j)
        (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
  | ⟨⟨j, .inr i⟩, ha⟩ =>
      fun z => (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j)
        (Nat.lt_of_not_ge ha) z).toReal

noncomputable def allocatedLongJetDensity (z : AllocatedLongJetRows B U basis S O) : ℝ :=
  ∏ a, allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a (z a)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α) (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "source" => allocatedLongCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S O

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongImage
namespace OAI

section

namespace Erdos3

noncomputable def translatedIntegerMappedJetMatrix {Z X K α O N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℤ)
    (rows : O → Finset α) (x : X → ℤ) (c : K → ℤ) : Matrix O N ℤ :=
  integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1)
    (fun t k => c k + integerMappedCubeTuple input z x t k) rows

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

noncomputable def allocatedTranslatedPartitionedJetMatrix
    (c : LayerSamplerVariables G I n B → ℤ) (j : Fin m) :
    Matrix (O j) (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) ℤ :=
  translatedIntegerMappedJetMatrix Subtype.val (partitionedPrincipalInput grid (fun g a => (g, a))) (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (rows j) (principalTupleIntegers v) c

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "split" => allocatedCoefficientSplit B U b S
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "longSource" => allocatedLongCoefficientSource B U b hR hσ S

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "joined" => principalAxisJoin grid u v
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x joined
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x joined

noncomputable def allocatedPhysicalLongJetMap
    (a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    AllocatedLongJetRows B U b S O :=
  fun i => coefficientJetAxisEquiv O I n (canonicalCoefficientJetArrays root dirs rows a) i.val

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFrozenGridLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

def AllocatedFrozenSupported (a : AllocatedFrozenCoefficients B U b S) : Prop :=
  ∀ (j : Fin m) (i : Fin (n j)) (hi : grid ⟨j, Sum.inr i⟩) d,
    a ⟨⟨j, Sum.inr i⟩, hi⟩ d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S j i d).support

abbrev AllocatedFrozenJetRows (O : Fin m → Type*) :=
  ∀ a : {a // grid a}, CoefficientJetAxisRow O a.val

variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v w : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

noncomputable def allocatedFrozenJetMap (a : AllocatedFrozenCoefficients B U b S) :
    AllocatedFrozenJetRows B U b S O :=
  fun i => coefficientJetAxisMap (allocatedPartitionedJetMatrix B U b S x u v rows) i.val (a i)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedFrozenJetDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

namespace VectorPolynomial

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (pivot : ∀ j, O j ↪ BoundedCoefficientExponent K (j.val + 1))
variable (hpivot : ∀ j, ((boundedCoefficientJetMatrix root A (j.val + 1) (rows j)).submatrix
  id (pivot j)).det ≠ 0)
variable (c w : ∀ j, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (hw : ∀ j i e, 0 < w j i e)
variable (p : ∀ j, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "axis" => coefficientJetAxisEquiv O I n

noncomputable def allocatedGridJetFactor :
    ∀ a : {a // grid a}, CoefficientJetAxisRow O a.val → ℝ
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, _⟩ => fun z =>
      (integerMatrixImagePMF (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j))
        (allocatedLayerIntegerPMFs B U b hR hσ S j i) z).toReal

noncomputable def allocatedGridJetDensity (z : AllocatedFrozenJetRows B U b S O) : ℝ :=
  ∏ a, allocatedGridJetFactor B U b hR hσ S x u v rows a (z a)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

noncomputable def allocatedFrozenJetReference : Measure (AllocatedFrozenJetRows B U b S O) :=
  Measure.pi (fun a : {a // allocatedGridAxis (I := I) U b S.value a} =>
    coefficientJetAxisReference O a.val)

instance allocatedFrozenJetReference_sigmaFinite : SigmaFinite (allocatedFrozenJetReference B U b S O) := by
  unfold allocatedFrozenJetReference
  infer_instance

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFrozenBlockPMF
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

noncomputable def allocatedFrozenBlockPMF :
    ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val)
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, ha⟩ =>
      (independentProductPMF (allocatedLayerIntegerPMFs B U b hR hσ S j i)).map
        (fun c t => booleanCoefficient (fun _ => c (constantCoefficientSlot _ _)) (rows j t) +
          ∑ q : B ⟨j, Sum.inr i⟩,
            c (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ q) *
              integerBooleanBlockJet
                (fun v r => (u ⟨⟨⟨j, Sum.inr i⟩, ha⟩, q, v⟩ r : ℤ)) (rows j t))

end Erdos3.VectorPolynomial

end

end OAI

end


