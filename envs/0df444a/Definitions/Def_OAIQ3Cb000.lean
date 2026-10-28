-- Prove2me | Definitions.Def_OAIQ3Cb000
-- name    : OAIQ3Cb000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:26:47.297006+00:00
-- url     : https://prove2.me/theorems/c45df819-755d-48a2-8074-00feedf8391d
-- title:
--   Definitions bundle OAIQ3Cb000 of the split of OpenAI, Bounded-degree coboundary expanders in every dimension
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoboundaryExpanders.main`, carved from OpenAI's openai/math development (OpenAI, *Bounded-degree coboundary expanders in every dimension*, OpenAI Math Release, September 24, 2026, result family 177, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 809 declarations of OpenAI's Lean: 356 definitions, 6 inductive types or structures, 18 instances and 429 theorems. The definitions and types are `Finset.equivOfEq`, `OAI.CoboundaryExpanders.Actions.coeff`, `OAI.CoboundaryExpanders.Actions.conjugation`, `OAI.CoboundaryExpanders.Actions.fixingImage`, `OAI.CoboundaryExpanders.Actions.fixingSubgroup`, `OAI.CoboundaryExpanders.Actions.induced`, `OAI.CoboundaryExpanders.ActualParabolic.Idx`, `OAI.CoboundaryExpanders.ActualParabolic.group`, `OAI.CoboundaryExpanders.ActualParabolic.idxEquiv`, `OAI.CoboundaryExpanders.ActualParabolic.inclusion`, `OAI.CoboundaryExpanders.ActualParabolic.kernelColumn`, `OAI.CoboundaryExpanders.ActualParabolic.project`, `OAI.CoboundaryExpanders.ActualParabolic.projectSL`, `OAI.CoboundaryExpanders.ActualParabolic.projectValue`, `OAI.CoboundaryExpanders.ActualParabolic.rowFixed`, `OAI.CoboundaryExpanders.ActualParabolic.sectionHom`, `OAI.CoboundaryExpanders.ActualParabolic.sectionValue`, `OAI.CoboundaryExpanders.ActualParabolic.shear`, `OAI.CoboundaryExpanders.ActualParabolic.shearConj`, `OAI.CoboundaryExpanders.ActualParabolic.shearFin`, `OAI.CoboundaryExpanders.ActualParabolic.stableFixed`, `OAI.CoboundaryExpanders.ActualShapiro.barEquiv`, `OAI.CoboundaryExpanders.ActualShapiro.barF`, `OAI.CoboundaryExpanders.ActualShapiro.barHomotopy`, `OAI.CoboundaryExpanders.ActualShapiro.barMap`, `OAI.CoboundaryExpanders.ActualShapiro.indBase`, `OAI.CoboundaryExpanders.ActualShapiro.inducedChainEquiv`, `OAI.CoboundaryExpanders.ActualShapiro.inducedChainMap`, `OAI.CoboundaryExpanders.ActualShapiro.restrictedResolution`, `OAI.CoboundaryExpanders.AffineLattices.Compatible`, `OAI.CoboundaryExpanders.AffineLattices.Homothetic`, `OAI.CoboundaryExpanders.AffineLattices.IsFace`, `OAI.CoboundaryExpanders.AffineLattices.IsVertex`, `OAI.CoboundaryExpanders.AffineLattices.Vertex`, `OAI.CoboundaryExpanders.AffineLattices.ball`, `OAI.CoboundaryExpanders.AffineLattices.base`, `OAI.CoboundaryExpanders.AffineLattices.complex`, `OAI.CoboundaryExpanders.AffineLattices.iterIso`, `OAI.CoboundaryExpanders.AffineLattices.level`, `OAI.CoboundaryExpanders.AffineLattices.mapVertex` and 322 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/Coboundary, in whole or in part: `Coboundary_Averaging`, `Coboundary_Chains`, `Coboundary_Chambers`, `Coboundary_Complex`, `Coboundary_Cones`, `Coboundary_Cosets`, `Coboundary_Flags`, `Coboundary_Frames`, `Coboundary_Joins`, `Coboundary_LatticeCones`, `Coboundary_Lattices`, `Coboundary_LinkSpectrum`, `Coboundary_Links`, `Coboundary_Mixing`, `Coboundary_Polynomial`, `Coboundary_Realization`, `Coboundary_Skeleton`, `Coboundary_Windows`, `Congruence_Basic`, `Congruence_Coinvariants`, `Congruence_CongruenceFrames`, `Congruence_Elementary`, `Congruence_FrameHomology`, `Congruence_OddHomology`, `Congruence_Parabolic`, `Congruence_Patterns`, `Congruence_Resolution`, `Congruence_Stabilization`, `Congruence_Transfer`.
--
--   **Imports.** It imports the published bundle `Def_CoboundaryExpanders`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ3Cb002`; the statements `OAI.CoboundaryExpanders.Construction.actual_uniform_cosystolic`, `OAI.CoboundaryExpanders.Construction.uniform_infinite_coset_positive` and `OAI.CoboundaryExpanders.uniform_gamma_vanishing`.
-- source:
--   OpenAI, Bounded-degree coboundary expanders in every dimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 177; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Bounded-degree-coboundary-expanders-in-every-dimension-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Coboundary at commit adc7f12

import Mathlib
import Definitions.Def_CoboundaryExpanders

set_option allowUnsafeReducibility true in
attribute [local reducible] _root_.OAI.CoboundaryExpanders.Complex.Face
section
-- module Solutions.OAIQ3_Cob.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib d13f23b's `Finset.equivOfEq`: the equivalence between the subtypes of equal finsets
(Coboundary CongruenceFrames, 2026-10-26). -/
def _root_.Finset.equivOfEq {α : Type*} {s t : Finset α} (h : s = t) : s ≃ t :=
  Equiv.subtypeEquivRight (fun _ => by rw [h])
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Chains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Augmented F2 simplicial chains, boundaries, exactness, and relative attachments.
-/

noncomputable section
open scoped BigOperators

namespace CoboundaryExpanders.InfiniteChains

section
variable {V : Type} [DecidableEq V]
abbrev k := ZMod 2

def rawBoundary : (Finset V →₀ k) →ₗ[k] (Finset V →₀ k) :=
  Finsupp.linearCombination k (fun s => ∑ v ∈ s, Finsupp.single (s.erase v) 1)

@[simp] lemma rawBoundary_single (s : Finset V) (r : k) :
    rawBoundary (Finsupp.single s r) = ∑ v ∈ s, Finsupp.single (s.erase v) r := by
  simp [rawBoundary, Finset.smul_sum]

lemma rawBoundary_squared : (rawBoundary (V := V)).comp rawBoundary = 0 := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, rawBoundary_single, map_sum,
    LinearMap.zero_apply]
  have he : (∑ a ∈ s, ∑ b ∈ s.erase a, Finsupp.single ((s.erase a).erase b) r) =
      ∑ x ∈ s.offDiag, Finsupp.single ((s.erase x.1).erase x.2) r := by
    have hd : s.offDiag = (s ×ˢ s).filter (fun x => x.1 ≠ x.2) := by
      ext x; simp [Finset.mem_offDiag, and_assoc]
    rw [hd, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_filter]
    congr 1
    ext b
    simp [Finset.mem_erase, ne_comm, and_comm]
  rw [he]
  apply Finset.sum_involution (fun x _ => x.swap)
  · intro x hx
    rw [Finset.erase_right_comm]
    ext z
    simp only [Finsupp.add_apply]
    exact CharTwo.add_self_eq_zero _
  · intro x hx _ heq
    exact (Finset.mem_offDiag.mp hx).2.2 (congrArg Prod.fst heq).symm
  · intro x _; exact Prod.swap_swap x
  · intro x hx
    exact Finset.mem_offDiag.mpr ⟨(Finset.mem_offDiag.mp hx).2.1,
      (Finset.mem_offDiag.mp hx).1, (Finset.mem_offDiag.mp hx).2.2.symm⟩

def rawCone (a : V) : (Finset V →₀ k) →ₗ[k] (Finset V →₀ k) :=
  Finsupp.linearCombination k (fun s =>
    if a ∈ s then 0 else Finsupp.single (insert a s) 1)

@[simp] lemma rawCone_single (a : V) (s : Finset V) (r : k) :
    rawCone a (Finsupp.single s r) =
      if a ∈ s then 0 else Finsupp.single (insert a s) r := by
  by_cases h : a ∈ s <;> simp [rawCone, h]

structure Complex (V : Type) where
  faces : Set (Finset V)
  empty_mem : ∅ ∈ faces
  downward : ∀ {σ τ}, σ ∈ faces → τ ⊆ σ → τ ∈ faces

namespace Complex
variable (X : CoboundaryExpanders.InfiniteChains.Complex V)
abbrev Face (n : ℕ) := {s : Finset V // s ∈ X.faces ∧ s.card = n}
abbrev Chains (n : ℕ) := X.Face n →₀ k

def erase (n : ℕ) (s : X.Face (n+1)) (v : ↥s.val) : X.Face n :=
  ⟨s.val.erase v.val, X.downward s.property.1 (Finset.erase_subset _ _), by
    rw [Finset.card_erase_of_mem v.property, s.property.2]; omega⟩

def boundary (n : ℕ) : X.Chains (n+1) →ₗ[k] X.Chains n :=
  Finsupp.linearCombination k (fun s => ∑ v : ↥s.val, Finsupp.single (X.erase n s v) 1)

@[simp] lemma boundary_single (n : ℕ) (s : X.Face (n+1)) (r : k) :
    X.boundary n (Finsupp.single s r) = ∑ v : ↥s.val, Finsupp.single (X.erase n s v) r := by
  simp [boundary, Finset.smul_sum]

def embed (n : ℕ) : X.Chains n →ₗ[k] (Finset V →₀ k) := Finsupp.lmapDomain k k Subtype.val

omit [DecidableEq V] in
@[simp] lemma embed_single (n : ℕ) (s : X.Face n) (r : k) :
    X.embed n (Finsupp.single s r) = Finsupp.single s.val r := by
  change Finsupp.mapDomain Subtype.val (Finsupp.single s r) = _
  exact Finsupp.mapDomain_single

omit [DecidableEq V] in
lemma embed_injective (n : ℕ) : Function.Injective (X.embed n) :=
  Finsupp.mapDomain_injective Subtype.val_injective

lemma embed_boundary (n : ℕ) :
    (X.embed n).comp (X.boundary n) = rawBoundary.comp (X.embed (n+1)) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, boundary_single,
    map_sum, embed_single, rawBoundary_single]
  exact Finset.sum_coe_sort s.val (fun v => Finsupp.single (s.val.erase v) r)

@[simp] lemma boundary_squared (n : ℕ) :
    (X.boundary n).comp (X.boundary (n+1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply X.embed_injective n
  change (X.embed n).comp (X.boundary n) (X.boundary (n+1) c) = _
  rw [embed_boundary]
  change rawBoundary ((X.embed (n+1)).comp (X.boundary (n+1)) c) = _
  rw [embed_boundary]
  change rawBoundary.comp rawBoundary (X.embed (n+2) c) = _
  rw [rawBoundary_squared]
  simp

open CategoryTheory

def chainComplex : ChainComplex (ModuleCat k) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of k (X.Chains (i+1)))
    (fun i => ModuleCat.ofHom (X.boundary (i+1)))
    (fun i => ModuleCat.hom_ext (X.boundary_squared (i+1)))

@[simp] lemma chainComplex_d (n : ℕ) :
    X.chainComplex.d (n+1) n = ModuleCat.ofHom (X.boundary (n+1)) := by
  simp [chainComplex, ChainComplex.of_d]

def full (V : Type) : CoboundaryExpanders.InfiniteChains.Complex V where
  faces := Set.univ
  empty_mem := Set.mem_univ _
  downward := fun _ _ => Set.mem_univ _

def sumCoefficients (n : ℕ) : X.Chains n →ₗ[k] k :=
  Finsupp.linearCombination k (fun _ => 1)

omit [DecidableEq V] in
@[simp] lemma sumCoefficients_single (n : ℕ) (s : X.Face n) (r : k) :
    X.sumCoefficients n (Finsupp.single s r) = r := by
  simp [sumCoefficients]

lemma augmentation_boundary_zero :
    (X.sumCoefficients 0).comp (X.boundary 0) = X.sumCoefficients 1 := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, boundary_single,
    map_sum, sumCoefficients_single]
  simp [s.property.2]

lemma augmentation_boundary :
    (X.sumCoefficients 1).comp (X.boundary 1) = 0 := by
  rw [← augmentation_boundary_zero, LinearMap.comp_assoc, boundary_squared, LinearMap.comp_zero]

end Complex
end

namespace Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]
abbrev Raw (V : Type) := Finset V →₀ k

def supported (P : Set (Finset V)) : Submodule k (Raw V) :=
  Finsupp.supported k k P

def append (F : Finset W) : Raw V →ₗ[k] Raw (W ⊕ V) :=
  Finsupp.lmapDomain k k (F.disjSum ·)

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma append_single (F : Finset W) (s : Finset V) (a : k) :
    append F (Finsupp.single s a) = Finsupp.single (F.disjSum s) a :=
  Finsupp.mapDomain_single

def project (F : Finset W) : Raw (W ⊕ V) →ₗ[k] Raw V :=
  Finsupp.linearCombination k (fun s =>
    if s.toLeft = F then Finsupp.single s.toRight 1 else 0)

omit [DecidableEq V] in
@[simp] lemma project_single (F : Finset W) (s : Finset (W ⊕ V)) (a : k) :
    project F (Finsupp.single s a) =
      if s.toLeft = F then Finsupp.single s.toRight a else 0 := by
  by_cases h : s.toLeft = F <;> simp [project, h]

omit [DecidableEq V] in
@[simp] lemma project_append (F : Finset W) :
    (project (V := V) F).comp (append F) = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp

def graded (P : Set (Finset V)) (n : ℕ) : Set (Finset V) :=
  {s | s ∈ P ∧ s.card = n}

end Attachment
end CoboundaryExpanders.InfiniteChains

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Cones
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Quantitative chain cones, face-model transport, relabeling, and exactness under retractions.
-/

section
open scoped BigOperators

namespace CoboundaryExpanders.InfiniteChains.Cone
open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def size (c : Raw V) : ℕ := c.support.card

omit [DecidableEq V] in
@[simp] lemma size_zero : size (0 : Raw V) = 0 := by simp [size]

noncomputable def carrierFill (apex : Finset V → V) (s : Finset V) : Raw V :=
  rawCone (apex s) (Finsupp.single s 1 + ∑ v : s, carrierFill apex (s.erase v.val))
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem v.property

noncomputable def carrierMap (apex : Finset V → V) : Raw V →ₗ[k] Raw V :=
  Finsupp.linearCombination k (carrierFill apex)

@[simp] lemma carrierMap_single (apex : Finset V → V) (s : Finset V) (a : k) :
    carrierMap apex (Finsupp.single s a) = a • carrierFill apex s := by
  simp [carrierMap]

def link (v : V) : Raw V →ₗ[k] Raw V :=
  Finsupp.linearCombination k (fun s =>
    if v ∈ s then Finsupp.single (s.erase v) 1 else 0)

@[simp] lemma link_single (v : V) (s : Finset V) (a : k) :
    link v (Finsupp.single s a) =
      if v ∈ s then Finsupp.single (s.erase v) a else 0 := by
  by_cases h : v ∈ s <;> simp [link, h]

def without (v : V) : Raw V →ₗ[k] Raw V :=
  Finsupp.linearCombination k (fun s =>
    if v ∈ s then 0 else Finsupp.single s 1)

@[simp] lemma without_single (v : V) (s : Finset V) (a : k) :
    without v (Finsupp.single s a) = if v ∈ s then 0 else Finsupp.single s a := by
  by_cases h : v ∈ s <;> simp [without, h]

structure BoundedCone (X : CoboundaryExpanders.InfiniteChains.Complex V) (n R : ℕ) where
  hom : Raw V →ₗ[k] Raw V
  support : ∀ s ∈ X.faces, s.card ≤ n →
    hom (Finsupp.single s 1) ∈ supported (graded X.faces (s.card+1))
  contraction : ∀ s ∈ X.faces, s.card ≤ n →
    rawBoundary (hom (Finsupp.single s 1)) + hom (rawBoundary (Finsupp.single s 1)) =
      Finsupp.single s 1
  bound : ∀ s ∈ X.faces, s.card ≤ n → size (hom (Finsupp.single s 1)) ≤ R

def relabel (f : V → W) : Raw V →ₗ[k] Raw W :=
  Finsupp.lmapDomain k k (Finset.image f)

omit [DecidableEq V] in
@[simp] lemma relabel_single (f : V → W) (s : Finset V) (a : k) :
    relabel f (Finsupp.single s a) = Finsupp.single (s.image f) a := by
  simp [relabel]

end CoboundaryExpanders.InfiniteChains.Cone

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.InfiniteChains.Cone
open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def unlabel (f : V → W) (hf : Function.Injective f) : Raw W →ₗ[k] Raw V :=
  Finsupp.lmapDomain k k (fun s : Finset W => s.preimage f hf.injOn)

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma unlabel_single (f : V → W) (hf : Function.Injective f) (s : Finset W) (a : k) :
    unlabel f hf (Finsupp.single s a) = Finsupp.single (s.preimage f hf.injOn) a := by
  simp [unlabel]

omit [DecidableEq V] in
lemma preimage_image (f : V → W) (hf : Function.Injective f) (s : Finset V) :
    (s.image f).preimage f hf.injOn = s := by
  ext v
  simp [hf.eq_iff]

omit [DecidableEq V] in
@[simp] lemma unlabel_relabel (f : V → W) (hf : Function.Injective f) (c : Raw V) :
    unlabel f hf (relabel f c) = c := by
  have he : (unlabel f hf).comp (relabel f) = LinearMap.id := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, relabel_single, unlabel_single,
      preimage_image f hf s, LinearMap.id_apply]
  exact LinearMap.congr_fun he c

structure FaceModel (X : CoboundaryExpanders.InfiniteChains.Complex V) (Y : CoboundaryExpanders.InfiniteChains.Complex W) where
  vertex : V → W
  injective : Function.Injective vertex
  face_iff : ∀ s : Finset V, s.image vertex ∈ Y.faces ↔ s ∈ X.faces
  cover : ∀ t ∈ Y.faces, ∃ s ∈ X.faces, s.image vertex = t

end CoboundaryExpanders.InfiniteChains.Cone

end

section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.InfiniteChains.Cone
open Attachment
variable {V : Type} [DecidableEq V]
attribute [local instance] Classical.propDecidable

def vertexEval (P : V → Prop) : Raw V →ₗ[k] k :=
  Finsupp.linearCombination k (fun s => ∑v∈s, (if P v then 1 else 0 : k))
omit [DecidableEq V] in
@[simp] lemma vertexEval_single (P : V → Prop) (s : Finset V) (a : k) :
    vertexEval P (Finsupp.single s a) = a * ∑v∈s, (if P v then 1 else 0 : k) := by
  simp [vertexEval]

end CoboundaryExpanders.InfiniteChains.Cone

end

open scoped Polynomial BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Joins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Binary and finite joins, augmented exactness, and bounded cone constructions.
-/

section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.InfiniteChains.Join

section
open Attachment Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def prepend (B : Finset V) : Raw W →ₗ[k] Raw (W ⊕ V) :=
  Finsupp.lmapDomain k k (·.disjSum B)

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma prepend_single (B : Finset V) (A : Finset W) (a : k) :
    prepend B (Finsupp.single A a) = Finsupp.single (A.disjSum B) a :=
  Finsupp.mapDomain_single

def leftAction (T : Raw W →ₗ[k] Raw W) : Raw (W ⊕ V) →ₗ[k] Raw (W ⊕ V) :=
  Finsupp.linearCombination k (fun s => prepend s.toRight (T (Finsupp.single s.toLeft 1)))

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma leftAction_single (T : Raw W →ₗ[k] Raw W)
    (s : Finset (W ⊕ V)) (a : k) :
    leftAction T (Finsupp.single s a) = prepend s.toRight (T (Finsupp.single s.toLeft a)) := by
  simp [leftAction, ← map_smul]

end

open Attachment Cone

end CoboundaryExpanders.InfiniteChains.Join

namespace CoboundaryExpanders.InfiniteChains.Cone.BoundedCone
open Attachment
variable {V : Type} [DecidableEq V] {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ}

def cut (H : BoundedCone X n R) : Raw V →ₗ[k] Raw V :=
  Finsupp.linearCombination k (fun s => if s.card ≤ n then H.hom (Finsupp.single s 1) else 0)

@[simp] lemma cut_single (H : BoundedCone X n R) (s : Finset V) (a : k) :
    H.cut (Finsupp.single s a) = if s.card ≤ n then H.hom (Finsupp.single s a) else 0 := by
  by_cases h : s.card ≤ n <;> simp [cut, h, ← map_smul]

end CoboundaryExpanders.InfiniteChains.Cone.BoundedCone

namespace CoboundaryExpanders.InfiniteChains.Join

section
open Attachment Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def crossLinear : Raw W →ₗ[k] (Raw V →ₗ[k] Raw (W ⊕ V)) :=
  Finsupp.linearCombination k (fun A => append A)

def cross (c : Raw W) (d : Raw V) : Raw (W ⊕ V) := crossLinear c d

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma cross_single_left (A : Finset W) (a : k) (d : Raw V) :
    cross (Finsupp.single A a) d = a • append A d := by simp [cross, crossLinear]

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma cross_single_right (c : Raw W) (B : Finset V) (b : k) :
    cross c (Finsupp.single B b) = b • prepend B c := by
  induction c using Finsupp.induction_linear with
  | zero => simp [cross]
  | add c d hc hd => simp only [cross, map_add, LinearMap.add_apply] at *; rw [hc, hd, smul_add]
  | single A a => simp [cross_single_left, mul_comm]

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma cross_zero_left (d : Raw V) : cross (0 : Raw W) d = 0 := by simp [cross]
omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma cross_zero_right (c : Raw W) : cross c (0 : Raw V) = 0 := by simp [cross]

def operator (T : Raw W →ₗ[k] Raw W) (U : Raw V →ₗ[k] Raw V) :
    Raw (W ⊕ V) →ₗ[k] Raw (W ⊕ V) :=
  Finsupp.linearCombination k (fun s =>
    cross (T (Finsupp.single s.toLeft 1)) (U (Finsupp.single s.toRight 1)))

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma operator_single (T : Raw W →ₗ[k] Raw W) (U : Raw V →ₗ[k] Raw V)
    (A : Finset W) (B : Finset V) :
    operator T U (Finsupp.single (A.disjSum B) 1) =
      cross (T (Finsupp.single A 1)) (U (Finsupp.single B 1)) := by simp [operator]

end

open Attachment Cone

end CoboundaryExpanders.InfiniteChains.Join

end

open scoped Polynomial BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Polynomial congruence groups, truncation ideals, and finite nilpotent quotients.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix

namespace CoboundaryExpanders.Construction

section
abbrev R (q : ℕ) := Polynomial (ZMod q)
def powerIdeal (q m : ℕ) : Ideal (R q) := Ideal.span {Polynomial.X ^ m}
def Gamma (q a m : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin a) (R q)) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal q m))).ker
abbrev Trunc (q m : ℕ) := R q ⧸ powerIdeal q m

instance finiteTrunc (q m : ℕ) [NeZero q] : Finite (Trunc q m) := by
  let : Module.Finite (ZMod q) (Trunc q m) :=
    (Polynomial.monic_X.pow m).finite_quotient
  exact Module.finite_of_finite (ZMod q)

def tbar (q m : ℕ) : Trunc q m := Ideal.Quotient.mk (powerIdeal q m) Polynomial.X

@[simp] theorem tbar_pow (q m : ℕ) : tbar q m ^ m = 0 := by
  rw [tbar, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem exists_prime_power_unipotent {A : Type*} [Ring A] {p : ℕ}
    (hp : p.Prime) (hp0 : (p : A) = 0) (x : A) (hx : IsNilpotent x) :
    ∃ r : ℕ, (1 + x) ^ p ^ r = 1 := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  obtain ⟨z, hz⟩ := (Commute.one_left x).exists_add_pow_prime_pow_eq hp n
  rw [hz, hp0, zero_mul, zero_mul, zero_mul, add_zero, one_pow,
    pow_eq_zero_of_le (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt)) hn, add_zero]

theorem strict_upper_pow_zero {A : Type*} [Semiring A] (a : ℕ)
    (M : Matrix (Fin a) (Fin a) A) (hM : ∀ i j, j ≤ i → M i j = 0) :
    M ^ a = 0 := by
  have hpow : ∀ r : ℕ, ∀ i j : Fin a, j.val < i.val + r → (M ^ r) i j = 0 := by
    intro r
    induction r with
    | zero =>
      intro i j hij
      have hne : i ≠ j := by intro h; subst j; omega
      simp [hne]
    | succ r ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : l.val < i.val + r
      · rw [ih i l hl, zero_mul]
      · have hjl : j ≤ l := by omega
        rw [hM l j hjl, mul_zero]
  ext i j
  exact hpow a i j (by omega)

theorem mem_gamma_iff (q a m : ℕ) (A : Matrix.SpecialLinearGroup (Fin a) (R q)) :
    A ∈ Gamma q a m ↔ ∀ i j,
      Polynomial.X ^ m ∣ (A : Matrix (Fin a) (Fin a) (R q)) i j -
        (1 : Matrix (Fin a) (Fin a) (R q)) i j := by
  rw [Gamma, MonoidHom.mem_ker, Matrix.SpecialLinearGroup.ext_iff]
  constructor
  · intro h i j
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk (powerIdeal q m) _ = 0
    rw [map_sub]
    change Ideal.Quotient.mk (powerIdeal q m) _ -
      Ideal.Quotient.mk (powerIdeal q m) ((1 : Matrix (Fin a) (Fin a) (R q)) i j) = 0
    have he := h i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.SpecialLinearGroup.coe_one] at he
    rw [he]
    simp [Matrix.one_apply]
  · intro h i j
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (h i j))
    change Ideal.Quotient.mk (powerIdeal q m) _ = 0 at he
    rw [map_sub, sub_eq_zero] at he
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply] using he

theorem gamma_antitone (q a : ℕ) : Antitone (Gamma q a) := by
  intro m n hmn A hA
  rw [mem_gamma_iff] at hA ⊢
  intro i j
  exact dvd_trans (pow_dvd_pow _ hmn) (hA i j)

def congruenceReduction (p a m n : ℕ) : Gamma p a m →*
    Matrix.SpecialLinearGroup (Fin a) (Trunc p n) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p n))).comp
    (Gamma p a m).subtype

def deeperCongruence (p a m n : ℕ) : Subgroup (Gamma p a m) :=
  (congruenceReduction p a m n).ker

instance finiteCongruenceQuotient (p a m n : ℕ) [NeZero p] :
    Finite (Gamma p a m ⧸ deeperCongruence p a m n) :=
  Finite.of_injective
    (QuotientGroup.quotientKerEquivRange (congruenceReduction p a m n))
    (QuotientGroup.quotientKerEquivRange (congruenceReduction p a m n)).injective

def IsUpperUnitriangular {A : Type*} [CommRing A] (a : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin a) A) : Prop :=
  ∀ i j, j ≤ i → (g : Matrix (Fin a) (Fin a) A) i j =
    (1 : Matrix (Fin a) (Fin a) A) i j

def upperUnitriangularMonoid (p a : ℕ) :
    Submonoid (Matrix.SpecialLinearGroup (Fin a) (ZMod p)) where
  carrier := {g | IsUpperUnitriangular a g}
  one_mem' := by intro i j h; rfl
  mul_mem' := by
    intro g h hg hh i j hij
    change ((g : Matrix (Fin a) (Fin a) (ZMod p)) *
      (h : Matrix (Fin a) (Fin a) (ZMod p))) i j = _
    rw [Matrix.mul_apply]
    by_cases he : i = j
    · subst j
      rw [Finset.sum_eq_single i]
      · rw [hg i i le_rfl, hh i i le_rfl]
        simp
      · intro l _ hli
        rcases lt_or_gt_of_ne hli with hl | hl
        · rw [hg i l hl.le]
          simp [ne_of_gt hl]
        · rw [hh l i hl.le]
          simp [ne_of_gt hl]
      · simp
    · rw [Matrix.one_apply_ne he]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : l < i
      · rw [hg i l hl.le]
        simp [ne_of_gt hl]
      · have hjl : j < l := lt_of_lt_of_le (lt_of_le_of_ne hij (Ne.symm he)) (le_of_not_gt hl)
        rw [hh l j hjl.le]
        simp [ne_of_gt hjl]

def upperUnitriangular (p a : ℕ) [NeZero p] :
    Subgroup (Matrix.SpecialLinearGroup (Fin a) (ZMod p)) :=
  { upperUnitriangularMonoid p a with
    inv_mem' := by
      intro g hg
      change g⁻¹ ∈ upperUnitriangularMonoid p a
      rw [← one_mul g⁻¹, ← pow_one g, ← pow_orderOf_eq_one g,
        ← pow_sub g (orderOf_pos g)]
      exact (upperUnitriangularMonoid p a).pow_mem hg (orderOf g - 1) }

def evalZero (p a : ℕ) : Matrix.SpecialLinearGroup (Fin a) (R p) →*
    Matrix.SpecialLinearGroup (Fin a) (ZMod p) :=
  Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom 0)

def U (p a : ℕ) [NeZero p] : Subgroup (Matrix.SpecialLinearGroup (Fin a) (R p)) :=
  (upperUnitriangular p a).comap (evalZero p a)

theorem gamma_one_eq_ker_evalZero (p a : ℕ) : Gamma p a 1 = (evalZero p a).ker := by
  ext g
  rw [mem_gamma_iff, MonoidHom.mem_ker, Matrix.SpecialLinearGroup.ext_iff]
  simp [pow_one, Polynomial.X_dvd_iff, evalZero,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply, Matrix.one_apply, apply_ite, Polynomial.coeff_zero_eq_eval_zero,
    sub_eq_zero]

theorem gamma_le_U (p a m : ℕ) [NeZero p] (hm : 1 ≤ m) : Gamma p a m ≤ U p a := by
  intro g hg
  have h1 := gamma_antitone p a hm hg
  rw [gamma_one_eq_ker_evalZero, MonoidHom.mem_ker] at h1
  change evalZero p a g ∈ upperUnitriangular p a
  rw [h1]
  exact (upperUnitriangular p a).one_mem

def uReduction (p a m : ℕ) [NeZero p] : U p a →*
    Matrix.SpecialLinearGroup (Fin a) (Trunc p m) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m))).comp (U p a).subtype

def Gquot (p a m : ℕ) [NeZero p] := U p a ⧸ (uReduction p a m).ker
instance instGroupGquot (p a m : ℕ) [NeZero p] : Group (Gquot p a m) := inferInstanceAs (Group (_ ⧸ _))
instance instFiniteGquot (p a m : ℕ) [NeZero p] : Finite (Gquot p a m) :=
  Finite.of_injective (QuotientGroup.quotientKerEquivRange (uReduction p a m))
    (QuotientGroup.quotientKerEquivRange (uReduction p a m)).injective

variable (p n : ℕ) [Fact p.Prime]
abbrev Frac := FractionRing (R p)

def diagonalUnits {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]
    (u : ι → Kˣ) : Matrix.GeneralLinearGroup ι K where
  val := Matrix.diagonal (fun i => (u i).val)
  inv := Matrix.diagonal (fun i => (u i).inv)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

@[simp] theorem diagonalUnits_val {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing K] (u : ι → Kˣ) :
    (diagonalUnits u).val = Matrix.diagonal (fun i => (u i).val) := rfl

@[simp] theorem diagonalUnits_inv_val {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing K] (u : ι → Kˣ) :
    (diagonalUnits u)⁻¹.val = Matrix.diagonal (fun i => (u i).inv) := rfl

def cutUnit (cut i : Fin (n + 1)) : (Frac p)ˣ :=
  if i.val < cut.val then
    Units.mk0 (algebraMap (R p) (Frac p) Polynomial.X)
      (by exact fun h => Polynomial.X_ne_zero ((IsFractionRing.injective (R p) (Frac p)) (h.trans (map_zero _).symm)))
  else 1

def edgeSource (j : Fin (n + 1)) : Fin (n + 1) :=
  if h : j = 0 then Fin.last n else ⟨j.val - 1, by omega⟩

theorem edgeSource_ne (hn : 1 ≤ n) (j : Fin (n + 1)) : edgeSource n j ≠ j := by
  unfold edgeSource
  split_ifs with h
  · subst j
    intro he
    have := congrArg Fin.val he
    simp only [Fin.val_last, Fin.val_zero] at this
    omega
  · intro he
    have := congrArg Fin.val he
    have hj : j.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using h
    dsimp only at this
    omega

def cycleRoot (hn : 1 ≤ n) (j : Fin (n + 1)) :
    Matrix.SpecialLinearGroup (Fin (n + 1)) (R p) :=
  Matrix.SpecialLinearGroup.transvection (edgeSource_ne n hn j)
    (if j = 0 then Polynomial.X else 1)

def localGroup (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)) :=
  Subgroup.closure {g | ∃ j, j ≠ cut ∧ g = cycleRoot p n hn j}

def cutConjugation (cut : Fin (n + 1)) :
    Matrix.SpecialLinearGroup (Fin (n + 1)) (R p) →*
      Matrix.GeneralLinearGroup (Fin (n + 1)) (Frac p) :=
  (MulAut.conj (diagonalUnits (cutUnit p n cut))).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.mapGL (Frac p))

theorem cutConjugation_injective (cut : Fin (n + 1)) :
    Function.Injective (cutConjugation p n cut) := by
  apply (MulAut.conj _).injective.comp
  intro A B h
  exact (Matrix.SpecialLinearGroup.mapGL_inj (S := Frac p) A B).mp h

theorem diagonal_conj_transvection {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing K] (u : ι → Kˣ) {i j : ι} (hij : i ≠ j) (b : K) :
    MulAut.conj (diagonalUnits u) (Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.transvection hij b)) =
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij
      ((u i).val * b * (u j).inv)) := by
  apply Matrix.GeneralLinearGroup.ext
  intro a c
  change ((diagonalUnits u).val *
    (1 + Matrix.single i j b) * (diagonalUnits u).inv) a c =
      (1 + Matrix.single i j ((u i).val * b * (u j).inv)) a c
  simp only [diagonalUnits, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases ha : a = i <;> by_cases hc : c = j <;> by_cases hac : a = c
  all_goals simp_all [mul_add, add_mul]

theorem cut_root_coefficient (cut j : Fin (n + 1)) (hj : j ≠ cut) :
    (cutUnit p n cut (edgeSource n j)).val *
      (algebraMap (R p) (Frac p)) (if j = 0 then Polynomial.X else 1) *
      (cutUnit p n cut j).inv = 1 := by
  by_cases h0 : j = 0
  · subst j
    have hc : 0 < cut.val := by
      have : cut.val ≠ 0 := fun h => hj (Fin.ext h.symm)
      omega
    have hncut : ¬ n < cut.val := by omega
    simp [edgeSource, cutUnit, hncut, hc]
  · have hj0 : 0 < j.val := by
      have : j.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using h0
      omega
    have hne : j.val ≠ cut.val := fun h => hj (Fin.ext h)
    have heq : j.val - 1 < cut.val ↔ j.val < cut.val := by omega
    simp only [edgeSource, dite_eq_right h0, cutUnit, Fin.val_mk, heq, ite_eq_right h0, map_one]
    split_ifs <;> simp

theorem map_transvection {ι A B : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing A] [CommRing B] (f : A →+* B) {i j : ι} (hij : i ≠ j) (b : A) :
    Matrix.SpecialLinearGroup.map f (Matrix.SpecialLinearGroup.transvection hij b) =
    Matrix.SpecialLinearGroup.transvection hij (f b) := by
  ext a c
  simp [Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply,
    Matrix.one_apply, apply_ite f]

theorem cutConjugation_root (hn : 1 ≤ n) (cut j : Fin (n + 1)) (hj : j ≠ cut) :
    cutConjugation p n cut (cycleRoot p n hn j) =
    Matrix.GeneralLinearGroup.map (algebraMap (ZMod p) (Frac p))
      (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection (edgeSource_ne n hn j) (1 : ZMod p))) := by
  change MulAut.conj (diagonalUnits (cutUnit p n cut))
    (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map _ _)) = _
  rw [cycleRoot, map_transvection, diagonal_conj_transvection,
    cut_root_coefficient p n cut j hj]
  apply Matrix.GeneralLinearGroup.ext
  intro a c
  simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.GeneralLinearGroup.map,
    Matrix.single_apply, Matrix.one_apply]

theorem localGroup_le_constant (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    localGroup p n hn cut ≤
      (Matrix.GeneralLinearGroup.map (n := Fin (n + 1)) (algebraMap (ZMod p) (Frac p))).range.comap
        (cutConjugation p n cut) := by
  apply (Subgroup.closure_le _).2
  rintro g ⟨j, hj, rfl⟩
  exact ⟨Matrix.SpecialLinearGroup.toGL
    (Matrix.SpecialLinearGroup.transvection (edgeSource_ne n hn j) 1),
      (cutConjugation_root p n hn cut j hj).symm⟩

def localGroupEmbedding (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    localGroup p n hn cut ↪
      (Matrix.GeneralLinearGroup.map (n := Fin (n + 1)) (algebraMap (ZMod p) (Frac p))).range where
  toFun g := ⟨cutConjugation p n cut g, localGroup_le_constant p n hn cut g.property⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    exact cutConjugation_injective p n cut (congrArg Subtype.val h)

instance localGroup_finite (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    Finite (localGroup p n hn cut) :=
  Finite.of_injective (localGroupEmbedding p n hn cut)
    (localGroupEmbedding p n hn cut).injective

end

variable (p n : ℕ) [Fact p.Prime]

theorem upper_transvection_mem_U {a : ℕ} {i j : Fin a} (hij : i < j) (f : R p) :
    Matrix.SpecialLinearGroup.transvection hij.ne f ∈ U p a := by
  change IsUpperUnitriangular a (evalZero p a _) 
  rw [evalZero, map_transvection]
  intro b c hcb
  change (1 + Matrix.single i j (Polynomial.evalRingHom 0 f)) b c = (1 : Matrix _ _ _) b c
  simp only [Matrix.add_apply]
  suffices Matrix.single i j (Polynomial.evalRingHom 0 f) b c = 0 by rw [this, add_zero]
  simp only [Matrix.single_apply]
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    exact False.elim (not_le_of_gt hij hcb)
  · rfl

theorem cycleRoot_mem_U (hn : 1 ≤ n) (j : Fin (n + 1)) :
    cycleRoot p n hn j ∈ U p (n + 1) := by
  by_cases h : j = 0
  · subst j
    have he : evalZero p (n + 1) (cycleRoot p n hn 0) = 1 := by
      simp [evalZero, cycleRoot, map_transvection]
    change evalZero p (n + 1) (cycleRoot p n hn 0) ∈ upperUnitriangular p (n + 1)
    rw [he]
    exact (upperUnitriangular p (n + 1)).one_mem
  · have hlt : edgeSource n j < j := by
      have hj : j.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using h
      simp only [edgeSource, dite_eq_right h, Fin.lt_def]
      omega
    simpa only [cycleRoot, ite_eq_right h] using upper_transvection_mem_U p hlt (1 : R p)

theorem localGroup_le_U (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    localGroup p n hn cut ≤ U p (n + 1) := by
  apply (Subgroup.closure_le _).2
  rintro g ⟨j, _, rfl⟩
  exact cycleRoot_mem_U p n hn j

def uLocalGroup (hn : 1 ≤ n) (cut : Fin (n + 1)) : Subgroup (U p (n + 1)) :=
  (localGroup p n hn cut).subgroupOf (U p (n + 1))

def reducedLocalGroup (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n + 1)) :
    Subgroup (Gquot p (n + 1) m) :=
  (uLocalGroup p n hn cut).map (QuotientGroup.mk' (uReduction p (n + 1) m).ker)

def cutPolynomial (cut i : Fin (n + 1)) : R p :=
  if i.val < cut.val then Polynomial.X else 1

@[simp] theorem cutUnit_coe (cut i : Fin (n + 1)) :
    (cutUnit p n cut i).val = algebraMap (R p) (Frac p) (cutPolynomial p n cut i) := by
  simp only [cutUnit, cutPolynomial]
  split_ifs <;> simp

theorem cutConjugation_apply (cut : Fin (n + 1))
    (A : Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)) (i j : Fin (n + 1)) :
    cutConjugation p n cut A i j =
      (cutUnit p n cut i).val * algebraMap (R p) (Frac p) (A i j) *
        (cutUnit p n cut j).inv := by
  change ((diagonalUnits (cutUnit p n cut)).val *
    (A.val.map (algebraMap (R p) (Frac p))) *
    (diagonalUnits (cutUnit p n cut)).inv) i j = _
  simp [diagonalUnits, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem localGroup_entry_equation (hn : 1 ≤ n) (cut : Fin (n + 1))
    (A : localGroup p n hn cut) (i j : Fin (n + 1)) :
    ∃ c : ZMod p, cutPolynomial p n cut i * A.val i j =
      Polynomial.C c * cutPolynomial p n cut j := by
  obtain ⟨B, hB⟩ := localGroup_le_constant p n hn cut A.property
  refine ⟨B i j, IsFractionRing.injective (R p) (Frac p) ?_⟩
  have he := congrArg (fun g : Matrix.GeneralLinearGroup (Fin (n + 1)) (Frac p) => g i j) hB
  change algebraMap (ZMod p) (Frac p) (B i j) = cutConjugation p n cut A.val i j at he
  rw [cutConjugation_apply] at he
  have he' := congrArg (fun x : Frac p => x * (cutUnit p n cut j).val) he
  simp only [mul_assoc, Units.inv_val, mul_one] at he'
  rw [map_mul, map_mul, ← cutUnit_coe, ← cutUnit_coe]
  simpa only [IsScalarTower.algebraMap_apply (ZMod p) (R p) (Frac p), Polynomial.algebraMap_eq] using he'.symm

theorem localGroup_entry_degree_le_one (hn : 1 ≤ n) (cut : Fin (n + 1))
    (A : localGroup p n hn cut) (i j : Fin (n + 1)) :
    (A.val i j).natDegree ≤ 1 := by
  obtain ⟨c, hc⟩ := localGroup_entry_equation p n hn cut A i j
  unfold cutPolynomial at hc
  by_cases hi : i.val < cut.val
  · rw [ite_eq_left hi] at hc
    by_cases ha : A.val i j = 0
    · simp [ha]
    · have hd := congrArg Polynomial.natDegree hc
      rw [Polynomial.natDegree_mul Polynomial.X_ne_zero ha, Polynomial.natDegree_X] at hd
      have hright : (Polynomial.C c * (if j.val < cut.val then Polynomial.X else 1)).natDegree ≤ 1 := by
        exact (Polynomial.natDegree_C_mul_le _ _).trans (by split_ifs <;> simp)
      omega
  · rw [ite_eq_right hi, one_mul] at hc
    rw [hc]
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by split_ifs <;> simp)

theorem eq_of_small_degree_congruent {m : ℕ} (hm : 2 ≤ m) (f g : R p)
    (hf : f.natDegree ≤ 1) (hg : g.natDegree ≤ 1)
    (he : Ideal.Quotient.mk (powerIdeal p m) f = Ideal.Quotient.mk (powerIdeal p m) g) :
    f = g := by
  have hdvd : Polynomial.X ^ m ∣ f - g := by
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  by_contra hfg
  have hfg0 : f - g ≠ 0 := sub_ne_zero.mpr hfg
  have hle := Polynomial.natDegree_le_of_dvd hdvd hfg0
  rw [Polynomial.natDegree_X_pow] at hle
  have hsmall := Polynomial.natDegree_sub_le f g
  omega

theorem localGroups_reduction_injective (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (cut cut' : Fin (n + 1)) (A : localGroup p n hn cut) (B : localGroup p n hn cut')
    (he : Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) A.val =
      Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) B.val) :
    A.val = B.val := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  apply eq_of_small_degree_congruent p hm _ _
    (localGroup_entry_degree_le_one p n hn cut A i j)
    (localGroup_entry_degree_le_one p n hn cut' B i j)
  exact congrArg (fun g : Matrix.SpecialLinearGroup (Fin (n + 1)) (Trunc p m) => g i j) he

def localQuotientMap (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n + 1)) :
    localGroup p n hn cut →* Gquot p (n + 1) m :=
  (QuotientGroup.mk' (uReduction p (n + 1) m).ker).comp
    (Subgroup.inclusion (localGroup_le_U p n hn cut))

end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Cosets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Typed coset complexes, their links, face models, and connectedness from generation.
-/

section
open scoped BigOperators

namespace CoboundaryExpanders.TypedCosetFaces
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)
abbrev Vertex := (i : I) × G ⧸ H i
instance instDecidableEqVertex : DecidableEq (Vertex H) := Classical.decEq _
def vertex (g : G) (i : I) : Vertex H := ⟨i, QuotientGroup.mk g⟩
def face (g : G) (A : Finset I) : Finset (Vertex H) := A.image (vertex H g)
def types (σ : Finset (Vertex H)) : Finset I := σ.image Sigma.fst
def IsFace (σ : Finset (Vertex H)) : Prop := ∃ g A, face H g A = σ
def stabilizer (A : Finset I) : Subgroup G := ⨅ i ∈ A, H i

omit [DecidableEq I] in
@[simp] theorem mem_stabilizer (A : Finset I) (g : G) :
    g ∈ stabilizer H A ↔ ∀ i ∈ A, g ∈ H i := by simp [stabilizer]

omit [DecidableEq I] in
lemma vertex_injective (g : G) : Function.Injective (vertex H g) := by
  intro i j hij
  exact congrArg Sigma.fst hij

omit [DecidableEq I] in
@[simp] theorem face_card (g : G) (A : Finset I) : (face H g A).card = A.card :=
  Finset.card_image_of_injective _ (vertex_injective H g)

@[simp] theorem types_face (g : G) (A : Finset I) : types H (face H g A) = A := by
  simp [types, face, Finset.image_image, vertex, Function.comp_def]

omit [DecidableEq I] in
@[simp] lemma vertex_mem (g h : G) (i : I) (A : Finset I) :
    vertex H g i ∈ face H h A ↔ i ∈ A ∧ (QuotientGroup.mk g : G ⧸ H i) = QuotientGroup.mk h := by
  constructor
  · intro hi
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hi
    have hji : j = i := congrArg Sigma.fst he
    subst j
    exact ⟨hj, (eq_of_heq (Sigma.mk.inj_iff.mp he).2).symm⟩
  · rintro ⟨hi,he⟩
    apply Finset.mem_image.mpr
    exact ⟨i, hi, by simp [vertex, he]⟩

omit [DecidableEq I] in
lemma face_eq_iff (g h : G) (A : Finset I) :
    face H g A = face H h A ↔ g⁻¹*h ∈ stabilizer H A := by
  rw [mem_stabilizer]
  constructor
  · intro he i hi
    have hm : vertex H g i ∈ face H h A := by
      rw [← he]
      exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
    exact QuotientGroup.leftRel_apply.mp (Quotient.exact ((vertex_mem H g h i A).mp hm).2)
  · intro he
    apply Finset.ext
    intro x
    rcases x with ⟨i,x⟩
    induction x using Quotient.inductionOn with | h x =>
      change vertex H x i ∈ face H g A ↔ vertex H x i ∈ face H h A
      rw [vertex_mem, vertex_mem]
      by_cases hi : i ∈ A
      · have hg : (QuotientGroup.mk g : G ⧸ H i) = QuotientGroup.mk h :=
          Quotient.sound (QuotientGroup.leftRel_apply.mpr (he i hi))
        rw [hg]
      · simp [hi]

abbrev FaceOfType (A : Finset I) := {σ : Finset (Vertex H) // IsFace H σ ∧ types H σ = A}

def quotientFace (A : Finset I) : G ⧸ stabilizer H A → FaceOfType H A :=
  Quotient.lift (fun g => ⟨face H g A, ⟨g,A,rfl⟩, types_face H g A⟩) (by
    intro g h he
    apply Subtype.ext
    exact (face_eq_iff H g h A).mpr (QuotientGroup.leftRel_apply.mp he))

lemma quotientFace_bijective (A : Finset I) : Function.Bijective (quotientFace H A) := by
  constructor
  · intro a b he
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    exact (face_eq_iff H a b A).mp (congrArg Subtype.val he)
  · rintro ⟨σ,hσ,hA⟩
    obtain ⟨g,B,rfl⟩ := hσ
    have hBA : B = A := by simpa using hA
    subst B
    exact ⟨QuotientGroup.mk g,rfl⟩

end CoboundaryExpanders.TypedCosetFaces

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.TypedCosetFaces

section
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

abbrev Remaining (A : Finset I) := {i : I // i ∉ A}

def linkGroups (A : Finset I) (j : Remaining A) : Subgroup (stabilizer H A) :=
  (H j.val).comap (stabilizer H A).subtype

def linkVertex (A : Finset I) : Vertex (linkGroups H A) → Vertex H :=
  fun x => ⟨x.1.val,Quotient.lift (fun g : stabilizer H A =>
    (QuotientGroup.mk g.val : G ⧸ H x.1.val)) (by
      intro g h he
      apply Quotient.sound
      have hh : g⁻¹*h ∈ linkGroups H A x.1 := QuotientGroup.leftRel_apply.mp he
      exact QuotientGroup.leftRel_apply.mpr hh) x.2⟩

omit [DecidableEq I] in
@[simp] lemma linkVertex_vertex (A : Finset I) (g : stabilizer H A) (j : Remaining A) :
    linkVertex H A (vertex (linkGroups H A) g j) = vertex H g.val j.val := rfl

omit [DecidableEq I] in
lemma linkVertex_injective (A : Finset I) : Function.Injective (linkVertex H A) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  have hij : i = j := Subtype.ext (congrArg Sigma.fst he)
  subst j
  congr 1
  induction x using Quotient.inductionOn with | h x =>
  induction y using Quotient.inductionOn with | h y =>
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  have hq := (Sigma.mk.inj_iff.mp he).2
  have hh := QuotientGroup.leftRel_apply.mp (Quotient.exact (eq_of_heq hq))
  exact hh

@[simp] lemma linkFace_image (A : Finset I) (g : stabilizer H A) (B : Finset (Remaining A)) :
    (face (linkGroups H A) g B).image (linkVertex H A) = face H g.val (B.image Subtype.val) := by
  simp only [face,Finset.image_image,Function.comp_def,linkVertex_vertex]

def IsLinkFace (A : Finset I) (s : Finset (Vertex H)) : Prop :=
  Disjoint s (face H 1 A) ∧ IsFace H (s ∪ face H 1 A)

omit [DecidableEq I] in
lemma face_subset_iff (g h : G) (A B : Finset I) :
    face H g A ⊆ face H h B ↔ A ⊆ B ∧ ∀ i ∈ A,
      (QuotientGroup.mk g : G ⧸ H i) = QuotientGroup.mk h := by
  constructor
  · intro hs
    have hh i hi := (vertex_mem H g h i B).mp (hs (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
    exact ⟨fun i hi => (hh i hi).1,fun i hi => (hh i hi).2⟩
  · rintro ⟨hAB,hgh⟩ v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact (vertex_mem H g h i B).mpr ⟨hAB hi,hgh i hi⟩

theorem isLinkFace_iff (A : Finset I) (s : Finset (Vertex H)) :
    IsLinkFace H A s ↔ ∃ g : stabilizer H A, ∃ B : Finset (Remaining A),
      (face (linkGroups H A) g B).image (linkVertex H A) = s := by
  classical
  constructor
  · rintro ⟨hdis,g,C,hgC⟩
    have hAs : face H 1 A ⊆ face H g C := by rw [hgC]; exact Finset.subset_union_right
    obtain ⟨hAC,hAg⟩ := (face_subset_iff H 1 g A C).mp hAs
    have hg : g ∈ stabilizer H A := by
      rw [mem_stabilizer]
      intro i hi
      have hh := QuotientGroup.leftRel_apply.mp (Quotient.exact (hAg i hi))
      simpa only [inv_one,one_mul] using hh
    let gg : stabilizer H A := ⟨g,hg⟩
    let B : Finset (Remaining A) := (C \ A).subtype (fun i => i ∉ A)
    have hB : B.image Subtype.val = C \ A := by
      ext i
      simp only [B,Finset.mem_image,Finset.mem_subtype,Finset.mem_sdiff]
      constructor
      · rintro ⟨j,hj,rfl⟩; exact hj
      · intro hi; exact ⟨⟨i,hi.2⟩,hi,rfl⟩
    refine ⟨gg,B,?_⟩
    rw [linkFace_image,hB]
    ext v
    constructor
    · intro hv
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      have his := Finset.mem_sdiff.mp hi
      have hm : vertex H g i ∈ s ∪ face H 1 A := by
        rw [← hgC]; exact Finset.mem_image.mpr ⟨i,his.1,rfl⟩
      rcases Finset.mem_union.mp hm with hm | hm
      · exact hm
      · exact False.elim (his.2 ((vertex_mem H g 1 i A).mp hm).1)
    · intro hv
      have hvc : v ∈ face H g C := by rw [hgC]; exact Finset.mem_union_left _ hv
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hvc
      have hiA : i ∉ A := by
        intro hiA
        have hmm : vertex H g i ∈ face H 1 A :=
          (vertex_mem H g 1 i A).mpr ⟨hiA,(hAg i hiA).symm⟩
        exact Finset.disjoint_left.mp hdis hv hmm
      exact Finset.mem_image.mpr ⟨i,Finset.mem_sdiff.mpr ⟨hi,hiA⟩,rfl⟩
  · rintro ⟨g,B,rfl⟩
    rw [linkFace_image]
    have hA : face H g.val A = face H 1 A := by
      apply (face_eq_iff H g.val 1 A).mpr
      simpa only [mul_one] using (stabilizer H A).inv_mem g.property
    constructor
    · apply Finset.disjoint_left.mpr
      intro v hv hvA
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      exact j.property ((vertex_mem H g.val 1 j.val A).mp hvA).1
    · refine ⟨g.val,B.image Subtype.val ∪ A,?_⟩
      rw [face,Finset.image_union]
      change face H g.val (B.image Subtype.val) ∪ face H g.val A = _
      rw [hA]

theorem linkFace_iff (A : Finset I) (s : Finset (Vertex (linkGroups H A))) :
    IsFace (linkGroups H A) s ↔ IsLinkFace H A (s.image (linkVertex H A)) := by
  rw [isLinkFace_iff]
  constructor
  · rintro ⟨g,B,rfl⟩; exact ⟨g,B,rfl⟩
  · rintro ⟨g,B,he⟩
    exact ⟨g,B,Finset.image_injective (linkVertex_injective H A) he⟩

end

section
variable {G G' I I' : Type} [Group G] [Group G'] [DecidableEq I] [DecidableEq I']
  (H : I → Subgroup G) (H' : I' → Subgroup G')
  (e : G ≃* G') (r : I ≃ I')
  (he : ∀ i g, g ∈ H i ↔ e g ∈ H' (r i))

def isoVertex : Vertex H → Vertex H' := fun x =>
  ⟨r x.1,Quotient.lift (fun g : G => (QuotientGroup.mk (e g) : G' ⧸ H' (r x.1))) (by
    intro g h hh
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    have hm := (he x.1 (g⁻¹*h)).mp (QuotientGroup.leftRel_apply.mp hh)
    simpa using hm) x.2⟩

omit [DecidableEq I] [DecidableEq I'] in
@[simp] lemma isoVertex_vertex (g : G) (i : I) :
    isoVertex H H' e r he (vertex H g i) = vertex H' (e g) (r i) := rfl

omit [DecidableEq I] [DecidableEq I'] in
lemma isoVertex_injective : Function.Injective (isoVertex H H' e r he) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ hxy
  have hij : i = j := r.injective (congrArg Sigma.fst hxy)
  subst j
  congr 1
  induction x using Quotient.inductionOn with | h x =>
  induction y using Quotient.inductionOn with | h y =>
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  have hh := QuotientGroup.leftRel_apply.mp
    (Quotient.exact (eq_of_heq (Sigma.mk.inj_iff.mp hxy).2))
  apply (he i (x⁻¹*y)).mpr
  simpa using hh

omit [DecidableEq I] in
@[simp] lemma isoFace_image (g : G) (A : Finset I) :
    (face H g A).image (isoVertex H H' e r he) = face H' (e g) (A.image r) := by
  simp only [face,Finset.image_image,Function.comp_def,isoVertex_vertex]

theorem isoFace_iff (s : Finset (Vertex H)) :
    IsFace H' (s.image (isoVertex H H' e r he)) ↔ IsFace H s := by
  constructor
  · rintro ⟨g,A,hg⟩
    refine ⟨e.symm g,A.image r.symm,?_⟩
    apply Finset.image_injective (isoVertex_injective H H' e r he)
    rw [isoFace_image,e.apply_symm_apply]
    have hi : (A.image r.symm).image r = A := by ext i; simp
    rw [hi]
    exact hg
  · rintro ⟨g,A,rfl⟩
    exact ⟨e g,A.image r,(isoFace_image H H' e r he g A).symm⟩

end

section
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

def vertexLinkGroups (i : I) (j : {j : I // j ≠ i}) : Subgroup (H i) :=
  (H j.val).comap (H i).subtype

def singleStabilizerEquiv (i : I) : H i ≃* stabilizer H {i} :=
  MulEquiv.subgroupCongr (by ext g; simp [mem_stabilizer])

def singleTypesEquiv (i : I) : {j : I // j ≠ i} ≃ Remaining ({i} : Finset I) :=
  Equiv.subtypeEquivRight (fun j => by simp)

omit [DecidableEq I] in
lemma singletonGroups_correspond (i : I) (j : {j : I // j ≠ i}) (g : H i) :
    g ∈ vertexLinkGroups H i j ↔ singleStabilizerEquiv H i g ∈
      linkGroups H {i} (singleTypesEquiv i j) := Iff.rfl

def vertexLinkEmbedding (i : I) : Vertex (vertexLinkGroups H i) → Vertex H :=
  (linkVertex H {i}) ∘ isoVertex (vertexLinkGroups H i) (linkGroups H {i})
    (singleStabilizerEquiv H i) (singleTypesEquiv i) (singletonGroups_correspond H i)

omit [DecidableEq I] in
lemma vertexLinkEmbedding_injective (i : I) : Function.Injective (vertexLinkEmbedding H i) :=
  (linkVertex_injective H {i}).comp (isoVertex_injective _ _ _ _ _)

omit [DecidableEq I] in
@[simp] lemma vertexLinkEmbedding_vertex (i : I) (g : H i) (j : {j : I // j ≠ i}) :
    vertexLinkEmbedding H i (vertex (vertexLinkGroups H i) g j) = vertex H g.val j.val := rfl

theorem vertexLinkFace_iff (i : I) (s : Finset (Vertex (vertexLinkGroups H i))) :
    IsFace (vertexLinkGroups H i) s ↔ IsLinkFace H {i} (s.image (vertexLinkEmbedding H i)) := by
  unfold vertexLinkEmbedding
  rw [← Finset.image_image,← linkFace_iff,isoFace_iff]

lemma vertexLinkFace_surjective (i : I) (s : Finset (Vertex H)) (hs : IsLinkFace H {i} s) :
    ∃ t : Finset (Vertex (vertexLinkGroups H i)), IsFace (vertexLinkGroups H i) t ∧
      t.image (vertexLinkEmbedding H i) = s := by
  obtain ⟨g,A,hg⟩ := (isLinkFace_iff H {i} s).mp hs
  let e := singleStabilizerEquiv H i
  let r := singleTypesEquiv i
  refine ⟨face _ (e.symm g) (A.image r.symm),⟨_,_,rfl⟩,?_⟩
  unfold vertexLinkEmbedding
  rw [← Finset.image_image,isoFace_image,e.apply_symm_apply]
  have hi : (A.image r.symm).image r = A := by
    rw [Finset.image_image]
    have hcomp : (r ∘ r.symm) = id := by funext x; exact r.apply_symm_apply x
    rw [hcomp,Finset.image_id]
  rw [hi]
  exact hg

end

open InfiniteChains InfiniteChains.Cone
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

lemma subset_face {s : Finset (Vertex H)} {g : G} {A : Finset I} (hs : s ⊆ face H g A) :
    face H g (types H s) = s := by
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hi
    obtain ⟨j,hj,hje⟩ := Finset.mem_image.mp (hs hw)
    have hj' : j = i := by simpa only [←hje,vertex] using he
    subst j
    simpa only [hje] using hw
  · intro v hv
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp (hs hv)
    apply Finset.mem_image.mpr
    refine ⟨i,?_,he⟩
    exact Finset.mem_image.mpr ⟨v,hv,by rw [←he]; rfl⟩

lemma IsFace.downward {s t : Finset (Vertex H)} (hs : IsFace H s) (ht : t ⊆ s) : IsFace H t := by
  obtain ⟨g,A,rfl⟩ := hs
  exact ⟨g,types H t,subset_face H ht⟩

def complex : CoboundaryExpanders.InfiniteChains.Complex (Vertex H) where
  faces := {s | IsFace H s}
  empty_mem := ⟨1,∅,Finset.image_empty _⟩
  downward := fun hs ht => hs.downward H ht

def linkComplex (A : Finset I) : CoboundaryExpanders.InfiniteChains.Complex (Vertex H) where
  faces := {s | IsLinkFace H A s}
  empty_mem := ⟨Finset.disjoint_empty_left _,by simpa only [Finset.empty_union] using (show IsFace H (face H 1 A) from ⟨1,A,rfl⟩)⟩
  downward := by
    intro s t hs ht
    refine ⟨Finset.disjoint_left.mpr ?_,hs.2.downward H (Finset.union_subset_union ht (Finset.Subset.refl _))⟩
    intro v hv hv'
    exact Finset.disjoint_left.mp hs.1 (ht hv) hv'

end CoboundaryExpanders.TypedCosetFaces

end

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Flags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Complete flags, spherical opposition, unitriangular groups, and the flag-coset model.
-/

noncomputable section
open scoped BigOperators

namespace CoboundaryExpanders.SphericalOpposition
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

structure CompleteFlag (K V : Type) [Field K] [AddCommGroup V] [Module K V] (N : ℕ) where
  space : Fin (N+1) → Submodule K V
  mono : Monotone space
  dimension : finrank K V = N
  rank : ∀ i, finrank K (space i) = i.val

end CoboundaryExpanders.SphericalOpposition

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

def prefixIndex (i : Fin (N+1)) (j : Fin i.val) : Fin N := ⟨j.val, by omega⟩

lemma prefixIndex_injective (i : Fin (N+1)) : Function.Injective (prefixIndex i) := by
  intro a b h
  apply Fin.ext
  simpa only [prefixIndex] using congrArg (fun j : Fin N => j.val) h

lemma adapted_prefix (F : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ j : Fin N, b j ∈ F.space j.succ) (i : Fin (N+1)) :
    span K (Set.range (fun j : Fin i.val => b (prefixIndex i j))) = F.space i := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact F.mono (by change j.val+1 ≤ i.val; omega) (hb (prefixIndex i j))
  · simpa only [Function.comp_def, Fintype.card_fin, F.rank] using
      finrank_span_eq_card (b.linearIndependent.comp _ (prefixIndex_injective i))

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

open scoped Pointwise

def flagStabilizer (F : CompleteFlag K V N) : Subgroup (V ≃ₗ[K] V) :=
  ⨅ i : Fin (N+1), MulAction.stabilizer (V ≃ₗ[K] V) (F.space i)

omit [FiniteDimensional K V] in
lemma mem_flagStabilizer (F : CompleteFlag K V N) (e : V ≃ₗ[K] V) :
    e ∈ F.flagStabilizer ↔ ∀ i, (F.space i).map e.toLinearMap = F.space i := by
  simp only [flagStabilizer, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  rfl

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

omit [FiniteDimensional K V] in
lemma prefix_span_image (b : Basis (Fin N) K V) (i : Fin (N+1)) :
    Set.range (fun j : Fin i.val => b (prefixIndex i j)) =
      b '' {j : Fin N | j.val < i.val} := by
  ext v
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨prefixIndex i j,j.isLt,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    exact ⟨⟨j.val,hj⟩,rfl⟩

lemma mem_flag_iff_repr (F : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ F.space i.succ) (k : Fin (N+1)) (v : V) :
    v ∈ F.space k ↔ ∀ j : Fin N, k.val ≤ j.val → b.repr v j = 0 := by
  rw [← F.adapted_prefix b hb k, prefix_span_image, b.mem_span_image]
  constructor
  · intro h j hj
    by_contra hn
    have hh := h (Finsupp.mem_support_iff.mpr hn)
    exact Nat.not_lt_of_ge hj hh
  · intro h j hj
    by_contra hn
    have hh := h j (Nat.le_of_not_gt hn)
    exact (Finsupp.mem_support_iff.mp hj) hh

def Unitriangular (b : Basis (Fin N) K V) (e : V ≃ₗ[K] V) : Prop :=
  ∀ i j : Fin N, i ≤ j → b.repr (e (b i)) j = if j = i then 1 else 0

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

omit [FiniteDimensional K V] in
lemma flagStabilizer_mem (F : CompleteFlag K V N) (e : V ≃ₗ[K] V)
    (he : e ∈ F.flagStabilizer) (i : Fin (N+1)) {x : V} (hx : x ∈ F.space i) :
    e x ∈ F.space i := by
  rw [← (F.mem_flagStabilizer e).mp he i]
  exact Submodule.mem_map_of_mem hx

def unipotentFlagStabilizer (F : CompleteFlag K V N) : Subgroup (V ≃ₗ[K] V) where
  carrier := {e | e ∈ F.flagStabilizer ∧ ∀ i : Fin N, ∀ x ∈ F.space i.succ,
    e x - x ∈ F.space i.castSucc}
  one_mem' := ⟨F.flagStabilizer.one_mem,by intro i x hx; simp⟩
  mul_mem' := by
    rintro e f ⟨he,he'⟩ ⟨hf,hf'⟩
    refine ⟨F.flagStabilizer.mul_mem he hf,?_⟩
    intro i x hx
    have h1 := F.flagStabilizer_mem e he i.castSucc (hf' i x hx)
    have h2 := he' i x hx
    have hadd := (F.space i.castSucc).add_mem h1 h2
    simpa only [map_sub, LinearEquiv.mul_apply, sub_add_sub_cancel] using hadd
  inv_mem' := by
    rintro e ⟨he,he'⟩
    refine ⟨F.flagStabilizer.inv_mem he,?_⟩
    intro i x hx
    have hy := F.flagStabilizer_mem e⁻¹ (F.flagStabilizer.inv_mem he) i.succ hx
    have hh := (F.space i.castSucc).neg_mem (he' i (e⁻¹ x) hy)
    have hex : e (e⁻¹ x) = x := e.apply_symm_apply x
    simpa only [hex, neg_sub] using hh

lemma unitriangular_difference (F : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ F.space i.succ) (e : V ≃ₗ[K] V)
    (he : Unitriangular b e) (i : Fin N) : e (b i) - b i ∈ F.space i.castSucc := by
  apply (F.mem_flag_iff_repr b hb i.castSucc _).mpr
  intro j hj
  rw [map_sub, Finsupp.sub_apply, Basis.repr_self, Finsupp.single_apply, he i j hj]
  simp [eq_comm]

lemma unitriangular_grading (F : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ F.space i.succ) (e : V ≃ₗ[K] V)
    (he : Unitriangular b e) (i : Fin N) (x : V) (hx : x ∈ F.space i.succ) :
    e x - x ∈ F.space i.castSucc := by
  let D : V →ₗ[K] V := e.toLinearMap - LinearMap.id
  change x ∈ (F.space i.castSucc).comap D
  have hle : F.space i.succ ≤ (F.space i.castSucc).comap D := by
    rw [← F.adapted_prefix b hb i.succ]
    apply span_le.mpr
    rintro _ ⟨j,rfl⟩
    change e (b (prefixIndex i.succ j)) - b (prefixIndex i.succ j) ∈ F.space i.castSucc
    exact F.mono (by change j.val ≤ i.val; have := j.isLt; simp only [Fin.val_succ] at this; omega)
      (F.unitriangular_difference b hb e he (prefixIndex i.succ j))
  exact hle hx

lemma unipotent_unitriangular (F : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ F.space i.succ) (e : F.unipotentFlagStabilizer) :
    Unitriangular b e.val := by
  intro i j hij
  have h := (F.mem_flag_iff_repr b hb i.castSucc _).mp (e.property.2 i (b i) (hb i)) j hij
  rw [map_sub, Finsupp.sub_apply, Basis.repr_self, Finsupp.single_apply] at h
  simpa [eq_comm] using sub_eq_zero.mp h

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule TypedCosetFaces
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

open scoped Pointwise
def properIndex (i : Fin (N-1)) : Fin (N+1) := ⟨i.val+1, by omega⟩
def baseSpace (E : CompleteFlag K V N) (i : Fin (N-1)) : Submodule K V :=
  E.space (properIndex (N:=N) i)
omit [FiniteDimensional K V] in
@[simp] lemma baseSpace_rank (E : CompleteFlag K V N) (i : Fin (N-1)) :
    finrank K (E.baseSpace i) = i.val+1 := E.rank _

def vertexStabilizers (F E : CompleteFlag K V N) (i : Fin (N-1)) :
    Subgroup F.unipotentFlagStabilizer :=
  MulAction.stabilizer F.unipotentFlagStabilizer (E.baseSpace i)

def cosetVertexMap (F E : CompleteFlag K V N) :
    Vertex (F.vertexStabilizers E) → Submodule K V :=
  fun x => MulAction.ofQuotientStabilizer F.unipotentFlagStabilizer (E.baseSpace x.1) x.2

omit [FiniteDimensional K V] in
@[simp] lemma cosetVertexMap_vertex (F E : CompleteFlag K V N)
    (g : F.unipotentFlagStabilizer) (i : Fin (N-1)) :
    F.cosetVertexMap E (vertex (F.vertexStabilizers E) g i) = g • E.baseSpace i := rfl

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

def basisFlag (b : Basis (Fin N) K V) : CompleteFlag K V N where
  space i := span K (Set.range (fun j : Fin i.val => b (prefixIndex i j)))
  mono := by
    intro i j hij
    apply span_mono
    rintro v ⟨k,rfl⟩
    exact ⟨⟨k.val,by omega⟩,rfl⟩
  dimension := by simpa using Module.finrank_eq_card_basis b
  rank i := by
    have hi : Function.Injective (prefixIndex i) := by
      intro j k he; apply Fin.ext; exact congrArg (fun x : Fin N => x.val) he
    simpa only [Function.comp_def, Fintype.card_fin] using finrank_span_eq_card (b.linearIndependent.comp _ hi)

omit [FiniteDimensional K V] in
lemma basisFlag_adapted (b : Basis (Fin N) K V) (i : Fin N) :
    b i ∈ (basisFlag b).space i.succ := by
  apply Submodule.subset_span
  refine ⟨⟨i.val,by simp⟩,?_⟩
  rfl

lemma unitriangular_flag (F : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ F.space i.succ) (e : V ≃ₗ[K] V)
    (he : Unitriangular b e) (i : Fin (N+1)) :
    (F.space i).map e.toLinearMap = F.space i := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [← F.adapted_prefix b hb i,Submodule.map_span]
    apply span_le.mpr
    rintro x ⟨v,⟨j,rfl⟩,rfl⟩
    rw [F.adapted_prefix b hb i]
    apply (F.mem_flag_iff_repr b hb i _).mpr
    intro k hik
    have hjk : prefixIndex i j ≤ k := by
      change j.val ≤ k.val
      omega
    have hne : k ≠ prefixIndex i j := by
      intro hh; have := congrArg Fin.val hh; dsimp [prefixIndex] at this; omega
    exact (he _ _ hjk).trans (ite_eq_right hne)
  · exact e.finrank_map_eq _

theorem mem_unipotent_iff_unitriangular (F : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ F.space i.succ) (e : V ≃ₗ[K] V) :
    e ∈ F.unipotentFlagStabilizer ↔ Unitriangular b e := by
  constructor
  · intro he; exact F.unipotent_unitriangular b hb ⟨e,he⟩
  · intro he
    exact ⟨(F.mem_flagStabilizer e).mpr (unitriangular_flag F b hb e he),
      F.unitriangular_grading b hb e he⟩

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Elementary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Elementary matrices, Euclidean generation, block matrices, and residue-field pivot arguments.
-/

section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Elementary
variable {A : Type*} [CommRing A] {n : ℕ}

abbrev E {i j : Fin n} (h : i ≠ j) (c : A) :=
  Matrix.SpecialLinearGroup.transvection h c

theorem E_mul_apply {i j : Fin n} (h : i ≠ j) (c : A)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (a b : Fin n) :
    (E h c * g : Matrix.SpecialLinearGroup (Fin n) A) a b =
      g a b + if a = i then c * g j b else 0 := by
  change ((Matrix.transvection i j c) * g.val) a b = _
  by_cases ha : a = i
  · subst a
    simp
  · simp [ha]

def Upper (g : Matrix.SpecialLinearGroup (Fin n) A) : Prop :=
  ∀ i j, j ≤ i → g i j = (1 : Matrix (Fin n) (Fin n) A) i j

theorem upper_E_mul {i j : Fin n} (hij : i < j) (c : A)
    {g : Matrix.SpecialLinearGroup (Fin n) A} (hg : Upper g) :
    Upper (E hij.ne c * g) := by
  intro a b hba
  rw [E_mul_apply, hg a b hba]
  by_cases ha : a = i
  · subst a
    rw [ite_eq_left rfl, hg j b (hba.trans hij.le), Matrix.one_apply_ne (ne_of_gt (lt_of_le_of_lt hba hij))]
    simp
  · simp [ha]

def Cleared (g : Matrix.SpecialLinearGroup (Fin n) A) (k : ℕ) : Prop :=
  ∀ i j, i.val * n + j.val < k → g i j = (1 : Matrix (Fin n) (Fin n) A) i j

theorem E_commutator {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : A) : E hij a * E hjk b * (E hij a)⁻¹ * (E hjk b)⁻¹ = E hik (a * b) := by
  rw [Matrix.SpecialLinearGroup.transvection_inv, Matrix.SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change (1 + Matrix.single i j a) * (1 + Matrix.single j k b) *
    (1 + Matrix.single i j (-a)) * (1 + Matrix.single j k (-b)) =
      1 + Matrix.single i k (a * b)
  simp [mul_add, add_mul,
    hij.symm, hjk.symm, hik.symm, ← Matrix.single_neg]
  abel

end CoboundaryExpanders.Elementary

namespace CoboundaryExpanders.Blocks
variable {A B : Type*} [CommRing A] [CommRing B]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def reindexSL (e : ι ≃ κ) : Matrix.SpecialLinearGroup ι A ≃* Matrix.SpecialLinearGroup κ A where
  toFun g := ⟨Matrix.reindex e e g.val, by rw [Matrix.det_reindex_self]; exact g.property⟩
  invFun g := ⟨Matrix.reindex e.symm e.symm g.val, by rw [Matrix.det_reindex_self]; exact g.property⟩
  left_inv g := by apply Subtype.ext; ext i j; simp [Matrix.reindex_apply]
  right_inv g := by apply Subtype.ext; ext i j; simp [Matrix.reindex_apply]
  map_mul' g h := by apply Subtype.ext; exact (Matrix.reindexRingEquiv A e).map_mul _ _

@[simp] theorem reindexSL_apply (e : ι ≃ κ) (g : Matrix.SpecialLinearGroup ι A) (i j : ι) :
    reindexSL e g (e i) (e j) = g i j := by
  change g.val (e.symm (e i)) (e.symm (e j)) = _
  simp

theorem reindexSL_map (e : ι ≃ κ) (f : A →+* B) (g : Matrix.SpecialLinearGroup ι A) :
    Matrix.SpecialLinearGroup.map f (reindexSL e g) = reindexSL e (Matrix.SpecialLinearGroup.map f g) := by
  ext i j; rfl

def blockSL (a b : ℕ) : Matrix.SpecialLinearGroup (Fin a) A →*
    Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) A where
  toFun g := ⟨Matrix.fromBlocks g.val 0 0 1, by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]; exact g.property⟩
  map_one' := by apply Subtype.ext; exact Matrix.fromBlocks_one
  map_mul' g h := by
    apply Subtype.ext
    change Matrix.fromBlocks (g.val * h.val) 0 0 (1 : Matrix (Fin b) (Fin b) A) =
      Matrix.fromBlocks g.val 0 0 1 * Matrix.fromBlocks h.val 0 0 1
    simp [Matrix.fromBlocks_multiply]

@[simp] theorem blockSL_map (a b : ℕ) (f : A →+* B) (g : Matrix.SpecialLinearGroup (Fin a) A) :
    Matrix.SpecialLinearGroup.map f (blockSL a b g) = blockSL a b (Matrix.SpecialLinearGroup.map f g) := by
  ext i j
  change f (Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin b) (Fin b) A) i j) =
    Matrix.fromBlocks (g.val.map f) 0 0 (1 : Matrix (Fin b) (Fin b) B) i j
  cases i <;> cases j <;> simp [Matrix.one_apply]

def stabilizeSL (a b : ℕ) : Matrix.SpecialLinearGroup (Fin a) A →*
      Matrix.SpecialLinearGroup (Fin (a + b)) A :=
  (reindexSL (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).toMonoidHom.comp (blockSL a b)

theorem stabilizeSL_map (a b : ℕ) (f : A →+* B) (g : Matrix.SpecialLinearGroup (Fin a) A) :
    Matrix.SpecialLinearGroup.map f (stabilizeSL a b g) = stabilizeSL a b (Matrix.SpecialLinearGroup.map f g) := by
  change Matrix.SpecialLinearGroup.map f (reindexSL finSumFinEquiv (blockSL a b g)) = _
  rw [reindexSL_map, blockSL_map]; rfl

@[simp] theorem stabilizeSL_right_row (a b : ℕ) (g : Matrix.SpecialLinearGroup (Fin a) A)
    (i : Fin b) (j : Fin (a + b)) :
    stabilizeSL a b g (Fin.natAdd a i) j = (1 : Matrix (Fin (a + b)) (Fin (a + b)) A) (Fin.natAdd a i) j := by
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).surjective j
  change reindexSL finSumFinEquiv (blockSL a b g) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv j) = _
  rw [reindexSL_apply, Matrix.one_apply]
  change Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin b) (Fin b) A) (Sum.inr i) j = _
  simp only [← finSumFinEquiv_apply_right, finSumFinEquiv.injective.eq_iff]
  cases j <;> simp [Matrix.one_apply]

@[simp] theorem stabilizeSL_right_col (a b : ℕ) (g : Matrix.SpecialLinearGroup (Fin a) A)
    (i : Fin (a + b)) (j : Fin b) :
    stabilizeSL a b g i (Fin.natAdd a j) = (1 : Matrix (Fin (a + b)) (Fin (a + b)) A) i (Fin.natAdd a j) := by
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).surjective i
  change reindexSL finSumFinEquiv (blockSL a b g) (finSumFinEquiv i) (finSumFinEquiv (Sum.inr j)) = _
  rw [reindexSL_apply, Matrix.one_apply]
  change Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin b) (Fin b) A) i (Sum.inr j) = _
  simp only [← finSumFinEquiv_apply_right, finSumFinEquiv.injective.eq_iff]
  cases i <;> simp [Matrix.one_apply]

end CoboundaryExpanders.Blocks

namespace CoboundaryExpanders.Elementary
variable {A : Type*} [CommRing A] {n : ℕ}

theorem E_path_mem (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {a b : A} (ha : E hij a ∈ H) (hb : E hjk b ∈ H) : E hik (a * b) ∈ H := by
  rw [← E_commutator hij hjk hik]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem E_natCast_mul {i j : Fin n} (hij : i ≠ j) (a : A) (r : ℕ) :
    E hij ((r : A) * a) = E hij a ^ r := by
  induction r with
  | zero => simp [E]
  | succ r ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    change Matrix.SpecialLinearGroup.transvection hij (↑r * a + a) = _
    rw [Matrix.SpecialLinearGroup.transvection_add]
    change E hij (↑r * a) * E hij a = _
    rw [ih, pow_succ]

theorem clear_step_relative (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (g : Matrix.SpecialLinearGroup (Fin n) A) (hg : Upper g)
    (hE : ∀ i j (h : i < j), E h.ne (-g i j) ∈ H)
    (k : ℕ) (hk : k < n * n) (hc : Cleared g k) :
    ∃ e ∈ H, Upper (e * g) ∧ Cleared (e * g) (k + 1) := by
  have hn : 0 < n := by nlinarith
  let i : Fin n := ⟨k / n, (Nat.div_lt_iff_lt_mul hn).mpr hk⟩
  let j : Fin n := ⟨k % n, Nat.mod_lt k hn⟩
  have hkij : i.val * n + j.val = k := by
    dsimp [i, j]
    simpa [Nat.mul_comm] using Nat.div_add_mod k n
  by_cases hij : i < j
  · refine ⟨E hij.ne (-g i j), hE i j hij, upper_E_mul hij _ hg, ?_⟩
    intro a b hab
    rw [E_mul_apply]
    by_cases ha : a = i
    · subst a
      rw [ite_eq_left rfl]
      have hbj : b ≤ j := by change b.val ≤ j.val; omega
      rcases hbj.eq_or_lt with rfl | hbj
      · rw [hg j j le_rfl]
        simp [hij.ne]
      · rw [hg j b hbj.le, Matrix.one_apply_ne hbj.ne.symm, mul_zero, add_zero]
        exact hc i b (by omega)
    · rw [ite_eq_right ha, add_zero]
      apply hc a b
      have hne : a.val * n + b.val ≠ k := by
        intro he
        have := congrArg (fun r => r / n) he
        have hab' : b.val < n := b.isLt
        rw [Nat.mul_comm a.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt hab', add_zero] at this
        exact ha (Fin.ext this)
      omega
  · refine ⟨1, H.one_mem, by simpa using hg, ?_⟩
    rw [one_mul]
    intro a b hab
    by_cases hk' : a.val * n + b.val < k
    · exact hc a b hk'
    · have he : a.val * n + b.val = k := by omega
      have hai : a = i := by
        apply Fin.ext
        have := congrArg (fun r => r / n) he
        dsimp [i]
        simpa only [Nat.mul_comm a.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt b.isLt, add_zero] using this
      have hbj : b = j := by
        apply Fin.ext
        have := congrArg (fun r => r % n) he
        simpa [Nat.add_mod, Nat.mod_eq_of_lt b.isLt] using this
      subst a; subst b
      exact hg i j (le_of_not_gt hij)

theorem upper_subgroup_le (P H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hHP : H ≤ P) (hP : ∀ g ∈ P, Upper g)
    (hE : ∀ g ∈ P, ∀ i j (h : i < j), E h.ne (g i j) ∈ H) : P ≤ H := by
  intro g hg
  have hsteps : ∀ k, k ≤ n * n → ∃ h ∈ H, Upper (h * g) ∧ Cleared (h * g) k := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨1, H.one_mem, by simpa using hP g hg, by intro i j h; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨h, hh, hu, hc⟩ := ih (by omega)
      have hhg := P.mul_mem (hHP hh) hg
      have hE' : ∀ i j (hij : i < j), E hij.ne (-((h * g) i j)) ∈ H := by
        intro i j hij
        simpa only [E, Matrix.SpecialLinearGroup.transvection_inv] using
          H.inv_mem (hE (h * g) hhg i j hij)
      obtain ⟨e, he, hu', hc'⟩ := clear_step_relative H (h * g) hu hE' k (by omega) hc
      exact ⟨e * h, H.mul_mem he hh, by simpa only [mul_assoc] using hu',
        by simpa only [mul_assoc] using hc'⟩
  obtain ⟨h, hh, _, hc⟩ := hsteps (n * n) le_rfl
  have he : h * g = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    apply hc
    have hi := i.isLt
    have hj := j.isLt
    nlinarith
  rw [eq_inv_of_mul_eq_one_right he]
  exact H.inv_mem hh

end CoboundaryExpanders.Elementary

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.Elementary
variable {A F : Type*} [CommRing A] [CommRing F] {n : ℕ}

def D {i j : Fin n} (hij : i ≠ j) (u : Aˣ) :
    Matrix.SpecialLinearGroup (Fin n) A :=
  E hij (1 : A) * E hij.symm ((u : A) - 1) * E hij (-(↑(u⁻¹) : A)) *
    E hij.symm (-(((u : A) - 1) * (u : A)))

theorem D_mul_apply {i j : Fin n} (hij : i ≠ j) (u : Aˣ)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (a b : Fin n) :
    (D hij u * g) a b =
      (if a = i then ↑u else if a = j then ↑(u⁻¹) else (1 : A)) * g a b := by
  simp only [D, mul_assoc, E_mul_apply]
  by_cases hai : a = i
  · subst a
    simp only [ite_true, ite_eq_right hij, ite_eq_right hij.symm, one_mul, add_zero]
    have hu : (↑u : A) * ↑(u⁻¹) = 1 := Units.mul_inv u
    linear_combination (g i b * ((u : A)^2 - (u : A)) - g j b) * hu
  · by_cases haj : a = j
    · subst a
      simp only [ite_eq_right hij.symm, ite_eq_right hij, ite_true, one_mul, add_zero]
      have hu : (↑u : A) * ↑(u⁻¹) = 1 := Units.mul_inv u
      linear_combination (g i b * ((u : A) - 1)^2 - g j b) * hu
    · simp [hai, haj]

end CoboundaryExpanders.Elementary

end

section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Elementary

section
variable {A : Type*} [CommRing A] {n : ℕ}

def ColumnPrefix (g : Matrix.SpecialLinearGroup (Fin n) A) (k : ℕ) : Prop :=
  ∀ a b, b.val < k → a ≠ b → g a b = 0

theorem inverse_column_sum (g : Matrix.SpecialLinearGroup (Fin n) A) (i j : Fin n) :
    ∑ a, g⁻¹ i a * g a j = if i = j then 1 else 0 := by
  have h := congrArg (fun M : Matrix.SpecialLinearGroup (Fin n) A => M i j) (inv_mul_cancel g)
  change (g⁻¹.val * g.val) i j = (1 : Matrix (Fin n) (Fin n) A) i j at h
  simpa only [Matrix.mul_apply, Matrix.one_apply] using h

theorem column_diagonal_unit (g : Matrix.SpecialLinearGroup (Fin n) A) (j : Fin n)
    (hcol : ∀ i, i ≠ j → g i j = 0) : IsUnit (g j j) := by
  have hs := inverse_column_sum g j j
  rw [ite_eq_left rfl, Finset.sum_eq_single j] at hs
  · exact isUnit_of_dvd_one ⟨g⁻¹ j j, by rw [mul_comm]; exact hs.symm⟩
  · intro b hb hbj; rw [hcol b hbj, mul_zero]
  · simp

theorem inverse_prefix_zero (g : Matrix.SpecialLinearGroup (Fin n) A)
    {k : ℕ} (hg : ColumnPrefix g k) {i j : Fin n} (hj : j.val < k) (hij : i ≠ j) :
    g⁻¹ i j = 0 := by
  have hu : IsUnit (g j j) := column_diagonal_unit g j (fun a ha => hg a j hj ha)
  have hs := inverse_column_sum g i j
  rw [ite_eq_right hij, Finset.sum_eq_single j] at hs
  · exact (hu.mul_left_eq_zero).mp hs
  · intro b hb hbj; rw [hg b j hj hbj, mul_zero]
  · simp

theorem columnPrefix_E_mul {g : Matrix.SpecialLinearGroup (Fin n) A}
    {k : ℕ} (hg : ColumnPrefix g k) {i j : Fin n} (hij : i ≠ j)
    (hj : k ≤ j.val) (c : A) : ColumnPrefix (E hij c * g) k := by
  intro a b hb hab
  rw [E_mul_apply, hg a b hb hab, hg j b hb (by intro he; subst b; omega)]
  simp

def W {i j : Fin n} (hij : i ≠ j) : Matrix.SpecialLinearGroup (Fin n) A :=
  E hij (1 : A) * E hij.symm (-1) * E hij 1

theorem W_mul_apply {i j : Fin n} (hij : i ≠ j)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (a b : Fin n) :
    (W hij * g : Matrix.SpecialLinearGroup (Fin n) A) a b = if a = i then g j b else if a = j then -g i b else g a b := by
  simp only [W, mul_assoc, E_mul_apply]
  by_cases ha : a = i
  · subst a; simp [hij, hij.symm]
  · by_cases hb : a = j
    · subst a; simp [hij.symm]
    · simp [ha, hb]

theorem W_mem (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H) {i j : Fin n} (hij : i ≠ j) :
    W hij ∈ H := H.mul_mem (H.mul_mem (hE _ _ _ _) (hE _ _ _ _)) (hE _ _ _ _)

theorem columnPrefix_W_mul {g : Matrix.SpecialLinearGroup (Fin n) A}
    {k : ℕ} (hg : ColumnPrefix g k) {i j : Fin n} (hij : i ≠ j)
    (hi : k ≤ i.val) (hj : k ≤ j.val) : ColumnPrefix (W hij * g) k := by
  unfold W
  rw [mul_assoc, mul_assoc]
  exact columnPrefix_E_mul (columnPrefix_E_mul (columnPrefix_E_mul hg hij hj 1)
    hij.symm hi (-1)) hij hj 1

end

section
variable {A : Type*} [CommRing A] {n : ℕ}

theorem clear_column (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (j : Fin n)
    (hg : ColumnPrefix g j.val) (hu : IsUnit (g j j)) :
    ∃ e ∈ H, ColumnPrefix (e * g) (j.val + 1) := by
  classical
  obtain ⟨u, hu⟩ := hu
  have hclear : ∀ s : Finset (Fin n), (∀ a ∈ s, a ≠ j) →
      ∃ e ∈ H, ColumnPrefix (e * g) j.val ∧ (e * g) j j = (u : A) ∧
        ∀ a ∈ s, (e * g) a j = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, H.one_mem, by simpa using hg, by simpa using hu.symm, by simp⟩
    | @insert a s has ih =>
      intro hs
      obtain ⟨e, he, hpref, hpiv, hz⟩ := ih (fun b hb => hs b (Finset.mem_insert_of_mem hb))
      have haj : a ≠ j := hs a (Finset.mem_insert_self _ _)
      let c : A := -((e * g) a j) * (↑(u⁻¹) : A)
      refine ⟨E haj c * e, H.mul_mem (hE _ _ _ _) he, ?_, ?_, ?_⟩
      · rw [mul_assoc]
        exact columnPrefix_E_mul hpref haj le_rfl c
      · rw [mul_assoc, E_mul_apply, ite_eq_right haj.symm, add_zero, hpiv]
      · intro b hb
        rw [mul_assoc, E_mul_apply]
        rcases Finset.mem_insert.mp hb with rfl | hb
        · rw [ite_eq_left rfl, hpiv]
          dsimp [c]
          rw [mul_assoc, Units.inv_mul, mul_one, add_neg_cancel]
        · rw [ite_eq_right (by intro h; subst b; exact has hb), add_zero]
          exact hz b hb
  obtain ⟨e, he, hpref, _, hz⟩ := hclear (Finset.univ.erase j) (by simp)
  refine ⟨e, he, ?_⟩
  intro a b hb hab
  by_cases hbj : b.val < j.val
  · exact hpref a b hbj hab
  · have hbe : b = j := Fin.ext (by omega)
    subst b
    exact hz a (by simp [hab])

end

section
variable {A : Type*} [CommRing A] {n : ℕ}

theorem diagonal_mem_of_roots
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) A))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) A)
    (hdiag : ∀ i j, i ≠ j → g i j = 0) : g ∈ H := by
  have hsteps : ∀ k, k ≤ n → ∃ h ∈ H,
      (∀ i j, i ≠ j → (h * g) i j = 0) ∧
      (∀ i : Fin (n + 1), i.val < k → (h * g) i i = 1) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨1, H.one_mem, by simpa using hdiag,
        by intro i hi; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨h, hh, hd, hc⟩ := ih (by omega)
      let i : Fin (n + 1) := ⟨k, by omega⟩
      have hilast : i < Fin.last n := by change k < n; omega
      obtain ⟨u, hu⟩ := column_diagonal_unit (h * g) i (fun a ha => hd a i ha)
      let e := D hilast.ne u⁻¹
      have he : e ∈ H := H.mul_mem (H.mul_mem (H.mul_mem (hE _ _ _ _) (hE _ _ _ _))
        (hE _ _ _ _)) (hE _ _ _ _)
      refine ⟨e * h, H.mul_mem he hh, ?_, ?_⟩
      · intro a b hab
        rw [mul_assoc, D_mul_apply, hd a b hab, mul_zero]
      · intro a ha
        rw [mul_assoc, D_mul_apply]
        by_cases hai : a = i
        · subst a
          rw [ite_eq_left rfl, ← hu]
          exact Units.inv_mul u
        · have halast : a ≠ Fin.last n := by intro heq; subst a; simp only [Fin.val_last] at ha; omega
          rw [ite_eq_right hai, ite_eq_right halast, one_mul]
          apply hc
          have hne : a.val ≠ k := fun h => hai (Fin.ext h)
          omega
  obtain ⟨h, hh, hd, hc⟩ := hsteps n le_rfl
  have hmatrix : (h * g).val = Matrix.diagonal (fun i => (h * g) i i) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · rw [hd i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : ∏ i, (h * g) i i = (1 : A) := by
    rw [← Matrix.det_diagonal, ← hmatrix]
    exact (h * g).property
  have hfirst : ∀ i : Fin n, (h * g) i.castSucc i.castSucc = 1 := fun i => hc _ i.isLt
  have hlast : (h * g) (Fin.last n) (Fin.last n) = 1 := by
    simpa only [Fin.prod_univ_castSucc, hfirst, Finset.prod_const_one, one_mul] using hdet
  have heq : h * g = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (h * g) i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.one_apply_eq]
      by_cases hilast : i = Fin.last n
      · subst i; exact hlast
      · apply hc
        have := i.isLt
        have := Fin.val_ne_of_ne hilast
        simp only [Fin.val_last] at this
        omega
    · rw [hd i j hij, Matrix.one_apply_ne hij]
  rw [eq_inv_of_mul_eq_one_right heq]
  exact H.inv_mem hh

end

end CoboundaryExpanders.Elementary

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits
open Filter

end

section
open scoped BigOperators Matrix

namespace CoboundaryExpanders.Elementary
variable {A F : Type*} [CommRing A] [Field F] {n : ℕ}

lemma exists_unit_pivot_residue (π : A →+* F)
    (hu : ∀ a, π a ≠ 0 → IsUnit a)
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (j : Fin n)
    (hg : ColumnPrefix g j.val) :
    ∃ e ∈ H, ColumnPrefix (e * g) j.val ∧ IsUnit ((e * g) j j) := by
  classical
  have ha : ∃ a : Fin n, j ≤ a ∧ π (g a j) ≠ 0 := by
    by_contra! h
    have hs := congrArg π (inverse_column_sum g j j)
    simp only [ite_true, map_sum, map_mul, map_one] at hs
    have hz : (∑ a, π (g⁻¹ j a) * π (g a j)) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      by_cases hja : j ≤ a
      · rw [h a hja, mul_zero]
      · rw [inverse_prefix_zero g hg (show a.val < j.val from lt_of_not_ge hja)
          (ne_of_gt (lt_of_not_ge hja)), map_zero, zero_mul]
    exact zero_ne_one (hz.symm.trans hs)
  obtain ⟨a,hja,ha⟩ := ha
  by_cases haj : a = j
  · subst a
    exact ⟨1,H.one_mem,by simpa using hg,by simpa using hu (g j j) ha⟩
  · refine ⟨W (Ne.symm haj), W_mem H hE (Ne.symm haj),
      columnPrefix_W_mul hg (Ne.symm haj) le_rfl hja, ?_⟩
    rw [W_mul_apply]
    simpa [haj] using hu (g a j) ha

lemma diagonalize_residue (π : A →+* F) (hu : ∀ a, π a ≠ 0 → IsUnit a)
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) A) :
    ∃ e ∈ H, ∀ i j, i ≠ j → (e*g) i j = 0 := by
  have hsteps : ∀ k, k ≤ n → ∃ e ∈ H, ColumnPrefix (e*g) k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨1,H.one_mem,by intro a b h; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨e,he,hpref⟩ := ih (by omega)
      let j : Fin n := ⟨k,by omega⟩
      obtain ⟨h,hh,hpref',hpiv⟩ := exists_unit_pivot_residue π hu H hE (e*g) j hpref
      obtain ⟨r,hr,hcol⟩ := clear_column H hE (h*(e*g)) j hpref' hpiv
      exact ⟨r*h*e,H.mul_mem (H.mul_mem hr hh) he,by simpa [mul_assoc,j] using hcol⟩
  obtain ⟨e,he,hpref⟩ := hsteps n le_rfl
  exact ⟨e,he,fun i j hij => hpref i j j.isLt hij⟩

theorem SL_mem_of_residue_units (π : A →+* F) (hu : ∀ a, π a ≠ 0 → IsUnit a)
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) A) : g ∈ H := by
  cases n with
  | zero =>
    have hg : g = 1 := by ext i; exact Fin.elim0 i
    rw [hg]; exact H.one_mem
  | succ n =>
    obtain ⟨e,he,hd⟩ := diagonalize_residue π hu H hE g
    have hm := diagonal_mem_of_roots H hE (e*g) hd
    simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem he) hm

theorem SL_map_surjective {B : Type*} [CommRing B] (f : B →+* A)
    (hf : Function.Surjective f) (π : A →+* F) (hu : ∀ a, π a ≠ 0 → IsUnit a) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin n) f) := by
  intro g
  apply SL_mem_of_residue_units π hu (Matrix.SpecialLinearGroup.map f).range _ g
  intro i j hij c
  obtain ⟨c,rfl⟩ := hf c
  refine ⟨E hij c,?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro a b
  change f ((Matrix.transvection i j c) a b) = (Matrix.transvection i j (f c)) a b
  simp only [Matrix.transvection, Matrix.add_apply, map_add, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp
end CoboundaryExpanders.Elementary

end

open scoped BigOperators Matrix
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.Elementary
variable {A B : Type*} [CommRing A] [CommRing B] {ι : Type*}
    [Fintype ι] [DecidableEq ι]

lemma SL_map_surjective_reindex (f : A →+* B)
    (hf : Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin (Fintype.card ι)) f)) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n := ι) f) := by
  intro g
  let e := Fintype.equivFin ι
  obtain ⟨h,hh⟩ := hf (Blocks.reindexSL e g)
  refine ⟨Blocks.reindexSL e.symm h, ?_⟩
  rw [Blocks.reindexSL_map, hh]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change g (e.symm (e i)) (e.symm (e j)) = g i j
  simp
end CoboundaryExpanders.Elementary

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Patterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Pattern subgroups, matrix opposition, block decompositions, and suffix equivalences.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Patterns

section
open CoboundaryExpanders.Construction CoboundaryExpanders.Elementary
variable {n : ℕ}

def cutRank (cut i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨if i.val < cut.val then i.val + (n + 1) - cut.val else i.val - cut.val, by
    split_ifs <;> omega⟩

theorem cutRank_injective (cut : Fin (n + 1)) : Function.Injective (cutRank cut) := by
  intro i j he
  have he' := congrArg Fin.val he
  simp only [cutRank, Fin.val_mk] at he'
  apply Fin.ext
  split_ifs at he' <;> omega

def cutOrder (cut : Fin (n + 1)) : Fin (n + 1) ≃ Fin (n + 1) :=
  Equiv.ofBijective (cutRank cut) ⟨cutRank_injective cut, Finite.surjective_of_injective (cutRank_injective cut)⟩

def Arc (a b j : Fin (n + 1)) : Prop :=
  if a.val < b.val then a.val < j.val ∧ j.val ≤ b.val
  else a.val < j.val ∨ j.val ≤ b.val

theorem cutRank_lt_iff (cut a b : Fin (n + 1)) (hab : a ≠ b) :
    cutRank cut a < cutRank cut b ↔ ¬ Arc a b cut := by
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  change (if a.val < cut.val then a.val + (n + 1) - cut.val else a.val - cut.val) <
    (if b.val < cut.val then b.val + (n + 1) - cut.val else b.val - cut.val) ↔ _
  unfold Arc
  split_ifs <;> omega

def reindexSL {A : Type*} [CommRing A] (e : Fin (n + 1) ≃ Fin (n + 1)) :
    Matrix.SpecialLinearGroup (Fin (n + 1)) A ≃*
      Matrix.SpecialLinearGroup (Fin (n + 1)) A where
  toFun g := ⟨Matrix.reindex e e g.val, by rw [Matrix.det_reindex_self]; exact g.property⟩
  invFun g := ⟨Matrix.reindex e.symm e.symm g.val, by rw [Matrix.det_reindex_self]; exact g.property⟩
  left_inv g := by apply Subtype.ext; ext i j; simp [Matrix.reindex_apply]
  right_inv g := by apply Subtype.ext; ext i j; simp [Matrix.reindex_apply]
  map_mul' g h := by
    apply Subtype.ext
    exact (Matrix.reindexRingEquiv A e).map_mul g.val h.val

@[simp] theorem reindexSL_apply {A : Type*} [CommRing A]
    (e : Fin (n + 1) ≃ Fin (n + 1)) (g : Matrix.SpecialLinearGroup (Fin (n + 1)) A)
    (i j : Fin (n + 1)) : reindexSL e g (e i) (e j) = g i j := by
  change g.val (e.symm (e i)) (e.symm (e j)) = g i j
  simp

@[simp] theorem reindexSL_E {A : Type*} [CommRing A]
    (e : Fin (n + 1) ≃ Fin (n + 1)) {i j : Fin (n + 1)} (h : i ≠ j) (c : A) :
    reindexSL e (E h c) = E (show e i ≠ e j from fun he => h (e.injective he)) c := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply,
    Matrix.one_apply, e.injective.eq_iff]

variable (p : ℕ) [Fact p.Prime]

def upperMonoid (N : ℕ) : Submonoid (Matrix.SpecialLinearGroup (Fin N) (R p)) where
  carrier := {g | Upper g}
  one_mem' := by intro i j h; rfl
  mul_mem' := by
    intro g h hg hh i j hij
    change (g.val * h.val) i j = _
    rw [Matrix.mul_apply]
    by_cases he : i = j
    · subst j
      rw [Finset.sum_eq_single i]
      · rw [hg i i le_rfl, hh i i le_rfl]; simp
      · intro l _ hli
        rcases lt_or_gt_of_ne hli with hl | hl
        · rw [hg i l hl.le]; simp [ne_of_gt hl]
        · rw [hh l i hl.le]; simp [ne_of_gt hl]
      · simp
    · rw [Matrix.one_apply_ne he]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : l < i
      · rw [hg i l hl.le]; simp [ne_of_gt hl]
      · have hjl : j < l := lt_of_lt_of_le (lt_of_le_of_ne hij (Ne.symm he)) (le_of_not_gt hl)
        rw [hh l j hjl.le]; simp [ne_of_gt hjl]

theorem upper_prime_power (N : ℕ) (g : Matrix.SpecialLinearGroup (Fin N) (R p))
    (hg : Upper g) : ∃ r : ℕ, g ^ p ^ r = 1 := by
  have hn : IsNilpotent (g.val - 1) := by
    refine ⟨N, strict_upper_pow_zero N _ ?_⟩
    intro i j hij
    rw [Matrix.sub_apply, hg i j hij, sub_self]
  have hc : (p : Matrix (Fin N) (Fin N) (R p)) = 0 := by
    ext i j
    simp [Matrix.natCast_apply]
  obtain ⟨r, hr⟩ := exists_prime_power_unipotent (Fact.out : p.Prime) hc _ hn
  refine ⟨r, Subtype.ext ?_⟩
  simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
    add_sub_cancel] using hr

def upperSubgroup (N : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin N) (R p)) :=
  { upperMonoid p N with
    inv_mem' := by
      intro g hg
      obtain ⟨r, hr⟩ := upper_prime_power p N g hg
      have hp : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos _
      have he : g⁻¹ = g ^ (p ^ r - 1) := by
        apply inv_eq_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel hp, hr]
      rw [he]
      exact (upperMonoid p N).pow_mem hg _ }

def cutUpper (cut : Fin (n + 1)) : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)) :=
  (upperSubgroup p (n + 1)).comap (reindexSL (cutOrder cut)).toMonoidHom

theorem cutUpper_iff (cut : Fin (n + 1)) (g : Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)) :
    g ∈ cutUpper p cut ↔ ∀ i j, cutRank cut j ≤ cutRank cut i →
      g i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) (R p)) i j := by
  change Upper (reindexSL (cutOrder cut) g) ↔ _
  constructor
  · intro h i j hij
    have := h (cutOrder cut i) (cutOrder cut j) hij
    simpa only [reindexSL_apply, Matrix.one_apply, (cutOrder cut).injective.eq_iff] using this
  · intro h a b hab
    obtain ⟨i, rfl⟩ := (cutOrder cut).surjective a
    obtain ⟨j, rfl⟩ := (cutOrder cut).surjective b
    simpa only [reindexSL_apply, Matrix.one_apply, (cutOrder cut).injective.eq_iff] using h i j hab

end

section
open CoboundaryExpanders.Construction CoboundaryExpanders.Elementary
variable (p n : ℕ) [Fact p.Prime]

def rootGroup (hn : 1 ≤ n) (J : Set (Fin (n + 1))) :
    Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)) :=
  Subgroup.closure {g | ∃ j ∈ J, g = cycleRoot p n hn j}

omit [Fact p.Prime] in
theorem root_mem (hn : 1 ≤ n) (J : Set (Fin (n + 1))) {j : Fin (n + 1)} (hj : j ∈ J) :
    cycleRoot p n hn j ∈ rootGroup p n hn J := Subgroup.subset_closure ⟨j, hj, rfl⟩

omit [Fact p.Prime] in
theorem upper_adjacent_mem (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    {a b : Fin (n + 1)} (hab : a.val + 1 = b.val) (hb : b ∈ J) :
    E (show a ≠ b by intro he; subst b; omega) (1 : R p) ∈ rootGroup p n hn J := by
  have hb0 : b ≠ 0 := by intro he; subst b; simp at hab
  have hs : edgeSource n b = a := by
    apply Fin.ext
    simp only [edgeSource, dite_eq_right hb0, Fin.val_mk]
    omega
  simpa [cycleRoot, hs, hb0] using root_mem p n hn J hb

omit [Fact p.Prime] in
theorem upper_path_mem (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    {a b : Fin (n + 1)} (hab : a < b)
    (hpath : ∀ j, a.val < j.val → j.val ≤ b.val → j ∈ J) :
    E hab.ne (1 : R p) ∈ rootGroup p n hn J := by
  generalize hdiff : b.val - a.val = r
  induction r using Nat.strong_induction_on generalizing a b with
  | h r ih =>
    by_cases hadj : a.val + 1 = b.val
    · exact upper_adjacent_mem p n hn J hadj (hpath b hab le_rfl)
    · let c : Fin (n + 1) := ⟨b.val - 1, by omega⟩
      have hac : a < c := by dsimp [c]; change a.val < b.val - 1; omega
      have hcb : c.val + 1 = b.val := by dsimp [c]; omega
      have hcb' : c < b := by change c.val < b.val; omega
      have hc := ih (c.val - a.val) (by omega) hac (fun j hj hj' => hpath j hj (by omega)) rfl
      simpa only [mul_one] using E_path_mem (rootGroup p n hn J) hac.ne hcb'.ne hab.ne hc
        (upper_adjacent_mem p n hn J hcb (hpath b hab le_rfl))

omit [Fact p.Prime] in
theorem lower_path_mem (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    {a b : Fin (n + 1)} (hba : b < a)
    (hpath : ∀ j, a.val < j.val ∨ j.val ≤ b.val → j ∈ J) :
    E hba.ne.symm (Polynomial.X : R p) ∈ rootGroup p n hn J := by
  have ha0 : a ≠ 0 := by intro he; subst a; have := hba; change b.val < 0 at this; omega
  have hn0 : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    intro he; have := congrArg Fin.val he; simp only [Fin.val_last, Fin.val_zero] at this; omega
  have h0 : E hn0 (Polynomial.X : R p) ∈ rootGroup p n hn J := by
    simpa [cycleRoot, edgeSource] using root_mem p n hn J (hpath 0 (Or.inr (Nat.zero_le _)))
  have ha : E ha0 (Polynomial.X : R p) ∈ rootGroup p n hn J := by
    by_cases he : a = Fin.last n
    · subst a; exact h0
    · have hal : a < Fin.last n := by
        have hv : a.val ≠ n := fun h => he (Fin.ext h)
        change a.val < n
        omega
      have hau := upper_path_mem p n hn J hal (fun j hj _ => hpath j (Or.inl hj))
      simpa only [one_mul] using E_path_mem (rootGroup p n hn J) hal.ne hn0 ha0 hau h0
  by_cases hb0 : b = 0
  · subst b; exact ha
  · have h0b : (0 : Fin (n + 1)) < b := by
      have hv : b.val ≠ 0 := fun h => hb0 (Fin.ext h)
      change 0 < b.val
      omega
    have hbu := upper_path_mem p n hn J h0b (fun j _ hj => hpath j (Or.inr hj))
    simpa only [mul_one] using E_path_mem (rootGroup p n hn J) ha0 h0b.ne hba.ne.symm ha hbu

theorem scalar_root_mem (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    {a b : Fin (n + 1)} (hab : a ≠ b) (f : R p)
    (hf : E hab f ∈ rootGroup p n hn J) (c : ZMod p) :
    E hab (Polynomial.C c * f) ∈ rootGroup p n hn J := by
  have hc : Polynomial.C c = (c.val : R p) := by
    rw [← map_natCast Polynomial.C, ZMod.natCast_zmod_val]
  rw [hc, E_natCast_mul]
  exact (rootGroup p n hn J).pow_mem hf _

def pathCoefficient {a b : Fin (n + 1)} (c : ZMod p) : R p :=
  Polynomial.C c * if a.val < b.val then 1 else Polynomial.X

theorem path_root_mem (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    {a b : Fin (n + 1)} (hab : a ≠ b) (hpath : ∀ j, Arc a b j → j ∈ J) (c : ZMod p) :
    E hab (pathCoefficient (p := p) (n := n) (a := a) (b := b) c) ∈ rootGroup p n hn J := by
  unfold pathCoefficient
  by_cases hab' : a < b
  · rw [ite_eq_left (show a.val < b.val from hab')]
    exact scalar_root_mem p n hn J hab _ (upper_path_mem p n hn J hab'
      (fun j hj hj' => hpath j (by simpa [Arc, show a.val < b.val from hab'] using And.intro hj hj'))) c
  · rw [ite_eq_right (show ¬ a.val < b.val from hab')]
    have hba : b < a := lt_of_le_of_ne (le_of_not_gt hab') hab.symm
    exact scalar_root_mem p n hn J hab _ (lower_path_mem p n hn J hba
      (fun j hj => hpath j (by simpa [Arc, show ¬ a.val < b.val from hab'] using hj))) c

end

open CoboundaryExpanders.Construction CoboundaryExpanders.Elementary
variable (p n : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
@[simp] theorem rootGroup_empty (hn : 1 ≤ n) : rootGroup p n hn ∅ = ⊥ := by
  simp [rootGroup]

omit [Fact p.Prime] in
@[simp] theorem rootGroup_compl_singleton (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    rootGroup p n hn ({cut}ᶜ) = localGroup p n hn cut := by
  simp [rootGroup, localGroup]

end CoboundaryExpanders.Patterns

namespace CoboundaryExpanders.MatrixOpposition
open Module Submodule SphericalOpposition SphericalOpposition.CompleteFlag Elementary
open scoped Matrix Pointwise
variable {K : Type} [Field K] {N : ℕ}

abbrev stdFlag (K : Type) [Field K] (N : ℕ) : CompleteFlag K (Fin N → K) N :=
  basisFlag (K:=K) (V:=Fin N → K) (Pi.basisFun K (Fin N))

lemma upper_iff_unipotent (g : Matrix.SpecialLinearGroup (Fin N) K) :
    Upper g ↔ Matrix.SpecialLinearGroup.toLin' g ∈ (stdFlag K N).unipotentFlagStabilizer := by
  rw [mem_unipotent_iff_unitriangular _ _ (basisFlag_adapted _)]
  unfold Unitriangular Upper
  simp only [Pi.basisFun_repr, Pi.basisFun_apply, Matrix.SpecialLinearGroup.toLin'_apply,
    Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.one_apply]
  exact ⟨fun h i j hij => h j i hij,fun h i j hij => h j i hij⟩

def upperGroup (K : Type) [Field K] (N : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin N) K) :=
  (stdFlag K N).unipotentFlagStabilizer.comap Matrix.SpecialLinearGroup.toLin'

@[simp] lemma mem_upperGroup (g : Matrix.SpecialLinearGroup (Fin N) K) :
    g ∈ upperGroup K N ↔ Upper g := (upper_iff_unipotent g).symm

end CoboundaryExpanders.MatrixOpposition

namespace CoboundaryExpanders.Patterns

section
open Construction Elementary MatrixOpposition SphericalOpposition.CompleteFlag
open scoped Matrix Pointwise
variable {n : ℕ}

@[simp] lemma cutOrder_cut (cut : Fin (n+1)) : cutOrder cut cut = 0 := by
  apply Fin.ext
  change (cutRank cut cut).val = 0
  simp [cutRank]

end

end CoboundaryExpanders.Patterns

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Links
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coset-link identifications, product and cut models, and all proper-link cone bounds.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Construction

section
open Patterns MatrixOpposition SphericalOpposition.CompleteFlag
open scoped Pointwise
variable (p n : ℕ) [Fact p.Prime]

def localReducedHom (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n+1)) :
    localGroup p n hn cut →* reducedLocalGroup p n hn m cut where
  toFun g := ⟨localQuotientMap p n hn m cut g,
    ⟨⟨g.val,localGroup_le_U p n hn cut g.property⟩,g.property,rfl⟩⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' g h := by apply Subtype.ext; exact map_mul _ g h

lemma localReducedHom_surjective (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n+1)) :
    Function.Surjective (localReducedHom p n hn m cut) := by
  rintro ⟨q,hq⟩
  obtain ⟨g,hg,hgq⟩ := hq
  exact ⟨⟨g.val,hg⟩,Subtype.ext hgq⟩

lemma localQuotient_cross_injective (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (cut j : Fin (n+1)) (g : localGroup p n hn cut) (h : localGroup p n hn j)
    (he : localQuotientMap p n hn m cut g = localQuotientMap p n hn m j h) :
    g.val = h.val := by
  apply localGroups_reduction_injective p n hn hm cut j g h
  exact congrArg (fun q : Gquot p (n+1) m =>
    (QuotientGroup.quotientKerEquivRange (uReduction p (n+1) m) q).val) he

lemma localReducedHom_injective (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1)) :
    Function.Injective (localReducedHom p n hn m cut) := by
  intro g h he
  apply Subtype.ext
  exact localQuotient_cross_injective p n hn hm cut cut g h (congrArg Subtype.val he)

def localReducedEquiv (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1)) :
    localGroup p n hn cut ≃* reducedLocalGroup p n hn m cut :=
  MulEquiv.ofBijective (localReducedHom p n hn m cut)
    ⟨localReducedHom_injective p n hn hm cut,localReducedHom_surjective p n hn m cut⟩

lemma localReducedHom_mem_iff (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (cut j : Fin (n+1)) (g : localGroup p n hn cut) :
    (localReducedHom p n hn m cut g).val ∈ reducedLocalGroup p n hn m j ↔
      g.val ∈ localGroup p n hn j := by
  constructor
  · rintro ⟨b,hb,he⟩
    have he' : localQuotientMap p n hn m j ⟨b.val,hb⟩ =
        localQuotientMap p n hn m cut g := he
    exact (localQuotient_cross_injective p n hn hm j cut ⟨b.val,hb⟩ g he') ▸ hb
  · intro hg
    exact ⟨⟨g.val,localGroup_le_U p n hn j hg⟩,hg,rfl⟩

end

section
open Patterns MatrixOpposition TypedCosetFaces SphericalOpposition.CompleteFlag
open scoped Pointwise
variable (p n : ℕ) [Fact p.Prime]

def quotientLinkGroups (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n+1))
    (j : {j : Fin (n+1) // j ≠ cut}) : Subgroup (reducedLocalGroup p n hn m cut) :=
  (reducedLocalGroup p n hn m j.val).comap (reducedLocalGroup p n hn m cut).subtype

def actualLinkEmbedding (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n+1)) :
    Vertex (quotientLinkGroups p n hn m cut) → Vertex (reducedLocalGroup p n hn m) :=
  vertexLinkEmbedding (reducedLocalGroup p n hn m) cut

lemma actualLinkEmbedding_injective (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n+1)) :
    Function.Injective (actualLinkEmbedding p n hn m cut) :=
  vertexLinkEmbedding_injective _ _

lemma actualLinkFace_surjective (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n+1))
    (s : Finset (Vertex (reducedLocalGroup p n hn m)))
    (hs : IsLinkFace (reducedLocalGroup p n hn m) {cut} s) :
    ∃ t : Finset (Vertex (quotientLinkGroups p n hn m cut)),
      IsFace (quotientLinkGroups p n hn m cut) t ∧
      t.image (actualLinkEmbedding p n hn m cut) = s :=
  vertexLinkFace_surjective _ _ _ hs

end

open InfiniteChains InfiniteChains.Cone TypedCosetFaces SphericalOpposition.CompleteFlag
open Patterns MatrixOpposition
variable (p n : ℕ) [Fact p.Prime]

def actualVertexLinkModel (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n+1)) :
    FaceModel (TypedCosetFaces.complex (quotientLinkGroups p n hn m cut))
      (linkComplex (reducedLocalGroup p n hn m) {cut}) where
  vertex := actualLinkEmbedding p n hn m cut
  injective := actualLinkEmbedding_injective p n hn m cut
  face_iff := fun s => (vertexLinkFace_iff (reducedLocalGroup p n hn m) cut s).symm
  cover := fun t ht => actualLinkFace_surjective p n hn m cut t ht

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.TypedCosetFaces
variable {G K I J : Type} [Group G] [Group K] [DecidableEq I] [DecidableEq J]
  (H : I → Subgroup G) (L : J → Subgroup K)

def productGroups : I ⊕ J → Subgroup (G × K)
  | Sum.inl i => (H i).prod ⊤
  | Sum.inr j => (⊤ : Subgroup G).prod (L j)

def productVertex : Vertex (productGroups H L) → Vertex H ⊕ Vertex L
  | ⟨Sum.inl i,q⟩ => Quotient.lift (fun g : G × K => Sum.inl (vertex H g.1 i)) (by
      intro g h hgh
      apply congrArg Sum.inl
      refine Sigma.ext (by rfl) (heq_of_eq ?_)
      apply Quotient.sound
      exact QuotientGroup.leftRel_apply.mpr (QuotientGroup.leftRel_apply.mp hgh).1) q
  | ⟨Sum.inr j,q⟩ => Quotient.lift (fun g : G × K => Sum.inr (vertex L g.2 j)) (by
      intro g h hgh
      apply congrArg Sum.inr
      refine Sigma.ext (by rfl) (heq_of_eq ?_)
      apply Quotient.sound
      exact QuotientGroup.leftRel_apply.mpr (QuotientGroup.leftRel_apply.mp hgh).2) q

omit [DecidableEq I] [DecidableEq J] in
@[simp] lemma productVertex_left (g : G × K) (i : I) :
    productVertex H L (vertex (productGroups H L) g (Sum.inl i)) = Sum.inl (vertex H g.1 i) := rfl
omit [DecidableEq I] [DecidableEq J] in
@[simp] lemma productVertex_right (g : G × K) (j : J) :
    productVertex H L (vertex (productGroups H L) g (Sum.inr j)) = Sum.inr (vertex L g.2 j) := rfl

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone
open scoped Pointwise
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

instance vertexAction : MulAction G (Vertex H) where
  smul g v := ⟨v.1,g • v.2⟩
  one_smul v := by rcases v with ⟨i,v⟩; exact congrArg (Sigma.mk i) (one_smul G v)
  mul_smul g h v := by rcases v with ⟨i,v⟩; exact congrArg (Sigma.mk i) (mul_smul g h v)

omit [DecidableEq I] in
@[simp] lemma smul_vertex (g h : G) (i : I) : g • vertex H h i = vertex H (g*h) i := rfl

omit [DecidableEq I] in
@[simp] lemma smul_face (g h : G) (A : Finset I) : g • face H h A = face H (g*h) A := by
  simp only [Finset.smul_finset_def,face,Finset.image_image,Function.comp_def,smul_vertex]

end CoboundaryExpanders.TypedCosetFaces

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_LinkSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Rank-two incidence geometry, weighted Rayleigh inequalities, and spectral bounds for links.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.InfiniteChains
namespace FiniteWeights
variable {V : Type} [Fintype V] [DecidableEq V]
def level (X : CoboundaryExpanders.InfiniteChains.Complex V) (r : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun s => s ∈ X.faces ∧ s.card = r)

omit [DecidableEq V] in
@[simp] lemma mem_level (X : CoboundaryExpanders.InfiniteChains.Complex V) (r : ℕ) (s : Finset V) :
    s ∈ level X r ↔ s ∈ X.faces ∧ s.card = r := by simp [level]

end FiniteWeights

open FiniteWeights
attribute [local instance] Classical.propDecidable

end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.Construction
open InfiniteChains Cone TypedCosetFaces SphericalOpposition.CompleteFlag MatrixOpposition
noncomputable local instance finiteFintype (A : Type) [Finite A] : Fintype A := Fintype.ofFinite A

end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Averaging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite F2 averaging and bounded-cone estimates for weighted local cochains.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.Averaging

section
open scoped BigOperators
variable {A B G : Type} [Fintype A] [Fintype B] [Fintype G]
  [DecidableEq A] [DecidableEq B] [DecidableEq G]

def supportNorm (w : A → ℝ) (f : A → ZMod 2) : ℝ :=
  ∑ a, if f a = 0 then 0 else w a

end

open scoped BigOperators

end CoboundaryExpanders.Averaging

namespace CoboundaryExpanders.InfiniteChains.Cone
open Attachment
variable {V : Type} [DecidableEq V]

def eval (f : Finset V → k) : Raw V →ₗ[k] k := Finsupp.linearCombination k f

omit [DecidableEq V] in
@[simp] lemma eval_single (f : Finset V → k) (s : Finset V) (a : k) :
    eval f (Finsupp.single s a) = a * f s := by simp [eval, smul_eq_mul]

def delta (f : Finset V → k) (s : Finset V) : k :=
  eval f (rawBoundary (Finsupp.single s 1))

@[simp] lemma delta_eq_sum (f : Finset V → k) (s : Finset V) :
    delta f s = ∑ v ∈ s, f (s.erase v) := by simp [delta]

variable {G : Type} [Group G] [MulAction G V]
open scoped Pointwise

def pull (g : G) (f : Finset V → k) (s : Finset V) : k := f (g • s)

@[simp] lemma pull_inv (g : G) (f : Finset V → k) : pull g (pull g⁻¹ f) = f := by
  funext s
  simp [pull]

end CoboundaryExpanders.InfiniteChains.Cone

namespace CoboundaryExpanders.InfiniteChains.FiniteWeights

section
open Attachment Cone Averaging
open scoped BigOperators Pointwise
variable {V : Type} [Fintype V] [DecidableEq V]

variable {G : Type} [Group G] [Fintype G] [MulAction G V]

def Invariant (G : Type) [Group G] [MulAction G V] (X : CoboundaryExpanders.InfiniteChains.Complex V) : Prop :=
  ∀ (g : G) s, s ∈ X.faces → g • s ∈ X.faces

@[instance_reducible]
def faceAction {X : CoboundaryExpanders.InfiniteChains.Complex V} (hX : Invariant G X) (r : ℕ) : MulAction G (X.Face r) where
  smul g s := ⟨g • s.val, hX g s.val s.property.1, by simp [s.property.2]⟩
  one_smul s := Subtype.ext (one_smul _ _)
  mul_smul g h s := Subtype.ext (mul_smul g h s.val)

end

open Attachment Cone Averaging
open scoped BigOperators Pointwise

end CoboundaryExpanders.InfiniteChains.FiniteWeights

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Lattices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Affine and rational lattices, polynomial congruence actions, and lattice-chain geometry.
-/

noncomputable section


namespace CoboundaryExpanders.AffineLattices
open InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
open scoped BigOperators

variable {P : Type} [Lattice P] (T : P ≃o P) (C : P)

def level : ℕ → P
  | 0 => C
  | m+1 => T (level m)

@[simp] lemma level_zero : level T C 0 = C := rfl
@[simp] lemma level_succ (m : ℕ) : level T C (m+1) = T (level T C m) := rfl

lemma level_antitone (hC : T C ≤ C) : Antitone (level T C) := by
  apply antitone_nat_of_succ_le
  intro m
  induction m with
  | zero => exact hC
  | succ m ih => exact T.monotone ih

lemma level_le (hC : T C ≤ C) (m : ℕ) : level T C m ≤ C :=
  level_antitone T C hC (Nat.zero_le m)

def IsVertex (A : P) : Prop :=
  A ≤ C ∧ ¬ A ≤ T C ∧ (∃ m, level T C m ≤ A) ∧ T A ≤ A

abbrev Vertex := {A : P // IsVertex T C A}

instance instPartialOrderVertex : PartialOrder (Vertex T C) := Subtype.partialOrder _

noncomputable instance instDecidableEqVertex : DecidableEq (Vertex T C) := Classical.decEq _

lemma vertex_le (A : Vertex T C) : (A : P) ≤ C := A.property.1
lemma vertex_normalized (A : Vertex T C) : ¬ (A : P) ≤ T C := A.property.2.1
lemma vertex_bounded (A : Vertex T C) : ∃ m, level T C m ≤ (A : P) := A.property.2.2.1
lemma vertex_shift_le (A : Vertex T C) : T (A : P) ≤ (A : P) := A.property.2.2.2

def base (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) : Vertex T C :=
  ⟨C,le_rfl,hstrict,⟨0,le_rfl⟩,hC⟩

def IsFace (s : Finset (Vertex T C)) : Prop :=
  (∀ A ∈ s, ∀ B ∈ s, A ≤ B ∨ B ≤ A) ∧
  (∀ A ∈ s, ∀ B ∈ s, T (A : P) ≤ (B : P))

def complex : InfiniteChains.Complex (Vertex T C) where
  faces := {s | IsFace T C s}
  empty_mem := by simp [IsFace]
  downward := by
    intro s t hs ht
    exact ⟨fun A hA B hB => hs.1 A (ht hA) B (ht hB),
      fun A hA B hB => hs.2 A (ht hA) B (ht hB)⟩

def ball (m : ℕ) : InfiniteChains.Complex (Vertex T C) where
  faces := {s | IsFace T C s ∧ ∀ A ∈ s, level T C m ≤ (A : P)}
  empty_mem := ⟨(complex T C).empty_mem,by simp⟩
  downward := fun hs ht => ⟨(complex T C).downward hs.1 ht,fun A hA => hs.2 A (ht hA)⟩

def raise (hC : T C ≤ C) (m : ℕ) (A : Vertex T C) : Vertex T C :=
  ⟨(A : P) ⊔ level T C m, sup_le (vertex_le T C A) (level_le T C hC m),
    fun h => vertex_normalized T C A (le_sup_left.trans h),
    ⟨m,le_sup_right⟩, by
      rw [T.map_sup]
      exact sup_le_sup (vertex_shift_le T C A) (level_antitone T C hC (Nat.le_succ m))⟩

@[simp] lemma raise_val (hC : T C ≤ C) (m : ℕ) (A : Vertex T C) :
    (raise T C hC m A : P) = (A : P) ⊔ level T C m := rfl

end CoboundaryExpanders.AffineLattices

namespace CoboundaryExpanders.RationalLattices
open InfiniteChains InfiniteChains.Attachment
open scoped Polynomial
variable (K : Type) [Field K] (N : ℕ)

abbrev V := Fin N → RatFunc K
abbrev LatticeSpace := Submodule K[X] (V K N)

def uniformizer : RatFunc K := algebraMap K[X] (RatFunc K) Polynomial.X
lemma uniformizer_ne_zero : uniformizer K ≠ 0 :=
  RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero

noncomputable def shiftLinear : V K N ≃ₗ[K[X]] V K N :=
  (LinearEquiv.smulOfNeZero (RatFunc K) (V K N) (uniformizer K)
    (uniformizer_ne_zero K)).restrictScalars K[X]

@[simp] lemma shiftLinear_apply (v : V K N) (i : Fin N) :
    shiftLinear K N v i = uniformizer K * v i := rfl

noncomputable def shift : LatticeSpace K N ≃o LatticeSpace K N :=
  Submodule.orderIsoMapComap (shiftLinear K N)

def standard : LatticeSpace K N where
  carrier := {v | ∀ i, ∃ f : K[X], algebraMap K[X] (RatFunc K) f = v i}
  zero_mem' := fun _ => ⟨0,map_zero _⟩
  add_mem' := by
    intro v w hv hw i
    obtain ⟨f,hf⟩ := hv i
    obtain ⟨g,hg⟩ := hw i
    exact ⟨f+g,by simp only [map_add,hf,hg,Pi.add_apply]⟩
  smul_mem' := by
    intro a v hv i
    obtain ⟨f,hf⟩ := hv i
    refine ⟨a*f,?_⟩
    simp only [map_mul,hf,Pi.smul_apply,Algebra.smul_def]

lemma mem_shift (A : LatticeSpace K N) (v : V K N) :
    v ∈ shift K N A ↔ ∃ w ∈ A, shiftLinear K N w = v :=
  Submodule.mem_map

lemma shift_standard_le : shift K N (standard K N) ≤ standard K N := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := (mem_shift K N _ _).mp hv
  intro i
  obtain ⟨f,hf⟩ := hw i
  refine ⟨Polynomial.X*f,?_⟩
  simp only [map_mul,hf,shiftLinear_apply,uniformizer]

lemma shift_le_self (A : LatticeSpace K N) : shift K N A ≤ A := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := (mem_shift K N _ _).mp hv
  have he : shiftLinear K N w = (Polynomial.X : K[X]) • w := by
    ext i
    simp only [shiftLinear_apply,Pi.smul_apply,Algebra.smul_def,uniformizer]
  rw [he]
  exact A.smul_mem Polynomial.X hw

lemma standard_not_le_shift (hN : 0 < N) :
    ¬ standard K N ≤ shift K N (standard K N) := by
  intro hle
  let v : V K N := fun _ => 1
  have hv : v ∈ standard K N := fun _ => ⟨1,map_one _⟩
  obtain ⟨w,hw,he⟩ := (mem_shift K N _ _).mp (hle hv)
  obtain ⟨f,hf⟩ := hw ⟨0,hN⟩
  have hm : algebraMap K[X] (RatFunc K) (Polynomial.X*f) =
      algebraMap K[X] (RatFunc K) 1 := by
    simpa only [map_mul,hf,map_one,uniformizer,shiftLinear_apply] using
      congr_fun he ⟨0,hN⟩
  have hp : Polynomial.X*f = 1 := RatFunc.algebraMap_injective K hm
  have hc := congrArg Polynomial.constantCoeff hp
  simp at hc

noncomputable abbrev Vertex := AffineLattices.Vertex (shift K N) (standard K N)

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
variable (K : Type) [Field K]

noncomputable def positive : K[X] →+* RatFunc K :=
  Polynomial.eval₂RingHom (algebraMap K (RatFunc K)) (uniformizer K)⁻¹

lemma eval_uniformizer (f : K[X]) :
    Polynomial.eval₂ (algebraMap K (RatFunc K)) (uniformizer K) f =
      algebraMap K[X] (RatFunc K) f := by
  exact Polynomial.eval₂_algebraMap_X f (IsScalarTower.toAlgHom K K[X] (RatFunc K))

lemma positive_mul_uniformizer (f : K[X]) :
    positive K f * uniformizer K ^ f.natDegree =
      algebraMap K[X] (RatFunc K) f.reverse := by
  let : Invertible ((uniformizer K)⁻¹) := invertibleOfNonzero (inv_ne_zero (uniformizer_ne_zero K))
  have he := Polynomial.eval₂_reverse_mul_pow (algebraMap K (RatFunc K)) ((uniformizer K)⁻¹) f
  simp only [invOf_eq_inv,inv_inv,eval_uniformizer,inv_pow] at he
  change _ = positive K f at he
  rw [← he]
  rw [mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ (uniformizer_ne_zero K)),mul_one]

lemma positive_regular_iff (f : K[X]) (b : ℕ) :
    (∃ g : K[X], algebraMap K[X] (RatFunc K) g = positive K f * uniformizer K ^ b) ↔
      f.natDegree ≤ b := by
  constructor
  · rintro ⟨g,hg⟩
    by_cases hf : f = 0
    · simp [hf]
    by_contra hle
    have hlt : b < f.natDegree := by omega
    have he : f.reverse * Polynomial.X^b = g * Polynomial.X^f.natDegree := by
      apply RatFunc.algebraMap_injective K
      simp only [map_mul,map_pow]
      rw [hg,← positive_mul_uniformizer K f]
      unfold uniformizer
      ring
    have hc := congrArg (fun p : K[X] => p.coeff b) he
    have hright : (g*Polynomial.X^f.natDegree).coeff b = 0 := by
      rw [Polynomial.coeff_mul_X_pow']
      simp [not_le.mpr hlt]
    rw [hright] at hc
    have hleft : (f.reverse*Polynomial.X^b).coeff b = f.leadingCoeff := by
      simpa using Polynomial.coeff_mul_X_pow f.reverse b 0
    rw [hleft] at hc
    exact Polynomial.leadingCoeff_ne_zero.mpr hf hc
  · intro hf
    refine ⟨f.reverse * Polynomial.X^(b-f.natDegree),?_⟩
    rw [map_mul,map_pow,← positive_mul_uniformizer K f]
    change (positive K f * uniformizer K ^ f.natDegree) * uniformizer K ^ (b-f.natDegree) = positive K f * uniformizer K ^ b
    rw [mul_assoc,← pow_add,Nat.add_sub_of_le hf]

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
variable (K : Type) [Field K]
lemma positive_zero_of_uniformizer_dvd (f g : K[X])
    (hg : uniformizer K * algebraMap K[X] (RatFunc K) g = positive K f) : f = 0 := by
  by_contra hf
  have he : f.reverse = Polynomial.X^(f.natDegree+1)*g := by
    apply RatFunc.algebraMap_injective K
    rw [← positive_mul_uniformizer K f,← hg]
    simp only [map_mul,map_pow,pow_succ]
    unfold uniformizer
    ring
  have hc := congrArg Polynomial.constantCoeff he
  have hleft : f.reverse.constantCoeff = f.leadingCoeff := by simp
  rw [hleft] at hc
  have hright : (Polynomial.X^(f.natDegree+1)*g).constantCoeff = 0 := by simp
  rw [hright] at hc
  exact Polynomial.leadingCoeff_ne_zero.mpr hf hc

lemma positive_C (c : K) : positive K (Polynomial.C c) = algebraMap K (RatFunc K) c := by
  simp [positive]
lemma positive_X : positive K Polynomial.X = (uniformizer K)⁻¹ := by simp [positive]

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.Construction
open CoboundaryExpanders.Elementary CoboundaryExpanders.Patterns
variable (p n : ℕ) [Fact p.Prime]

def cutPolynomialStabilizer (cut : Fin (n+1)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin (n+1)) (R p)) :=
  U p (n+1) ⊓ (Matrix.GeneralLinearGroup.map (n := Fin (n+1)) (algebraMap (ZMod p) (Frac p))).range.comap (cutConjugation p n cut)

lemma polynomialStabilizer_equation (cut : Fin (n+1))
    (g : cutPolynomialStabilizer p n cut) (i j : Fin (n+1)) :
    ∃ c : ZMod p, cutPolynomial p n cut i * g.val i j =
      Polynomial.C c * cutPolynomial p n cut j := by
  obtain ⟨B,hB⟩ := g.property.2
  refine ⟨B i j, IsFractionRing.injective (R p) (Frac p) ?_⟩
  have he := congrArg (fun g : Matrix.GeneralLinearGroup (Fin (n+1)) (Frac p) => g i j) hB
  change algebraMap (ZMod p) (Frac p) (B i j) = cutConjugation p n cut g.val i j at he
  rw [cutConjugation_apply] at he
  have he' := congrArg (fun x : Frac p => x * (cutUnit p n cut j).val) he
  simp only [mul_assoc, Units.inv_val, mul_one] at he'
  rw [map_mul, map_mul, ← cutUnit_coe, ← cutUnit_coe]
  simpa only [IsScalarTower.algebraMap_apply (ZMod p) (R p) (Frac p), Polynomial.algebraMap_eq] using he'.symm

lemma polynomialStabilizer_upper (cut : Fin (n+1)) :
    cutPolynomialStabilizer p n cut ≤ cutUpper p cut := by
  intro g hg
  rw [cutUpper_iff]
  intro a b hba
  obtain ⟨c,hc⟩ := polynomialStabilizer_equation p n cut ⟨g,hg⟩ a b
  have hu : ∀ a b : Fin (n+1), b ≤ a →
      Polynomial.eval 0 (g a b) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod p)) a b := hg.1
  unfold cutPolynomial at hc
  change (if b.val < cut.val then b.val+(n+1)-cut.val else b.val-cut.val) ≤
    (if a.val < cut.val then a.val+(n+1)-cut.val else a.val-cut.val) at hba
  have hconstant : ∀ (f : R p) (c : ZMod p), f = Polynomial.C c → b ≤ a →
      Polynomial.eval 0 f = (1 : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod p)) a b →
      f = (1 : Matrix (Fin (n+1)) (Fin (n+1)) (R p)) a b := by
    intro f c hf _ he
    rw [hf] at he ⊢
    simp only [Polynomial.eval_C,Matrix.one_apply] at he
    rw [he]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  by_cases ha : a.val < cut.val <;> by_cases hb : b.val < cut.val
  · rw [ite_eq_left ha,ite_eq_left hb] at hc
    have he : g a b = Polynomial.C c := mul_left_cancel₀ Polynomial.X_ne_zero
      (hc.trans (mul_comm _ _))
    have hle : b ≤ a := by simp only [ite_eq_left ha,ite_eq_left hb] at hba; change b.val ≤ a.val; omega
    exact hconstant _ _ he hle (hu a b hle)
  · rw [ite_eq_left ha,ite_eq_right hb,mul_one] at hc
    have hc0 : c = 0 := by
      have he := congrArg Polynomial.constantCoeff hc
      simpa using he.symm
    rw [hc0,Polynomial.C_0] at hc
    have hg0 : g a b = 0 := (mul_eq_zero.mp hc).resolve_left Polynomial.X_ne_zero
    rw [hg0,Matrix.one_apply,ite_eq_right (by intro he; subst b; omega)]
  · simp only [ite_eq_right ha,ite_eq_left hb] at hba
    omega
  · rw [ite_eq_right ha,ite_eq_right hb,one_mul,mul_one] at hc
    have hle : b ≤ a := by simp only [ite_eq_right ha,ite_eq_right hb] at hba; change b.val ≤ a.val; omega
    exact hconstant _ _ hc hle (hu a b hle)

lemma polynomialStabilizer_coefficient (cut : Fin (n+1))
    (g : cutPolynomialStabilizer p n cut) {a b : Fin (n+1)}
    (hlt : cutRank cut a < cutRank cut b) :
    ∃ c : ZMod p, g.val a b = pathCoefficient (p := p) (n := n) (a := a) (b := b) c := by
  obtain ⟨c,hc⟩ := polynomialStabilizer_equation p n cut g a b
  refine ⟨c,?_⟩
  unfold cutPolynomial at hc
  unfold pathCoefficient
  change (if a.val < cut.val then a.val+(n+1)-cut.val else a.val-cut.val) <
    (if b.val < cut.val then b.val+(n+1)-cut.val else b.val-cut.val) at hlt
  by_cases ha : a.val < cut.val <;> by_cases hb : b.val < cut.val
  · rw [ite_eq_left ha,ite_eq_left hb] at hc
    have hab : a.val < b.val := by simp only [ite_eq_left ha,ite_eq_left hb] at hlt; omega
    rw [ite_eq_left hab,mul_one]
    exact mul_left_cancel₀ Polynomial.X_ne_zero (hc.trans (mul_comm _ _))
  · simp only [ite_eq_left ha,ite_eq_right hb] at hlt
    omega
  · rw [ite_eq_right ha,ite_eq_left hb,one_mul] at hc
    rw [ite_eq_right (by omega : ¬ a.val < b.val)]
    exact hc
  · rw [ite_eq_right ha,ite_eq_right hb,one_mul,mul_one] at hc
    have hab : a.val < b.val := by simp only [ite_eq_right ha,ite_eq_right hb] at hlt; omega
    rw [ite_eq_left hab,mul_one]
    exact hc

theorem cutPolynomialStabilizer_eq_localGroup (hn : 1 ≤ n) (cut : Fin (n+1)) :
    cutPolynomialStabilizer p n cut = localGroup p n hn cut := by
  have hHP : localGroup p n hn cut ≤ cutPolynomialStabilizer p n cut :=
    le_inf (localGroup_le_U p n hn cut) (localGroup_le_constant p n hn cut)
  apply le_antisymm _ hHP
  let e := reindexSL (A := R p) (cutOrder cut)
  let P := (cutPolynomialStabilizer p n cut).map e.toMonoidHom
  let H := (localGroup p n hn cut).map e.toMonoidHom
  have hP : ∀ g ∈ P, Upper g := by
    rintro _ ⟨g,hg,rfl⟩
    exact polynomialStabilizer_upper p n cut hg
  have hE : ∀ g ∈ P, ∀ i j (h : i < j), E h.ne (g i j) ∈ H := by
    rintro _ ⟨g,hg,rfl⟩ i j hij
    obtain ⟨a,rfl⟩ := (cutOrder cut).surjective i
    obtain ⟨b,rfl⟩ := (cutOrder cut).surjective j
    have hab : a ≠ b := fun he => hij.ne (congrArg (cutOrder cut) he)
    obtain ⟨c,hc⟩ := polynomialStabilizer_coefficient p n cut ⟨g,hg⟩ hij
    have hmem : E hab (g a b) ∈ localGroup p n hn cut := by
      rw [hc]
      apply path_root_mem p n hn {j | j ≠ cut} hab
      intro j hj he
      subst j
      exact ((cutRank_lt_iff cut a b hab).mp hij) hj
    refine ⟨E hab (g a b),hmem,?_⟩
    change reindexSL (cutOrder cut) _ = _
    rw [reindexSL_E]
    congr 1
    exact (reindexSL_apply (cutOrder cut) g a b).symm
  have hPH := upper_subgroup_le P H (Subgroup.map_mono hHP) hP hE
  intro g hg
  obtain ⟨h,hh,he⟩ := hPH ⟨g,hg,rfl⟩
  exact e.injective he ▸ hh
end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.Construction
variable (p n : ℕ) [Fact p.Prime]
lemma mem_polynomialStabilizer_of_equations (cut : Fin (n+1))
    (g : Matrix.SpecialLinearGroup (Fin (n+1)) (R p))
    (hu : g ∈ U p (n+1))
    (he : ∀ i j, ∃ c : ZMod p, cutPolynomial p n cut i * g i j =
      Polynomial.C c * cutPolynomial p n cut j) :
    g ∈ cutPolynomialStabilizer p n cut := by
  classical
  choose c hc using he
  let B : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod p) := c
  have hmap : B.map (algebraMap (ZMod p) (Frac p)) = (cutConjugation p n cut g).val := by
    ext i j
    change algebraMap (ZMod p) (Frac p) (c i j) = cutConjugation p n cut g i j
    rw [cutConjugation_apply]
    have h := congrArg (algebraMap (R p) (Frac p)) (hc i j)
    simp only [map_mul,← cutUnit_coe] at h
    have hm := congrArg (fun x : Frac p => x * (cutUnit p n cut j).inv) h
    simpa only [mul_assoc,Units.val_inv, mul_one,
      IsScalarTower.algebraMap_apply (ZMod p) (R p) (Frac p), Polynomial.algebraMap_eq] using hm.symm
  have hd : B.det ≠ 0 := by
    intro hz
    have hm := congrArg Matrix.det hmap
    change ((algebraMap (ZMod p) (Frac p)).mapMatrix B).det = _ at hm
    rw [← RingHom.map_det, hz,map_zero] at hm
    exact Matrix.GeneralLinearGroup.det_ne_zero _ hm.symm
  refine ⟨hu, Matrix.GeneralLinearGroup.mk'' B (isUnit_iff_ne_zero.mpr hd), ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact congrFun (congrFun hmap i) j

theorem mem_localGroup_iff_cut_equations (hn : 1 ≤ n) (cut : Fin (n+1))
    (g : Matrix.SpecialLinearGroup (Fin (n+1)) (R p)) :
    g ∈ localGroup p n hn cut ↔ g ∈ U p (n+1) ∧
      ∀ i j, ∃ c : ZMod p, cutPolynomial p n cut i * g i j =
        Polynomial.C c * cutPolynomial p n cut j := by
  constructor
  · intro hg
    exact ⟨localGroup_le_U p n hn cut hg,fun i j => localGroup_entry_equation p n hn cut ⟨g,hg⟩ i j⟩
  · rintro ⟨hu,he⟩
    rw [← cutPolynomialStabilizer_eq_localGroup p n hn cut]
    exact mem_polynomialStabilizer_of_equations p n cut g hu he
end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
variable (K : Type) [Field K] (N : ℕ)

def cutExponent (cut i : Fin N) : ℕ := if i.val < cut.val then 1 else 0

def cutLattice (cut : Fin N) : LatticeSpace K N where
  carrier := {v | ∀ i, ∃ f : K[X], algebraMap K[X] (RatFunc K) f * uniformizer K ^ cutExponent N cut i = v i}
  zero_mem' := fun i => ⟨0,by simp⟩
  add_mem' := by
    intro v w hv hw i
    obtain ⟨f,hf⟩ := hv i
    obtain ⟨g,hg⟩ := hw i
    exact ⟨f+g,by rw [map_add,add_mul,hf,hg]; rfl⟩
  smul_mem' := by
    intro a v hv i
    obtain ⟨f,hf⟩ := hv i
    refine ⟨a*f,?_⟩
    simp only [map_mul,mul_assoc,hf,Pi.smul_apply,Algebra.smul_def]

noncomputable def positiveMatrix (g : Matrix (Fin N) (Fin N) K[X]) : Matrix (Fin N) (Fin N) (RatFunc K) :=
  g.map (positive K)

def CutRegular (cut i j : Fin N) (f : K[X]) : Prop :=
  ∃ h : K[X], algebraMap K[X] (RatFunc K) h * uniformizer K ^ cutExponent N cut i =
    positive K f * uniformizer K ^ cutExponent N cut j

lemma preserves_cut_iff (cut : Fin N) (g : Matrix (Fin N) (Fin N) K[X]) :
    (∀ v ∈ cutLattice K N cut, (positiveMatrix K N g).mulVec v ∈ cutLattice K N cut) ↔
    ∀ i j, CutRegular K N cut i j (g i j) := by
  classical
  constructor
  · intro h i j
    let v : V K N := Pi.single j (uniformizer K ^ cutExponent N cut j)
    have hv : v ∈ cutLattice K N cut := by
      intro a
      by_cases ha : a = j
      · subst a
        exact ⟨1,by simp [v]⟩
      · exact ⟨0,by simp [v,ha]⟩
    obtain ⟨f,hf⟩ := h v hv i
    refine ⟨f,?_⟩
    simpa [v,Matrix.mulVec_single,positiveMatrix,mul_comm] using hf
  · intro h v hv i
    choose f hf using hv
    choose a ha using fun j => h i j
    refine ⟨∑ j, a j * f j,?_⟩
    simp only [map_sum,map_mul,Finset.sum_mul,Matrix.mulVec,dotProduct,positiveMatrix,Matrix.map_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [← hf j]
    calc
      _ = (algebraMap K[X] (RatFunc K) (a j) * uniformizer K ^ cutExponent N cut i) * algebraMap K[X] (RatFunc K) (f j) := by ring
      _ = _ := by rw [ha j]; ring

lemma regular_same (f : K[X]) (b : ℕ) :
    (∃ h : K[X], algebraMap K[X] (RatFunc K) h * uniformizer K ^ b = positive K f * uniformizer K ^ b) ↔
      ∃ c : K, f = Polynomial.C c := by
  constructor
  · rintro ⟨h,hh⟩
    have he := mul_right_cancel₀ (pow_ne_zero _ (uniformizer_ne_zero K)) hh
    have hd := (positive_regular_iff K f 0).mp ⟨h,by simpa using he⟩
    exact ⟨f.coeff 0,Polynomial.eq_C_of_natDegree_le_zero hd⟩
  · rintro ⟨c,rfl⟩
    exact ⟨Polynomial.C c,by simp [positive_C]⟩

lemma regular_cut_equation (cut i j : Fin N) (f : K[X])
    (hzero : j.val < i.val → Polynomial.eval 0 f = 0)
    (hr : CutRegular K N cut i j f) :
    ∃ c : K, (if i.val < cut.val then (Polynomial.X : K[X]) else 1) * f =
      Polynomial.C c * (if j.val < cut.val then Polynomial.X else 1) := by
  obtain ⟨h,hh⟩ := hr
  by_cases hi : i.val < cut.val <;> by_cases hj : j.val < cut.val
  · simp only [cutExponent,ite_eq_left hi,ite_eq_left hj,pow_one] at hh
    obtain ⟨c,hc⟩ := (regular_same K f 1).mp ⟨h,by simpa using hh⟩
    exact ⟨c,by rw [ite_eq_left hi,ite_eq_left hj,hc,mul_comm]⟩
  · simp only [cutExponent,ite_eq_left hi,ite_eq_right hj,pow_one,pow_zero,mul_one] at hh
    have hf : f = 0 := positive_zero_of_uniformizer_dvd K f h (by simpa only [mul_comm] using hh)
    exact ⟨0,by simp [hf]⟩
  · simp only [cutExponent,ite_eq_right hi,ite_eq_left hj,pow_one,pow_zero,mul_one] at hh
    have hd := (positive_regular_iff K f 1).mp ⟨h,by simpa using hh⟩
    have hz : f.coeff 0 = 0 := by simpa only [Polynomial.coeff_zero_eq_eval_zero] using hzero (by omega)
    have hf := Polynomial.eq_X_add_C_of_natDegree_le_one hd
    rw [hz,Polynomial.C_0,add_zero] at hf
    exact ⟨f.coeff 1,by simpa only [ite_eq_right hi,ite_eq_left hj,one_mul] using hf⟩
  · simp only [cutExponent,ite_eq_right hi,ite_eq_right hj,pow_zero,mul_one] at hh
    obtain ⟨c,hc⟩ := (regular_same K f 0).mp ⟨h,by simpa using hh⟩
    exact ⟨c,by simp [hi,hj,hc]⟩

lemma regular_of_cut_equation (cut i j : Fin N) (f : K[X]) (c : K)
    (hc : (if i.val < cut.val then (Polynomial.X : K[X]) else 1) * f =
      Polynomial.C c * (if j.val < cut.val then Polynomial.X else 1)) :
    CutRegular K N cut i j f := by
  have he := congrArg (positive K) hc
  simp only [map_mul,apply_ite,map_one,positive_X,positive_C] at he
  refine ⟨Polynomial.C c,?_⟩
  have hC : algebraMap K[X] (RatFunc K) (Polynomial.C c) = algebraMap K (RatFunc K) c := by
    exact (IsScalarTower.algebraMap_apply K K[X] (RatFunc K) c).symm
  rw [hC]
  by_cases hi : i.val < cut.val <;> by_cases hj : j.val < cut.val
  · simp only [ite_eq_left hi,ite_eq_left hj] at he
    simp only [cutExponent,ite_eq_left hi,ite_eq_left hj,pow_one]
    have he' : positive K f = algebraMap K (RatFunc K) c := by
      apply mul_left_cancel₀ (inv_ne_zero (uniformizer_ne_zero K))
      simpa only [mul_comm] using he
    rw [he']
  · simp only [ite_eq_left hi,ite_eq_right hj,mul_one] at he
    simp only [cutExponent,ite_eq_left hi,ite_eq_right hj,pow_one,pow_zero,mul_one]
    rw [← he]
    field_simp [uniformizer_ne_zero K]
  · simp only [ite_eq_right hi,ite_eq_left hj,one_mul] at he
    simp only [cutExponent,ite_eq_right hi,ite_eq_left hj,pow_one,pow_zero,mul_one]
    rw [he,mul_assoc,inv_mul_cancel₀ (uniformizer_ne_zero K),mul_one]
  · simp only [ite_eq_right hi,ite_eq_right hj,one_mul,mul_one] at he
    simpa only [cutExponent,ite_eq_right hi,ite_eq_right hj,pow_zero,mul_one] using he.symm

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.Construction
open CoboundaryExpanders.RationalLattices
variable (p n : ℕ) [Fact p.Prime]

theorem preserves_cutLattice_iff_localGroup (hn : 1 ≤ n) (cut : Fin (n+1))
    (g : Matrix.SpecialLinearGroup (Fin (n+1)) (R p)) (hu : g ∈ U p (n+1)) :
    (∀ v ∈ cutLattice (ZMod p) (n+1) cut,
      (positiveMatrix (ZMod p) (n+1) g.val).mulVec v ∈ cutLattice (ZMod p) (n+1) cut) ↔
      g ∈ localGroup p n hn cut := by
  rw [preserves_cut_iff,mem_localGroup_iff_cut_equations]
  constructor
  · intro h
    refine ⟨hu,fun i j => ?_⟩
    apply regular_cut_equation (ZMod p) (n+1) cut i j (g i j) _ (h i j)
    intro hji
    have he := hu i j (show j ≤ i from le_of_lt hji)
    change Polynomial.eval 0 (g i j) = _ at he
    simpa only [Matrix.one_apply,ite_eq_right (show i ≠ j by intro h; subst j; omega)] using he
  · rintro ⟨_,h⟩ i j
    obtain ⟨c,hc⟩ := h i j
    exact regular_of_cut_equation (ZMod p) (n+1) cut i j (g i j) c hc
end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
variable (K : Type) [Field K] (N : ℕ)

lemma cut_le_standard (cut : Fin N) : cutLattice K N cut ≤ standard K N := by
  intro v hv i
  obtain ⟨f,hf⟩ := hv i
  exact ⟨f * Polynomial.X ^ cutExponent N cut i,by simpa only [map_mul,map_pow,uniformizer] using hf⟩

lemma shift_standard_le_cut (cut : Fin N) : shift K N (standard K N) ≤ cutLattice K N cut := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := (mem_shift K N _ _).mp hv
  intro i
  obtain ⟨f,hf⟩ := hw i
  by_cases hi : i.val < cut.val
  · exact ⟨f,by simp only [cutExponent,ite_eq_left hi,pow_one,hf,shiftLinear_apply,mul_comm]⟩
  · exact ⟨Polynomial.X*f,by simp only [cutExponent,ite_eq_right hi,pow_zero,mul_one,map_mul,hf,shiftLinear_apply,uniformizer]⟩

lemma uniformizer_mul_ne_one (f : K[X]) : uniformizer K * algebraMap K[X] (RatFunc K) f ≠ 1 := by
  intro hf
  have hp : Polynomial.X * f = 1 := RatFunc.algebraMap_injective K (by simpa only [map_mul,map_one,uniformizer] using hf)
  have hz := congrArg Polynomial.constantCoeff hp
  simp at hz

lemma single_mem_cut (cut : Fin N) : Pi.single cut (1 : RatFunc K) ∈ cutLattice K N cut := by
  intro i
  by_cases hi : i = cut
  · subst i
    exact ⟨1,by simp [cutExponent]⟩
  · exact ⟨0,by simp [hi]⟩

lemma cut_not_le_shift (cut : Fin N) : ¬ cutLattice K N cut ≤ shift K N (standard K N) := by
  intro hle
  obtain ⟨w,hw,he⟩ := (mem_shift K N _ _).mp (hle (single_mem_cut K N cut))
  obtain ⟨f,hf⟩ := hw cut
  apply uniformizer_mul_ne_one K f
  simpa only [shiftLinear_apply,Pi.single_eq_same,hf] using congr_fun he cut

noncomputable def cutVertex (cut : Fin N) : Vertex K N :=
  ⟨cutLattice K N cut,cut_le_standard K N cut,cut_not_le_shift K N cut,
    ⟨1,shift_standard_le_cut K N cut⟩,shift_le_self K N _⟩

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.AffineLattices
variable {P : Type} [Lattice P] (T : P ≃o P) (C : P)

noncomputable def iterIso : ℕ → P ≃o P
  | 0 => OrderIso.refl P
  | m+1 => (iterIso m).trans T

@[simp] lemma iterIso_apply (m : ℕ) (A : P) : iterIso T m A = level T A m := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg T ih

lemma level_map (A : P) (m : ℕ) : level T (T A) m = T (level T A m) := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg T ih

lemma level_add (A : P) (a b : ℕ) : level T A (a+b) = level T (level T A a) b := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg T ih

lemma level_mono (m : ℕ) {A B : P} (h : A ≤ B) : level T A m ≤ level T B m :=
  by simpa only [iterIso_apply] using (iterIso T m).monotone h

lemma level_injective (m : ℕ) : Function.Injective (fun A => level T A m) :=
  by
    intro A B he
    apply (iterIso T m).injective
    simpa only [iterIso_apply] using he

lemma exists_normalized (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) (m : ℕ)
    (B : P) (hBC : B ≤ C) (hlow : level T C m ≤ B) (hB : T B ≤ B) :
    ∃ A : Vertex T C, ∃ j : ℕ, j ≤ m ∧ B = level T A.val j := by
  induction m generalizing B with
  | zero =>
    have he : B = C := le_antisymm hBC hlow
    subst B
    exact ⟨base T C hC hstrict,0,le_rfl,rfl⟩
  | succ m ih =>
    by_cases hb : B ≤ T C
    · have hBC' : T.symm B ≤ C := by
        simpa only [T.symm_apply_apply] using T.symm.monotone hb
      have hlow' : level T C m ≤ T.symm B := by
        simpa only [level_succ,T.symm_apply_apply] using T.symm.monotone hlow
      have hB' : T (T.symm B) ≤ T.symm B := by
        simpa only [T.apply_symm_apply,T.symm_apply_apply] using T.symm.monotone hB
      obtain ⟨A,j,hj,he⟩ := ih (T.symm B) hBC' hlow' hB'
      refine ⟨A,j+1,by omega,?_⟩
      simpa only [T.apply_symm_apply,level_succ] using congrArg T he
    · exact ⟨⟨B,hBC,hb,⟨m+1,hlow⟩,hB⟩,0,Nat.zero_le _,rfl⟩

lemma level_vertex_le (A : Vertex T C) (m : ℕ) : level T A.val m ≤ level T C m :=
  level_mono T m (vertex_le T C A)

lemma normalized_unique (hC : T C ≤ C) (A B : Vertex T C) (a b : ℕ)
    (he : level T A.val a = level T B.val b) : A = B ∧ a = b := by
  have hle : ∀ {A B : Vertex T C} {a b : ℕ}, a ≤ b →
      level T A.val a = level T B.val b → a = b := by
    intro A B a b hab he
    obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hab
    have he' : A.val = level T B.val c := by
      apply level_injective T a
      dsimp only
      rw [← level_add, Nat.add_comm c a]
      exact he
    cases c with
    | zero => simp
    | succ c =>
      exfalso
      apply vertex_normalized T C A
      rw [he']
      exact (level_vertex_le T C B (c+1)).trans
        (level_antitone T C hC (show 1 ≤ c+1 by omega))
  have hab : a = b := by
    rcases le_total a b with h | h
    · exact hle h he
    · exact (hle h he.symm).symm
  subst b
  exact ⟨Subtype.ext (level_injective T a he),rfl⟩

def Homothetic (A B : P) : Prop := ∃ a b : ℕ, level T A a = level T B b

lemma homothetic_refl (A : P) : Homothetic T A A := ⟨0,0,rfl⟩
lemma homothetic_symm {A B : P} : Homothetic T A B → Homothetic T B A := by
  rintro ⟨a,b,h⟩; exact ⟨b,a,h.symm⟩
lemma homothetic_trans {A B D : P} : Homothetic T A B → Homothetic T B D → Homothetic T A D := by
  rintro ⟨a,b,h₁⟩ ⟨c,d,h₂⟩
  refine ⟨a+c,d+b,?_⟩
  rw [level_add,level_add,h₁,← level_add,Nat.add_comm b c,level_add,h₂]

lemma homothetic_normalized_iff (hC : T C ≤ C) (A B : Vertex T C) :
    Homothetic T A.val B.val ↔ A = B := by
  constructor
  · rintro ⟨a,b,h⟩
    exact (normalized_unique T C hC A B a b h).1
  · rintro rfl
    exact homothetic_refl T _

end CoboundaryExpanders.AffineLattices

namespace CoboundaryExpanders.AffineLattices
variable {P : Type} [Lattice P] (T : P ≃o P) (C : P)

def Compatible (A B : P) : Prop :=
  ∃ a b : ℕ, T (level T A a) ≤ level T B b ∧ level T B b ≤ level T A a

end CoboundaryExpanders.AffineLattices

namespace CoboundaryExpanders.AffineLattices
variable {P : Type} [Lattice P] (T : P ≃o P) (C : P)

lemma map_level (S : P ≃o P) (hS : ∀ A, S (T A) = T (S A)) (A : P) (m : ℕ) :
    S (level T A m) = level T (S A) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [level_succ,hS,ih,level_succ]

lemma homothetic_map (S : P ≃o P) (hS : ∀ A, S (T A) = T (S A))
    {A B : P} (h : Homothetic T A B) : Homothetic T (S A) (S B) := by
  obtain ⟨a,b,he⟩ := h
  exact ⟨a,b,by simpa only [map_level T S hS] using congrArg S he⟩

lemma exists_mapVertex (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) (S : P ≃o P)
    (hS : ∀ A, S (T A) = T (S A))
    (hupper : ∃ r, level T (S C) r ≤ C) (hlower : ∃ s, level T C s ≤ S C)
    (A : Vertex T C) : ∃ B : Vertex T C, Homothetic T (S A.val) B.val := by
  obtain ⟨r,hr⟩ := hupper
  obtain ⟨s,hs⟩ := hlower
  obtain ⟨m,hm⟩ := vertex_bounded T C A
  have hu : level T (S A.val) r ≤ C :=
    (level_mono T r (S.monotone (vertex_le T C A))).trans hr
  have hl : level T C (s+m) ≤ S A.val := by
    rw [level_add]
    exact (level_mono T m hs).trans (by
      rw [← map_level T S hS]
      exact S.monotone hm)
  have hb : T (S A.val) ≤ S A.val := by
    rw [← hS]
    exact S.monotone (vertex_shift_le T C A)
  have hl' : level T C (s+m+r) ≤ level T (S A.val) r := by
    rw [level_add]
    exact level_mono T r hl
  have hb' : T (level T (S A.val) r) ≤ level T (S A.val) r := by
    rw [← level_map]
    exact level_mono T r hb
  obtain ⟨B,j,_,he⟩ := exists_normalized T C hC hstrict (s+m+r) _ hu hl' hb'
  exact ⟨B,r,j,he⟩

noncomputable def mapVertex (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) (S : P ≃o P)
    (hS : ∀ A, S (T A) = T (S A))
    (hu : ∃ r, level T (S C) r ≤ C) (hl : ∃ s, level T C s ≤ S C)
    (A : Vertex T C) : Vertex T C :=
  (exists_mapVertex T C hC hstrict S hS hu hl A).choose

lemma mapVertex_homothetic (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) (S : P ≃o P)
    (hS : ∀ A, S (T A) = T (S A))
    (hu : ∃ r, level T (S C) r ≤ C) (hl : ∃ s, level T C s ≤ S C)
    (A : Vertex T C) : Homothetic T (S A.val) (mapVertex T C hC hstrict S hS hu hl A).val :=
  (exists_mapVertex T C hC hstrict S hS hu hl A).choose_spec

end CoboundaryExpanders.AffineLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open Module
variable (K : Type) [Field K] (N : ℕ)

noncomputable def polynomialToStandard : (Fin N → K[X]) →ₗ[K[X]] standard K N where
  toFun f := ⟨fun i => algebraMap K[X] (RatFunc K) (f i),fun i => ⟨f i,rfl⟩⟩
  map_add' f g := by ext i; simp
  map_smul' a f := by ext i; simp [Algebra.smul_def]

lemma polynomialToStandard_bijective : Function.Bijective (polynomialToStandard K N) := by
  constructor
  · intro f g he
    funext i
    exact RatFunc.algebraMap_injective K (congr_fun (congrArg Subtype.val he) i)
  · intro v
    choose f hf using v.property
    refine ⟨f,?_⟩
    apply Subtype.ext
    exact funext hf

noncomputable def standardEquiv : (Fin N → K[X]) ≃ₗ[K[X]] standard K N :=
  LinearEquiv.ofBijective (polynomialToStandard K N) (polynomialToStandard_bijective K N)

noncomputable def standardBasis : Basis (Fin N) K[X] (standard K N) :=
  (Pi.basisFun K[X] (Fin N)).map (standardEquiv K N)

lemma shiftLinear_eq_smul (v : V K N) : shiftLinear K N v = (Polynomial.X : K[X]) • v := by
  ext i
  simp only [shiftLinear_apply,Pi.smul_apply,Algebra.smul_def,uniformizer]

lemma smul_pow_mem_level (m : ℕ) (v : V K N) (hv : v ∈ standard K N) :
    (Polynomial.X^m : K[X]) • v ∈ AffineLattices.level (shift K N) (standard K N) m := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    apply (mem_shift K N _ _).mpr
    refine ⟨(Polynomial.X^m : K[X]) • v,ih,?_⟩
    rw [shiftLinear_eq_smul,smul_smul,pow_succ']

noncomputable def boundedBasis (A : Vertex K N) : Σ r : ℕ, Basis (Fin r) K[X] (A.val) :=
  Submodule.basisOfPidOfLE (AffineLattices.vertex_le _ _ A) (standardBasis K N)

lemma boundedBasis_rank (A : Vertex K N) : (boundedBasis K N A).1 = N := by
  let b := (boundedBasis K N A).2
  let : Module.Free K[X] A.val := Module.Free.of_basis b
  let : Module.Finite K[X] A.val := Module.Finite.of_basis b
  let : Module.Free K[X] (standard K N) := Module.Free.of_basis (standardBasis K N)
  let : Module.Finite K[X] (standard K N) := Module.Finite.of_basis (standardBasis K N)
  have hstd : Module.finrank K[X] (standard K N) = N := by
    simpa using Module.finrank_eq_card_basis (standardBasis K N)
  have hA : Module.finrank K[X] A.val = (boundedBasis K N A).1 := by
    simpa using Module.finrank_eq_card_basis b
  have hle := LinearMap.finrank_le_finrank_of_injective
    (Submodule.inclusion_injective (AffineLattices.vertex_le _ _ A))
  obtain ⟨m,hm⟩ := AffineLattices.vertex_bounded _ _ A
  let f : standard K N →ₗ[K[X]] A.val :=
    { toFun := fun v => ⟨(Polynomial.X^m : K[X]) • v.val,hm (smul_pow_mem_level K N m v.val v.property)⟩
      map_add' := by intros; ext; simp [smul_add]
      map_smul' := by intros; ext; simp [smul_smul,mul_comm] }
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    have he' : (Polynomial.X^m : K[X]) • v.val = (Polynomial.X^m : K[X]) • w.val := congrArg Subtype.val he
    ext i
    have hei := congr_fun he' i
    simp only [Pi.smul_apply,Algebra.smul_def,map_pow] at hei
    exact mul_left_cancel₀ (pow_ne_zero _ (uniformizer_ne_zero K)) hei
  have hge := LinearMap.finrank_le_finrank_of_injective hf
  rw [hstd,hA] at hle hge
  exact le_antisymm hle hge

noncomputable def latticeBasis (A : Vertex K N) : Basis (Fin N) K[X] A.val :=
  (boundedBasis K N A).2.reindex (finCongr (boundedBasis_rank K N A))

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open Module
variable (K : Type) [Field K] (N : ℕ)

noncomputable def constantVector : (Fin N → K[X]) →ₗ[K] (Fin N → K) where
  toFun f i := (f i).coeff 0
  map_add' f g := by ext i; simp
  map_smul' a f := by ext i; simp

noncomputable def residueMap (A : Vertex K N) : A.val →ₗ[K] (Fin N → K) :=
  (constantVector K N).comp ((latticeBasis K N A).equivFun.restrictScalars K).toLinearMap

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)

lemma mem_level (A : LatticeSpace K N) (m : ℕ) (v : V K N) :
    v ∈ level (shift K N) A m ↔ ∃ w ∈ A, (Polynomial.X^m : K[X]) • w = v := by
  induction m generalizing v with
  | zero => simp [level]
  | succ m ih =>
    rw [level_succ,mem_shift]
    constructor
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨w,hw,rfl⟩ := (ih z).mp hz
      exact ⟨w,hw,by rw [shiftLinear_eq_smul,smul_smul,pow_succ']⟩
    · rintro ⟨w,hw,rfl⟩
      refine ⟨(Polynomial.X^m : K[X]) • w,(ih _).mpr ⟨w,hw,rfl⟩,?_⟩
      rw [shiftLinear_eq_smul,smul_smul,pow_succ']

noncomputable def positiveLinear (g : Matrix.SpecialLinearGroup (Fin N) K[X]) :
    V K N ≃ₗ[K[X]] V K N :=
  (Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.map (positive K) g)).restrictScalars K[X]

lemma positiveLinear_apply (g : Matrix.SpecialLinearGroup (Fin N) K[X]) (v : V K N) :
    positiveLinear K N g v = (positiveMatrix K N g.val).mulVec v := rfl

lemma positiveLinear_mul (g h : Matrix.SpecialLinearGroup (Fin N) K[X]) (v : V K N) :
    positiveLinear K N (g*h) v = positiveLinear K N g (positiveLinear K N h v) := by
  simp only [positiveLinear,map_mul,LinearEquiv.mul_apply,LinearEquiv.restrictScalars_apply]

@[simp] lemma positiveLinear_one (v : V K N) :
    positiveLinear K N 1 v = v := by
  simp [positiveLinear]

lemma positiveLinear_inv (g : Matrix.SpecialLinearGroup (Fin N) K[X]) :
    positiveLinear K N g⁻¹ = (positiveLinear K N g).symm := by
  apply LinearEquiv.ext
  intro v
  apply (positiveLinear K N g).injective
  rw [← positiveLinear_mul,mul_inv_cancel,positiveLinear_one,LinearEquiv.apply_symm_apply]

lemma positiveLinear_shift (g : Matrix.SpecialLinearGroup (Fin N) K[X]) (v : V K N) :
    positiveLinear K N g (shiftLinear K N v) = shiftLinear K N (positiveLinear K N g v) := by
  rw [shiftLinear_eq_smul,shiftLinear_eq_smul,map_smul]

noncomputable def positiveAction (g : Matrix.SpecialLinearGroup (Fin N) K[X]) :
    LatticeSpace K N ≃o LatticeSpace K N := Submodule.orderIsoMapComap (positiveLinear K N g)

lemma mem_positiveAction (g : Matrix.SpecialLinearGroup (Fin N) K[X]) (A : LatticeSpace K N)
    (v : V K N) : v ∈ positiveAction K N g A ↔ ∃ w ∈ A, positiveLinear K N g w = v :=
  Submodule.mem_map

lemma positiveAction_inv (g : Matrix.SpecialLinearGroup (Fin N) K[X]) :
    positiveAction K N g⁻¹ = (positiveAction K N g).symm := by
  apply OrderIso.ext
  funext A
  rw [positiveAction,positiveLinear_inv,positiveAction,Submodule.orderIsoMapComap_symm_apply']
  rfl

lemma positiveAction_shift (g : Matrix.SpecialLinearGroup (Fin N) K[X]) (A : LatticeSpace K N) :
    positiveAction K N g (shift K N A) = shift K N (positiveAction K N g A) := by
  ext v
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := (mem_positiveAction K N g _ _).mp hv
    obtain ⟨z,hz,rfl⟩ := (mem_shift K N _ _).mp hw
    exact (mem_shift K N _ _).mpr ⟨positiveLinear K N g z,
      (mem_positiveAction K N g _ _).mpr ⟨z,hz,rfl⟩,(positiveLinear_shift K N g z).symm⟩
  · intro hv
    obtain ⟨w,hw,rfl⟩ := (mem_shift K N _ _).mp hv
    obtain ⟨z,hz,rfl⟩ := (mem_positiveAction K N g _ _).mp hw
    exact (mem_positiveAction K N g _ _).mpr ⟨shiftLinear K N z,
      (mem_shift K N _ _).mpr ⟨z,hz,rfl⟩,positiveLinear_shift K N g z⟩

lemma positiveAction_upper (g : Matrix.SpecialLinearGroup (Fin N) K[X]) :
    ∃ r, level (shift K N) (positiveAction K N g (standard K N)) r ≤ standard K N := by
  classical
  let r := Finset.univ.sup (fun i : Fin N => Finset.univ.sup (fun j : Fin N => (g i j).natDegree))
  have hr : ∀ i j, (g i j).natDegree ≤ r := by
    intro i j
    exact (Finset.le_sup (f := fun j : Fin N => (g i j).natDegree) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun i : Fin N => Finset.univ.sup (fun j : Fin N => (g i j).natDegree)) (Finset.mem_univ i))
  refine ⟨r,?_⟩
  intro v hv
  obtain ⟨w,hw,rfl⟩ := (mem_level K N _ _ _).mp hv
  obtain ⟨z,hz,rfl⟩ := (mem_positiveAction K N g _ _).mp hw
  choose f hf using hz
  intro i
  choose a ha using fun j => (positive_regular_iff K (g i j) r).mpr (hr i j)
  refine ⟨∑ j, a j * f j,?_⟩
  simp only [map_sum,map_mul,positiveLinear_apply,Pi.smul_apply,Algebra.smul_def,
    map_pow,Matrix.mulVec,dotProduct,
    positiveMatrix,Matrix.map_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [ha j,hf j]
  change (positive K (g i j) * uniformizer K ^ r) * z j =
    uniformizer K ^ r * (positive K (g i j) * z j)
  ring

lemma positiveAction_lower (g : Matrix.SpecialLinearGroup (Fin N) K[X]) :
    ∃ s, level (shift K N) (standard K N) s ≤ positiveAction K N g (standard K N) := by
  obtain ⟨s,hs⟩ := positiveAction_upper K N g⁻¹
  refine ⟨s,?_⟩
  have hm := (positiveAction K N g).monotone hs
  rw [map_level _ _ (positiveAction_shift K N g),positiveAction_inv,
    OrderIso.apply_symm_apply] at hm
  exact hm

noncomputable def actVertex (hN : 0 < N) (g : Matrix.SpecialLinearGroup (Fin N) K[X]) :
    Vertex K N → Vertex K N :=
  mapVertex (shift K N) (standard K N) (shift_standard_le K N) (standard_not_le_shift K N hN)
    (positiveAction K N g) (positiveAction_shift K N g) (positiveAction_upper K N g) (positiveAction_lower K N g)

lemma actVertex_homothetic (hN : 0 < N) (g : Matrix.SpecialLinearGroup (Fin N) K[X]) (A : Vertex K N) :
    Homothetic (shift K N) (positiveAction K N g A.val) (actVertex K N hN g A).val :=
  mapVertex_homothetic _ _ _ _ _ _ _ _ _

end CoboundaryExpanders.RationalLattices

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Polynomial-vector leading terms, degree reduction, and normalized rational lattice representatives.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)

noncomputable def polynomialEmbedding : (Fin N → K[X]) →ₗ[K[X]] V K N :=
  (standard K N).subtype.comp (polynomialToStandard K N)

@[simp] lemma polynomialEmbedding_apply (v : Fin N → K[X]) (i : Fin N) :
    polynomialEmbedding K N v i = algebraMap K[X] (RatFunc K) (v i) := rfl

end CoboundaryExpanders.RationalLattices

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Windows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Affine windows, residue chambers, lattice flags, and chamber parametrizations.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.AffineWindow

variable {N : ℕ}

def pairCost (N : ℕ) (a b : ℤ) : ℕ := ((b-a)/(N : ℤ)).natAbs

def inversion : List ℤ → ℕ
  | [] => 0
  | a :: l => (l.map (pairCost N a)).sum + inversion l

end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.AffineWindow
variable {N : ℕ}

def pairs (f : ℤ → ℤ → ℕ) : List ℤ → ℕ
  | [] => 0
  | a :: l => (l.map (f a)).sum + pairs f l

def sortedCost (N : ℕ) (a b : ℤ) : ℕ := pairCost N (min a b) (max a b)
def disorder (a b : ℤ) : ℕ := if b < a then 1 else 0

end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.AffineWindow
variable {N : ℕ}

def periodicEnd (hN : 0 < N) (p : Fin N → ℤ) (r : Fin (N+1)) : ℤ :=
  if hr : r.val < N then p ⟨r.val,hr⟩ else p ⟨0,hN⟩ + N

@[simp] lemma periodicEnd_castSucc (hN : 0 < N) (p : Fin N → ℤ) (r : Fin N) :
    periodicEnd hN p r.castSucc = p r := by
  simp only [periodicEnd,Fin.val_castSucc,dite_eq_left r.isLt]

@[simp] lemma periodicEnd_last (hN : 0 < N) (p : Fin N → ℤ) :
    periodicEnd hN p (Fin.last N) = p ⟨0,hN⟩ + N := by
  simp only [periodicEnd,Fin.val_last,lt_self_iff_false,dite_eq_right,not_false_eq_true]

@[simp] lemma periodicEnd_zero (hN : 0 < N) (p : Fin N → ℤ) :
    periodicEnd hN p 0 = p ⟨0,hN⟩ := by
  change (if hr : 0 < N then p ⟨0,hr⟩ else p ⟨0,hN⟩ + N) = p ⟨0,hN⟩
  rw [dite_eq_left hN]

noncomputable def descents (hN : 0 < N) (p : Fin N → ℤ) : Finset (Fin N) :=
  Finset.univ.filter fun r => periodicEnd hN p r.succ < p r

end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.AffineWindow
open scoped BigOperators
variable {N : ℕ}

def cutDegree (N t : ℕ) (i : Fin N) : ℕ := t/N + if i.val < t%N then 1 else 0

end CoboundaryExpanders.AffineWindow

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Chambers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bounded and full chambers, codistance, descent cores, and their affine-window descriptions.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.AffineWindow
variable {N : ℕ}
def slice (p : Fin N → ℤ) (a b : Fin (N+1)) : List ℤ :=
  List.ofFn fun r : Fin (b.val-a.val) => p ⟨a.val+r.val,by have := r.isLt; have := b.isLt; omega⟩
end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.AffineWindow
variable {N L : ℕ}
def blocks (p : Fin N → ℤ) (c : Fin (L+1) → Fin (N+1)) : List (List ℤ) :=
  List.ofFn fun r : Fin L => slice p (c r.castSucc) (c r.succ)
end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.AffineWindow
variable {N L : ℕ}

noncomputable def cutSet (hN : 0 < N) (p : Fin N → ℤ) : Finset (Fin (N+1)) :=
  insert 0 (insert (Fin.last N) ((descents hN p).image Fin.succ))
end CoboundaryExpanders.AffineWindow

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite pure complexes, weighted F2 norms, distance to actual coboundaries, and the full main statement.
-/

section
open scoped BigOperators
open Filter

namespace CoboundaryExpanders

namespace Complex

def cocycles (X : Complex) (i : ℕ) : Set (X.Cochain i) :=
  {f | X.coboundary i f = 0}

end Complex

end CoboundaryExpanders

end

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits
open Filter

namespace CoboundaryExpanders.Complex

local instance instFintypeFace_1 (X : Complex) (i : ℕ) : Fintype (X.Face i) := X.instFintypeFace i

@[simp] theorem mem_facesOf (X : Complex) (i : ℕ) (σ) :
    σ ∈ X.facesOf i ↔ σ ∈ X.faces ∧ σ.card = i + 1 := by
  simp [facesOf]

@[simp] theorem face_card {X : Complex} {i : ℕ} (σ : X.Face i) :
    σ.val.card = i + 1 := (mem_facesOf X i _).1 σ.property |>.2

theorem face_mem {X : Complex} {i : ℕ} (σ : X.Face i) :
    σ.val ∈ X.faces := (mem_facesOf X i _).1 σ.property |>.1

@[simp] theorem norm_zero (X : Complex) (s i : ℕ) : X.norm s i 0 = 0 := by
  simp [norm]

@[simp] theorem coboundary_zero (X : Complex) (i : ℕ) : X.coboundary i 0 = 0 := by
  ext τ
  simp [coboundary]

@[simp] theorem coboundary_add (X : Complex) (i : ℕ) (f g : X.Cochain i) :
    X.coboundary i (f + g) = X.coboundary i f + X.coboundary i g := by
  ext τ
  simp only [coboundary, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

@[simp] theorem coboundary_smul (X : Complex) (i : ℕ) (c : ZMod 2) (f : X.Cochain i) :
    X.coboundary i (c • f) = c • X.coboundary i f := by
  ext τ
  simp only [coboundary, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

def coboundaryLinear (X : Complex) (i : ℕ) : X.Cochain i →ₗ[ZMod 2] X.Cochain (i + 1) where
  toFun := X.coboundary i
  map_add' := X.coboundary_add i
  map_smul' := X.coboundary_smul i

@[simp] theorem zero_mem_coboundaries (X : Complex) (i : ℕ) :
    0 ∈ X.coboundaries i := by
  cases i with
  | zero => exact ⟨0, rfl⟩
  | succ i => exact ⟨0, X.coboundary_zero i⟩

theorem card_between_faces {X : Complex} {i j k : ℕ}
    (σ : X.Face i) (τ : X.Face k) (hστ : σ.val ⊆ τ.val) (hij : i ≤ j) :
    (Finset.univ.filter (fun ρ : X.Face j =>
      σ.val ⊆ ρ.val ∧ ρ.val ⊆ τ.val)).card =
      Nat.choose ((k + 1) - (i + 1)) ((j + 1) - (i + 1)) := by
  classical
  have himage :
      (Finset.univ.filter (fun ρ : X.Face j =>
        σ.val ⊆ ρ.val ∧ ρ.val ⊆ τ.val)).image Subtype.val =
      (τ.val.powersetCard (j + 1)).filter (σ.val ⊆ ·) := by
    ext ρ
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨ρ', ⟨hσρ, hρτ⟩, rfl⟩
      exact ⟨⟨hρτ, face_card ρ'⟩, hσρ⟩
    · rintro ⟨⟨hρτ, hρcard⟩, hσρ⟩
      exact ⟨⟨ρ, (mem_facesOf X j ρ).mpr
        ⟨X.downward (face_mem τ) hρτ, hρcard⟩⟩, ⟨hσρ, hρτ⟩, rfl⟩
  have h := Finset.card_filter_powersetCard_subset σ.val τ.val (j + 1) hστ
    (by simpa using Nat.succ_le_succ hij)
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective] at h
  simpa only [face_card] using h

@[simp] theorem coboundary_coboundary (X : Complex) (i : ℕ) (f : X.Cochain i) :
    X.coboundary (i + 1) (X.coboundary i f) = 0 := by
  classical
  ext τ
  change (∑ ρ : X.Face (i + 1), if ρ.val ⊆ τ.val then
    (∑ σ : X.Face i, if σ.val ⊆ ρ.val then f σ else 0) else 0) = 0
  calc
    _ = ∑ ρ : X.Face (i + 1), ∑ σ : X.Face i,
        if σ.val ⊆ ρ.val ∧ ρ.val ⊆ τ.val then f σ else 0 := by
      apply Finset.sum_congr rfl
      intro ρ _
      by_cases h : ρ.val ⊆ τ.val <;> simp [h]
    _ = ∑ σ : X.Face i, ∑ ρ : X.Face (i + 1),
        if σ.val ⊆ ρ.val ∧ ρ.val ⊆ τ.val then f σ else 0 := Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro σ _
      by_cases hστ : σ.val ⊆ τ.val
      · have hc : (Finset.univ.filter (fun ρ : X.Face (i + 1) =>
            σ.val ⊆ ρ.val ∧ ρ.val ⊆ τ.val)).card = 2 := by
          simpa using card_between_faces σ τ hστ (Nat.le_succ i)
        rw [← Finset.sum_filter, Finset.sum_const, hc]
        have htwo : (2 : ZMod 2) = 0 := by decide
        simp [nsmul_eq_mul, htwo]
      · apply Finset.sum_eq_zero
        intro ρ _
        exact ite_eq_right (fun h => hστ (h.1.trans h.2))

def cofaceCount (X : Complex) (s : ℕ) (σ : Finset (Fin X.vertexCount)) : ℕ :=
  ((X.facesOf s).filter (σ ⊆ ·)).card

@[simp] theorem cofaceCount_self {X : Complex} {i : ℕ} (σ : X.Face i) :
    X.cofaceCount i σ.val = 1 := by
  classical
  have hfilter : (X.facesOf i).filter (σ.val ⊆ ·) = {σ.val} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hτ, hστ⟩
      exact (Finset.eq_of_subset_of_card_le hστ (by
        rw [face_card σ, ((mem_facesOf X i τ).mp hτ).2])).symm
    · rintro rfl
      exact ⟨σ.property, Finset.Subset.refl _⟩
  simp [cofaceCount, hfilter]

def skeletonScale (X : Complex) (n s : ℕ) : ℝ :=
  ((Nat.choose (n + 1) (s + 1) : ℝ) * (X.facesOf n).card) / (X.facesOf s).card

@[reducible] def skeleton (X : Complex) (s : ℕ) : Complex where
  vertexCount := X.vertexCount
  faces := X.faces.filter (fun σ => σ.card ≤ s + 1)
  empty_mem := Finset.mem_filter.mpr ⟨X.empty_mem, by simp⟩
  downward := by
    intro σ τ hσ hτ
    rw [Finset.mem_filter] at hσ ⊢
    exact ⟨X.downward hσ.1 hτ, (Finset.card_le_card hτ).trans hσ.2⟩
  vertex_mem := fun v => Finset.mem_filter.mpr ⟨X.vertex_mem v, by simp⟩

@[simp] theorem mem_skeleton_faces (X : Complex) (s : ℕ) (σ) :
    σ ∈ (X.skeleton s).faces ↔ σ ∈ X.faces ∧ σ.card ≤ s + 1 :=
  by simp only [skeleton, Finset.mem_filter]

@[simp] theorem skeleton_facesOf {X : Complex} {s i : ℕ} (his : i ≤ s) :
    (X.skeleton s).facesOf i = X.facesOf i := by
  ext σ
  simp only [mem_facesOf, skeleton, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · exact fun h => ⟨⟨h.1, h.2 ▸ Nat.succ_le_succ his⟩, h.2⟩

def skeletonFaceEquiv (X : Complex) {i s : ℕ} (his : i ≤ s) :
    X.Face i ≃ (X.skeleton s).Face i :=
  Equiv.subtypeEquivRight (fun σ => by rw [skeleton_facesOf his])

@[simp] theorem skeletonFaceEquiv_val (X : Complex) {i s : ℕ} (his : i ≤ s)
    (σ : X.Face i) : (X.skeletonFaceEquiv his σ).val = σ.val := rfl

@[simp] theorem skeletonFaceEquiv_symm_val (X : Complex) {i s : ℕ} (his : i ≤ s)
    (σ : (X.skeleton s).Face i) : ((X.skeletonFaceEquiv his).symm σ).val = σ.val := rfl

def skeletonCochainEquiv (X : Complex) {i s : ℕ} (his : i ≤ s) :
    X.Cochain i ≃ₗ[ZMod 2] (X.skeleton s).Cochain i :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (X.skeletonFaceEquiv his).symm

@[simp] theorem skeletonCochainEquiv_apply (X : Complex) {i s : ℕ} (his : i ≤ s)
    (f : X.Cochain i) (σ : (X.skeleton s).Face i) :
    X.skeletonCochainEquiv his f σ = f ((X.skeletonFaceEquiv his).symm σ) := rfl

@[simp] theorem skeleton_weight (X : Complex) {i s : ℕ} (his : i ≤ s)
    (σ : X.Face i) :
    (X.skeleton s).weight s i (X.skeletonFaceEquiv his σ) = X.weight s i σ := by
  simp only [weight, skeleton_facesOf le_rfl, skeletonFaceEquiv_val]

@[simp] theorem skeleton_norm (X : Complex) {i s : ℕ} (his : i ≤ s)
    (f : X.Cochain i) :
    (X.skeleton s).norm s i (X.skeletonCochainEquiv his f) = X.norm s i f := by
  unfold norm
  apply (Fintype.sum_equiv (X.skeletonFaceEquiv his) _ _ ?_).symm
  intro σ
  simp only [skeletonCochainEquiv_apply, Equiv.symm_apply_apply, skeleton_weight]

@[simp] theorem skeleton_coboundary (X : Complex) {i s : ℕ} (his : i < s)
    (f : X.Cochain i) :
    (X.skeleton s).coboundary i (X.skeletonCochainEquiv his.le f) =
      X.skeletonCochainEquiv his (X.coboundary i f) := by
  ext τ
  simp only [coboundary, skeletonCochainEquiv_apply]
  apply (Fintype.sum_equiv (X.skeletonFaceEquiv his.le) _ _ ?_).symm
  intro σ
  simp only [Equiv.symm_apply_apply,
    skeletonFaceEquiv_val, skeletonFaceEquiv_symm_val]
  rfl

@[simp] theorem skeleton_distance_image (X : Complex) {i s : ℕ} (his : i ≤ s)
    (f : X.Cochain i) (A : Set (X.Cochain i)) :
    (X.skeleton s).distance s i (X.skeletonCochainEquiv his f)
      ((X.skeletonCochainEquiv his) '' A) = X.distance s i f A := by
  unfold distance
  congr 1
  rw [Set.image_image]
  have hf : (fun a => (X.skeleton s).norm s i
      (X.skeletonCochainEquiv his f - X.skeletonCochainEquiv his a)) =
      (fun a => X.norm s i (f - a)) := by
    funext a
    rw [← map_sub, skeleton_norm]
  rw [hf]

def vertexFaceEquiv (X : Complex) : Fin X.vertexCount ≃ X.Face 0 :=
  Equiv.ofBijective (fun v => ⟨{v}, (mem_facesOf X 0 _).mpr
    ⟨X.vertex_mem v, Finset.card_singleton v⟩⟩) (by
      constructor
      · intro v w h
        exact Finset.singleton_injective (congrArg Subtype.val h)
      · intro σ
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (face_card σ)
        exact ⟨v, Subtype.ext hv.symm⟩)

@[simp] theorem vertexFaceEquiv_val (X : Complex) (v : Fin X.vertexCount) :
    (X.vertexFaceEquiv v).val = {v} := rfl

end CoboundaryExpanders.Complex

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Frames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Unimodular frames, bad-simplex transport, height reduction, and partial-basis exactness.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

namespace CoboundaryExpanders.Unimodular
variable {R M S T : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def IsFrame (R : Type*) [CommRing R] {M S : Type*} [AddCommGroup M] [Module R M]
    (f : S → M) : Prop :=
  ∃ r : M →ₗ[R] (S → R), ∀ i, r (f i) = Pi.single i 1

lemma frame_empty (f : S → M) [IsEmpty S] : IsFrame R f := by
  refine ⟨0, ?_⟩
  intro i
  exact isEmptyElim i

lemma frame_reindex {f : S → M} (hf : IsFrame R f) (e : T ↪ S) :
    IsFrame R (f ∘ e) := by
  classical
  obtain ⟨r, hr⟩ := hf
  refine ⟨LinearMap.pi (fun j => (LinearMap.proj (e j)).comp r), ?_⟩
  intro i
  ext j
  simp [hr, Pi.single_apply, e.injective.eq_iff]

lemma frame_equiv {f : S → M} (e : T ≃ S) :
    IsFrame R (f ∘ e) ↔ IsFrame R f := by
  constructor
  · intro h
    simpa only [Function.comp_def, Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using frame_reindex h e.symm.toEmbedding
  · exact fun h => frame_reindex h e.toEmbedding

variable [Fintype S]

def combine (f : S → M) : (S → R) →ₗ[R] M :=
  ∑ i, (LinearMap.proj i).smulRight (f i)

lemma combine_apply (f : S → M) (x : S → R) :
    combine f x = ∑ i, x i • f i := by simp [combine]

@[simp] lemma combine_single (f : S → M) (i : S) :
    combine f (Pi.single i 1 : S → R) = f i := by
  classical
  simp [combine_apply, Pi.single_apply]

@[simp] lemma retract_combine (f : S → M) (r : M →ₗ[R] (S → R))
    (hr : ∀ i, r (f i) = Pi.single i 1) (x : S → R) : r (combine f x) = x := by
  classical
  ext j
  simp [combine_apply, map_sum, hr, Finset.sum_apply, Pi.single_apply]

def quotientProjection (f : S → M) (r : M →ₗ[R] (S → R))
    (hr : ∀ i, r (f i) = Pi.single i 1) : M →ₗ[R] r.ker :=
  LinearMap.codRestrict r.ker (LinearMap.id - (combine f).comp r) (by
    intro x
    change r (x - combine f (r x)) = 0
    rw [map_sub, retract_combine f r hr, sub_self])

@[simp] lemma quotientProjection_val (f : S → M) (r : M →ₗ[R] (S → R))
    (hr : ∀ i, r (f i) = Pi.single i 1) (x : M) :
    (quotientProjection f r hr x : M) = x - combine f (r x) := rfl

@[simp] lemma quotientProjection_family (f : S → M) (r : M →ₗ[R] (S → R))
    (hr : ∀ i, r (f i) = Pi.single i 1) (i : S) :
    quotientProjection f r hr (f i) = 0 := by
  apply Subtype.ext
  simp [hr]

@[simp] lemma quotientProjection_ker (f : S → M) (r : M →ₗ[R] (S → R))
    (hr : ∀ i, r (f i) = Pi.single i 1) (x : r.ker) :
    quotientProjection f r hr x = x := by
  apply Subtype.ext
  simp [show r (x : M) = 0 from x.property]

def splitEquiv (f : S → M) (r : M →ₗ[R] (S → R))
    (hr : ∀ i, r (f i) = Pi.single i 1) : M ≃ₗ[R] (S → R) × r.ker where
  toFun x := (r x, quotientProjection f r hr x)
  invFun x := combine f x.1 + x.2
  left_inv x := by simp
  right_inv x := by
    apply Prod.ext
    · simp [retract_combine f r hr]
    · apply Subtype.ext
      simp [retract_combine f r hr]
  map_add' x y := by simp
  map_smul' a x := by simp

variable [Fintype T]

lemma frame_rank_split [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Free R M] [Module.Finite R M]
    (f : S → M) (r : M →ₗ[R] (S → R))
    (hr : ∀ i, r (f i) = Pi.single i 1) :
    Fintype.card S + Module.finrank R r.ker = Module.finrank R M := by
  have hh := (splitEquiv f r hr).finrank_eq
  rw [Module.finrank_prod, Module.finrank_pi] at hh
  exact hh.symm

end CoboundaryExpanders.Unimodular

end

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

namespace CoboundaryExpanders.Unimodular
open InfiniteChains InfiniteChains.Attachment
variable {R M V W : Type} [CommRing R] [AddCommGroup M] [Module R M]
variable [DecidableEq V] [DecidableEq W]

def complex (R : Type) [CommRing R] {M V : Type} [AddCommGroup M] [Module R M]
    (f : V → M) : CoboundaryExpanders.InfiniteChains.Complex V where
  faces := {s | IsFrame R (fun v : s => f v)}
  empty_mem := frame_empty _
  downward := by
    intro s t hs hts
    let e : t ↪ s := ⟨(fun v => ⟨v.val, hts v.property⟩),
      fun x y h => Subtype.ext (congrArg (fun z : s => z.val) h)⟩
    exact frame_reindex hs e

end CoboundaryExpanders.Unimodular

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Mixing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Small-set expansion, local spectral descent, connectedness, and uniform coset mixing.
-/

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.Construction

section
open Elementary
variable (p n : ℕ) [Fact p.Prime]

def cycleGenerated (hn : 1 ≤ n) : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)) :=
  Subgroup.closure (Set.range (cycleRoot p n hn))

end

open Elementary
variable (p n m : ℕ) [Fact p.Prime]

def residue (hm : 1 ≤ m) : Trunc p m →+* ZMod p :=
  Ideal.Quotient.lift (powerIdeal p m) (Polynomial.evalRingHom 0) (by
    change powerIdeal p m ≤ RingHom.ker (Polynomial.evalRingHom (R := ZMod p) 0)
    apply Ideal.span_le.mpr
    intro f hf
    have hf' : f = Polynomial.X ^ m := by simpa using hf
    subst f
    simp [show m ≠ 0 by omega])

@[simp] theorem residue_mk (hm : 1 ≤ m) (f : R p) :
    residue p m hm (Ideal.Quotient.mk (powerIdeal p m) f) = f.eval 0 := rfl

theorem residue_one_isUnit (hm : 1 ≤ m) (a : Trunc p m)
    (ha : residue p m hm a = 1) : IsUnit a := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hf : (f - 1).eval 0 = 0 := by simpa using sub_eq_zero.mpr ha
  have hdiv : Polynomial.X ∣ f - 1 := Polynomial.X_dvd_iff.mpr (by simpa [Polynomial.coeff_zero_eq_eval_zero] using hf)
  obtain ⟨b, hb⟩ := hdiv
  have he : Ideal.Quotient.mk (powerIdeal p m) f - 1 =
      tbar p m * Ideal.Quotient.mk (powerIdeal p m) b := by
    simpa only [map_sub, map_one, map_mul, tbar] using congrArg (Ideal.Quotient.mk (powerIdeal p m)) hb
  have hn : IsNilpotent (Ideal.Quotient.mk (powerIdeal p m) f - 1) := by
    rw [he]
    refine ⟨m, ?_⟩
    rw [mul_pow, tbar_pow, zero_mul]
  simpa only [sub_add_cancel] using hn.isUnit_add_one

end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Transfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Odd-index transfer, comparison of bar resolutions, and homology-coinvariant models.
-/

section
open CategoryTheory
open scoped BigOperators

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp

namespace CoboundaryExpanders.BarComparison
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
  (S : Subgroup G)

abbrev restrictedBar : ProjectiveResolution (Rep.trivial k S k) :=
  (Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution k G)

def inclusionF (n : ℕ) :
    (Rep.barComplex k S).X n ⟶
      (Rep.resFunctor S.subtype).obj ((Rep.barComplex k G).X n) :=
  Rep.freeLift k S _ (fun x : Fin n → S =>
    Finsupp.single (fun i => (x i : G)) (.single (1 : G) (1 : k)))

omit [DecidableEq G] in
@[simp] theorem inclusionF_single (n : ℕ) (x : Fin n → S) (h : S) (r : k) :
    (inclusionF (k := k) S n).hom (Finsupp.single x (.single h r)) =
      Finsupp.single (fun i => (x i : G)) (.single (h : G) r) := by
  change (Representation.freeLift
    ((Representation.free k G (Fin n → G)).comp S.subtype)
    (fun x : Fin n → S => Finsupp.single (fun i => (x i : G)) (.single (1 : G) (1 : k))))
    (Finsupp.single x (.single h r)) = _
  rw [Representation.freeLift_single_single]
  change r • Representation.free k G (Fin n → G) (h : G) _ = _
  rw [Representation.free_single_single]
  simp

def inclusion : (Rep.barComplex k S) ⟶ (restrictedBar (k := k) S).complex where
  f n := inclusionF S n
  comm' i j hij := by
    cases hij
    apply Rep.free_ext
    intro x
    change ((Rep.barComplex k G).d (j + 1) j).hom
      ((inclusionF (k := k) S (j + 1)).hom (Finsupp.single x (.single 1 1))) =
      (inclusionF (k := k) S j).hom
      (((Rep.barComplex k S).d (j + 1) j).hom (Finsupp.single x (.single 1 1)))
    have hdG : (Rep.barComplex k G).d (j + 1) j = Rep.barComplex.d k G j :=
      Rep.barComplex.d_def k G (n := j)
    have hdS : (Rep.barComplex k S).d (j + 1) j = Rep.barComplex.d k S j :=
      Rep.barComplex.d_def k S (n := j)
    have hincl : ∀ (n : ℕ) (x : Fin n → S) (h : S) (r : k),
        (inclusionF (k := k) S n).hom (Finsupp.single x (.single h r)) =
          Finsupp.single (fun i => (x i : G)) (.single (h : G) r) :=
      inclusionF_single S
    rw [hdG, hdS, hincl]
    simp only [Subgroup.coe_one]
    rw [Rep.barComplex.d_single, Rep.barComplex.d_single]
    simp only [map_add, map_sum, hincl]

    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    exact (Fin.comp_contractNth (· * ·) (· * ·) (fun a b : S => rfl) i x).symm

open Rep TensorProduct

omit [DecidableEq G] in
lemma diagonal_inv_single (n : ℕ) (x : Fin n → G) (g : G) (r : k) :
    (diagonalSuccIsoFree k G n).inv.hom (single x (.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd x) r := by
  simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  have step1 : (Hom.hom (leftRegularTensorTrivialIsoFree k G (Fin n → G)).inv)
      (single x (.single g r)) = .single g 1 ⊗ₜ[k] .single x r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single x g r
  rw [step1]
  simp only [Action.tensorObj_V, tensor_V, tensor_ρ]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G n).inv (g, x) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin n → G)) g x 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G n).inv) z) key₂).trans key₁).trans (by
      rw [one_mul]
      exact congrArg (fun f : Fin (n + 1) → G => MonoidAlgebra.single f r)
        (Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g x))

omit [DecidableEq G] in
@[simp] theorem bar_augmentation_single (x : Fin 0 → G) (g : G) (r : k) :
    ((Rep.barResolution k G).π.f 0).hom (single x (.single g r)) = r := by
  change (Rep.standardComplex.ε k G).hom
    ((Rep.diagonalSuccIsoFree k G 0).inv.hom (single x (.single g r))) = r
  rw [diagonal_inv_single]
  simp [Rep.standardComplex.ε]

omit [DecidableEq G] in
theorem inclusion_augmentation :
    inclusion (k := k) S ≫ (restrictedBar S).π = (Rep.barResolution k S).π := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    apply Rep.free_ext
    intro x
    change ((Rep.barResolution k G).π.f 0).hom
      ((inclusionF (k := k) S 0).hom (single x (.single 1 1))) =
      ((Rep.barResolution k S).π.f 0).hom (single x (.single 1 1))
    rw [inclusionF_single, bar_augmentation_single, bar_augmentation_single]
  | succ n =>
    apply Limits.IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_single_obj_X (V := Rep k S)
      (ComplexShape.down ℕ) 0 (Rep.trivial k S k) (n + 1) (by omega)

def inclusionHomotopy : Homotopy (inclusion (k := k) S)
    ((Rep.barResolution k S).homotopyEquiv (restrictedBar S)).hom :=
  ProjectiveResolution.liftHomotopy (P := Rep.barResolution k S) (Q := restrictedBar S)
    (𝟙 (Rep.trivial k S k)) (inclusion S)
    ((Rep.barResolution k S).homotopyEquiv (restrictedBar S)).hom
    (by
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact inclusion_augmentation (k := k) S)
    (by
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact ProjectiveResolution.homotopyEquiv_hom_π _ _)

def inclusionEquiv : HomotopyEquiv (Rep.barComplex k S) (restrictedBar (k := k) S).complex where
  hom := inclusion S
  inv := ((Rep.barResolution k S).homotopyEquiv (restrictedBar S)).inv
  homotopyHomInvId :=
    ((inclusionHomotopy S).compRight _).trans
      ((Rep.barResolution k S).homotopyEquiv (restrictedBar S)).homotopyHomInvId
  homotopyInvHomId :=
    ((inclusionHomotopy S).compLeft _).trans
      ((Rep.barResolution k S).homotopyEquiv (restrictedBar S)).homotopyInvHomId

end CoboundaryExpanders.BarComparison

end

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory

namespace CoboundaryExpanders.CoinvariantModel
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]

abbrev complex : ChainComplex (ModuleCat k) ℕ :=
  ((Rep.coinvariantsFunctor k G).mapHomologicalComplex _).obj (Rep.barComplex k G)

def chainsIso : groupHomology.inhomogeneousChains (Rep.trivial k G k) ≅
    complex (k := k) (G := G) :=
  groupHomology.inhomogeneousChainsIso (Rep.trivial k G k) ≪≫
    (NatIso.mapHomologicalComplex
      (Functor.isoWhiskerRight (leftUnitorNatIso (Rep k G)) (Rep.coinvariantsFunctor k G)) _).app
        (Rep.barComplex k G)

@[simp] theorem chainsIso_hom_single (n : ℕ) (x : Fin n → G) (r : k) :
    (chainsIso (k := k) (G := G)).hom.f n (single x r) =
      Representation.Coinvariants.mk (Representation.free k G (Fin n → G))
        (single x (.single (1 : G) r)) := by
  change (Rep.coinvariantsFunctor k G).map (λ_ (Rep.free k G (Fin n → G))).hom
    (Rep.finsuppToCoinvariantsTensorFree (Rep.trivial k G k) (Fin n → G)
      (single x r)) = _
  rw [Rep.finsuppToCoinvariantsTensorFree_single]
  simp

end CoboundaryExpanders.CoinvariantModel

namespace CoboundaryExpanders.BarComparison
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
    (S : Subgroup G) [S.Normal]

def adjustedF (g : G) (n : ℕ) :
    (Rep.barComplex k S).X n ⟶
      (Rep.resFunctor S.subtype).obj ((Rep.barComplex k G).X n) :=
  Rep.freeLift k S _ (fun x : Fin n → S =>
    Finsupp.single (fun i => g * (x i : G) * g⁻¹) (.single g⁻¹ (1 : k)))

omit [DecidableEq G] [S.Normal] in
@[simp] theorem adjustedF_single (g : G) (n : ℕ) (x : Fin n → S) (h : S) (r : k) :
    (adjustedF (k := k) S g n).hom (Finsupp.single x (.single h r)) =
      Finsupp.single (fun i => g * (x i : G) * g⁻¹) (.single ((h : G) * g⁻¹) r) := by
  change (Representation.freeLift
    ((Representation.free k G (Fin n → G)).comp S.subtype)
    (fun x : Fin n → S => Finsupp.single (fun i => g * (x i : G) * g⁻¹)
      (.single g⁻¹ (1 : k)))) (Finsupp.single x (.single h r)) = _
  rw [Representation.freeLift_single_single]
  change r • Representation.free k G (Fin n → G) (h : G) _ = _
  rw [Representation.free_single_single]
  simp

omit [DecidableEq G] in
theorem bar_d_single_coeff (n : ℕ) (x : Fin (n + 1) → G) (h : G) :
    (Rep.barComplex.d k G n).hom (single x (.single h (1 : k))) =
      single (fun i => x i.succ) (.single (h * x 0) 1) +
      ∑ i : Fin (n + 1), single (i.contractNth (· * ·) x)
        (.single h ((-1 : k) ^ (i.val + 1))) := by
  have hh := Rep.hom_comm_apply (Rep.barComplex.d k G n) h
    (single x (.single 1 (1 : k)))
  change (Rep.barComplex.d k G n).hom
    (Representation.free k G (Fin (n + 1) → G) h (single x (.single 1 1))) =
    Representation.free k G (Fin n → G) h
      ((Rep.barComplex.d k G n).hom (single x (.single 1 1))) at hh
  rw [Representation.free_single_single, mul_one, Rep.barComplex.d_single] at hh
  rw [hh]
  simp [map_add, map_sum]

def adjusted (g : G) : (Rep.barComplex k S) ⟶ (restrictedBar (k := k) S).complex where
  f n := adjustedF S g n
  comm' i j hij := by
    cases hij
    apply Rep.free_ext
    intro x
    change ((Rep.barComplex k G).d (j + 1) j).hom
      ((adjustedF (k := k) S g (j + 1)).hom (Finsupp.single x (.single 1 1))) =
      (adjustedF (k := k) S g j).hom
      (((Rep.barComplex k S).d (j + 1) j).hom (Finsupp.single x (.single 1 1)))
    rw [Rep.barComplex.d_def, Rep.barComplex.d_def, adjustedF_single]
    have hadj : ∀ (n : ℕ) (x : Fin n → S) (h : S) (r : k),
        (adjustedF (k := k) S g n).hom (single x (.single h r)) =
          single (fun i => g * (x i : G) * g⁻¹) (.single ((h : G) * g⁻¹) r) :=
      adjustedF_single S g
    rw [bar_d_single_coeff, Rep.barComplex.d_single]
    simp only [map_add, map_sum, hadj, Subgroup.coe_one, one_mul]
    congr 1
    · simp only [mul_assoc, inv_mul_cancel_left]
    · apply Finset.sum_congr rfl
      intro i _
      congr 2
      exact (Fin.comp_contractNth (· * ·) (· * ·)
        (f := fun a : S => g * (a : G) * g⁻¹)
        (fun a b : S => by simp [mul_assoc]) i x).symm

omit [DecidableEq G] [S.Normal] in
theorem adjusted_augmentation (g : G) :
    adjusted (k := k) S g ≫ (restrictedBar S).π = (Rep.barResolution k S).π := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    apply Rep.free_ext
    intro x
    change ((Rep.barResolution k G).π.f 0).hom
      ((adjustedF (k := k) S g 0).hom (single x (.single 1 1))) =
      ((Rep.barResolution k S).π.f 0).hom (single x (.single 1 1))
    rw [adjustedF_single, bar_augmentation_single, bar_augmentation_single]
  | succ n =>
    apply Limits.IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_single_obj_X (V := Rep k S)
      (ComplexShape.down ℕ) 0 (Rep.trivial k S k) (n + 1) (by omega)

def adjustedHomotopy (g : G) :
    Homotopy (adjusted (k := k) S g) (inclusion S) :=
  ProjectiveResolution.liftHomotopy (P := Rep.barResolution k S) (Q := restrictedBar S)
    (𝟙 (Rep.trivial k S k)) (adjusted S g) (inclusion S)
    (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact adjusted_augmentation S g)
    (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact inclusion_augmentation S)

end CoboundaryExpanders.BarComparison

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Coinvariants
attribute [-instance] _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Simplicial group actions, permutation modules, coset sums, and chain coinvariants.
-/

section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.InfiniteChains
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def rawMap (f : V ↪ W) : (Finset V →₀ k) →ₗ[k] (Finset W →₀ k) :=
  Finsupp.lmapDomain k k (Finset.map f)

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma rawMap_single (f : V ↪ W) (s : Finset V) (r : k) :
    rawMap f (Finsupp.single s r) = Finsupp.single (s.map f) r :=
  Finsupp.mapDomain_single

lemma rawMap_boundary (f : V ↪ W) :
    (rawMap f).comp rawBoundary = rawBoundary.comp (rawMap f) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, rawBoundary_single,
    map_sum, rawMap_single, Finset.sum_map]
  simp only [Finset.map_erase]

namespace Complex
variable (X : CoboundaryExpanders.InfiniteChains.Complex V) (Y : CoboundaryExpanders.InfiniteChains.Complex W) (f : V ↪ W)
  (hf : ∀ s ∈ X.faces, s.map f ∈ Y.faces)

def mapFace (n : ℕ) (s : X.Face n) : Y.Face n :=
  ⟨s.val.map f, hf s.val s.property.1, by rw [Finset.card_map]; exact s.property.2⟩

def map (n : ℕ) : X.Chains n →ₗ[k] Y.Chains n :=
  Finsupp.lmapDomain k k (X.mapFace Y f hf n)

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma map_single (n : ℕ) (s : X.Face n) (r : k) :
    X.map Y f hf n (Finsupp.single s r) = Finsupp.single (X.mapFace Y f hf n s) r :=
  Finsupp.mapDomain_single

omit [DecidableEq V] [DecidableEq W] in
lemma embed_map (n : ℕ) :
    (Y.embed n).comp (X.map Y f hf n) = (rawMap f).comp (X.embed n) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, map_single,
    embed_single, rawMap_single]
  rfl

lemma map_boundary (n : ℕ) :
    (X.map Y f hf n).comp (X.boundary n) =
      (Y.boundary n).comp (X.map Y f hf (n+1)) := by
  apply LinearMap.ext
  intro c
  apply Y.embed_injective n
  change (Y.embed n).comp (X.map Y f hf n) (X.boundary n c) =
    (Y.embed n).comp (Y.boundary n) (X.map Y f hf (n+1) c)
  rw [embed_map, embed_boundary]
  change rawMap f ((X.embed n).comp (X.boundary n) c) =
    rawBoundary ((Y.embed (n+1)).comp (X.map Y f hf (n+1)) c)
  rw [embed_boundary, embed_map]
  exact LinearMap.congr_fun (rawMap_boundary f) (X.embed (n+1) c)

end Complex
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.FinsuppPermutation
open CategoryTheory
variable (k G A : Type) [CommRing k] [Group G] [MulAction G A]

def ρ : Representation k G (A →₀ k) where
  toFun g := Finsupp.lmapDomain k k (g • ·)
  map_one' := by
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext
    intro r
    simp
  map_mul' g h := by
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext
    intro r
    simp [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, mul_smul]

@[simp] lemma ρ_single (g : G) (a : A) (r : k) :
    ρ k G A g (Finsupp.single a r) = Finsupp.single (g • a) r :=
  Finsupp.mapDomain_single

abbrev rep : Rep k G := Rep.of (ρ k G A)

end CoboundaryExpanders.FinsuppPermutation

namespace CoboundaryExpanders.InfiniteChains.Complex
open CategoryTheory
variable {V G : Type} [DecidableEq V] [Group G] [MulAction G V] (X : CoboundaryExpanders.InfiniteChains.Complex V)

def Invariant : Prop :=
  ∀ (g : G) (s : Finset V), s ∈ X.faces → s.map (MulAction.toPerm g).toEmbedding ∈ X.faces

variable [Fact (X.Invariant (G := G))]

instance faceMulAction (n : ℕ) : MulAction G (X.Face n) where
  smul g s := X.mapFace X (MulAction.toPerm g).toEmbedding (Fact.out (p := X.Invariant (G := G)) g) n s
  one_smul s := by
    apply Subtype.ext
    change s.val.map (MulAction.toPerm (1 : G)).toEmbedding = s.val
    ext v
    simp
  mul_smul g h s := by
    apply Subtype.ext
    change s.val.map (MulAction.toPerm (g*h)).toEmbedding =
      (s.val.map (MulAction.toPerm h).toEmbedding).map (MulAction.toPerm g).toEmbedding
    rw [Finset.map_map]
    congr 1
    ext v
    exact mul_smul g h v

omit [DecidableEq V] in
@[simp] lemma smul_face_val (g : G) (n : ℕ) (s : X.Face n) :
    (g • s).val = s.val.map (MulAction.toPerm g).toEmbedding := rfl

abbrev chainsRep (n : ℕ) : Rep k G := FinsuppPermutation.rep k G (X.Face n)

def boundaryRep (n : ℕ) : X.chainsRep (G := G) (n+1) ⟶ X.chainsRep (G := G) n :=
  Rep.ofHom ⟨X.boundary n, by
    intro g
    exact (X.map_boundary X (MulAction.toPerm g).toEmbedding (Fact.out (p := X.Invariant (G := G)) g) n).symm⟩

@[simp] lemma boundaryRep_squared (n : ℕ) :
    X.boundaryRep (G := G) (n+1) ≫ X.boundaryRep (G := G) n = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact X.boundary_squared n

def repComplex : ChainComplex (Rep k G) ℕ :=
  ChainComplex.of (fun n => X.chainsRep (G := G) (n+1))
    (fun n => X.boundaryRep (G := G) (n+1))
    (fun n => X.boundaryRep_squared (G := G) (n+1))

@[simp] lemma repComplex_d (n : ℕ) :
    X.repComplex.d (n+1) n = X.boundaryRep (G := G) (n+1) := by
  simp [repComplex, ChainComplex.of_d]

def augmentationRep : X.chainsRep (G := G) 1 ⟶ Rep.trivial k G k :=
  Rep.ofHom ⟨X.sumCoefficients 1, by
    intro g
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro r
    simp [FinsuppPermutation.ρ_single]⟩

@[simp] lemma augmentationRep_boundary :
    X.boundaryRep (G := G) 1 ≫ X.augmentationRep (G := G) = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact X.augmentation_boundary

lemma repComplex_exactAt (n : ℕ) (h : X.chainComplex.ExactAt (n+1)) :
    (X.repComplex (G := G)).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)] at h ⊢
  apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k))).mp
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  have hh := (ShortComplex.moduleCat_exact_iff _).mp h
  change ∀ c, X.repComplex.d (n+1) n c = 0 → ∃ b, X.repComplex.d (n+2) (n+1) b = c
  change ∀ c, X.chainComplex.d (n+1) n c = 0 → ∃ b, X.chainComplex.d (n+2) (n+1) b = c at hh
  simp only [repComplex_d, chainComplex_d] at hh ⊢
  exact hh

lemma augmentationRep_exact (h : Function.Exact (X.boundary 1) (X.sumCoefficients 1)) :
    (ShortComplex.mk (X.boundaryRep (G := G) 1) X.augmentationRep X.augmentationRep_boundary).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k))).mp
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  exact fun c hc => (h c).mp hc

omit [DecidableEq V] in
lemma augmentationRep_epi [Nonempty (X.Face 1)] : Epi (X.augmentationRep (G := G)) := by
  apply (Rep.epi_iff_surjective _).mpr
  intro r
  let s : X.Face 1 := Classical.choice inferInstance
  exact ⟨Finsupp.single s r, X.sumCoefficients_single 1 s r⟩

end CoboundaryExpanders.InfiniteChains.Complex

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

instance vertexMulAction : MulAction G (Vertex H) where
  smul g x := ⟨x.1, g • x.2⟩
  one_smul x := congrArg (Sigma.mk x.1) (one_smul G x.2)
  mul_smul g h x := congrArg (Sigma.mk x.1) (mul_smul g h x.2)

omit [DecidableEq I] in
@[simp] lemma map_face (g h : G) (A : Finset I) :
    (face H h A).map (MulAction.toPerm g).toEmbedding = face H (g*h) A := by
  rw [Finset.map_eq_image, face, Finset.image_image]
  rfl

lemma types_card {σ : Finset (Vertex H)} (hσ : IsFace H σ) :
    (types H σ).card = σ.card := by
  obtain ⟨g,A,rfl⟩ := hσ
  simp

instance complexInvariant : Fact ((complex H).Invariant (G := G)) := ⟨by
  rintro g σ ⟨h,A,rfl⟩
  rw [map_face]
  exact ⟨g*h,A,rfl⟩⟩

abbrev Types (n : ℕ) := {A : Finset I // A.card = n}
abbrev Basis (n : ℕ) := (A : Types (I := I) n) × G ⧸ stabilizer H A.val

def gradedFace (n : ℕ) (x : Basis H n) : (complex H).Face n :=
  let q := quotientFace H x.1.val x.2
  ⟨q.val, q.property.1, by
    have hh := types_card H q.property.1
    rw [q.property.2] at hh
    exact hh.symm.trans x.1.property⟩

lemma gradedFace_bijective (n : ℕ) : Function.Bijective (gradedFace H n) := by
  constructor
  · rintro ⟨A,x⟩ ⟨B,y⟩ he
    have ht : A.val = B.val := by
      have hh := congrArg (fun s : (complex H).Face n => types H s.val) he
      exact (quotientFace H A.val x).property.2.symm.trans
        (hh.trans (quotientFace H B.val y).property.2)
    have hAB : A=B := Subtype.ext ht
    subst B
    congr 1
    apply (quotientFace_bijective H A.val).1
    have hv := congrArg (fun z : (complex H).Face n => z.val) he
    exact Subtype.ext hv
  · rintro ⟨σ,hσ,hc⟩
    obtain ⟨g,A,rfl⟩ := hσ
    have hA : A.card = n := by simpa using hc
    exact ⟨⟨⟨A,hA⟩,QuotientGroup.mk g⟩,rfl⟩

@[simp] lemma gradedFace_mk (n : ℕ) (A : Types (I := I) n) (g : G) :
    (gradedFace H n ⟨A,QuotientGroup.mk g⟩).val = face H g A.val := rfl

end CoboundaryExpanders.TypedCosetFaces

end

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra

namespace CoboundaryExpanders.CosetModules

section
universe u
variable {k G : Type u} [Field k] [Group G]

abbrev permutation (H : Subgroup G) : Rep k G := Rep.ofMulAction k G (G ⧸ H)

end

end CoboundaryExpanders.CosetModules

namespace CoboundaryExpanders.CosetSums
variable {k G I : Type} [Field k] [Group G] (H : I → Subgroup G)
abbrev Basis := (i : I) × G ⧸ H i
instance instMulActionBasis : MulAction G (Basis H) where
  smul g x := ⟨x.1, g • x.2⟩
  one_smul x := congrArg (Sigma.mk x.1) (one_smul G x.2)
  mul_smul g h x := congrArg (Sigma.mk x.1) (mul_smul g h x.2)
abbrev permutation : Rep k G := Rep.ofMulAction k G (Basis H)

end CoboundaryExpanders.CosetSums

namespace CoboundaryExpanders.TypedCosetFaces

open InfiniteChains
open CategoryTheory
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

abbrev Simplex := CoboundaryExpanders.InfiniteChains.Complex.full I

def typeFace (n : ℕ) (s : (complex H).Face n) : (Simplex (I := I)).Face n :=
  ⟨types H s.val, Set.mem_univ _, (types_card H s.property.1).trans s.property.2⟩

def baseFace (n : ℕ) (A : (Simplex (I := I)).Face n) : (complex H).Face n :=
  ⟨face H 1 A.val, ⟨1,A.val,rfl⟩, by simp [A.property.2]⟩

@[simp] lemma typeFace_baseFace (n : ℕ) (A : (Simplex (I := I)).Face n) :
    typeFace H n (baseFace H n A) = A := Subtype.ext (types_face H 1 A.val)

@[simp] lemma typeFace_smul (n : ℕ) (g : G) (s : (complex H).Face n) :
    typeFace H n (g • s) = typeFace H n s := by
  obtain ⟨g',A,hA⟩ := s.property.1
  apply Subtype.ext
  change types H (s.val.map (MulAction.toPerm g).toEmbedding) = types H s.val
  rw [← hA, map_face, types_face, types_face]

def typeMap (n : ℕ) : (complex H).Chains n →ₗ[k] (Simplex (I := I)).Chains n :=
  Finsupp.lmapDomain k k (typeFace H n)

@[simp] lemma typeMap_single (n : ℕ) (s : (complex H).Face n) (r : k) :
    typeMap H n (Finsupp.single s r) = Finsupp.single (typeFace H n s) r :=
  Finsupp.mapDomain_single

lemma typeMap_invariant (n : ℕ) (g : G) :
    (typeMap H n).comp (((complex H).chainsRep (G := G) n).ρ g) = typeMap H n := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp [FinsuppPermutation.ρ_single]

abbrev CoinvariantChains (n : ℕ) := ((complex H).chainsRep (G := G) n).ρ.Coinvariants

def toTypes (n : ℕ) : CoinvariantChains H n →ₗ[k] (Simplex (I := I)).Chains n :=
  Representation.Coinvariants.lift _ (typeMap H n) (typeMap_invariant H n)

@[simp] lemma toTypes_single (n : ℕ) (s : (complex H).Face n) (r : k) :
    toTypes H n (Representation.Coinvariants.mk (FinsuppPermutation.ρ k G ((complex H).Face n)) (Finsupp.single s r)) =
      Finsupp.single (typeFace H n s) r := typeMap_single H n s r

def fromTypes (n : ℕ) : (Simplex (I := I)).Chains n →ₗ[k] CoinvariantChains H n :=
  Finsupp.linearCombination k (fun A =>
    Representation.Coinvariants.mk (FinsuppPermutation.ρ k G ((complex H).Face n)) (Finsupp.single (baseFace H n A) 1))

@[simp] lemma fromTypes_single (n : ℕ) (A : (Simplex (I := I)).Face n) (r : k) :
    fromTypes H n (Finsupp.single A r) =
      Representation.Coinvariants.mk (FinsuppPermutation.ρ k G ((complex H).Face n)) (Finsupp.single (baseFace H n A) r) := by
  simp [fromTypes, ← map_smul]

end CoboundaryExpanders.TypedCosetFaces

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Stabilization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Block stabilization, homology actions, quotient vanishing, and congruence cokernels.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Blocks

section
open CoboundaryExpanders.Construction

def gammaStabilization (p a b m : ℕ) : Gamma p a m →* Gamma p (a + b) m where
  toFun g := ⟨stabilizeSL a b g.val, by
    change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m))
      (stabilizeSL a b g.val) = 1
    rw [stabilizeSL_map, g.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

def gammaReindex (p N m : ℕ) (e : Fin N ≃ Fin N) : Gamma p N m ≃* Gamma p N m where
  toFun g := ⟨reindexSL e g.val, by
    change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) (reindexSL e g.val) = 1
    rw [reindexSL_map, g.property, map_one]⟩
  invFun g := ⟨reindexSL e.symm g.val, by
    change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) (reindexSL e.symm g.val) = 1
    rw [reindexSL_map, g.property, map_one]⟩
  left_inv g := by apply Subtype.ext; exact (reindexSL e).left_inv g.val
  right_inv g := by apply Subtype.ext; exact (reindexSL e).right_inv g.val
  map_mul' g h := Subtype.ext (map_mul _ _ _)

end

open CoboundaryExpanders.Elementary CoboundaryExpanders.Construction
variable {A : Type*} [CommRing A]

@[simp] theorem reindexSL_E {N : ℕ} (e : Fin N ≃ Fin N) {i j : Fin N}
    (hij : i ≠ j) (c : A) :
    reindexSL e (E hij c) = E (show e i ≠ e j from fun he => hij (e.injective he)) c := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply,
    Matrix.one_apply, e.injective.eq_iff]

end CoboundaryExpanders.Blocks

namespace CoboundaryExpanders.Actions
universe u
variable {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]

def coeff (f : H →* G) : Rep.trivial k H k ⟶ Rep.res f (Rep.trivial k G k) :=
  𝟙 (Rep.trivial k H k)

def induced (f : H →* G) (j : ℕ) :
    groupHomology (Rep.trivial k H k) j ⟶ groupHomology (Rep.trivial k G k) j :=
  groupHomology.map f (coeff f) j

@[simp] theorem induced_id (j : ℕ) : induced (k := k) (MonoidHom.id G) j = 𝟙 _ :=
  groupHomology.map_id j

theorem induced_congr {f g : H →* G} (h : f = g) (j : ℕ) :
    induced (k := k) f j = induced g j := by rw [h]

theorem induced_comp (f : H →* G) (g : G →* K) (j : ℕ) :
    induced (k := k) (g.comp f) j = induced f j ≫ induced g j := by
  unfold induced
  rw [← groupHomology.map_comp]
  exact groupHomology.map_congr rfl rfl j

variable (S : Subgroup G) [S.Normal]

def conjugation (g : G) (j : ℕ) :
    groupHomology (Rep.trivial k S k) j ⟶ groupHomology (Rep.trivial k S k) j :=
  induced (MulAut.conjNormal (H := S) g).toMonoidHom j

@[simp] theorem conjugation_one (j : ℕ) : conjugation (k := k) S 1 j = 𝟙 _ := by
  unfold conjugation
  have he : (MulAut.conjNormal (H := S) (1 : G)).toMonoidHom = MonoidHom.id S := by
    ext x; simp
  rw [he, induced_id]

theorem conjugation_mul (g h : G) (j : ℕ) :
    conjugation (k := k) S (g * h) j = conjugation S h j ≫ conjugation S g j := by
  unfold conjugation
  rw [← induced_comp]
  apply induced_congr
  ext x
  simp [MulAut.conjNormal_apply, mul_assoc]

def fixingSubgroup (j : ℕ) : Subgroup G where
  carrier := {g | conjugation (k := k) S g j = 𝟙 _}
  one_mem' := conjugation_one S j
  mul_mem' := by
    intro g h hg hh
    change conjugation S (g * h) j = _
    rw [conjugation_mul, hg, hh, Category.id_comp]
  inv_mem' := by
    intro g hg
    have he := conjugation_mul (k := k) S g g⁻¹ j
    rw [mul_inv_cancel, conjugation_one] at he
    change conjugation S g j = 𝟙 _ at hg
    rw [hg, Category.comp_id] at he
    exact he.symm

end CoboundaryExpanders.Actions

namespace CoboundaryExpanders.Blocks
open CoboundaryExpanders.Construction CoboundaryExpanders.Elementary
open CoboundaryExpanders.Actions CategoryTheory

instance gammaNormal (p a m : ℕ) : (Gamma p a m).Normal :=
  MonoidHom.normal_ker _

end CoboundaryExpanders.Blocks

namespace CoboundaryExpanders.QuotientVanishing
open CategoryTheory CoboundaryExpanders.Construction CoboundaryExpanders.Actions

variable (p a m : ℕ) [NeZero p]
abbrev K := (uReduction p a m).ker

def gammaInU (hm : 1 ≤ m) : Gamma p a m ≃* K p a m where
  toFun x := ⟨⟨x.val, gamma_le_U p a m hm x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end CoboundaryExpanders.QuotientVanishing

namespace CoboundaryExpanders.Blocks

section
open CoboundaryExpanders.Construction

@[simp] theorem gammaStabilization_coe (p a b m : ℕ) (x : Gamma p a m) :
    (gammaStabilization p a b m x).val = stabilizeSL a b x.val := rfl

theorem gammaStabilization_natural (p a b m n : ℕ)
    (ha : Gamma p a n ≤ Gamma p a m)
    (hab : Gamma p (a + b) n ≤ Gamma p (a + b) m) :
    (Subgroup.inclusion hab).comp (gammaStabilization p a b n) =
      (gammaStabilization p a b m).comp (Subgroup.inclusion ha) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  simp only [MonoidHom.comp_apply, Subgroup.coe_inclusion, gammaStabilization_coe]

end

variable {A : Type*} [CommRing A]

@[simp] theorem stabilizeSL_left_block (a b : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin a) A) (i j : Fin a) :
    stabilizeSL a b g (Fin.castAdd b i) (Fin.castAdd b j) = g i j := by
  change reindexSL finSumFinEquiv (blockSL a b g)
    (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = _
  rw [reindexSL_apply]
  rfl

open CoboundaryExpanders.Construction

end CoboundaryExpanders.Blocks

namespace CoboundaryExpanders.Cokernel
variable {k : Type*} [CommRing k]
variable {A A' B B' : Type*}
  [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
  [Module k A] [Module k A'] [Module k B] [Module k B']

abbrev Coker (f : A →ₗ[k] B) := B ⧸ LinearMap.range f

def transition (f : A →ₗ[k] B) (f' : A' →ₗ[k] B')
    (u : A' →ₗ[k] A) (v : B' →ₗ[k] B) (h : v.comp f' = f.comp u) :
    Coker f' →ₗ[k] Coker f :=
  (LinearMap.range f').mapQ (LinearMap.range f) v (by
    rintro y ⟨x, rfl⟩
    change v (f' x) ∈ LinearMap.range f
    exact ⟨u x, (LinearMap.congr_fun h x).symm⟩)

@[simp] theorem transition_mk (f : A →ₗ[k] B) (f' : A' →ₗ[k] B')
    (u : A' →ₗ[k] A) (v : B' →ₗ[k] B) (h : v.comp f' = f.comp u) (x : B') :
    transition f f' u v h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (v x) := rfl

end CoboundaryExpanders.Cokernel

namespace CoboundaryExpanders.CongruenceCokernels
open CoboundaryExpanders.Construction CoboundaryExpanders.Blocks
open CoboundaryExpanders.Actions CategoryTheory

abbrev H (p a m j : ℕ) := groupHomology (Rep.trivial (ZMod 2) (Gamma p a m) (ZMod 2)) j

def stabilization (p a m j : ℕ) : H p a m j →ₗ[ZMod 2] H p (a + 1) m j :=
  (induced (gammaStabilization p a 1 m) j).hom

def transition (p a m n j : ℕ) (hmn : m ≤ n) : H p a n j →ₗ[ZMod 2] H p a m j :=
  (induced (Subgroup.inclusion (gamma_antitone p a hmn)) j).hom

theorem group_natural (p a m n : ℕ) (hmn : m ≤ n) :
    (Subgroup.inclusion (gamma_antitone p (a + 1) hmn)).comp (gammaStabilization p a 1 n) =
      (gammaStabilization p a 1 m).comp (Subgroup.inclusion (gamma_antitone p a hmn)) :=
  gammaStabilization_natural p a 1 m n (gamma_antitone p a hmn)
    (gamma_antitone p (a + 1) hmn)

theorem natural (p a m n j : ℕ) (hmn : m ≤ n) :
    (transition p (a + 1) m n j hmn).comp (stabilization p a n j) =
      (stabilization p a m j).comp (transition p a m n j hmn) := by
  have hh := induced_congr (k := ZMod 2) (group_natural p a m n hmn) j
  rw [induced_comp, induced_comp] at hh
  exact congrArg ModuleCat.Hom.hom hh

abbrev C (p a m j : ℕ) := Cokernel.Coker (stabilization p a m j)

def cokerTransition (p a m n j : ℕ) (hmn : m ≤ n) : C p a n j →ₗ[ZMod 2] C p a m j :=
  Cokernel.transition (stabilization p a m j) (stabilization p a n j)
    (transition p a m n j hmn) (transition p (a + 1) m n j hmn) (natural p a m n j hmn)

def ProZero (p a j : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ n : ℕ, ∃ hmn : m ≤ n, cokerTransition p a m n j hmn = 0

end CoboundaryExpanders.CongruenceCokernels

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Resolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Partial resolutions, orbit projectivity, and homology of finite congruence coset complexes.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits

namespace CoboundaryExpanders.PartialResolution
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : ChainComplex C ℕ) (h : ℕ)
variable (P : ProjectiveResolution (kernel (K.d (h + 1) h)))

abbrev X (n : ℕ) : C := if n ≤ h + 1 then K.X n else P.complex.X (n - (h + 2))

def lowIso (n : ℕ) (hn : n ≤ h + 1) : X K h P n ≅ K.X n :=
  eqToIso (ite_eq_left hn)

def highIso (n : ℕ) (hn : ¬ n ≤ h + 1) :
    X K h P n ≅ P.complex.X (n - (h + 2)) := eqToIso (ite_eq_right hn)

def augment : P.complex.X 0 ⟶ kernel (K.d (h + 1) h) :=
  P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 _).hom

@[reassoc (attr := simp)] theorem augment_condition :
    P.complex.d 1 0 ≫ augment K h P = 0 := by
  unfold augment
  rw [← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]

instance instEpiAugment : Epi (augment K h P) := by unfold augment; infer_instance

def d (n : ℕ) : X K h P (n + 1) ⟶ X K h P n :=
  if hn : n + 1 ≤ h + 1 then
    (lowIso K h P (n+1) hn).hom ≫ K.d (n+1) n ≫
      (lowIso K h P n (by omega)).inv
  else if he : n = h + 1 then
    (highIso K h P (n+1) hn).hom ≫
      eqToHom (congrArg P.complex.X (show n+1-(h+2)=0 by omega)) ≫
      augment K h P ≫ kernel.ι (K.d (h+1) h) ≫
      eqToHom (congrArg K.X he.symm) ≫ (lowIso K h P n (by omega)).inv
  else
    (highIso K h P (n+1) hn).hom ≫
      P.complex.d (n+1-(h+2)) (n-(h+2)) ≫
      (highIso K h P n (by omega)).inv

@[reassoc (attr := simp)] theorem lowIso_inv_hom (n : ℕ) (h₁ h₂ : n ≤ h+1) :
    (lowIso K h P n h₁).inv ≫ (lowIso K h P n h₂).hom = 𝟙 _ := by
  simp

@[reassoc (attr := simp)] theorem highIso_inv_hom (n : ℕ) (h₁ h₂ : ¬ n ≤ h+1) :
    (highIso K h P n h₁).inv ≫ (highIso K h P n h₂).hom = 𝟙 _ := by
  simp

theorem d_comp_d (n : ℕ) : d K h P (n + 1) ≫ d K h P n = 0 := by
  by_cases hn2 : n + 2 ≤ h + 1
  · have hn1 : n + 1 ≤ h + 1 := by omega
    simp [d, hn2, hn1, Category.assoc]
  · by_cases hn1 : n + 1 ≤ h + 1
    · have he : n = h := by omega
      subst n
      simp [d, Category.assoc]
    · by_cases hn0 : n = h + 1
      · subst n
        have he : h+1+1+1-(h+2) = 1 := by omega
        simp [d, Category.assoc]
        rw [he]
        simp
      · have hn' : n ≠ h := by omega
        simp [d, hn2, hn1, hn0, hn', Category.assoc]

def complex : ChainComplex C ℕ := ChainComplex.of (X K h P) (d K h P) (d_comp_d K h P)

@[simp] theorem complex_d (n : ℕ) :
    (complex K h P).d (n+1) n = d K h P n := by
  simp only [complex, ChainComplex.of_d]

def short (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (d K h P (n+1)) (d K h P n) (d_comp_d K h P n)

def kernelShort : ShortComplex C :=
  ShortComplex.mk (augment K h P ≫ kernel.ι (K.d (h+1) h)) (K.d (h+1) h)
    (by simp)

theorem kernelShort_exact : (kernelShort K h P).Exact := by
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  change Epi (kernel.lift (K.d (h+1) h)
    (augment K h P ≫ kernel.ι (K.d (h+1) h)) (by simp))
  have he : kernel.lift (K.d (h+1) h)
      (augment K h P ≫ kernel.ι (K.d (h+1) h)) (by simp) = augment K h P := by
    apply (cancel_mono (kernel.ι (K.d (h+1) h))).mp
    exact kernel.lift_ι _ _ _
  rw [he]
  infer_instance

def augmentShort : ShortComplex C :=
  ShortComplex.mk (P.complex.d 1 0) (augment K h P ≫ kernel.ι (K.d (h+1) h))
    (by simp)

theorem augmentShort_exact : (augmentShort K h P).Exact := by
  let S : ShortComplex C := ShortComplex.mk _ _ P.complex_d_comp_π_f_zero
  let φ : S ⟶ augmentShort K h P :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 _).hom ≫
        kernel.ι (K.d (h+1) h)
      comm₁₂ := by simp [S, augmentShort]
      comm₂₃ := by
        change 𝟙 (P.complex.X 0) ≫ (augment K h P ≫ kernel.ι (K.d (h+1) h)) =
          P.π.f 0 ≫
            ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 _).hom ≫
              kernel.ι (K.d (h+1) h))
        rw [Category.id_comp, augment, Category.assoc] }
  have : Epi φ.τ₁ := by
    change Epi (𝟙 (P.complex.X 1))
    infer_instance
  have : IsIso φ.τ₂ := by
    change IsIso (𝟙 (P.complex.X 0))
    infer_instance
  have : Mono φ.τ₃ := by
    change Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 _).hom ≫
      kernel.ι (K.d (h+1) h))
    infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp P.exact₀

def lowShortIso (n : ℕ) (hn : n+2 ≤ h+1) :
    short K h P n ≅ ShortComplex.mk _ _ (K.d_comp_d (n+2) (n+1) n) :=
  ShortComplex.isoMk (lowIso K h P (n+2) hn)
    (lowIso K h P (n+1) (by omega)) (lowIso K h P n (by omega))
      (by dsimp [short]; simp [d, show n+1+1 ≤ h+1 by omega, Category.assoc])
      (by dsimp [short]; simp [d, show n+1 ≤ h+1 by omega, Category.assoc])

def kernelShortIso : short K h P h ≅ kernelShort K h P :=
  ShortComplex.isoMk
    (highIso K h P (h+2) (by omega) ≪≫ eqToIso (by simp [kernelShort]))
    (lowIso K h P (h+1) (by omega)) (lowIso K h P h (by omega))
    (by dsimp [short, kernelShort]; simp [d, Category.assoc])
    (by dsimp [short, kernelShort]; simp [d, Category.assoc])

def augmentShortIso : short K h P (h+1) ≅ augmentShort K h P :=
  ShortComplex.isoMk
    (highIso K h P (h+3) (by omega) ≪≫ eqToIso (by congr 1; omega))
    (highIso K h P (h+2) (by omega) ≪≫ eqToIso (by simp [augmentShort]))
    (lowIso K h P (h+1) (by omega))
    (by dsimp [short, augmentShort]; simp [d, Category.assoc])
    (by dsimp [short, augmentShort]; simp [d, Category.assoc])

lemma d_high (n : ℕ) (hn : h+2 ≤ n) :
    d K h P n = (highIso K h P (n+1) (by omega)).hom ≫
      P.complex.d (n+1-(h+2)) (n-(h+2)) ≫ (highIso K h P n (by omega)).inv := by
  rw [d, dite_eq_right (by omega), dite_eq_right (by omega)]

def tailShortIso (r : ℕ) : short K h P (h+2+r) ≅
    ShortComplex.mk _ _ (P.complex.d_comp_d (r+2) (r+1) r) :=
  ShortComplex.isoMk
    (highIso K h P (h+2+r+2) (by omega) ≪≫ P.complex.XIsoOfEq (by omega))
    (highIso K h P (h+2+r+1) (by omega) ≪≫ P.complex.XIsoOfEq (by omega))
    (highIso K h P (h+2+r) (by omega) ≪≫ P.complex.XIsoOfEq (by omega))
    (by
      dsimp [short]
      rw [d_high K h P _ (by omega)]
      simp [Category.assoc])
    (by
      dsimp [short]
      rw [d_high K h P _ (by omega)]
      simp [Category.assoc])

theorem complex_exactAt_succ
    (hK : ∀ n, n < h → K.ExactAt (n+1)) (n : ℕ) :
    (complex K h P).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', complex_d]
  change (short K h P n).Exact
  by_cases hn : n < h
  · apply (ShortComplex.exact_iff_of_iso (lowShortIso K h P n (by omega))).mpr
    exact (HomologicalComplex.exactAt_iff' K (n+2) (n+1) n (by simp) (by simp)).mp (hK n hn)
  · by_cases hn' : n = h
    · subst n
      exact (ShortComplex.exact_iff_of_iso (kernelShortIso K h P)).mpr (kernelShort_exact K h P)
    · by_cases hn'' : n = h+1
      · subst n
        exact (ShortComplex.exact_iff_of_iso (augmentShortIso K h P)).mpr (augmentShort_exact K h P)
      · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show h+2 ≤ n by omega)
        exact (ShortComplex.exact_iff_of_iso (tailShortIso K h P r)).mpr (P.exact_succ r)

theorem complex_projective (hK : ∀ n ≤ h+1, Projective (K.X n)) (n : ℕ) :
    Projective ((complex K h P).X n) := by
  by_cases hn : n ≤ h+1
  · exact Projective.of_iso (lowIso K h P n hn).symm (hK n hn)
  · exact Projective.of_iso (highIso K h P n hn).symm inferInstance

variable {Z : C} (ε : K.X 0 ⟶ Z) (hε : K.d 1 0 ≫ ε = 0)

def π : complex K h P ⟶ (ChainComplex.single₀ C).obj Z :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(lowIso K h P 0 (by omega)).hom ≫ ε, by
      rw [complex_d]
      change d K h P 0 ≫ (lowIso K h P 0 (by omega)).hom ≫ ε = 0
      simp [d, Category.assoc, hε]⟩

def augmentationShortIso :
    ShortComplex.mk ((complex K h P).d 1 0) ((π K h P ε hε).f 0)
      (by
        rw [← HomologicalComplex.Hom.comm]
        simp
        exact comp_zero) ≅
    ShortComplex.mk (K.d 1 0) ε hε :=
  ShortComplex.isoMk (lowIso K h P 1 (by omega))
    (lowIso K h P 0 (by omega)) (Iso.refl Z)
    (by
      dsimp only
      rw [complex_d]
      change (lowIso K h P 1 (by omega)).hom ≫ K.d 1 0 =
        d K h P 0 ≫ (lowIso K h P 0 (by omega)).hom
      simp [d, Category.assoc])
    (by simp [π])

def resolution
    (hproj : ∀ n ≤ h+1, Projective (K.X n))
    (hexact : ∀ n, n < h → K.ExactAt (n+1))
    (hzero : (ShortComplex.mk (K.d 1 0) ε hε).Exact) [Epi ε] :
    ProjectiveResolution Z where
  complex := complex K h P
  projective := complex_projective K h P hproj
  π := π K h P ε hε
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · exact (ShortComplex.exact_and_epi_g_iff_of_iso
          (augmentationShortIso K h P ε hε)).mpr ⟨hzero, inferInstance⟩
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exactAt_succ K h P hexact n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

lemma complex_d_low (a b : ℕ) (ha : a ≤ h+1) (hb : b ≤ h+1) :
    (complex K h P).d a b = (lowIso K h P a ha).hom ≫ K.d a b ≫
      (lowIso K h P b hb).inv := by
  by_cases he : a = b+1
  · subst a
    rw [complex_d, d, dite_eq_left ha]
  · rw [(complex K h P).shape a b (by simpa using Ne.symm he),
      K.shape a b (by simpa using Ne.symm he)]
    simp
    rfl

lemma low_comm (a b : ℕ) (ha : a ≤ h+1) (hb : b ≤ h+1) :
    (lowIso K h P a ha).hom ≫ K.d a b =
      (complex K h P).d a b ≫ (lowIso K h P b hb).hom := by
  exact (Iso.comp_inv_eq (lowIso K h P b hb)).mp
    ((Category.assoc _ _ _).trans (complex_d_low K h P a b ha hb).symm)

universe v' u'
variable {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive]

def mappedLowShortIso (j : ℕ) (hj : j ≤ h) :
    ((F.mapHomologicalComplex _).obj (complex K h P)).sc' (j+1) j (j-1) ≅
    ((F.mapHomologicalComplex _).obj K).sc' (j+1) j (j-1) :=
  ShortComplex.isoMk (F.mapIso (lowIso K h P (j+1) (by omega)))
    (F.mapIso (lowIso K h P j (by omega)))
    (F.mapIso (lowIso K h P (j-1) (by omega)))
    (by
      change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg F.map (low_comm K h P (j+1) j (by omega) (by omega)))
    (by
      change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg F.map (low_comm K h P j (j-1) (by omega) (by omega)))

def mappedHomologyIso (j : ℕ) (hj : j ≤ h) :
    ((F.mapHomologicalComplex _).obj (complex K h P)).homology j ≅
    ((F.mapHomologicalComplex _).obj K).homology j :=
  (HomologicalComplex.homologyFunctorIso' D (ComplexShape.down ℕ)
    (j+1) j (j-1) (by simp) (by cases j <;> simp)).app _ ≪≫
  (ShortComplex.homologyFunctor D).mapIso (mappedLowShortIso K h P F j hj) ≪≫
  ((HomologicalComplex.homologyFunctorIso' D (ComplexShape.down ℕ)
    (j+1) j (j-1) (by simp) (by cases j <;> simp)).app _).symm

def derivedIso [HasProjectiveResolutions C]
    (hproj : ∀ n ≤ h+1, Projective (K.X n))
    (hexact : ∀ n, n < h → K.ExactAt (n+1))
    (hzero : (ShortComplex.mk (K.d 1 0) ε hε).Exact) [Epi ε]
    (j : ℕ) (hj : j ≤ h) :
    (F.leftDerived j).obj Z ≅ ((F.mapHomologicalComplex _).obj K).homology j :=
  (resolution K h P ε hε hproj hexact hzero).isoLeftDerivedObj F j ≪≫
    mappedHomologyIso K h P F j hj

end CoboundaryExpanders.PartialResolution

namespace CoboundaryExpanders.CoinvariantHomology
open CategoryTheory.MonoidalCategory
variable (k G : Type) [CommRing k] [Group G]

def trivialTensorIso : (Rep.coinvariantsTensor k G).obj (Rep.trivial k G k) ≅
    Rep.coinvariantsFunctor k G :=
  Functor.isoWhiskerRight (leftUnitorNatIso (Rep k G)) (Rep.coinvariantsFunctor k G) ≪≫
    Functor.leftUnitor _

variable (K : ChainComplex (Rep k G) ℕ)

def coinvariantChainsIso : K.coinvariantsTensorObj (Rep.trivial k G k) ≅
    ((Rep.coinvariantsFunctor k G).mapHomologicalComplex _).obj K :=
  (NatIso.mapHomologicalComplex (trivialTensorIso k G) _).app K

def homologyIso [DecidableEq G] (h : ℕ)
    (ε : K.X 0 ⟶ Rep.trivial k G k) (hε : K.d 1 0 ≫ ε = 0)
    (hproj : ∀ n ≤ h+1, Projective (K.X n))
    (hexact : ∀ n, n < h → K.ExactAt (n+1))
    (hzero : (ShortComplex.mk (K.d 1 0) ε hε).Exact) [Epi ε]
    (j : ℕ) (hj : j ≤ h) :
    groupHomology (Rep.trivial k G k) j ≅
      (((Rep.coinvariantsFunctor k G).mapHomologicalComplex _).obj K).homology j :=
  groupHomologyIsoTor _ j ≪≫
    PartialResolution.derivedIso K h (projectiveResolution (kernel (K.d (h+1) h)))
      ε hε ((Rep.coinvariantsTensor k G).obj (Rep.trivial k G k))
        hproj hexact hzero j hj ≪≫
    (HomologicalComplex.homologyFunctor _ _ j).mapIso (coinvariantChainsIso k G K)

end CoboundaryExpanders.CoinvariantHomology

namespace CoboundaryExpanders.Construction
open CategoryTheory InfiniteChains
variable (p n : ℕ) [Fact p.Prime]

abbrev infiniteCosetComplex (hn : 1 ≤ n) :=
  TypedCosetFaces.complex (uLocalGroup p n hn)

def OppositionAcyclic (hn : 1 ≤ n) : Prop :=
  Function.Exact ((infiniteCosetComplex p n hn).boundary 1)
    ((infiniteCosetComplex p n hn).sumCoefficients 1) ∧
  ∀ j : ℕ, 0 < j → j < n-1 → (infiniteCosetComplex p n hn).chainComplex.ExactAt j

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.KernelCosetOrbits
variable {G Q : Type} [Group G] [Group Q] (f : G →* Q) (H : Subgroup G)

def cosetMap : G ⧸ H → Q ⧸ H.map f :=
  Quotient.map f (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    exact ⟨a⁻¹*b, QuotientGroup.leftRel_apply.mp hab, by simp⟩)

@[simp] lemma cosetMap_mk (a : G) :
    cosetMap f H (QuotientGroup.mk a) = QuotientGroup.mk (f a) := rfl

lemma cosetMap_smul (k : f.ker) (a : G ⧸ H) :
    cosetMap f H (k • a) = cosetMap f H a := by
  induction a using Quotient.inductionOn with | h a =>
    change QuotientGroup.mk (f (k.val*a)) = QuotientGroup.mk (f a)
    rw [map_mul, show f k.val = 1 from k.property, one_mul]

lemma cosetMap_eq_iff (a b : G ⧸ H) :
    cosetMap f H a = cosetMap f H b ↔ MulAction.orbitRel f.ker (G ⧸ H) a b := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  constructor
  · intro hab
    obtain ⟨h, hh, he⟩ := QuotientGroup.leftRel_apply.mp (Quotient.exact hab)
    have hk : a*h*b⁻¹ ∈ f.ker := by
      change f (a*h*b⁻¹) = 1
      rw [map_mul, map_mul, map_inv, he]
      simp
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨a*h*b⁻¹, hk⟩, ?_⟩
    change QuotientGroup.mk ((a*h*b⁻¹)*b) = QuotientGroup.mk a
    simp only [inv_mul_cancel_right]
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    simpa using H.inv_mem hh
  · intro hab
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp hab
    rw [← hk]
    exact cosetMap_smul f H k _

end CoboundaryExpanders.KernelCosetOrbits

namespace CoboundaryExpanders.TypedCosetFaces

section
open InfiniteChains
attribute [local instance 1100] InfiniteChains.Complex.faceMulAction
variable {G Q I : Type} [Group G] [Group Q] [DecidableEq I]
variable (H : I → Subgroup G) (f : G →* Q)
abbrev imageGroups : I → Subgroup Q := fun i => (H i).map f

def vertexMap : Vertex H → Vertex (imageGroups H f) :=
  fun x => ⟨x.1, KernelCosetOrbits.cosetMap f (H x.1) x.2⟩

omit [DecidableEq I] in
@[simp] lemma vertexMap_vertex (g : G) (i : I) :
    vertexMap H f (vertex H g i) = vertex (imageGroups H f) (f g) i := rfl

omit [DecidableEq I] in
@[simp] lemma image_face (g : G) (A : Finset I) :
    (face H g A).image (vertexMap H f) = face (imageGroups H f) (f g) A := by
  simp [face, Finset.image_image, Function.comp_def]

omit [DecidableEq I] in
lemma vertexMap_injOn (s : Finset (Vertex H)) (hs : IsFace H s) :
    Set.InjOn (vertexMap H f) s := by
  obtain ⟨g,A,rfl⟩ := hs
  intro x hx y hy hxy
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
  have he : i=j := congrArg Sigma.fst hxy
  subst j
  rfl

def quotientFaceMap (n : ℕ) (s : (complex H).Face n) :
    (complex (imageGroups H f)).Face n :=
  ⟨s.val.image (vertexMap H f), by
    obtain ⟨g,A,hA⟩ := s.property.1
    rw [← hA, image_face]
    exact ⟨f g,A,rfl⟩,
    (Finset.card_image_of_injOn (vertexMap_injOn H f s.val s.property.1)).trans s.property.2⟩

@[simp] lemma quotientFaceMap_graded (n : ℕ) (A : Types (I := I) n) (g : G) :
    quotientFaceMap H f n (gradedFace H n ⟨A,QuotientGroup.mk g⟩) =
      gradedFace (imageGroups H f) n ⟨A,QuotientGroup.mk (f g)⟩ := by
  apply Subtype.ext
  exact image_face H f g A.val

lemma quotientFaceMap_surjective (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (quotientFaceMap H f n) := by
  intro s
  obtain ⟨⟨A,q⟩,rfl⟩ := (gradedFace_bijective (imageGroups H f) n).2 s
  induction q using Quotient.inductionOn with | h q =>
    obtain ⟨g,rfl⟩ := hf q
    exact ⟨gradedFace H n ⟨A,QuotientGroup.mk g⟩,quotientFaceMap_graded H f n A g⟩

instance kernelInvariant : Fact ((complex H).Invariant (G := f.ker)) := ⟨by
  rintro k s ⟨g,A,rfl⟩
  change (face H g A).map (MulAction.toPerm (k.val)).toEmbedding ∈ (complex H).faces
  rw [map_face]
  exact ⟨k.val*g,A,rfl⟩⟩

lemma kernel_smul_graded (n : ℕ) (k : f.ker) (A : Types (I := I) n) (g : G) :
    k • gradedFace H n ⟨A,QuotientGroup.mk g⟩ =
      gradedFace H n ⟨A,QuotientGroup.mk (k.val*g)⟩ := by
  apply Subtype.ext
  exact map_face H k.val g A.val

lemma quotientFaceMap_invariant (n : ℕ) (k : f.ker) (s : (complex H).Face n) :
    quotientFaceMap H f n (k • s) = quotientFaceMap H f n s := by
  obtain ⟨⟨A,q⟩,rfl⟩ := (gradedFace_bijective H n).2 s
  induction q using Quotient.inductionOn with | h g =>
  rw [kernel_smul_graded, quotientFaceMap_graded, quotientFaceMap_graded]
  rw [map_mul, show f k.val = 1 from k.property, one_mul]

lemma quotientFaceMap_eq_iff
    (hinter : ∀ A : Finset I, (stabilizer H A).map f = stabilizer (imageGroups H f) A)
    (n : ℕ) (s t : (complex H).Face n) :
    quotientFaceMap H f n s = quotientFaceMap H f n t ↔
      MulAction.orbitRel f.ker ((complex H).Face n) s t := by
  constructor
  · intro he
    obtain ⟨⟨A,q⟩,rfl⟩ := (gradedFace_bijective H n).2 s
    obtain ⟨⟨B,r⟩,rfl⟩ := (gradedFace_bijective H n).2 t
    induction q using Quotient.inductionOn with | h g =>
    induction r using Quotient.inductionOn with | h h =>
    rw [quotientFaceMap_graded, quotientFaceMap_graded] at he
    have he' := (gradedFace_bijective (imageGroups H f) n).1 he
    have hAB : A = B := congrArg Sigma.fst he'
    subst B
    have hgh : (QuotientGroup.mk (f g) : Q ⧸ stabilizer (imageGroups H f) A.val) =
        QuotientGroup.mk (f h) := eq_of_heq (Sigma.mk.inj_iff.mp he').2
    have hm : (f g)⁻¹ * f h ∈ (stabilizer H A.val).map f := by
      rw [hinter]
      exact QuotientGroup.leftRel_apply.mp (Quotient.exact hgh)
    have hem : KernelCosetOrbits.cosetMap f (stabilizer H A.val) (QuotientGroup.mk g) =
        KernelCosetOrbits.cosetMap f (stabilizer H A.val) (QuotientGroup.mk h) :=
      Quotient.sound (QuotientGroup.leftRel_apply.mpr hm)
    obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp
      ((KernelCosetOrbits.cosetMap_eq_iff f (stabilizer H A.val) _ _).mp hem)
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨k,?_⟩
    rw [kernel_smul_graded]
    exact congrArg (fun c => gradedFace H n ⟨A,c⟩) hk
  · rintro ⟨k,hk⟩
    rw [← hk]
    exact quotientFaceMap_invariant H f n k t

end

section
open InfiniteChains CategoryTheory
attribute [local instance 1100] InfiniteChains.Complex.faceMulAction
variable {G Q I : Type} [Group G] [Group Q] [DecidableEq I]
variable (H : I → Subgroup G) (f : G →* Q)
variable (hf : Function.Surjective f)
variable (hinter : ∀ A : Finset I, (stabilizer H A).map f = stabilizer (imageGroups H f) A)

abbrev KernelCoinvariantChains (n : ℕ) := ((complex H).chainsRep (G := f.ker) n).ρ.Coinvariants

def quotientChainMap (n : ℕ) : (complex H).Chains n →ₗ[k] (complex (imageGroups H f)).Chains n :=
  Finsupp.lmapDomain k k (quotientFaceMap H f n)

@[simp] lemma quotientChainMap_single (n : ℕ) (s : (complex H).Face n) (r : k) :
    quotientChainMap H f n (Finsupp.single s r) = Finsupp.single (quotientFaceMap H f n s) r :=
  Finsupp.mapDomain_single

lemma quotientChainMap_invariant (n : ℕ) (g : f.ker) :
    (quotientChainMap H f n).comp (((complex H).chainsRep (G := f.ker) n).ρ g) =
      quotientChainMap H f n := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp [FinsuppPermutation.ρ_single, quotientFaceMap_invariant]

def toQuotient (n : ℕ) : KernelCoinvariantChains H f n →ₗ[k] (complex (imageGroups H f)).Chains n :=
  Representation.Coinvariants.lift _ (quotientChainMap H f n) (quotientChainMap_invariant H f n)

@[simp] lemma toQuotient_single (n : ℕ) (s : (complex H).Face n) (r : k) :
    toQuotient H f n (Representation.Coinvariants.mk
      (FinsuppPermutation.ρ k f.ker ((complex H).Face n)) (Finsupp.single s r)) =
      Finsupp.single (quotientFaceMap H f n s) r := quotientChainMap_single H f n s r

def liftFace (n : ℕ) (s : (complex (imageGroups H f)).Face n) : (complex H).Face n :=
  Classical.choose (quotientFaceMap_surjective H f hf n s)

@[simp] lemma quotient_liftFace (n : ℕ) (s : (complex (imageGroups H f)).Face n) :
    quotientFaceMap H f n (liftFace H f hf n s) = s :=
  Classical.choose_spec (quotientFaceMap_surjective H f hf n s)

def fromQuotient (n : ℕ) : (complex (imageGroups H f)).Chains n →ₗ[k] KernelCoinvariantChains H f n :=
  Finsupp.linearCombination k (fun s => Representation.Coinvariants.mk
    (FinsuppPermutation.ρ k f.ker ((complex H).Face n)) (Finsupp.single (liftFace H f hf n s) 1))

@[simp] lemma fromQuotient_single (n : ℕ) (s : (complex (imageGroups H f)).Face n) (r : k) :
    fromQuotient H f hf n (Finsupp.single s r) = Representation.Coinvariants.mk
      (FinsuppPermutation.ρ k f.ker ((complex H).Face n)) (Finsupp.single (liftFace H f hf n s) r) := by
  simp [fromQuotient, ← map_smul]

include hinter in
lemma fromQuotient_toQuotient (n : ℕ) :
    (fromQuotient H f hf n).comp (toQuotient H f n) = LinearMap.id := by
  apply Representation.Coinvariants.hom_ext
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  change fromQuotient H f hf n (quotientChainMap H f n (Finsupp.single s r)) =
    Representation.Coinvariants.mk (FinsuppPermutation.ρ k f.ker ((complex H).Face n))
      (Finsupp.single s r)
  rw [quotientChainMap_single, fromQuotient_single]
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp ((quotientFaceMap_eq_iff H f hinter n _ _).mp
    (quotient_liftFace H f hf n (quotientFaceMap H f n s)))
  have hh := Representation.Coinvariants.mk_self_apply
    (FinsuppPermutation.ρ k f.ker ((complex H).Face n)) g (Finsupp.single s r)
  simpa only [FinsuppPermutation.ρ_single, hg] using hh

lemma toQuotient_fromQuotient (n : ℕ) :
    (toQuotient H f n).comp (fromQuotient H f hf n) = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp

def quotientChainsEquiv (n : ℕ) :
    KernelCoinvariantChains H f n ≃ₗ[k] (complex (imageGroups H f)).Chains n :=
  LinearEquiv.ofLinearMap (toQuotient H f n) (fromQuotient H f hf n)
    (toQuotient_fromQuotient H f hf n) (fromQuotient_toQuotient H f hf hinter n)

lemma image_erase_vertex (g : G) (A : Finset I) (i : I) :
    ((face H g A).erase (vertex H g i)).image (vertexMap H f) =
      (face (imageGroups H f) (f g) A).erase (vertex (imageGroups H f) (f g) i) := by
  rw [show (face H g A).erase (vertex H g i) = face H g (A.erase i) from
    (Finset.image_erase (vertex_injective H g) A i).symm]
  rw [image_face]
  exact Finset.image_erase (vertex_injective (imageGroups H f) (f g)) A i

lemma quotientChainMap_boundary (n : ℕ) :
    (quotientChainMap H f n).comp ((complex H).boundary n) =
      (complex (imageGroups H f)).boundary n ∘ₗ quotientChainMap H f (n+1) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  apply (complex (imageGroups H f)).embed_injective n
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, CoboundaryExpanders.InfiniteChains.Complex.boundary_single,
    map_sum, quotientChainMap_single, CoboundaryExpanders.InfiniteChains.Complex.embed_single]
  change (∑ v : ↥s.val, Finsupp.single ((s.val.erase v.val).image (vertexMap H f)) r) =
    ∑ v : ↥(s.val.image (vertexMap H f)), Finsupp.single
      ((s.val.image (vertexMap H f)).erase v.val) r
  rw [Finset.sum_coe_sort s.val
    (fun v => Finsupp.single ((s.val.erase v).image (vertexMap H f)) r),
    Finset.sum_coe_sort (s.val.image (vertexMap H f))
    (fun v => Finsupp.single ((s.val.image (vertexMap H f)).erase v) r)]
  obtain ⟨g,A,hA⟩ := s.property.1
  rw [← hA, image_face]
  change (∑ v ∈ A.image (vertex H g), _) = ∑ v ∈ A.image (vertex (imageGroups H f) (f g)), _
  rw [Finset.sum_image, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [image_erase_vertex]
  · exact fun _ _ _ _ he => vertex_injective (imageGroups H f) (f g) he
  · exact fun _ _ _ _ he => vertex_injective H g he

def kernelCoinvariantBoundary (n : ℕ) :
    KernelCoinvariantChains H f (n+1) →ₗ[k] KernelCoinvariantChains H f n :=
  Representation.Coinvariants.map _ _ ((complex H).boundaryRep (G := f.ker) n).hom

abbrev kernelCoinvariantComplex : ChainComplex (ModuleCat k) ℕ :=
  ((Rep.coinvariantsFunctor k f.ker).mapHomologicalComplex _).obj
    ((complex H).repComplex (G := f.ker))

end

open InfiniteChains CategoryTheory
attribute [local instance 1100] InfiniteChains.Complex.faceMulAction

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.PermutationProjectivity
open CategoryTheory
variable {k G X : Type} [Field k] [Group G] [MulAction G X]
abbrev Orbit := MulAction.orbitRel.Quotient G X
def orbitStabilizer : Orbit (G := G) (X := X) → Subgroup G :=
  fun q => MulAction.stabilizer G q.out

end CoboundaryExpanders.PermutationProjectivity

namespace CoboundaryExpanders.Construction
open CategoryTheory TypedCosetFaces
variable (p n : ℕ) [Fact p.Prime]

abbrev quotientProjection (m : ℕ) : U p (n+1) →* Gquot p (n+1) m :=
  QuotientGroup.mk' (uReduction p (n+1) m).ker

lemma quotientProjection_cross_injective (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (i j : Fin (n+1)) (a b : U p (n+1))
    (ha : a ∈ uLocalGroup p n hn i) (hb : b ∈ uLocalGroup p n hn j)
    (he : quotientProjection p n m a = quotientProjection p n m b) : a = b := by
  apply Subtype.ext
  apply localGroups_reduction_injective p n hn hm i j ⟨a.val,ha⟩ ⟨b.val,hb⟩
  exact congrArg (fun g : Gquot p (n+1) m =>
    (QuotientGroup.quotientKerEquivRange (uReduction p (n+1) m) g).val) he

lemma quotientProjection_intersections (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (A : Finset (Fin (n+1))) :
    (stabilizer (uLocalGroup p n hn) A).map (quotientProjection p n m) =
      stabilizer (reducedLocalGroup p n hn m) A := by
  classical
  apply le_antisymm
  · rintro g hg
    obtain ⟨a,ha,rfl⟩ := Subgroup.mem_map.mp hg
    apply (mem_stabilizer _ _ _).mpr
    intro i hi
    exact Subgroup.mem_map.mpr ⟨a, ((mem_stabilizer _ _ _).mp ha) i hi,rfl⟩
  · intro g hg
    by_cases hA : A.Nonempty
    · obtain ⟨i,hi⟩ := hA
      obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp (((mem_stabilizer _ _ _).mp hg) i hi)
      refine Subgroup.mem_map.mpr ⟨a, (mem_stabilizer _ _ _).mpr ?_,he⟩
      intro j hj
      obtain ⟨b,hb,hbe⟩ := Subgroup.mem_map.mp (((mem_stabilizer _ _ _).mp hg) j hj)
      have hab := quotientProjection_cross_injective p n hn hm i j a b ha hb (he.trans hbe.symm)
      exact hab.symm ▸ hb
    · have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      subst A
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (uReduction p (n+1) m).ker g
      exact Subgroup.mem_map.mpr ⟨a,by simp,rfl⟩

abbrev quotientTypedComplex (hn : 1 ≤ n) (m : ℕ) :=
  TypedCosetFaces.complex (reducedLocalGroup p n hn m)

def gammaQuotientKernelEquiv (m : ℕ) (hm : 1 ≤ m) :
    Gamma p (n+1) m ≃* (quotientProjection p n m).ker :=
  (QuotientVanishing.gammaInU p (n+1) m hm).trans
    (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' _).symm)

end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite labeled coset complexes, purity, growth, incidence bounds, and weighted expansion reduction.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits
open Filter

namespace CoboundaryExpanders.CosetConstruction

section

open CoboundaryExpanders.Complex

variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

abbrev Vertex (H : Fin (n + 1) → Subgroup G) := (i : Fin (n + 1)) × (G ⧸ H i)

noncomputable instance vertexFintype (H : Fin (n + 1) → Subgroup G) :
    Fintype (Vertex H) := Fintype.ofFinite _

def labelEquiv (H : Fin (n + 1) → Subgroup G) :
    Vertex H ≃ Fin (Fintype.card (Vertex H)) := Fintype.equivFin _

def vertex (H : Fin (n + 1) → Subgroup G) (g : G) (i : Fin (n + 1)) :
    Fin (Fintype.card (Vertex H)) := labelEquiv H ⟨i, QuotientGroup.mk g⟩

theorem vertex_surjective (H : Fin (n + 1) → Subgroup G)
    (v : Fin (Fintype.card (Vertex H))) : ∃ i g, vertex H g i = v := by
  obtain ⟨⟨i, c⟩, rfl⟩ := (labelEquiv H).surjective v
  induction c using QuotientGroup.induction_on with
  | H g => exact ⟨i, g, rfl⟩

def chamber (H : Fin (n + 1) → Subgroup G) (g : G) :
    Finset (Fin (Fintype.card (Vertex H))) := Finset.univ.image (vertex H g)

@[simp] theorem mem_chamber {H : Fin (n + 1) → Subgroup G} {g : G} {v} :
    v ∈ chamber H g ↔ ∃ i, vertex H g i = v := by
  simp [chamber]

@[simp] theorem vertex_mem_chamber (H : Fin (n + 1) → Subgroup G) (g : G) (i) :
    vertex H g i ∈ chamber H g := mem_chamber.mpr ⟨i, rfl⟩

@[reducible] def complex (H : Fin (n + 1) → Subgroup G) : Complex where
  vertexCount := Fintype.card (Vertex H)
  faces := Finset.univ.biUnion (fun g : G => (chamber H g).powerset)
  empty_mem := Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _,
    Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
  downward := by
    intro σ τ hσ hτ
    obtain ⟨g, _, hg⟩ := Finset.mem_biUnion.mp hσ
    exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _,
      Finset.mem_powerset.mpr (hτ.trans (Finset.mem_powerset.mp hg))⟩
  vertex_mem := by
    intro v
    obtain ⟨i, g, rfl⟩ := vertex_surjective H v
    exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _,
      Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr (vertex_mem_chamber H g i))⟩

@[simp] theorem mem_faces {H : Fin (n + 1) → Subgroup G} {σ} :
    σ ∈ (complex H).faces ↔ ∃ g, σ ⊆ chamber H g := by
  simp [complex]

def incidentInChamber (H : Fin (n + 1) → Subgroup G) (g : G)
    (v : Fin (Fintype.card (Vertex H))) (d : ℕ) :=
  ((chamber H g).powersetCard (d + 1)).filter (v ∈ ·)

@[simp] theorem mem_incidentInChamber {H : Fin (n + 1) → Subgroup G} {g v d σ} :
    σ ∈ incidentInChamber H g v d ↔ σ ⊆ chamber H g ∧ σ.card = d + 1 ∧ v ∈ σ := by
  simp [incidentInChamber, Finset.mem_powersetCard, and_assoc]

end

end CoboundaryExpanders.CosetConstruction

namespace CoboundaryExpanders.Construction

section
open Filter CosetConstruction _root_.OAI.CoboundaryExpanders.Complex
variable (p n : ℕ) [Fact p.Prime]

def localBound : ℕ := Nat.card (Matrix.GeneralLinearGroup (Fin (n + 1)) (ZMod p))

def finiteCosetComplex (hn : 1 ≤ n) (m : ℕ) : Complex :=
  letI : Fintype (Gquot p (n + 1) m) := Fintype.ofFinite _
  CosetConstruction.complex (reducedLocalGroup p n hn m)

def finiteSkeleton (hn : 1 ≤ n) (d m : ℕ) : Complex :=
  (finiteCosetComplex p n hn (m + 2)).skeleton d

end

open Filter _root_.OAI.CoboundaryExpanders.Complex

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.Complex
local instance instFintypeFace_2 (X : Complex) (i : ℕ) : Fintype (X.Face i) := X.instFintypeFace i
local instance instDecidableEqFace_2 (X : Complex) (i : ℕ) : DecidableEq (X.Face i) := X.instDecidableEqFace i

abbrev Chain (X : Complex) (i : ℕ) := Module.Dual (ZMod 2) (X.Cochain i)

def chainBasis (X : Complex) (i : ℕ) :
    Module.Basis (X.Face i) (ZMod 2) (X.Chain i) :=
  (Pi.basisFun (ZMod 2) (X.Face i)).dualBasis

@[simp] theorem chainBasis_apply (X : Complex) (i : ℕ) (σ : X.Face i)
    (f : X.Cochain i) : X.chainBasis i σ f = f σ := by
  exact (Pi.basisFun (ZMod 2) (X.Face i)).dualBasis_apply σ f

def boundaryLinear (X : Complex) (i : ℕ) : X.Chain (i + 1) →ₗ[ZMod 2] X.Chain i :=
  (X.coboundaryLinear i).dualMap

@[simp] theorem boundary_on_face (X : Complex) (i : ℕ) (τ : X.Face (i + 1)) :
    X.boundaryLinear i (X.chainBasis (i + 1) τ) =
      ∑ σ : X.Face i, if σ.val ⊆ τ.val then X.chainBasis i σ else 0 := by
  apply LinearMap.ext
  intro f
  change X.chainBasis (i + 1) τ (X.coboundary i f) = _
  rw [chainBasis_apply]
  simp only [coboundary, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

@[simp] theorem boundary_boundary (X : Complex) (i : ℕ) :
    (X.boundaryLinear i).comp (X.boundaryLinear (i + 1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro f
  change c (X.coboundary (i + 1) (X.coboundary i f)) = 0
  rw [coboundary_coboundary, map_zero]

open CategoryTheory

def chainComplex (X : Complex) : ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of (ZMod 2) (X.Chain i))
    (fun i => ModuleCat.ofHom (X.boundaryLinear i))
    (fun i => ModuleCat.hom_ext (X.boundary_boundary i))

@[simp] theorem chainComplex_d (X : Complex) (i : ℕ) :
    X.chainComplex.d (i + 1) i = ModuleCat.ofHom (X.boundaryLinear i) :=
  by simp only [chainComplex, ChainComplex.of_d]

end CoboundaryExpanders.Complex

namespace CoboundaryExpanders.CosetConstruction
open CategoryTheory
variable {G : Type} [Group G] [Fintype G] {n : ℕ}
variable (H : Fin (n+1) → Subgroup G)

lemma labelled_face_image (g : G) (A : Finset (Fin (n+1))) :
    (TypedCosetFaces.face H g A).image (labelEquiv H) = A.image (vertex H g) := by
  simp only [TypedCosetFaces.face, Finset.image_image]
  rfl

lemma labelled_mem_faces (s : Finset (Vertex H)) :
    s.image (labelEquiv H) ∈ (complex H).faces ↔ TypedCosetFaces.IsFace H s := by
  classical
  constructor
  · intro hs
    obtain ⟨g,hg⟩ := mem_faces.mp hs
    apply (TypedCosetFaces.complex H).downward (σ := TypedCosetFaces.face H g Finset.univ)
      ⟨g,Finset.univ,rfl⟩
    intro x hx
    have hh := hg (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    obtain ⟨i,hi⟩ := mem_chamber.mp hh
    apply Finset.mem_image.mpr
    exact ⟨i,Finset.mem_univ _,(labelEquiv H).injective hi⟩
  · rintro ⟨g,A,rfl⟩
    rw [labelled_face_image]
    exact mem_faces.mpr ⟨g,Finset.image_subset_image (Finset.subset_univ A)⟩

def typedFaceEquiv (i : ℕ) :
    (TypedCosetFaces.complex H).Face (i+1) ≃ (complex H).Face i where
  toFun s := ⟨s.val.image (labelEquiv H), (Complex.mem_facesOf _ _ _).mpr
    ⟨(labelled_mem_faces H s.val).mpr s.property.1,
      (Finset.card_image_of_injective _ (labelEquiv H).injective).trans s.property.2⟩⟩
  invFun s := ⟨s.val.image (labelEquiv H).symm, by
    constructor
    · apply (labelled_mem_faces H _).mp
      simpa only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply, Finset.image_id']
        using Complex.face_mem s
    · exact (Finset.card_image_of_injective _ (labelEquiv H).symm.injective).trans (Complex.face_card s)⟩
  left_inv s := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.symm_apply_apply, Finset.image_id']
  right_inv s := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply, Finset.image_id']

def typedChainEquiv (i : ℕ) :
    (TypedCosetFaces.complex H).Chains (i+1) ≃ₗ[ZMod 2] (complex H).Chain i :=
  (Finsupp.domLCongr (typedFaceEquiv H i)).trans ((complex H).chainBasis i).repr.symm

@[simp] lemma typedChainEquiv_single (i : ℕ)
    (s : (TypedCosetFaces.complex H).Face (i+1)) (r : ZMod 2) :
    typedChainEquiv H i (Finsupp.single s r) = r • (complex H).chainBasis i (typedFaceEquiv H i s) := by
  simp [typedChainEquiv, Module.Basis.repr_symm_apply]

end CoboundaryExpanders.CosetConstruction

namespace CoboundaryExpanders.Construction
open _root_.OAI.CoboundaryExpanders.Complex Filter
variable (p n : ℕ) [Fact p.Prime]

def UniformCosystolic (hn : 1 ≤ n) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∀ m : ℕ, 2 ≤ m → ∀ i : ℕ, i < n-1 →
    ∀ f : ((finiteCosetComplex p n hn m).skeleton (n-1)).Cochain i,
      η * ((finiteCosetComplex p n hn m).skeleton (n-1)).distance (n-1) i f
          (((finiteCosetComplex p n hn m).skeleton (n-1)).cocycles i) ≤
        ((finiteCosetComplex p n hn m).skeleton (n-1)).norm (n-1) (i+1)
          (((finiteCosetComplex p n hn m).skeleton (n-1)).coboundary i f)

end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Skeleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Skeleton-weight identities and conversion of raw cosystolic estimates to the finite weighted norms.
-/

section
open scoped BigOperators
open Filter

namespace CoboundaryExpanders.Complex

section
local instance instFintypeFace_4 (X : Complex) (i : ℕ) : Fintype (X.Face i) := X.instFintypeFace i
variable (X : Complex)

def rawCochain (i : ℕ) (f : X.Cochain i) (s : Finset (Fin X.vertexCount)) : ZMod 2 :=
  if h : s ∈ X.facesOf i then f ⟨s,h⟩ else 0

def ofRaw (i : ℕ) (f : Finset (Fin X.vertexCount) → ZMod 2) : X.Cochain i := fun s => f s.val

@[simp] lemma ofRaw_rawCochain (i : ℕ) (f : X.Cochain i) :
    X.ofRaw i (X.rawCochain i f) = f := by
  ext s
  simp only [ofRaw,rawCochain,dite_eq_left s.property]

@[simp] lemma ofRaw_add (i : ℕ) (f g : Finset (Fin X.vertexCount) → ZMod 2) :
    X.ofRaw i (f+g) = X.ofRaw i f + X.ofRaw i g := rfl

end

end CoboundaryExpanders.Complex

end

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_LatticeCones
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bounded-chamber and codistance attachments, lattice acyclicity, and uniform positive coset exactness.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)

lemma positive_power_equation (f h : K[X]) (a b : ℕ) (hf : f ≠ 0)
    (he : algebraMap K[X] (RatFunc K) h * uniformizer K ^ b =
      positive K f * uniformizer K ^ a) : b ≤ a := by
  by_contra hab
  obtain ⟨c,hc⟩ := Nat.exists_eq_add_of_lt (lt_of_not_ge hab)
  have hf0 : f = 0 := positive_zero_of_uniformizer_dvd K f (h*Polynomial.X^c) (by
    apply mul_right_cancel₀ (pow_ne_zero a (uniformizer_ne_zero K))
    rw [← he,hc]
    simp only [map_mul,map_pow,uniformizer]
    ring)
  exact hf hf0

lemma mem_level_cut (cut : Fin N) (a : ℕ) (v : V K N) :
    v ∈ level (shift K N) (cutLattice K N cut) a ↔
      ∀ i, ∃ f : K[X], algebraMap K[X] (RatFunc K) f *
        uniformizer K ^ (a + cutExponent N cut i) = v i := by
  classical
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := (mem_level K N _ _ _).mp hv
    intro i
    obtain ⟨f,hf⟩ := hw i
    refine ⟨f,?_⟩
    simp only [Pi.smul_apply,Algebra.smul_def,map_pow]
    rw [← hf,pow_add]
    change _ = uniformizer K ^ a * _
    ring
  · intro hv
    choose f hf using hv
    let w : V K N := fun i => algebraMap K[X] (RatFunc K) (f i) * uniformizer K ^ cutExponent N cut i
    refine (mem_level K N _ _ _).mpr ⟨w,(fun i => ⟨f i,rfl⟩),?_⟩
    funext i
    simp only [Pi.smul_apply,Algebra.smul_def,map_pow]
    rw [← hf i,pow_add]
    change uniformizer K ^ a * _ = _
    dsimp only [w]
    ring

lemma positiveAction_cut_le_exponents
    (g : Matrix.SpecialLinearGroup (Fin N) K[X]) (c d : Fin N) (a b : ℕ)
    (hle : level (shift K N) (positiveAction K N g (cutLattice K N c)) a ≤
      level (shift K N) (cutLattice K N d) b) (i j : Fin N) (hg : g i j ≠ 0) :
    b + cutExponent N d i ≤ a + cutExponent N c j := by
  classical
  let v : V K N := Pi.single j (uniformizer K ^ cutExponent N c j)
  have hv : v ∈ cutLattice K N c := by
    intro k
    by_cases hk : k = j
    · subst k; exact ⟨1,by simp [v]⟩
    · exact ⟨0,by simp [v,hk]⟩
  have hv' : (Polynomial.X^a : K[X]) • positiveLinear K N g v ∈
      level (shift K N) (positiveAction K N g (cutLattice K N c)) a :=
    (mem_level K N _ _ _).mpr ⟨positiveLinear K N g v,
      (mem_positiveAction K N g _ _).mpr ⟨v,hv,rfl⟩,rfl⟩
  obtain ⟨f,hf⟩ := (mem_level_cut K N d b _).mp (hle hv') i
  apply positive_power_equation K (g i j) f _ _ hg
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  simp only [positiveLinear_apply,v,Matrix.mulVec_single,Pi.smul_apply,Algebra.smul_def,
    map_pow,positiveMatrix]
  change positive K (g i j) * uniformizer K ^ (a + cutExponent N c j) =
    uniformizer K ^ a * (positive K (g i j) * uniformizer K ^ cutExponent N c j)
  rw [pow_add]
  ring

lemma positiveAction_mul (g h : Matrix.SpecialLinearGroup (Fin N) K[X]) (A : LatticeSpace K N) :
    positiveAction K N (g*h) A = positiveAction K N g (positiveAction K N h A) := by
  ext v
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := (mem_positiveAction K N _ _ _).mp hv
    exact (mem_positiveAction K N _ _ _).mpr ⟨positiveLinear K N h w,
      (mem_positiveAction K N _ _ _).mpr ⟨w,hw,rfl⟩,(positiveLinear_mul K N g h w).symm⟩
  · intro hv
    obtain ⟨w,hw,rfl⟩ := (mem_positiveAction K N _ _ _).mp hv
    obtain ⟨z,hz,rfl⟩ := (mem_positiveAction K N _ _ _).mp hw
    exact (mem_positiveAction K N _ _ _).mpr ⟨z,hz,positiveLinear_mul K N g h z⟩

@[simp] lemma positiveAction_one (A : LatticeSpace K N) : positiveAction K N 1 A = A := by
  ext v
  simp only [mem_positiveAction,positiveLinear_one,exists_eq_right]

lemma actVertex_one (hN : 0 < N) (A : Vertex K N) : actVertex K N hN 1 A = A := by
  apply (homothetic_normalized_iff (shift K N) (standard K N) (shift_standard_le K N) _ _).mp
  apply homothetic_symm
  simpa only [positiveAction_one] using actVertex_homothetic K N hN 1 A

lemma actVertex_mul (hN : 0 < N) (g h : Matrix.SpecialLinearGroup (Fin N) K[X]) (A : Vertex K N) :
    actVertex K N hN (g*h) A = actVertex K N hN g (actVertex K N hN h A) := by
  apply (homothetic_normalized_iff (shift K N) (standard K N) (shift_standard_le K N) _ _).mp
  refine homothetic_trans _ (homothetic_symm _ (actVertex_homothetic K N hN (g*h) A)) ?_
  rw [positiveAction_mul]
  exact homothetic_trans _
    (homothetic_map _ _ (positiveAction_shift K N g) (actVertex_homothetic K N hN h A))
    (actVertex_homothetic K N hN g (actVertex K N hN h A))

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.Construction
open CoboundaryExpanders.RationalLattices CoboundaryExpanders.AffineLattices
variable (p n : ℕ) [Fact p.Prime]

lemma U_diagonal_ne_zero (g : Matrix.SpecialLinearGroup (Fin (n+1)) (R p))
    (hu : g ∈ U p (n+1)) (i : Fin (n+1)) : g i i ≠ 0 := by
  intro hz
  have he := hu i i le_rfl
  change Polynomial.eval 0 (g i i) = _ at he
  simp [hz] at he

lemma homothetic_cut_recognition (hn : 1 ≤ n) (g : Matrix.SpecialLinearGroup (Fin (n+1)) (R p))
    (hu : g ∈ U p (n+1)) (c d : Fin (n+1)) :
    Homothetic (shift (ZMod p) (n+1))
      (positiveAction (ZMod p) (n+1) g (cutLattice (ZMod p) (n+1) c)) (cutLattice (ZMod p) (n+1) d) ↔
      c = d ∧ g ∈ localGroup p n hn c := by
  constructor
  · rintro ⟨a,b,he⟩
    have hi : ∀ i, b + cutExponent (n+1) d i ≤ a + cutExponent (n+1) c i :=
      fun i => positiveAction_cut_le_exponents (ZMod p) (n+1) g c d a b he.le i i (U_diagonal_ne_zero p n g hu i)
    have he' : level (shift (ZMod p) (n+1))
        (positiveAction (ZMod p) (n+1) g⁻¹ (cutLattice (ZMod p) (n+1) d)) b =
        level (shift (ZMod p) (n+1)) (cutLattice (ZMod p) (n+1) c) a := by
      have hh := congrArg (positiveAction (ZMod p) (n+1) g⁻¹) he.symm
      rw [map_level _ _ (positiveAction_shift _ _ _),map_level _ _ (positiveAction_shift _ _ _),
        positiveAction_inv,OrderIso.symm_apply_apply] at hh
      simpa only [positiveAction_inv] using hh
    have hj : ∀ i, a + cutExponent (n+1) c i ≤ b + cutExponent (n+1) d i :=
      fun i => positiveAction_cut_le_exponents (ZMod p) (n+1) g⁻¹ d c b a he'.le i i
        (U_diagonal_ne_zero p n g⁻¹ ((U p (n+1)).inv_mem hu) i)
    have hab : a = b := by
      have h₁ := hi (Fin.last n)
      have h₂ := hj (Fin.last n)
      simp only [cutExponent,Fin.val_last,ite_eq_right (show ¬ n < d.val by omega),
        ite_eq_right (show ¬ n < c.val by omega),add_zero] at h₁ h₂
      omega
    subst b
    have hcd : c = d := by
      apply le_antisymm
      · by_contra h
        have hh := hi d
        simp only [cutExponent,lt_self_iff_false,ite_false,
          ite_eq_left (show d.val < c.val from lt_of_not_ge h)] at hh
        have hh' := hj d
        simp only [cutExponent,lt_self_iff_false,ite_false,
          ite_eq_left (show d.val < c.val from lt_of_not_ge h)] at hh'
        omega
      · by_contra h
        have hh := hi c
        simp only [cutExponent,lt_self_iff_false,ite_false,
          ite_eq_left (show c.val < d.val from lt_of_not_ge h)] at hh
        omega
    refine ⟨hcd,?_⟩
    subst d
    have heq := level_injective (shift (ZMod p) (n+1)) a he
    apply (preserves_cutLattice_iff_localGroup p n hn c g hu).mp
    intro v hv
    change positiveLinear (ZMod p) (n+1) g v ∈ _
    rw [← heq]
    exact (mem_positiveAction _ _ _ _ _).mpr ⟨v,hv,rfl⟩
  · rintro ⟨rfl,hg⟩
    have hle : positiveAction (ZMod p) (n+1) g (cutLattice (ZMod p) (n+1) c) ≤ cutLattice (ZMod p) (n+1) c := by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := (mem_positiveAction _ _ _ _ _).mp hv
      exact (preserves_cutLattice_iff_localGroup p n hn c g hu).mpr hg w hw
    have hge : cutLattice (ZMod p) (n+1) c ≤ positiveAction (ZMod p) (n+1) g (cutLattice (ZMod p) (n+1) c) := by
      have hle' : positiveAction (ZMod p) (n+1) g⁻¹ (cutLattice (ZMod p) (n+1) c) ≤ cutLattice (ZMod p) (n+1) c := by
        intro v hv
        obtain ⟨w,hw,rfl⟩ := (mem_positiveAction _ _ _ _ _).mp hv
        exact (preserves_cutLattice_iff_localGroup p n hn c g⁻¹ ((U p (n+1)).inv_mem hu)).mpr
          ((localGroup p n hn c).inv_mem hg) w hw
      simpa only [positiveAction_inv,OrderIso.apply_symm_apply] using (positiveAction (ZMod p) (n+1) g).monotone hle'
    exact ⟨0,0,le_antisymm hle hge⟩

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.Construction
open CoboundaryExpanders.RationalLattices CoboundaryExpanders.AffineLattices
variable (p n : ℕ) [Fact p.Prime]

lemma act_cut_eq_iff (hn : 1 ≤ n) (g h : U p (n+1)) (c d : Fin (n+1)) :
    actVertex (ZMod p) (n+1) (by omega) g.val (cutVertex (ZMod p) (n+1) c) =
    actVertex (ZMod p) (n+1) (by omega) h.val (cutVertex (ZMod p) (n+1) d) ↔
    c = d ∧ g⁻¹*h ∈ uLocalGroup p n hn c := by
  constructor
  · intro he
    have he' : cutVertex (ZMod p) (n+1) c =
        actVertex (ZMod p) (n+1) (by omega) (g.val⁻¹*h.val) (cutVertex (ZMod p) (n+1) d) := by
      have hh := congrArg (actVertex (ZMod p) (n+1) (by omega) g.val⁻¹) he
      simpa only [← actVertex_mul,inv_mul_cancel,actVertex_one] using hh
    have hh := actVertex_homothetic (ZMod p) (n+1) (by omega) (g.val⁻¹*h.val)
      (cutVertex (ZMod p) (n+1) d)
    rw [← he'] at hh
    obtain ⟨hdc,hh⟩ := (homothetic_cut_recognition p n hn (g.val⁻¹*h.val)
      ((U p (n+1)).mul_mem ((U p (n+1)).inv_mem g.property) h.property) d c).mp hh
    subst d
    exact ⟨rfl,hh⟩
  · rintro ⟨rfl,hgh⟩
    have hh := (homothetic_cut_recognition p n hn (g.val⁻¹*h.val)
      ((U p (n+1)).mul_mem ((U p (n+1)).inv_mem g.property) h.property) c c).mpr ⟨rfl,hgh⟩
    have hh' : actVertex (ZMod p) (n+1) (by omega) (g.val⁻¹*h.val)
        (cutVertex (ZMod p) (n+1) c) = cutVertex (ZMod p) (n+1) c := by
      apply (homothetic_normalized_iff _ _ (shift_standard_le (ZMod p) (n+1)) _ _).mp
      exact homothetic_trans _ (homothetic_symm _ (actVertex_homothetic _ _ _ _ _)) hh
    have hhh := congrArg (actVertex (ZMod p) (n+1) (by omega) g.val) hh'
    simpa only [← actVertex_mul,mul_inv_cancel_left] using hhh.symm

end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_OddHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Permutation orbit parameters, locally finite odd groups, quotient coinvariants, and bar augmentations.
-/

namespace CoboundaryExpanders.FinsuppPermutation
open CategoryTheory

variable {k G X Y : Type} [CommRing k] [Group G] [MulAction G X]

structure OrbitParam (G X Y : Type) [Group G] [MulAction G X] where
  f : X → Y
  invariant : ∀ (g : G) (x : X), f (g • x) = f x
  surjective : Function.Surjective f
  fiber : ∀ x y, f x = f y → ∃ g : G, g • x = y

namespace OrbitParam
variable (P : OrbitParam G X Y)
def toCoin : (ρ k G X).Coinvariants →ₗ[k] (Y →₀ k) :=
  Representation.Coinvariants.lift _ (Finsupp.lmapDomain k k P.f) (by
    intro g
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext
    intro r
    simp [ρ_single, P.invariant])
@[simp] lemma toCoin_mk (c : X →₀ k) :
    P.toCoin (Representation.Coinvariants.mk (ρ k G X) c) = Finsupp.lmapDomain k k P.f c := rfl

def chosen (y : Y) : X := (P.surjective y).choose
@[simp] lemma chosen_spec (y : Y) : P.f (P.chosen y) = y := (P.surjective y).choose_spec

def fromCoin : (Y →₀ k) →ₗ[k] (ρ k G X).Coinvariants :=
  Finsupp.linearCombination k (fun y =>
    Representation.Coinvariants.mk (ρ k G X) (Finsupp.single (P.chosen y) 1))
@[simp] lemma fromCoin_single (y : Y) (r : k) :
    P.fromCoin (Finsupp.single y r) =
      Representation.Coinvariants.mk (ρ k G X) (Finsupp.single (P.chosen y) r) := by
  simp [fromCoin, ← map_smul]

lemma mk_eq (x y : X) (h : P.f x = P.f y) (r : k) :
    Representation.Coinvariants.mk (ρ k G X) (Finsupp.single x r) =
      Representation.Coinvariants.mk (ρ k G X) (Finsupp.single y r) := by
  obtain ⟨g,hg⟩ := P.fiber x y h
  rw [← hg, ← ρ_single]
  exact (Representation.Coinvariants.mk_self_apply _ _ _).symm

lemma from_to : (P.fromCoin (k := k)).comp P.toCoin = LinearMap.id := by
  apply Representation.Coinvariants.hom_ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, toCoin_mk,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, fromCoin_single, LinearMap.id_apply]
  exact P.mk_eq _ _ (P.chosen_spec _) r
lemma to_from : (P.toCoin (k := k)).comp P.fromCoin = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro y
  apply LinearMap.ext
  intro r
  simp

def coinEquiv : (ρ k G X).Coinvariants ≃ₗ[k] (Y →₀ k) :=
  LinearEquiv.ofLinearMap P.toCoin P.fromCoin P.to_from P.from_to
@[simp] lemma coinEquiv_mk (c : X →₀ k) :
    P.coinEquiv (Representation.Coinvariants.mk (ρ k G X) c) =
      Finsupp.lmapDomain k k P.f c := rfl

end OrbitParam
end CoboundaryExpanders.FinsuppPermutation


section
open scoped BigOperators

namespace CoboundaryExpanders.InfiniteChains.Complex
variable {V W : Type} [DecidableEq V] [DecidableEq W]

structure Reduction (X : CoboundaryExpanders.InfiniteChains.Complex V) (Y : CoboundaryExpanders.InfiniteChains.Complex W) where
  f : V → W
  injOn : ∀ s ∈ X.faces, Set.InjOn f (s : Set V)
  faces : ∀ s ∈ X.faces, s.image f ∈ Y.faces

namespace Reduction
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (r : Reduction X Y)

def face (n : ℕ) (s : X.Face n) : Y.Face n :=
  ⟨s.val.image r.f, r.faces s.val s.property.1,
    (Finset.card_image_of_injOn (r.injOn s.val s.property.1)).trans s.property.2⟩

def chains (n : ℕ) : X.Chains n →ₗ[k] Y.Chains n :=
  Finsupp.lmapDomain k k (r.face n)

omit [DecidableEq V] in
@[simp] lemma chains_single (n : ℕ) (s : X.Face n) (a : k) :
    r.chains n (Finsupp.single s a) = Finsupp.single (r.face n s) a :=
  Finsupp.mapDomain_single

end Reduction
end CoboundaryExpanders.InfiniteChains.Complex

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits

end

section
open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp
open CategoryTheory CategoryTheory.Limits Representation Finsupp Rep TensorProduct

namespace CoboundaryExpanders.QuotientBarAugmentation
variable {k G : Type} [CommRing k] [Group G] [DecidableEq G]
omit [DecidableEq G] in
lemma diagonal_inv_single (n : ℕ) (x : Fin n → G) (g : G) (r : k) :
    (diagonalSuccIsoFree k G n).inv.hom (single x (.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd x) r := by
  simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  have step1 : (Hom.hom (leftRegularTensorTrivialIsoFree k G (Fin n → G)).inv)
      (single x (.single g r)) = .single g 1 ⊗ₜ[k] .single x r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single x g r
  rw [step1]
  simp only [Action.tensorObj_V, tensor_V, tensor_ρ]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G n).inv (g, x) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin n → G)) g x 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G n).inv) z) key₂).trans key₁).trans (by
      rw [one_mul]
      exact congrArg (fun f : Fin (n + 1) → G => MonoidAlgebra.single f r)
        (Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g x))

omit [DecidableEq G] in
@[simp] theorem bar_augmentation_single (x : Fin 0 → G) (g : G) (r : k) :
    ((Rep.barResolution k G).π.f 0).hom (single x (.single g r)) = r := by
  change (Rep.standardComplex.ε k G).hom
    ((Rep.diagonalSuccIsoFree k G 0).inv.hom (single x (.single g r))) = r
  rw [diagonal_inv_single]
  simp [Rep.standardComplex.ε]

end CoboundaryExpanders.QuotientBarAugmentation

end

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp
open CategoryTheory CategoryTheory.Limits Representation Finsupp Rep TensorProduct
open CategoryTheory Finsupp MonoidalCategory
open CategoryTheory

namespace CoboundaryExpanders.QuotientCoinvariants

section
variable {G K : Type} [Group G] [Group K]

def trivialMap (f : G →* K) : Rep.trivial (ZMod 2) G (ZMod 2) ⟶
    Rep.res f (Rep.trivial (ZMod 2) K (ZMod 2)) := 𝟙 _

end

end CoboundaryExpanders.QuotientCoinvariants

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Parabolic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Actual parabolic stabilizers, F2 homological stability maps, and matrix duality.
-/

namespace CoboundaryExpanders.ActualParabolic
open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp
open CategoryTheory CategoryTheory.Limits Representation Finsupp Rep TensorProduct
open CategoryTheory Finsupp MonoidalCategory
open CategoryTheory
open scoped BigOperators Matrix


section
open Construction
variable (p a m : ℕ)
abbrev Idx (a : ℕ) := Fin a ⊕ Unit

def rowFixed : Subgroup (Matrix.SpecialLinearGroup (Idx a) (R p)) where
  carrier := {A | ∀ j, A (Sum.inr ()) j = (1 : Matrix (Idx a) (Idx a) (R p)) (Sum.inr ()) j}
  one_mem' := by intro j; rfl
  mul_mem' := by
    intro A B hA hB j
    change ∀ j, A.val (Sum.inr ()) j = (1 : Matrix (Idx a) (Idx a) (R p)) (Sum.inr ()) j at hA
    change ((A.val : Matrix (Idx a) (Idx a) (R p)) * (B.val : Matrix (Idx a) (Idx a) (R p))) _ j = _
    simpa [Matrix.mul_apply,hA,Matrix.one_apply] using hB j
  inv_mem' := by
    intro A hA j
    change ∀ j, A.val (Sum.inr ()) j = (1 : Matrix (Idx a) (Idx a) (R p)) (Sum.inr ()) j at hA
    have he : ((A.val : Matrix (Idx a) (Idx a) (R p)) * ((A⁻¹).val : Matrix (Idx a) (Idx a) (R p))) (Sum.inr ()) j =
        (1 : Matrix (Idx a) (Idx a) (R p)) (Sum.inr ()) j := by
      rw [← Matrix.SpecialLinearGroup.coe_mul,mul_inv_cancel,Matrix.SpecialLinearGroup.coe_one]
    simpa [Matrix.mul_apply,hA,Matrix.one_apply] using he

def group : Subgroup (Matrix.SpecialLinearGroup (Idx a) (R p)) :=
  rowFixed p a ⊓ (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m))).ker

theorem block_form (A : group p a m) : A.val.val =
    Matrix.fromBlocks (Matrix.toBlocks₁₁ A.val.val)
      (Matrix.toBlocks₁₂ A.val.val) 0 1 := by
  funext i j
  cases i with
  | inl i => cases j <;> rfl
  | inr i =>
    cases i
    have h := A.property.1 j
    cases j <;> simpa [Matrix.one_apply] using h

noncomputable def projectValue (A : group p a m) : Matrix.SpecialLinearGroup (Fin a) (R p) :=
  ⟨Matrix.toBlocks₁₁ A.val.val, by
    have h := A.val.property
    rw [block_form p a m A,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,mul_one] at h
    exact h⟩

noncomputable def projectSL : group p a m →* Matrix.SpecialLinearGroup (Fin a) (R p) where
  toFun := projectValue p a m
  map_one' := by
    apply Subtype.ext
    funext i j
    change (1 : Matrix (Idx a) (Idx a) (R p)) (Sum.inl i) (Sum.inl j) = (1 : Matrix (Fin a) (Fin a) (R p)) i j
    simp [Matrix.one_apply]
  map_mul' A B := by
    apply Subtype.ext
    change Matrix.toBlocks₁₁ (A.val.val * B.val.val) =
      Matrix.toBlocks₁₁ A.val.val * Matrix.toBlocks₁₁ B.val.val
    rw [block_form p a m A,block_form p a m B,Matrix.fromBlocks_multiply]
    simp

noncomputable def project : group p a m →* Gamma p a m :=
  (projectSL p a m).codRestrict _ (by
    intro A
    have h := A.property.2
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have he := congrArg (fun B : Matrix.SpecialLinearGroup (Idx a) (R p ⧸ powerIdeal p m) =>
      B (Sum.inl i) (Sum.inl j)) h
    change Ideal.Quotient.mk (powerIdeal p m) (A.val.val (Sum.inl i) (Sum.inl j)) = (1 : Matrix (Fin a) (Fin a) (R p ⧸ powerIdeal p m)) i j
    simpa [Matrix.one_apply] using he)

noncomputable def sectionValue (A : Gamma p a m) : group p a m :=
  ⟨⟨Matrix.fromBlocks A.val.val 0 0 1, by
      rw [Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,mul_one]; exact A.val.property⟩,
    by
      constructor
      · intro j
        cases j <;> simp
      · apply Matrix.SpecialLinearGroup.ext
        intro i j
        have he := A.property
        change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) A.val = 1 at he
        have hh (i j : Fin a) := congrArg (fun B : Matrix.SpecialLinearGroup (Fin a)
          (R p ⧸ powerIdeal p m) => B i j) he
        change Ideal.Quotient.mk (powerIdeal p m) (Matrix.fromBlocks A.val.val (0 : Matrix (Fin a) Unit (R p)) 0 1 i j) = (1 : Matrix (Idx a) (Idx a) (R p ⧸ powerIdeal p m)) i j
        cases i with
        | inl i => cases j with
          | inl j => simpa [Matrix.one_apply,Matrix.SpecialLinearGroup.map_apply_coe] using hh i j
          | inr j => simp
        | inr i => cases j <;> simp⟩

theorem kernel_form (A : (project p a m).ker) : A.val.val.val =
    Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) (R p))
      (Matrix.toBlocks₁₂ A.val.val.val) 0 1 := by
  have h := A.property
  have he := congrArg (fun x : Gamma p a m => x.val.val) h
  change Matrix.toBlocks₁₁ A.val.val.val = 1 at he
  rw [block_form p a m A.val,he]
  rfl

noncomputable def kernelColumn : (project p a m).ker →* Multiplicative (Fin a → R p) where
  toFun A := Multiplicative.ofAdd (fun i => A.val.val.val (Sum.inl i) (Sum.inr ()))
  map_one' := by
    change (fun i : Fin a => (1 : Matrix (Idx a) (Idx a) (R p)) (Sum.inl i) (Sum.inr ())) = 0
    funext i
    simp
  map_mul' A B := by
    change (fun i => (A.val.val.val * B.val.val.val) (Sum.inl i) (Sum.inr ())) =
      (fun i => A.val.val.val (Sum.inl i) (Sum.inr ()) + B.val.val.val (Sum.inl i) (Sum.inr ()))
    rw [kernel_form p a m A,kernel_form p a m B,Matrix.fromBlocks_multiply]
    funext i
    simp [add_comm]

end

section
open Construction CategoryTheory
variable (p a m : ℕ)

noncomputable def sectionHom : Gamma p a m →* group p a m where
  toFun := sectionValue p a m
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact Matrix.fromBlocks_one
  map_mul' A B := by
    apply Subtype.ext
    apply Subtype.ext
    change Matrix.fromBlocks (A.val.val * B.val.val) 0 0 (1 : Matrix Unit Unit (R p)) =
      Matrix.fromBlocks A.val.val 0 0 1 * Matrix.fromBlocks B.val.val 0 0 1
    simp [Matrix.fromBlocks_multiply]

end

section
open Construction
variable (p a m : ℕ)

def idxEquiv : Idx a ≃ Fin (a+1) :=
  (Equiv.sumCongr (Equiv.refl (Fin a)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv

def inclusion : group p a m →* Gamma p (a+1) m where
  toFun A := ⟨Blocks.reindexSL (idxEquiv a) A.val,by
    change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m))
      (Blocks.reindexSL (idxEquiv a) A.val) = 1
    rw [Blocks.reindexSL_map,A.property.2,map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' A B := Subtype.ext (map_mul _ _ _)

end

open Construction CategoryTheory

end CoboundaryExpanders.ActualParabolic


section
open CategoryTheory
open scoped Matrix

namespace CoboundaryExpanders.F2Stability

variable {G H K : Type} [Group G] [Group H] [Group K]

abbrev hom (f : G →* H) (j : ℕ) :=
  groupHomology.map f (QuotientCoinvariants.trivialMap f) j

def meetConj (S N : Subgroup G) [N.Normal] (g : G) (hg : g ∈ S) :
    ↥(S ⊓ N) →* ↥(S ⊓ N) :=
  ((MulAut.conj g).toMonoidHom.comp (S ⊓ N).subtype).codRestrict _ (by
    intro x
    exact ⟨S.mul_mem (S.mul_mem hg x.property.1) (S.inv_mem hg),
      Subgroup.Normal.conj_mem (inferInstance : N.Normal) x.val x.property.2 g⟩)

end CoboundaryExpanders.F2Stability

namespace CoboundaryExpanders.ActualParabolic
open Construction F2Stability
variable (p a m : ℕ)

def shear (v : Matrix (Fin a) Unit (R p)) :
    Matrix.SpecialLinearGroup (Idx a) (R p) :=
  ⟨Matrix.fromBlocks 1 v 0 1, by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, one_mul]⟩

lemma shear_mem (v : Matrix (Fin a) Unit (R p)) : shear p a v ∈ rowFixed p a := by
  intro j
  cases j <;> simp [shear]

def shearConj (v : Matrix (Fin a) Unit (R p)) : group p a m →* group p a m :=
  meetConj (rowFixed p a)
    (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m))).ker
    (shear p a v) (shear_mem p a v)

local instance gammaNormal : (Gamma p a m).Normal := by
  unfold Gamma
  infer_instance

def shearFin (v : Matrix (Fin a) Unit (R p)) :
    Matrix.SpecialLinearGroup (Fin (a+1)) (R p) :=
  Blocks.reindexSL (idxEquiv a) (shear p a v)

end CoboundaryExpanders.ActualParabolic

namespace CoboundaryExpanders.ActualParabolic
open Construction F2Stability
variable (p a m : ℕ)
local instance gammaNormalLast : (Gamma p a m).Normal := by unfold Gamma; infer_instance

end CoboundaryExpanders.ActualParabolic

end

open CategoryTheory

namespace CoboundaryExpanders.Actions
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (S : Subgroup G) [S.Normal] {X : ModuleCat.{u} k}

def fixingImage (j : ℕ) (f : X ⟶ groupHomology (Rep.trivial k S k) j) : Subgroup G where
  carrier := {g | f ≫ conjugation S g j = f}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change f ≫ conjugation S (g*h) j = f
    rw [conjugation_mul, ← Category.assoc, hh, hg]
  inv_mem' := by
    intro g hg
    change f ≫ conjugation S g⁻¹ j = f
    have he := conjugation_mul (k := k) S g⁻¹ g j
    rw [inv_mul_cancel, conjugation_one] at he
    calc
      f ≫ conjugation S g⁻¹ j = (f ≫ conjugation S g j) ≫ conjugation S g⁻¹ j := by rw [hg]
      _ = f := by rw [Category.assoc, ← he, Category.comp_id]

end CoboundaryExpanders.Actions

namespace CoboundaryExpanders.ActualParabolic
open Construction Elementary F2Stability Actions
variable (p a m : ℕ)
local instance gammaNorm : (Gamma p a m).Normal := by unfold Gamma; infer_instance

@[simp] lemma idxEquiv_inl (i : Fin a) : idxEquiv a (Sum.inl i) = i.castSucc := rfl
@[simp] lemma idxEquiv_inr : idxEquiv a (Sum.inr ()) = Fin.last a := rfl

abbrev stableFixed (j : ℕ) :=
  fixingImage (Gamma p (a+1) m) j (hom (Blocks.gammaStabilization p a 1 m) j)

end CoboundaryExpanders.ActualParabolic

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_CongruenceFrames
attribute [-instance] _root_.OAI.CoboundaryExpanders.TypedCosetFaces.kernelInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Row-parabolic groups, row-frame actions, finite images, and congruence stabilizers.
-/

section
open scoped BigOperators Matrix
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.RowParabolic
variable (A : Type*) [CommRing A] (a b : ℕ)
abbrev Idx := Fin a ⊕ Fin b

def fixed : Subgroup (Matrix.SpecialLinearGroup (Idx a b) A) where
  carrier := {g | ∀ i : Fin b, ∀ j, g (Sum.inr i) j = (1 : Matrix (Idx a b) (Idx a b) A) (Sum.inr i) j}
  one_mem' := by intro i j; rfl
  mul_mem' := by
    intro g h hg hh i j
    change ∀ i j, g.val (Sum.inr i) j = (1 : Matrix (Idx a b) (Idx a b) A) (Sum.inr i) j at hg
    change ∀ i j, h.val (Sum.inr i) j = (1 : Matrix (Idx a b) (Idx a b) A) (Sum.inr i) j at hh
    change (g.val * h.val) (Sum.inr i) j = _
    simpa [Matrix.mul_apply, hg, Matrix.one_apply] using hh i j
  inv_mem' := by
    intro g hg i j
    change ∀ i j, g.val (Sum.inr i) j = (1 : Matrix (Idx a b) (Idx a b) A) (Sum.inr i) j at hg
    have he : (g.val * (g⁻¹).val) (Sum.inr i) j = (1 : Matrix (Idx a b) (Idx a b) A) (Sum.inr i) j := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    simpa [Matrix.mul_apply, hg, Matrix.one_apply] using he

lemma block_form (g : fixed A a b) : g.val.val =
    Matrix.fromBlocks (Matrix.toBlocks₁₁ g.val.val) (Matrix.toBlocks₁₂ g.val.val) 0 1 := by
  funext i j
  cases i with
  | inl i => cases j <;> rfl
  | inr i =>
    have h := g.property i j
    cases j <;> simpa [Matrix.one_apply] using h

def project : fixed A a b →* Matrix.SpecialLinearGroup (Fin a) A where
  toFun g := ⟨Matrix.toBlocks₁₁ g.val.val, by
    have h := g.val.property
    rw [block_form A a b g, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one] at h
    exact h⟩
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (1 : Matrix (Idx a b) (Idx a b) A) _ _ = (1 : Matrix (Fin a) (Fin a) A) _ _
    simp [Matrix.one_apply]
  map_mul' g h := by
    apply Subtype.ext
    change Matrix.toBlocks₁₁ (g.val.val * h.val.val) = Matrix.toBlocks₁₁ g.val.val * Matrix.toBlocks₁₁ h.val.val
    rw [block_form A a b g, block_form A a b h, Matrix.fromBlocks_multiply]
    simp

def ofBlocks (g : Matrix.SpecialLinearGroup (Fin a) A) (v : Matrix (Fin a) (Fin b) A) : fixed A a b :=
  ⟨⟨Matrix.fromBlocks g.val v 0 1, by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]; exact g.property⟩,
    by intro i j; cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]⟩

@[simp] lemma project_ofBlocks (g : Matrix.SpecialLinearGroup (Fin a) A) (v : Matrix (Fin a) (Fin b) A) :
    project A a b (ofBlocks A a b g v) = g := rfl

variable {A} {B : Type*} [CommRing B]
def map (f : A →+* B) : fixed A a b →* fixed B a b where
  toFun g := ⟨Matrix.SpecialLinearGroup.map f g.val, by
    intro i j
    change f (g.val.val (Sum.inr i) j) = _
    rw [g.property i j]
    simp [Matrix.one_apply]⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' g h := by apply Subtype.ext; exact map_mul _ _ _

lemma map_surjective (f : A →+* B) (hf : Function.Surjective f)
    (hSL : Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin a) f)) :
    Function.Surjective (map a b f) := by
  intro g
  obtain ⟨h,hh⟩ := hSL (project B a b g)
  choose v hv using fun i j => hf (g.val.val (Sum.inl i) (Sum.inr j))
  refine ⟨ofBlocks A a b h v, ?_⟩
  apply Subtype.ext; apply Matrix.SpecialLinearGroup.ext
  intro i j
  change f (Matrix.fromBlocks h.val v 0 (1 : Matrix (Fin b) (Fin b) A) i j) = g.val.val i j
  cases i with
  | inl i => cases j with
    | inl j => exact congrArg (fun z : Matrix.SpecialLinearGroup (Fin a) B => z i j) hh
    | inr j => exact hv i j
  | inr i =>
    rw [g.property i j]
    cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]

end CoboundaryExpanders.RowParabolic

namespace CoboundaryExpanders.Unimodular
variable {R : Type*} [CommRing R] {a b : ℕ}

lemma normalize_rows (ha : 0 < a) (M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R)
    (hM : IsUnit M.det) :
    ∃ g : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) R,
      ∀ i : Fin b, ∀ j, g (Sum.inr i) j = M (Sum.inr i) j := by
  obtain ⟨u,hu⟩ := hM
  let z : Fin a ⊕ Fin b := Sum.inl ⟨0,ha⟩
  let D : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R :=
    Matrix.diagonal (fun i => if i = z then (↑u⁻¹ : R) else 1)
  have hD : D.det = ↑u⁻¹ := by simp [D, Matrix.det_diagonal]
  refine ⟨⟨D * M, ?_⟩, ?_⟩
  · rw [Matrix.det_mul, hD, ← hu]
    exact Units.inv_mul u
  · intro i j
    simp [D, Matrix.diagonal_mul, z]

theorem row_completion [IsDomain R] [IsPrincipalIdealRing R]
    (ha : 0 < a) (f : Fin b → (Fin a ⊕ Fin b → R)) (hf : IsFrame R f) :
    ∃ g : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) R,
      ∀ i j, g (Sum.inr i) j = f i j := by
  obtain ⟨r,hr⟩ := hf
  have hk : Module.finrank R r.ker = a := by
    have h := frame_rank_split f r hr
    simp only [Fintype.card_fin, Module.finrank_pi, Fintype.card_sum] at h
    omega
  let eK : r.ker ≃ₗ[R] (Fin a → R) :=
    ((Module.finBasis R r.ker).reindex (finCongr hk)).equivFun
  let e : (Fin a ⊕ Fin b → R) ≃ₗ[R] (Fin a ⊕ Fin b → R) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) R R).trans
      ((LinearEquiv.prodComm R (Fin a → R) (Fin b → R)).trans
        ((LinearEquiv.prodCongr (LinearEquiv.refl R (Fin b → R)) eK.symm).trans
          (splitEquiv f r hr).symm))
  have hei (i : Fin b) : e (Pi.single (Sum.inr i) 1) = f i := by
    change combine f (fun j => (Pi.single (Sum.inr i) 1 : Fin a ⊕ Fin b → R) (Sum.inr j)) +
      (eK.symm (fun j => (Pi.single (Sum.inr i) 1 : Fin a ⊕ Fin b → R) (Sum.inl j)) : r.ker) = f i
    have h1 : (fun j => (Pi.single (Sum.inr i) 1 : Fin a ⊕ Fin b → R) (Sum.inr j)) = Pi.single i 1 := by
      ext j; simp [Pi.single_apply]
    have h0 : (fun j => (Pi.single (Sum.inr i) 1 : Fin a ⊕ Fin b → R) (Sum.inl j)) = 0 := by
      ext j; simp
    rw [h1,h0,map_zero]
    change combine f (Pi.single i 1) + 0 = f i
    rw [add_zero]
    simp [combine_apply, Pi.single_apply]
  let M := (LinearMap.toMatrix' e.toLinearMap).transpose
  have hu : IsUnit M.det := by
    rw [Matrix.det_transpose]
    apply (isUnit_iff_exists_inv).mpr
    refine ⟨(LinearMap.toMatrix' e.symm.toLinearMap).det, ?_⟩
    rw [← Matrix.det_mul, ← LinearMap.toMatrix'_comp]
    simp
  obtain ⟨g,hg⟩ := normalize_rows ha M hu
  refine ⟨g,fun i j => (hg i j).trans ?_⟩
  change (e (Pi.single (Sum.inr i) 1)) j = f i j
  rw [hei]

end CoboundaryExpanders.Unimodular

end

section
open scoped Matrix BigOperators
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.Unimodular
variable {R A ι S M N : Type*} [CommRing R] [CommRing A]
    [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

lemma frame_linearEquiv (f : S → M) (e : M ≃ₗ[R] N) :
    IsFrame R (fun i => e (f i)) ↔ IsFrame R f := by
  constructor
  · rintro ⟨r,hr⟩
    exact ⟨r.comp e.toLinearMap, hr⟩
  · rintro ⟨r,hr⟩
    exact ⟨r.comp e.symm.toLinearMap, fun i => by simpa using hr i⟩

lemma frame_map (φ : R →+* A) (f : S → (ι → R)) (hf : IsFrame R f) :
    IsFrame A (fun i j => φ (f i j)) := by
  obtain ⟨r,hr⟩ := hf
  refine ⟨Matrix.toLin' ((LinearMap.toMatrix' r).map φ), ?_⟩
  intro i
  ext j
  have hh := congrArg φ (congrFun (hr i) j)
  rw [← LinearMap.toMatrix'_mulVec r (f i)] at hh
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.single_apply] at hh
  change ∑ x, φ (LinearMap.toMatrix' r j x) * φ (f i x) = _
  simpa only [apply_ite φ, map_one, map_zero, Pi.single_apply] using hh

lemma frame_injective [Nontrivial R] (f : S → M) (hf : IsFrame R f) :
    Function.Injective f := by
  obtain ⟨r,hr⟩ := hf
  intro i j hij
  by_contra h
  have hh := congrFun ((hr i).symm.trans ((congrArg r hij).trans (hr j))) i
  simp [h] at hh

end CoboundaryExpanders.Unimodular

namespace CoboundaryExpanders.RowFrames
variable {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]

scoped instance (priority := high) rowSMul : SMul (Matrix.SpecialLinearGroup ι A) (ι → A) :=
  ⟨fun g v => Matrix.vecMul v (g⁻¹).val⟩

scoped instance (priority := high) action : MulAction (Matrix.SpecialLinearGroup ι A) (ι → A) where
  smul g v := Matrix.vecMul v (g⁻¹).val
  one_smul v := by
    change Matrix.vecMul v ((1 : Matrix.SpecialLinearGroup ι A)⁻¹).val = v
    rw [inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  mul_smul g h v := by
    change Matrix.vecMul v ((g*h)⁻¹).val = Matrix.vecMul (Matrix.vecMul v (h⁻¹).val) (g⁻¹).val
    rw [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.vecMul_vecMul]

open scoped RowFrames
@[simp] lemma smul_eq (g : Matrix.SpecialLinearGroup ι A) (v : ι → A) :
    g • v = Matrix.vecMul v (g⁻¹).val := rfl

def linearAction (g : Matrix.SpecialLinearGroup ι A) : (ι → A) ≃ₗ[A] (ι → A) where
  toFun v := g • v
  invFun v := g⁻¹ • v
  left_inv v := inv_smul_smul g v
  right_inv v := smul_inv_smul g v
  map_add' first second := Matrix.add_vecMul _ first second
  map_smul' a v := Matrix.smul_vecMul a v _

lemma frame_smul {S : Type*} (f : S → (ι → A))
    (g : Matrix.SpecialLinearGroup ι A) :
    Unimodular.IsFrame A (fun i => g • f i) ↔ Unimodular.IsFrame A f :=
  Unimodular.frame_linearEquiv f (linearAction g)

lemma standard_fixed_iff {a b : ℕ} (g : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) A) :
    (∀ i : Fin b, g • (Pi.single (Sum.inr i) 1 : Fin a ⊕ Fin b → A) = Pi.single (Sum.inr i) 1) ↔
      g ∈ RowParabolic.fixed A a b := by
  have he (h : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) A) :
      (∀ i : Fin b, h • (Pi.single (Sum.inr i) 1 : Fin a ⊕ Fin b → A) = Pi.single (Sum.inr i) 1) ↔
        h⁻¹ ∈ RowParabolic.fixed A a b := by
    constructor
    · intro hh i j
      have hx := congrFun (hh i) j
      simpa [smul_eq, Matrix.single_vecMul, Pi.single_apply, Matrix.one_apply,eq_comm] using hx
    · intro hh i
      ext j
      have hx := hh i j
      simpa [smul_eq, Matrix.single_vecMul, Pi.single_apply, Matrix.one_apply,eq_comm] using hx
  rw [he, Subgroup.inv_mem_iff]

end CoboundaryExpanders.RowFrames

end

namespace CoboundaryExpanders.Construction
variable (p m : ℕ) [Fact p.Prime]

lemma residue_isUnit (hm : 1 ≤ m) (a : Trunc p m)
    (ha : residue p m hm a ≠ 0) : IsUnit a := by
  let c : Trunc p m := Ideal.Quotient.mk (powerIdeal p m) (Polynomial.C (residue p m hm a)⁻¹)
  have hc : residue p m hm c = (residue p m hm a)⁻¹ := by simp [c]
  have hu := residue_one_isUnit p m hm (a*c) (by rw [map_mul,hc,mul_inv_cancel₀ ha])
  exact isUnit_of_mul_isUnit_left hu

theorem trunc_SL_surjective (hm : 1 ≤ m) (a : ℕ) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin a)
      (Ideal.Quotient.mk (powerIdeal p m))) :=
  Elementary.SL_map_surjective _ (Ideal.Quotient.mk_surjective)
    (residue p m hm) (residue_isUnit p m hm)

end CoboundaryExpanders.Construction

section
open scoped BigOperators Matrix
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.Unimodular
variable {A F : Type*} [CommRing A] [Field F] {a b : ℕ}

theorem row_completion_of_residue_frame (π : A →+* F) (hp : Function.Surjective π)
    (hu : ∀ x, π x ≠ 0 → IsUnit x) (ha : 0 < a)
    (f : Fin b → (Fin a ⊕ Fin b → A))
    (hf : IsFrame F (fun i j => π (f i j))) :
    ∃ g : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) A,
      ∀ i j, g (Sum.inr i) j = f i j := by
  obtain ⟨g,hg⟩ := row_completion ha _ hf
  choose v hv using fun i : Fin a => fun j => hp (g (Sum.inl i) j)
  let M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) A := Sum.elim v f
  have hM : M.map π = g.val := by
    ext i j
    cases i with
    | inl i => exact hv i j
    | inr i => exact (hg i j).symm
  have hdet : π M.det = 1 := by
    rw [RingHom.map_det]
    change (M.map π).det = 1
    rw [hM]; exact g.property
  obtain ⟨G,hG⟩ := normalize_rows ha M (hu M.det (by rw [hdet]; exact one_ne_zero))
  exact ⟨G,hG⟩

end CoboundaryExpanders.Unimodular

namespace CoboundaryExpanders.Construction
variable (p m : ℕ) [Fact p.Prime]
lemma residue_surjective (hm : 1 ≤ m) : Function.Surjective (residue p m hm) := by
  intro a
  refine ⟨Ideal.Quotient.mk (powerIdeal p m) (Polynomial.C a), ?_⟩
  simp

theorem trunc_SL_surjective_any (hm : 1 ≤ m) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n := ι)
      (Ideal.Quotient.mk (powerIdeal p m))) :=
  Elementary.SL_map_surjective_reindex _ (trunc_SL_surjective p m hm _)

end CoboundaryExpanders.Construction

end

section
open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.RowFrames
variable {A B : Type*} [CommRing A] [CommRing B] {a b : ℕ}
abbrev standard (i : Fin b) : Fin a ⊕ Fin b → A := Pi.single (Sum.inr i) 1
lemma standard_frame : Unimodular.IsFrame A (standard (A := A) (a := a) (b := b)) := by
  refine ⟨LinearMap.pi (fun i : Fin b => LinearMap.proj (Sum.inr i)), ?_⟩
  intro i
  ext j
  simp [standard, Pi.single_apply]
@[simp] lemma inverse_smul_standard (g : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) A)
    (i : Fin b) : g⁻¹ • standard (a := a) i = g (Sum.inr i) := by
  ext j
  simp [smul_eq, standard, Matrix.single_vecMul]
lemma row_frame (g : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) A) :
    Unimodular.IsFrame A (fun i : Fin b => g (Sum.inr i)) := by
  simpa only [inverse_smul_standard] using
    (frame_smul (standard (A := A) (a := a) (b := b)) g⁻¹).mpr standard_frame

theorem same_reduction_orbit [IsDomain A] [IsPrincipalIdealRing A]
    (φ : A →+* B) (hφ : Function.Surjective φ)
    (hSL : Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin a) φ))
    (ha : 0 < a) (f g : Fin b → (Fin a ⊕ Fin b → A))
    (hf : Unimodular.IsFrame A f) (hg : Unimodular.IsFrame A g)
    (he : ∀ i j, φ (f i j) = φ (g i j)) :
    ∃ k : (Matrix.SpecialLinearGroup.map (n := Fin a ⊕ Fin b) φ).ker,
      ∀ i, k.val • f i = g i := by
  obtain ⟨P,hP⟩ := Unimodular.row_completion ha f hf
  obtain ⟨Q,hQ⟩ := Unimodular.row_completion ha g hg
  let bar := Matrix.SpecialLinearGroup.map (n := Fin a ⊕ Fin b) φ
  have hfix : bar P * (bar Q)⁻¹ ∈ RowParabolic.fixed B a b := by
    intro i j
    change ((bar P).val * ((bar Q)⁻¹).val) (Sum.inr i) j = _
    have hrow (x) : (bar P) (Sum.inr i) x = (bar Q) (Sum.inr i) x := by
      change φ (P (Sum.inr i) x) = φ (Q (Sum.inr i) x)
      rw [hP,hQ]; exact he i x
    have hx := congrArg (fun z : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) B => z (Sum.inr i) j)
      (mul_inv_cancel (bar Q))
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_apply, hrow] using hx
  obtain ⟨r,hr⟩ := RowParabolic.map_surjective a b φ hφ hSL
    ⟨bar P * (bar Q)⁻¹,hfix⟩
  have hr' : bar r.val = bar P * (bar Q)⁻¹ := congrArg Subtype.val hr
  let k := Q⁻¹ * r.val⁻¹ * P
  have hk : k ∈ bar.ker := by
    change bar k = 1
    simp only [k,map_mul,map_inv,hr']
    group
  refine ⟨⟨k,hk⟩, fun i => ?_⟩
  have hf' : f i = P⁻¹ • standard (a := a) i := by
    rw [inverse_smul_standard]; exact funext (hP i) |>.symm
  have hg' : g i = Q⁻¹ • standard (a := a) i := by
    rw [inverse_smul_standard]; exact funext (hQ i) |>.symm
  rw [hf',hg']
  have hrf : r.val⁻¹ • standard (a := a) i = standard i :=
    (standard_fixed_iff r.val⁻¹).mpr ((RowParabolic.fixed A a b).inv_mem r.property) i
  change (Q⁻¹ * r.val⁻¹ * P) • (P⁻¹ • standard (a := a) i) = _
  rw [mul_smul,mul_smul,smul_inv_smul,hrf]
end CoboundaryExpanders.RowFrames

end

namespace CoboundaryExpanders.MultiParabolic
open scoped Matrix BigOperators

open Construction RowParabolic CategoryTheory
variable (p a b m : ℕ)
abbrev group : Subgroup (Matrix.SpecialLinearGroup (Idx a b) (R p)) :=
  fixed (R p) a b ⊓ (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m))).ker

end CoboundaryExpanders.MultiParabolic


section
open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.RowFrames
variable {A B ι κ : Type} [CommRing A] [CommRing B] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma reindex_smul (e : ι ≃ κ) (g : Matrix.SpecialLinearGroup ι A) (v : κ → A) :
    (fun i => ((Blocks.reindexSL e g) • v) (e i)) = g • (fun i => v (e i)) := by
  have hi : (Blocks.reindexSL e g)⁻¹ = Blocks.reindexSL e g⁻¹ := (map_inv _ g).symm
  ext j
  simp only [smul_eq,hi,Matrix.vecMul,dotProduct]
  rw [← e.sum_comp (fun x => v x * (Blocks.reindexSL e g⁻¹) x (e j))]
  simp only [Blocks.reindexSL_apply]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma frame_coordinates {S : Type} [Fintype S] (e : ι ≃ κ) (f : S → (κ → A)) :
    Unimodular.IsFrame A (fun s i => f s (e i)) ↔ Unimodular.IsFrame A f :=
  Unimodular.frame_linearEquiv f (LinearEquiv.funCongrLeft A A e)

def kernelReindex (φ : A →+* B) (e : ι ≃ κ) :
    (Matrix.SpecialLinearGroup.map (n := ι) φ).ker ≃*
      (Matrix.SpecialLinearGroup.map (n := κ) φ).ker where
  toFun g := ⟨Blocks.reindexSL e g.val, by
    change Matrix.SpecialLinearGroup.map φ (Blocks.reindexSL e g.val) = 1
    rw [Blocks.reindexSL_map, g.property, map_one]⟩
  invFun g := ⟨Blocks.reindexSL e.symm g.val, by
    change Matrix.SpecialLinearGroup.map φ (Blocks.reindexSL e.symm g.val) = 1
    rw [Blocks.reindexSL_map, g.property, map_one]⟩
  left_inv g := by
    apply Subtype.ext
    exact (Blocks.reindexSL e).left_inv g.val
  right_inv g := by
    apply Subtype.ext
    exact (Blocks.reindexSL e).right_inv g.val
  map_mul' g h := by apply Subtype.ext; exact map_mul _ _ _

lemma same_reduction_orbit_coordinates [IsDomain A] [IsPrincipalIdealRing A]
    {a b : ℕ} (φ : A →+* B) (hφ : Function.Surjective φ)
    (hSL : Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin a) φ))
    (ha : 0 < a) (e : Fin a ⊕ Fin b ≃ ι) (f g : Fin b → (ι → A))
    (hf : Unimodular.IsFrame A f) (hg : Unimodular.IsFrame A g)
    (he : ∀ i j, φ (f i j) = φ (g i j)) :
    ∃ k : (Matrix.SpecialLinearGroup.map (n := ι) φ).ker,
      ∀ i, k.val • f i = g i := by
  obtain ⟨k,hk⟩ := same_reduction_orbit φ hφ hSL ha
    (fun i j => f i (e j)) (fun i j => g i (e j))
    ((frame_coordinates e f).mpr hf) ((frame_coordinates e g).mpr hg)
    (fun i j => he i (e j))
  refine ⟨kernelReindex φ e k, fun i => ?_⟩
  ext j
  obtain ⟨j,rfl⟩ := e.surjective j
  exact (congrFun (reindex_smul e k.val (f i)) j).trans (congrFun (hk i) j)

def splitCoordinates (n b : ℕ) (h : b ≤ n) : Fin (n-b) ⊕ Fin b ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel h))

end CoboundaryExpanders.RowFrames

end

namespace CoboundaryExpanders.FiniteImage

section
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def equiv (f : V → W) (s : Finset V) (h : Set.InjOn f (s : Set V)) : s ≃ s.image f :=
  Equiv.ofBijective (fun v => ⟨f v,Finset.mem_image.mpr ⟨v,v.property,rfl⟩⟩) (by
    constructor
    · intro x y he
      exact Subtype.ext (h x.property y.property (congrArg Subtype.val he))
    · rintro ⟨w,hw⟩
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact ⟨⟨v,hv⟩,rfl⟩)
omit [DecidableEq V] in
@[simp] lemma equiv_val (f : V → W) (s : Finset V) (h : Set.InjOn f (s : Set V)) (v : s) :
    (equiv f s h v).val = f v := rfl
omit [DecidableEq V] in
lemma equiv_symm_val (f : V → W) (s : Finset V) (h : Set.InjOn f (s : Set V)) (w : s.image f) :
    f (equiv f s h |>.symm w) = w.val := by
  exact congrArg Subtype.val ((equiv f s h).apply_symm_apply w)

def matching (f : V → W) (s t : Finset V)
    (hs : Set.InjOn f (s : Set V)) (ht : Set.InjOn f (t : Set V))
    (he : s.image f = t.image f) : s ≃ t :=
  (equiv f s hs).trans ((Finset.equivOfEq he).trans (equiv f t ht).symm)
omit [DecidableEq V] in
lemma matching_val (f : V → W) (s t : Finset V)
    (hs : Set.InjOn f (s : Set V)) (ht : Set.InjOn f (t : Set V))
    (he : s.image f = t.image f) (v : s) :
    f (matching f s t hs ht he v) = f v := by
  simp only [matching, Equiv.trans_apply, equiv_symm_val]
  rfl

omit [DecidableEq V] in
lemma image_eq_of_matching {G : Type} [Group G] [MulAction G V]
    (s t : Finset V) (e : s ≃ t) (g : G) (h : ∀ v : s, g • v.val = (e v).val) :
    s.map (MulAction.toPerm g).toEmbedding = t := by
  ext v
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, MulAction.toPerm_apply]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact h ⟨w,hw⟩ ▸ (e ⟨w,hw⟩).property
  · intro hv
    obtain ⟨w,hw⟩ := e.surjective ⟨v,hv⟩
    exact ⟨w.val,w.property,(h w).trans (congrArg Subtype.val hw)⟩
end

variable {V : Type} [DecidableEq V]
def enumeration {b : ℕ} (s : Finset V) (hs : s.card = b) : Fin b ≃ s :=
  (finCongr hs.symm).trans (Finset.equivFin s).symm

def familyEquiv {b : ℕ} (f : Fin b → V) (hf : Function.Injective f) :
    Fin b ≃ Finset.univ.image f :=
  Equiv.ofBijective (fun i => ⟨f i, Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩) (by
    constructor
    · intro i j h; exact hf (congrArg Subtype.val h)
    · rintro ⟨v,hv⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨i,rfl⟩)
@[simp] lemma familyEquiv_val {b : ℕ} (f : Fin b → V) (hf : Function.Injective f) (i : Fin b) :
    (familyEquiv f hf i).val = f i := rfl
end CoboundaryExpanders.FiniteImage

section
open scoped Matrix BigOperators CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.RowFrames
variable {A B ι : Type} [CommRing A] [CommRing B] [Fintype ι] [DecidableEq ι]
lemma map_smul (φ : A →+* B) (g : Matrix.SpecialLinearGroup ι A) (v : ι → A) :
    (fun j => φ ((g • v) j)) = (Matrix.SpecialLinearGroup.map φ g) • (fun j => φ (v j)) := by
  ext j
  simp only [smul_eq, Matrix.vecMul, dotProduct, map_sum, map_mul, ← map_inv,
    Matrix.SpecialLinearGroup.map_apply_coe]
  rfl

lemma kernel_smul (φ : A →+* B) (g : (Matrix.SpecialLinearGroup.map (n := ι) φ).ker)
    (v : ι → A) : (fun j => φ ((g.val • v) j)) = (fun j => φ (v j)) := by
  rw [map_smul,g.property,one_smul]

scoped instance (priority := high) subgroupRowSMul (H : Subgroup (Matrix.SpecialLinearGroup ι A)) :
    SMul H (ι → A) := ⟨fun g v => g.val • v⟩
scoped instance (priority := high) subgroupAction (H : Subgroup (Matrix.SpecialLinearGroup ι A)) :
    MulAction H (ι → A) where
  smul g v := g.val • v
  one_smul v := one_smul (Matrix.SpecialLinearGroup ι A) v
  mul_smul g h v := mul_smul g.val h.val v

lemma complex_invariant (H : Subgroup (Matrix.SpecialLinearGroup ι A)) :
    (Unimodular.complex A (id : (ι → A) → (ι → A))).Invariant (G := H) := by
  intro g s hs
  change Unimodular.IsFrame A (fun v : s.map (MulAction.toPerm g).toEmbedding => v.val)
  apply (Unimodular.frame_equiv (R := A)
    (f := fun v : s.map (MulAction.toPerm g).toEmbedding => v.val)
    (Finset.equivMap (MulAction.toPerm g).toEmbedding s)).mp
  exact (frame_smul (fun v : s => v.val) g.val).mpr hs
end CoboundaryExpanders.RowFrames

namespace CoboundaryExpanders.CongruenceFrames
open Construction Unimodular InfiniteChains
variable (p n m : ℕ) [Fact p.Prime]
abbrev source : CoboundaryExpanders.InfiniteChains.Complex (Fin n → R p) := complex (R p) id
abbrev reduce (v : Fin n → R p) : Fin n → Trunc p m :=
  fun j => Ideal.Quotient.mk (powerIdeal p m) (v j)
abbrev residueVector (hm : 1 ≤ m) (v : Fin n → Trunc p m) : Fin n → ZMod p :=
  fun j => residue p m hm (v j)
abbrev target (hm : 1 ≤ m) : CoboundaryExpanders.InfiniteChains.Complex (Fin n → Trunc p m) :=
  complex (ZMod p) (residueVector p n m hm)

instance invariant : Fact ((source p n).Invariant (G := Gamma p n m)) :=
  ⟨RowFrames.complex_invariant (Gamma p n m)⟩

lemma reduce_injOn (hm : 1 ≤ m) (s : Finset (Fin n → R p))
    (hs : s ∈ (source p n).faces) :
    Set.InjOn (reduce p n m) (s : Set (Fin n → R p)) := by
  intro v hv w hw he
  have hframe := frame_map (Polynomial.evalRingHom (R := ZMod p) 0) (fun v : s => v.val) hs
  apply congrArg Subtype.val (frame_injective _ hframe (a₁ := ⟨v,hv⟩) (a₂ := ⟨w,hw⟩) ?_)
  ext j
  exact congrArg (residue p m hm) (congrFun he j)

def reduction (hm : 1 ≤ m) : (source p n).Reduction (target p n m hm) where
  f := reduce p n m
  injOn := reduce_injOn p n m hm
  faces s hs := by
    change IsFrame (ZMod p) (fun v : s.image (reduce p n m) => residueVector p n m hm v.val)
    apply (frame_equiv (R := ZMod p)
      (f := fun v : s.image (reduce p n m) => residueVector p n m hm v.val)
      (FiniteImage.equiv (reduce p n m) s (reduce_injOn p n m hm s hs))).mp
    exact frame_map (Polynomial.evalRingHom (R := ZMod p) 0) (fun v : s => v.val) hs

lemma reduce_smul (g : Gamma p n m) (v : Fin n → R p) :
    reduce p n m (g • v) = reduce p n m v :=
  RowFrames.kernel_smul (Ideal.Quotient.mk (powerIdeal p m)) g v

lemma face_invariant (hm : 1 ≤ m) (b : ℕ) (g : Gamma p n m) (s : (source p n).Face b) :
    (reduction p n m hm).face b (g • s) = (reduction p n m hm).face b s := by
  apply Subtype.ext
  change (s.val.map (MulAction.toPerm g).toEmbedding).image (reduce p n m) = s.val.image (reduce p n m)
  rw [Finset.map_eq_image,Finset.image_image]
  congr 1
  funext v
  exact reduce_smul p n m g v

end CoboundaryExpanders.CongruenceFrames

end

open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.CongruenceFrames
open Construction Unimodular InfiniteChains RowFrames
variable (p n m : ℕ) [Fact p.Prime]

lemma ordered_lift (hm : 1 ≤ m) {b : ℕ} (hb : b < n)
    (f : Fin b → (Fin n → Trunc p m))
    (hf : IsFrame (ZMod p) (fun i => residueVector p n m hm (f i))) :
    ∃ g : Fin b → (Fin n → R p), IsFrame (R p) g ∧ ∀ i, reduce p n m (g i) = f i := by
  let e := splitCoordinates n b hb.le
  have hff : IsFrame (ZMod p) (fun i j => residue p m hm (f i (e j))) :=
    (frame_coordinates e _).mpr hf
  obtain ⟨P,hP⟩ := row_completion_of_residue_frame (residue p m hm)
    (residue_surjective p m hm) (residue_isUnit p m hm)
    (show 0 < n-b by omega) (fun i j => f i (e j)) hff
  obtain ⟨G,hG⟩ := trunc_SL_surjective_any p m hm (Fin (n-b) ⊕ Fin b) P
  let g : Fin b → (Fin n → R p) := fun i j => G (Sum.inr i) (e.symm j)
  refine ⟨g,?_,?_⟩
  · apply (frame_coordinates e g).mp
    simpa only [g,Equiv.symm_apply_apply] using row_frame G
  · intro i
    ext j
    have hx := congrArg (fun z : Matrix.SpecialLinearGroup (Fin (n-b) ⊕ Fin b) (Trunc p m) =>
      z (Sum.inr i) (e.symm j)) hG
    exact hx.trans ((hP i (e.symm j)).trans (congrArg (f i) (e.apply_symm_apply j)))

lemma face_surjective (hm : 1 ≤ m) (b : ℕ) (hb : b < n) :
    Function.Surjective ((reduction p n m hm).face b) := by
  intro s
  let e := FiniteImage.enumeration s.val s.property.2
  let f : Fin b → (Fin n → Trunc p m) := fun i => (e i).val
  have hf : IsFrame (ZMod p) (fun i => residueVector p n m hm (f i)) :=
    (frame_equiv (R := ZMod p) (f := fun v : s.val => residueVector p n m hm v.val) e).mpr s.property.1
  obtain ⟨g,hg,hred⟩ := ordered_lift p n m hm hb f hf
  have hgi := frame_injective g hg
  let t := Finset.univ.image g
  have ht : t ∈ (source p n).faces := by
    apply (frame_equiv (R := R p) (f := fun v : t => v.val)
      (FiniteImage.familyEquiv g hgi)).mp
    exact hg
  have htcard : t.card = b := by
    rw [Finset.card_image_of_injective _ hgi, Finset.card_univ,Fintype.card_fin]
  refine ⟨⟨t,ht,htcard⟩,?_⟩
  apply Subtype.ext
  change t.image (reduce p n m) = s.val
  ext v
  simp only [t,Finset.image_image,Finset.mem_image,Finset.mem_univ,true_and,Function.comp_apply,hred]
  constructor
  · rintro ⟨i,rfl⟩
    exact (e i).property
  · intro hv
    obtain ⟨i,hi⟩ := e.surjective ⟨v,hv⟩
    exact ⟨i,congrArg Subtype.val hi⟩

lemma face_fiber (hm : 1 ≤ m) (b : ℕ) (hb : b < n)
    (s t : (source p n).Face b)
    (he : (reduction p n m hm).face b s = (reduction p n m hm).face b t) :
    ∃ g : Gamma p n m, g • s = t := by
  have hs := reduce_injOn p n m hm s.val s.property.1
  have ht := reduce_injOn p n m hm t.val t.property.1
  have himg : s.val.image (reduce p n m) = t.val.image (reduce p n m) := congrArg Subtype.val he
  let e := FiniteImage.matching (reduce p n m) s.val t.val hs ht himg
  let eS := FiniteImage.enumeration s.val s.property.2
  let f : Fin b → (Fin n → R p) := fun i => (eS i).val
  let h : Fin b → (Fin n → R p) := fun i => (e (eS i)).val
  have hf : IsFrame (R p) f := (frame_equiv (R := R p) (f := fun v : s.val => v.val) eS).mpr s.property.1
  have hh : IsFrame (R p) h :=
    (frame_equiv (R := R p) (f := fun v : t.val => v.val) (eS.trans e)).mpr t.property.1
  obtain ⟨g,hg⟩ := same_reduction_orbit_coordinates
    (Ideal.Quotient.mk (powerIdeal p m)) Ideal.Quotient.mk_surjective
    (trunc_SL_surjective p m hm (n-b)) (show 0 < n-b by omega)
    (splitCoordinates n b hb.le) f h hf hh (by
      intro i j
      exact (congrFun (FiniteImage.matching_val (reduce p n m) s.val t.val hs ht himg (eS i)) j).symm)
  refine ⟨g,?_⟩
  apply Subtype.ext
  apply FiniteImage.image_eq_of_matching s.val t.val e g
  intro v
  obtain ⟨i,rfl⟩ := eS.surjective v
  exact hg i

def orbitParam (hm : 1 ≤ m) (b : ℕ) (hb : b < n) :
    FinsuppPermutation.OrbitParam (Gamma p n m) ((source p n).Face b) ((target p n m hm).Face b) where
  f := (reduction p n m hm).face b
  invariant := face_invariant p n m hm b
  surjective := face_surjective p n m hm b hb
  fiber := face_fiber p n m hm b hb
end CoboundaryExpanders.CongruenceFrames

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_FrameHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Shapiro comparison, frame resolution homology, augmentation ranges, and triviality of conjugation.
-/

namespace CoboundaryExpanders.ActualShapiro
open CategoryTheory CategoryTheory.Limits Representation Rep Finsupp MonoidalCategory TensorProduct

variable {k G H : Type} [CommRing k] [Group G] [Group H]
variable [DecidableEq G] [DecidableEq H]

def barF (f : H →* G) (n : ℕ) :
    (Rep.barComplex k H).X n ⟶ Rep.res f ((Rep.barComplex k G).X n) :=
  Rep.freeLift k H _ (fun x : Fin n → H =>
    single (f ∘ x) (.single (1 : G) (1 : k)))

omit [DecidableEq G] [DecidableEq H] in
@[simp] lemma barF_single (f : H →* G) (n : ℕ) (x : Fin n → H) (h : H) (r : k) :
    (barF (k := k) f n).hom (single x (.single h r)) =
      single (f ∘ x) (.single (f h) r) := by
  change (Representation.freeLift
    ((Representation.free k G (Fin n → G)).comp f)
    (fun x : Fin n → H => single (f ∘ x) (.single (1 : G) (1 : k))))
    (single x (.single h r)) = _
  rw [Representation.freeLift_single_single]
  change r • Representation.free k G (Fin n → G) (f h) _ = _
  rw [Representation.free_single_single]
  simp

def barMap (f : H →* G) : Rep.barComplex k H ⟶
    ((Rep.resFunctor f).mapHomologicalComplex _).obj (Rep.barComplex k G) where
  f n := barF f n
  comm' i j hij := by
    cases hij
    apply Rep.free_ext
    intro x
    change ((Rep.barComplex k G).d (j+1) j).hom
      ((barF f (j+1)).hom (single x (.single 1 1))) =
      (barF f j).hom (((Rep.barComplex k H).d (j+1) j).hom (single x (.single 1 1)))
    rw [Rep.barComplex.d_def, Rep.barComplex.d_def, barF_single]
    simp only [map_one]
    rw [Rep.barComplex.d_single, Rep.barComplex.d_single]
    have hq : ∀ (n : ℕ) (x : Fin n → H) (h : H) (r : k),
        (barF f n).hom (single x (.single h r)) = single (f ∘ x) (.single (f h) r) := barF_single f
    simp only [map_add, map_sum, hq, map_one]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    exact (Fin.comp_contractNth (· * ·) (· * ·) (fun a b : H => map_mul f a b) i x).symm

variable (S : Subgroup G)
abbrev restrictedResolution : ProjectiveResolution (Rep.trivial k S k) :=
  (Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution k G)

omit [DecidableEq G] in
lemma bar_augmentation : barMap (k := k) S.subtype ≫ (restrictedResolution (k := k) S).π =
    (Rep.barResolution k S).π := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    apply Rep.free_ext
    intro x
    change ((Rep.barResolution k G).π.f 0).hom
      ((barF S.subtype 0).hom (single x (.single 1 1))) =
      ((Rep.barResolution k S).π.f 0).hom (single x (.single 1 1))
    rw [barF_single, QuotientBarAugmentation.bar_augmentation_single,
      QuotientBarAugmentation.bar_augmentation_single]
  | succ n =>
    apply IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_single_obj_X (V := Rep k S)
      (ComplexShape.down ℕ) 0 (Rep.trivial k S k) (n+1) (by omega)

def barHomotopy : Homotopy (barMap (k := k) S.subtype)
    ((Rep.barResolution k S).homotopyEquiv (restrictedResolution (k := k) S)).hom :=
  ProjectiveResolution.liftHomotopy (P := Rep.barResolution k S)
    (Q := restrictedResolution (k := k) S) (𝟙 _) _ _
    (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact bar_augmentation S)
    (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact ProjectiveResolution.homotopyEquiv_hom_π _ _)

def barEquiv : HomotopyEquiv (Rep.barComplex k S)
    ((restrictedResolution (k := k) S).complex) where
  hom := barMap S.subtype
  inv := ((Rep.barResolution k S).homotopyEquiv (restrictedResolution (k := k) S)).inv
  homotopyHomInvId := ((barHomotopy S).compRight _).trans
    ((Rep.barResolution k S).homotopyEquiv (restrictedResolution (k := k) S)).homotopyHomInvId
  homotopyInvHomId := ((barHomotopy S).compLeft _).trans
    ((Rep.barResolution k S).homotopyEquiv (restrictedResolution (k := k) S)).homotopyInvHomId

variable (A : Rep k S)
def indBase : A ⟶ Rep.res S.subtype (Rep.ind S.subtype A) :=
  Rep.indResHomEquiv S.subtype A (Rep.ind S.subtype A) (𝟙 _)

omit [DecidableEq G] in
@[simp] lemma indBase_apply (x : A) : (indBase S A).hom x = IndV.mk S.subtype A.ρ 1 x := rfl

def inducedChainMap : (Rep.barComplex k S).coinvariantsTensorObj A ⟶
    (Rep.barComplex k G).coinvariantsTensorObj (Rep.ind S.subtype A) :=
  (((Rep.coinvariantsTensor k S).obj A).mapHomologicalComplex _).map (barMap S.subtype) ≫
    (groupHomology.coinvariantsTensorResProjectiveResolutionIso S A (Rep.barResolution k G)).hom

def inducedChainEquiv : HomotopyEquiv ((Rep.barComplex k S).coinvariantsTensorObj A)
    ((Rep.barComplex k G).coinvariantsTensorObj (Rep.ind S.subtype A)) :=
  (((Rep.coinvariantsTensor k S).obj A).mapHomotopyEquiv (barEquiv S)).trans
    (HomotopyEquiv.ofIso
      (groupHomology.coinvariantsTensorResProjectiveResolutionIso S A (Rep.barResolution k G)))

end CoboundaryExpanders.ActualShapiro


section
open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.RowFrames
variable {A : Type} [CommRing A] {a b : ℕ}
lemma normalization_fixed (P g : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) A) :
    P*g*P⁻¹ ∈ RowParabolic.fixed A a b ↔
      ∀ i : Fin b, g • P (Sum.inr i) = P (Sum.inr i) := by
  rw [← standard_fixed_iff]
  constructor
  · intro h i
    have hh := congrArg (fun v : Fin a ⊕ Fin b → A => P⁻¹ • v) (h i)
    simpa only [mul_smul,inv_smul_smul,inverse_smul_standard] using hh
  · intro h i
    simp only [mul_smul,inverse_smul_standard,h i]
    rw [← inverse_smul_standard,smul_inv_smul]
end CoboundaryExpanders.RowFrames

namespace CoboundaryExpanders.CongruenceFrames
open Construction Unimodular InfiniteChains RowFrames
variable (p n m : ℕ) [Fact p.Prime]

lemma face_fixed_iff (hm : 1 ≤ m) {b : ℕ} (s : (source p n).Face b) (g : Gamma p n m) :
    g • s = s ↔ ∀ v : s.val, g • v.val = v.val := by
  constructor
  · intro h v
    have hval := congrArg Subtype.val h
    have hv : g • v.val ∈ s.val := by
      have ht : g • v.val ∈ (g • s).val := Finset.mem_map.mpr ⟨v.val,v.property,rfl⟩
      simpa only [hval] using ht
    exact reduce_injOn p n m hm s.val s.property.1 hv v.property (reduce_smul p n m g v.val)
  · intro h
    apply Subtype.ext
    exact FiniteImage.image_eq_of_matching s.val s.val (Equiv.refl _) g h

def completion {b : ℕ} (s : (source p n).Face b) (hb : b < n) :
    Matrix.SpecialLinearGroup (Fin (n-b) ⊕ Fin b) (R p) :=
  (row_completion (show 0 < n-b by omega)
    (fun i j => (FiniteImage.enumeration s.val s.property.2 i).val (splitCoordinates n b hb.le j))
    ((frame_coordinates (splitCoordinates n b hb.le) _).mpr
      ((frame_equiv (R := R p) (f := fun v : s.val => v.val)
        (FiniteImage.enumeration s.val s.property.2)).mpr s.property.1))).choose
lemma completion_row {b : ℕ} (s : (source p n).Face b) (hb : b < n) (i : Fin b) (j) :
    completion p n s hb (Sum.inr i) j =
      (FiniteImage.enumeration s.val s.property.2 i).val (splitCoordinates n b hb.le j) :=
  (row_completion (show 0 < n-b by omega)
    (fun i j => (FiniteImage.enumeration s.val s.property.2 i).val (splitCoordinates n b hb.le j))
    ((frame_coordinates (splitCoordinates n b hb.le) _).mpr
      ((frame_equiv (R := R p) (f := fun v : s.val => v.val)
        (FiniteImage.enumeration s.val s.property.2)).mpr s.property.1))).choose_spec i j

local instance kernelNormal {A B ι : Type} [CommRing A] [CommRing B] [Fintype ι] [DecidableEq ι]
    (φ : A →+* B) : (Matrix.SpecialLinearGroup.map (n := ι) φ).ker.Normal := inferInstance

def normalize {b : ℕ} (s : (source p n).Face b) (hb : b < n) :
    Gamma p n m ≃* (Matrix.SpecialLinearGroup.map (n := Fin (n-b) ⊕ Fin b)
      (Ideal.Quotient.mk (powerIdeal p m))).ker :=
  (kernelReindex (Ideal.Quotient.mk (powerIdeal p m)) (splitCoordinates n b hb.le).symm).trans
    (MulAut.conjNormal (completion p n s hb))

lemma normalize_fixed_iff (hm : 1 ≤ m) {b : ℕ} (s : (source p n).Face b) (hb : b < n)
    (g : Gamma p n m) :
    (normalize p n m s hb g).val ∈ RowParabolic.fixed (R p) (n-b) b ↔ g • s = s := by
  change completion p n s hb * (kernelReindex (Ideal.Quotient.mk (powerIdeal p m))
    (splitCoordinates n b hb.le).symm g).val * (completion p n s hb)⁻¹ ∈ _ ↔ _
  rw [normalization_fixed,face_fixed_iff p n m hm]
  let e := splitCoordinates n b hb.le
  let q := FiniteImage.enumeration s.val s.property.2
  have hh (i : Fin b) :
      (kernelReindex (Ideal.Quotient.mk (powerIdeal p m)) e.symm g).val •
        completion p n s hb (Sum.inr i) = completion p n s hb (Sum.inr i) ↔
      g • (q i).val = (q i).val := by
    have row : completion p n s hb (Sum.inr i) = fun j => (q i).val (e j) := by
      funext j; exact completion_row p n s hb i j
    rw [row]
    constructor
    · intro h
      change g.val • (q i).val = (q i).val
      funext j
      have hx := congrFun (reindex_smul e.symm g.val (fun j => (q i).val (e j))) j
      have hh := congrFun h (e.symm j)
      have he : (fun i_1 => (q i).val (e (e.symm i_1))) = (q i).val := by funext z; rw [e.apply_symm_apply]
      rw [he] at hx
      exact hx.symm.trans (hh.trans (congrArg (q i).val (e.apply_symm_apply j)))
    · intro h
      funext j
      have hx := congrFun (reindex_smul e.symm g.val (fun j => (q i).val (e j))) (e j)
      have he : (fun i_1 => (q i).val (e (e.symm i_1))) = (q i).val := by funext z; rw [e.apply_symm_apply]
      rw [he,e.symm_apply_apply] at hx
      exact hx.trans (congrFun h (e j))
  constructor
  · intro h v
    obtain ⟨i,rfl⟩ := q.surjective v
    exact (hh i).mp (h i)
  · intro h i; exact (hh i).mpr (h (q i))

def stabilizerEquiv (hm : 1 ≤ m) {b : ℕ} (s : (source p n).Face b) (hb : b < n) :
    MulAction.stabilizer (Gamma p n m) s ≃* MultiParabolic.group p (n-b) b m where
  toFun g := ⟨(normalize p n m s hb g.val).val,
    (normalize_fixed_iff p n m hm s hb g.val).mpr g.property,
    (normalize p n m s hb g.val).property⟩
  invFun g := ⟨(normalize p n m s hb).symm ⟨g.val,g.property.2⟩, by
    apply (normalize_fixed_iff p n m hm s hb _).mp
    rw [MulEquiv.apply_symm_apply]
    exact g.property.1⟩
  left_inv g := by
    apply Subtype.ext
    exact (normalize p n m s hb).symm_apply_apply g.val
  right_inv g := by
    apply Subtype.ext
    change ((normalize p n m s hb) ((normalize p n m s hb).symm ⟨g.val,g.property.2⟩)).val = g.val
    exact congrArg Subtype.val ((normalize p n m s hb).apply_symm_apply ⟨g.val,g.property.2⟩)
  map_mul' g h := by
    apply Subtype.ext
    change (normalize p n m s hb (g.val*h.val)).val =
      (normalize p n m s hb g.val).val * (normalize p n m s hb h.val).val
    exact congrArg Subtype.val ((normalize p n m s hb).map_mul g.val h.val)

end CoboundaryExpanders.CongruenceFrames

end

section
open CategoryTheory CategoryTheory.Limits

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.CongruenceFrames
open Construction RowFrames F2Stability
variable (p a m : ℕ) [Fact p.Prime]
local instance gammaNormal : (Gamma p (a+1) m).Normal := by unfold Gamma; infer_instance

def vertexCompletion (s : (source p (a+1)).Face 1) (ha : 0 < a) :
    Matrix.SpecialLinearGroup (Fin (a+1)) (R p) :=
  Blocks.reindexSL finSumFinEquiv (completion p (a+1) s (by omega))

end CoboundaryExpanders.CongruenceFrames

end

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

end

end OAI
end


