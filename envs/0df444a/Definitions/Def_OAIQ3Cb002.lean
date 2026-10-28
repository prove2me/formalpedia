-- Prove2me | Definitions.Def_OAIQ3Cb002
-- name    : OAIQ3Cb002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:30:26.226159+00:00
-- url     : https://prove2.me/theorems/bb6ca337-244b-4239-b18e-93a2922949e5
-- title:
--   Definitions bundle OAIQ3Cb002 of the split of OpenAI, Bounded-degree coboundary expanders in every dimension
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoboundaryExpanders.main`, carved from OpenAI's openai/math development (OpenAI, *Bounded-degree coboundary expanders in every dimension*, OpenAI Math Release, September 24, 2026, result family 177, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 471 declarations of OpenAI's Lean: 192 definitions, 1 inductive type or structure, 8 instances and 270 theorems. The definitions and types are `OAI.CoboundaryExpanders.Construction.matrixKernelHomologyIso`, `OAI.CoboundaryExpanders.Construction.opposition`, `OAI.CoboundaryExpanders.Construction.oppositionVertex`, `OAI.CoboundaryExpanders.Construction.quotientLinkVertexModel`, `OAI.CoboundaryExpanders.Construction.reducedFlagEquiv`, `OAI.CoboundaryExpanders.Construction.reducedGenerated`, `OAI.CoboundaryExpanders.Construction.reducedLocalMap`, `OAI.CoboundaryExpanders.Construction.reducedRoot`, `OAI.CoboundaryExpanders.Construction.sphericalLinkModel`, `OAI.CoboundaryExpanders.Construction.truncatedIwahori`, `OAI.CoboundaryExpanders.Construction.uLocalEmbedding`, `OAI.CoboundaryExpanders.CosetConstruction.Walk`, `OAI.CoboundaryExpanders.CosetConstruction.typedChainIso`, `OAI.CoboundaryExpanders.CosetModules.base`, `OAI.CoboundaryExpanders.CosetModules.cosetToInd`, `OAI.CoboundaryExpanders.CosetModules.extend`, `OAI.CoboundaryExpanders.CosetModules.indCosetIso`, `OAI.CoboundaryExpanders.CosetModules.indToCoset`, `OAI.CoboundaryExpanders.CosetSums.descend`, `OAI.CoboundaryExpanders.CosetSums.inclusion`, `OAI.CoboundaryExpanders.CosetSums.projection`, `OAI.CoboundaryExpanders.FinitePivots.prefixFlag`, `OAI.CoboundaryExpanders.FinsuppPermutation.OrbitParam.H0Equiv`, `OAI.CoboundaryExpanders.FinsuppPermutation.coeffIso`, `OAI.CoboundaryExpanders.InfiniteChains.AllLinkCones`, `OAI.CoboundaryExpanders.InfiniteChains.Attachment.ExactIn`, `OAI.CoboundaryExpanders.InfiniteChains.Attachment.RelativeExactIn`, `OAI.CoboundaryExpanders.InfiniteChains.Attachment.joinFaces`, `OAI.CoboundaryExpanders.InfiniteChains.Attachment.oldFaces`, `OAI.CoboundaryExpanders.InfiniteChains.BadSimplex.BadFaces`, `OAI.CoboundaryExpanders.InfiniteChains.BadSimplex.goodLink`, `OAI.CoboundaryExpanders.InfiniteChains.BadSimplex.stage`, `OAI.CoboundaryExpanders.InfiniteChains.ChainTransport.relabel`, `OAI.CoboundaryExpanders.InfiniteChains.Complex.IsConePoint`, `OAI.CoboundaryExpanders.InfiniteChains.Complex.augmentedData`, `OAI.CoboundaryExpanders.InfiniteChains.Complex.cone`, `OAI.CoboundaryExpanders.InfiniteChains.Complex.faceLink`, `OAI.CoboundaryExpanders.InfiniteChains.Cone.BoundedCone.extend`, `OAI.CoboundaryExpanders.InfiniteChains.Cone.BoundedCone.initial`, `OAI.CoboundaryExpanders.InfiniteChains.Cone.BoundedCone.normalize` and 153 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/Coboundary, in whole or in part: `Coboundary_Averaging`, `Coboundary_Chains`, `Coboundary_ChamberCones`, `Coboundary_Chambers`, `Coboundary_Cones`, `Coboundary_Cosets`, `Coboundary_Expansion`, `Coboundary_Flags`, `Coboundary_Frames`, `Coboundary_Joins`, `Coboundary_LatticeCones`, `Coboundary_Lattices`, `Coboundary_LinkSpectrum`, `Coboundary_Links`, `Coboundary_Mixing`, `Coboundary_Polynomial`, `Coboundary_Realization`, `Coboundary_Windows`, `Congruence_Basic`, `Congruence_Coinvariants`, `Congruence_CongruenceFrames`, `Congruence_FrameHomology`, `Congruence_OddHomology`, `Congruence_Parabolic`, `Congruence_Patterns`, `Congruence_ProStability`, `Congruence_Resolution`, `Congruence_Transfer`.
--
--   **Imports.** It imports the published bundle `Def_CoboundaryExpanders`; the bundles `OAIQ3Cb000` and `OAIQ3Cb001` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.CoboundaryExpanders.Construction.actual_uniform_cosystolic`, `OAI.CoboundaryExpanders.Construction.uniform_infinite_coset_positive`, `OAI.CoboundaryExpanders.main` and `OAI.CoboundaryExpanders.uniform_gamma_vanishing`.
-- source:
--   OpenAI, Bounded-degree coboundary expanders in every dimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 177; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Bounded-degree-coboundary-expanders-in-every-dimension-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Coboundary at commit adc7f12

import Mathlib
import Definitions.Def_CoboundaryExpanders
import Definitions.Def_OAIQ3Cb000
import Definitions.Def_OAIQ3Cb001

section
-- module Solutions.OAIQ3_Cob.Coboundary_Chains
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction
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

lemma raw_contraction (a : V) :
    rawBoundary.comp (rawCone a) + (rawCone a).comp rawBoundary = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Finsupp.lsingle_apply,
    LinearMap.id_apply, rawCone_single, rawBoundary_single, map_sum]
  by_cases ha : a ∈ s
  · rw [ite_eq_left ha, map_zero, zero_add]
    rw [Finset.sum_eq_single a]
    · simp [Finset.insert_erase ha]
    · intro b hb hba
      simp [Finset.mem_erase, Ne.symm hba, ha]
    · exact fun h => (h ha).elim
  · rw [ite_eq_right ha, rawBoundary_single, Finset.sum_insert ha, Finset.erase_insert ha]
    have he : (∑ b ∈ s, Finsupp.single ((insert a s).erase b) r) =
        ∑ b ∈ s, Finsupp.single (insert a (s.erase b)) r := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.erase_insert_of_ne (show a ≠ b from by intro he; subst b; exact ha hb)]
    rw [he]
    have he' : (∑ b ∈ s, if a ∈ s.erase b then 0 else Finsupp.single (insert a (s.erase b)) r) =
        ∑ b ∈ s, Finsupp.single (insert a (s.erase b)) r := by
      apply Finset.sum_congr rfl
      intro b _
      rw [ite_eq_right (fun h => ha (Finset.mem_of_mem_erase h))]
    rw [he', add_assoc]
    have hz : (∑ b ∈ s, Finsupp.single (insert a (s.erase b)) r) +
        (∑ b ∈ s, Finsupp.single (insert a (s.erase b)) r) = 0 := by
      ext z
      exact CharTwo.add_self_eq_zero _
    rw [hz, add_zero]

namespace Complex
variable (X : CoboundaryExpanders.InfiniteChains.Complex V)
instance instDecidableEqFace (n : ℕ) : DecidableEq (X.Face n) := Classical.decEq _

def IsConePoint (a : V) : Prop := ∀ σ ∈ X.faces, insert a σ ∈ X.faces

def cone (a : V) (ha : X.IsConePoint a) (n : ℕ) : X.Chains n →ₗ[k] X.Chains (n+1) :=
  Finsupp.linearCombination k (fun s => if h : a ∈ s.val then 0 else
    Finsupp.single ⟨insert a s.val, ha s.val s.property.1, by
      rw [Finset.card_insert_of_notMem h, s.property.2]⟩ 1)

open CategoryTheory

end Complex
end

namespace Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma mem_supported (P : Set (Finset V)) (c : Raw V) :
    c ∈ supported P ↔ ∀ s, c s ≠ 0 → s ∈ P := by
  simp [supported, Finsupp.mem_supported, Set.subset_def, Finsupp.mem_support_iff]

lemma single_mem_supported {P : Set (Finset V)} {s : Finset V} (hs : s ∈ P) (a : k) :
    Finsupp.single s a ∈ supported P := by
  rw [mem_supported]
  intro t ht
  by_cases h : s = t
  · simpa [← h] using hs
  · exact (ht (Finsupp.single_eq_of_ne (Ne.symm h))).elim

omit [DecidableEq V] [DecidableEq W] in
lemma map_supported (T : Raw V →ₗ[k] Raw W) (P : Set (Finset V)) (Q : Set (Finset W))
    (h : ∀ s ∈ P, ∀ a : k, T (Finsupp.single s a) ∈ supported Q)
    (c : Raw V) (hc : c ∈ supported P) : T c ∈ supported Q := by
  rw [← Finsupp.sum_single c, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro s hs
  exact h s ((mem_supported P c).mp hc s (Finsupp.mem_support_iff.mp hs)) (c s)

def joinFaces (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) : Set (Finset (W ⊕ V)) :=
  {s | s.toLeft ⊆ F ∧ s.toRight ∈ O.faces}

def oldFaces (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) : Set (Finset (W ⊕ V)) :=
  {s | s ∈ joinFaces F O ∧ s.toLeft ≠ F}

lemma boundary_disjSum_single (A : Finset W) (B : Finset V) (a : k) :
    rawBoundary (Finsupp.single (A.disjSum B) a) =
      (∑ w ∈ A, Finsupp.single ((A.erase w).disjSum B) a) +
      (∑ v ∈ B, Finsupp.single (A.disjSum (B.erase v)) a) := by
  rw [rawBoundary_single, Finset.sum_disjSum]
  simp only [erase_disjSum_inl, erase_disjSum_inr]

omit [DecidableEq V] in
lemma supported_mono {P Q : Set (Finset V)} (h : P ⊆ Q) :
    supported P ≤ supported Q := by
  intro c hc
  rw [mem_supported] at hc ⊢
  exact fun s hs => h (hc s hs)

lemma boundary_graded (P : Set (Finset V))
    (hdown : ∀ {s t}, s ∈ P → t ⊆ s → t ∈ P) (n : ℕ)
    (c : Raw V) (hc : c ∈ supported (graded P (n+1))) :
    rawBoundary c ∈ supported (graded P n) := by
  apply map_supported rawBoundary (graded P (n+1)) (graded P n) _ c hc
  intro s hs a
  rw [rawBoundary_single]
  apply Submodule.sum_mem
  intro v hv
  apply single_mem_supported
  refine ⟨hdown hs.1 (Finset.erase_subset v s), ?_⟩
  rw [Finset.card_erase_of_mem hv, hs.2]
  omega

def ExactIn (P : Set (Finset V)) (n : ℕ) : Prop :=
  ∀ c ∈ supported (graded P n), rawBoundary c = 0 →
    ∃ b ∈ supported (graded P (n+1)), rawBoundary b = c

def RelativeExactIn (P Q : Set (Finset V)) (n : ℕ) : Prop :=
  ∀ c ∈ supported (graded Q n), rawBoundary c ∈ supported P →
    ∃ b ∈ supported (graded Q (n+1)),
      c - rawBoundary b ∈ supported (graded P n)

end Attachment
end CoboundaryExpanders.InfiniteChains

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Cones
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction
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

omit [DecidableEq V] in
lemma twice (c : Raw V) : c + c = 0 := by
  ext s
  exact CharTwo.add_self_eq_zero _

lemma size_add_le (c d : Raw V) : size (c+d) ≤ size c + size d :=
  (Finset.card_le_card Finsupp.support_add).trans (Finset.card_union_le _ _)

omit [DecidableEq V] in
lemma size_smul_le (a : k) (c : Raw V) : size (a • c) ≤ size c :=
  Finset.card_le_card Finsupp.support_smul

omit [DecidableEq V] in
lemma size_single_le (s : Finset V) (a : k) : size (Finsupp.single s a) ≤ 1 := by
  exact (Finset.card_le_card Finsupp.support_single_subset).trans (by simp)

lemma size_sum_le {ι : Type*} (S : Finset ι) (c : ι → Raw V) :
    size (∑ i ∈ S, c i) ≤ ∑ i ∈ S, size (c i) :=
  (Finset.card_le_card Finsupp.support_finsetSum).trans Finset.card_biUnion_le

omit [DecidableEq V] in
lemma size_map_le (T : Raw V →ₗ[k] Raw W) (P : Set (Finset V)) (C : ℕ)
    (hT : ∀ s ∈ P, size (T (Finsupp.single s 1)) ≤ C)
    (c : Raw V) (hc : c ∈ supported P) : size (T c) ≤ C * size c := by
  conv_lhs => rw [← Finsupp.sum_single c, Finsupp.sum, map_sum]
  calc
    size (∑ s ∈ c.support, T (Finsupp.single s (c s))) ≤
        ∑ s ∈ c.support, size (T (Finsupp.single s (c s))) := size_sum_le _ _
    _ ≤ ∑ _s ∈ c.support, C := by
      apply Finset.sum_le_sum
      intro s hs
      have he : Finsupp.single s (c s) = c s • Finsupp.single s (1 : k) := by simp
      rw [he, map_smul]
      exact (size_smul_le _ _).trans
        (hT s ((mem_supported P c).mp hc s (Finsupp.mem_support_iff.mp hs)))
    _ = C * size c := by simp [size, Nat.mul_comm]

lemma size_rawCone_le (a : V) (c : Raw V) : size (rawCone a c) ≤ size c := by
  have h := size_map_le (rawCone a) Set.univ 1 (fun s _ => by
    rw [rawCone_single]
    split_ifs
    · simp
    · exact size_single_le _ _) c (by rw [mem_supported]; simp)
  simpa using h

lemma boundary_single_size (s : Finset V) (a : k) :
    size (rawBoundary (Finsupp.single s a)) ≤ s.card := by
  rw [rawBoundary_single]
  calc
    size (∑ v ∈ s, Finsupp.single (s.erase v) a) ≤
        ∑ v ∈ s, size (Finsupp.single (s.erase v) a) := size_sum_le _ _
    _ ≤ ∑ _v ∈ s, 1 := Finset.sum_le_sum (fun _ _ => size_single_le _ _)
    _ = s.card := by simp

omit [DecidableEq V] [DecidableEq W] in
lemma linear_eq_on_supported (A B : Raw V →ₗ[k] Raw W) (P : Set (Finset V))
    (h : ∀ s ∈ P, A (Finsupp.single s 1) = B (Finsupp.single s 1))
    (c : Raw V) (hc : c ∈ supported P) : A c = B c := by
  conv_lhs => rw [← Finsupp.sum_single c, Finsupp.sum, map_sum]
  conv_rhs => rw [← Finsupp.sum_single c, Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have he : Finsupp.single s (c s) = c s • Finsupp.single s (1 : k) := by simp
  rw [he, map_smul, map_smul,
    h s ((mem_supported P c).mp hc s (Finsupp.mem_support_iff.mp hs))]

namespace BoundedCone
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)

lemma map_graded (r : ℕ) (hr : r ≤ n) (c : Raw V)
    (hc : c ∈ supported (graded X.faces r)) :
    H.hom c ∈ supported (graded X.faces (r+1)) := by
  apply map_supported _ (graded X.faces r) _ _ c hc
  intro s hs a
  have he : Finsupp.single s a = a • Finsupp.single s (1 : k) := by simp
  rw [he, map_smul]
  apply Submodule.smul_mem
  have h := H.support s hs.1 (hs.2.trans_le hr)
  simpa only [hs.2] using h

lemma contraction_apply (r : ℕ) (hr : r ≤ n) (c : Raw V)
    (hc : c ∈ supported (graded X.faces r)) :
    rawBoundary (H.hom c) + H.hom (rawBoundary c) = c := by
  apply linear_eq_on_supported
    (rawBoundary.comp H.hom + H.hom.comp rawBoundary) LinearMap.id
    (graded X.faces r) _ c hc
  intro s hs
  exact H.contraction s hs.1 (hs.2.trans_le hr)

lemma size_apply (r : ℕ) (hr : r ≤ n) (c : Raw V)
    (hc : c ∈ supported (graded X.faces r)) : size (H.hom c) ≤ R * size c :=
  size_map_le H.hom (graded X.faces r) R
    (fun s hs => H.bound s hs.1 (hs.2.trans_le hr)) c hc

lemma newCycle_supported (s : Finset V) (hs : s ∈ X.faces) (hr : s.card = n+1) :
    Finsupp.single s 1 + H.hom (rawBoundary (Finsupp.single s 1)) ∈
      supported (graded X.faces (n+1)) := by
  apply Submodule.add_mem
  · exact single_mem_supported (P := graded X.faces (n+1)) ⟨hs, hr⟩ _
  · apply H.map_graded n le_rfl
    apply boundary_graded X.faces (fun {_ _} hs h => X.downward hs h) n
    exact single_mem_supported (P := graded X.faces (n+1)) ⟨hs, hr⟩ _

lemma newCycle_cycle (s : Finset V) (hs : s ∈ X.faces) (hr : s.card = n+1) :
    rawBoundary (Finsupp.single s 1 + H.hom (rawBoundary (Finsupp.single s 1))) = 0 := by
  have hb : rawBoundary (Finsupp.single s 1) ∈ supported (graded X.faces n) := by
    apply boundary_graded X.faces (fun {_ _} hs h => X.downward hs h) n
    exact single_mem_supported (P := graded X.faces (n+1)) ⟨hs, hr⟩ _
  have hd := LinearMap.congr_fun (rawBoundary_squared (V := V)) (Finsupp.single s 1)
  have hh := H.contraction_apply n le_rfl _ hb
  rw [show rawBoundary (rawBoundary (Finsupp.single s 1)) = 0 from hd, map_zero, add_zero] at hh
  rw [map_add, hh, twice]

lemma newCycle_size (s : Finset V) (hs : s ∈ X.faces) (hr : s.card = n+1) :
    size (Finsupp.single s 1 + H.hom (rawBoundary (Finsupp.single s 1))) ≤ 1+R*(n+1) := by
  have hb : rawBoundary (Finsupp.single s 1) ∈ supported (graded X.faces n) := by
    apply boundary_graded X.faces (fun {_ _} hs h => X.downward hs h) n
    exact single_mem_supported (P := graded X.faces (n+1)) ⟨hs, hr⟩ _
  exact (size_add_le _ _).trans (Nat.add_le_add (size_single_le _ _)
    ((H.size_apply n le_rfl _ hb).trans
      (Nat.mul_le_mul_left R (by simpa [hr] using boundary_single_size s (1 : k)))))

noncomputable def extend (S : ℕ)
    (fill : ∀ c : Raw V, c ∈ supported (graded X.faces (n+1)) →
      rawBoundary c = 0 → size c ≤ 1+R*(n+1) →
      ∃ b : Raw V, b ∈ supported (graded X.faces (n+2)) ∧
        rawBoundary b = c ∧ size b ≤ S) : BoundedCone X (n+1) (max R S) := by
  classical
  let z (s : Finset V) := Finsupp.single s 1 + H.hom (rawBoundary (Finsupp.single s 1))
  have hex (s : Finset V) (hs : s ∈ X.faces ∧ s.card = n+1) :
      ∃ b : Raw V, b ∈ supported (graded X.faces (n+2)) ∧
        rawBoundary b = z s ∧ size b ≤ S :=
    fill (z s) (H.newCycle_supported s hs.1 hs.2)
      (H.newCycle_cycle s hs.1 hs.2) (H.newCycle_size s hs.1 hs.2)
  let f (s : Finset V) : Raw V :=
    if hs : s ∈ X.faces ∧ s.card = n+1 then (hex s hs).choose
    else H.hom (Finsupp.single s 1)
  let T : Raw V →ₗ[k] Raw V := Finsupp.linearCombination k f
  have hT (s : Finset V) : T (Finsupp.single s 1) = f s := by simp [T]
  have hold (s : Finset V) (hs : s.card ≤ n) :
      T (Finsupp.single s 1) = H.hom (Finsupp.single s 1) := by
    rw [hT]
    simp only [f, dite_eq_right (show ¬(s ∈ X.faces ∧ s.card = n+1) from by omega)]
  have hboundary (s : Finset V) (hs : s.card ≤ n+1) :
      T (rawBoundary (Finsupp.single s 1)) = H.hom (rawBoundary (Finsupp.single s 1)) := by
    rw [rawBoundary_single, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro v hv
    apply hold
    rw [Finset.card_erase_of_mem hv]
    omega
  refine ⟨T, ?_, ?_, ?_⟩
  · intro s hs hn
    by_cases he : s.card = n+1
    · rw [hT]
      have hspec := (hex s ⟨hs, he⟩).choose_spec.1
      dsimp only [f]
      rw [dite_eq_left (show s ∈ X.faces ∧ s.card = n+1 from ⟨hs, he⟩)]
      simpa only [he, Nat.add_assoc] using hspec
    · rw [hold s (by omega)]
      exact H.support s hs (by omega)
  · intro s hs hn
    rw [hboundary s hn]
    by_cases he : s.card = n+1
    · rw [hT]
      have hb : rawBoundary (f s) = z s := by
        dsimp only [f]
        rw [dite_eq_left (show s ∈ X.faces ∧ s.card = n+1 from ⟨hs, he⟩)]
        exact (hex s ⟨hs, he⟩).choose_spec.2.1
      rw [hb]
      dsimp [z]
      rw [add_assoc, twice, add_zero]
    · rw [hold s (by omega)]
      exact H.contraction s hs (by omega)
  · intro s hs hn
    by_cases he : s.card = n+1
    · rw [hT]
      have hb : size (f s) ≤ S := by
        dsimp only [f]
        rw [dite_eq_left (show s ∈ X.faces ∧ s.card = n+1 from ⟨hs, he⟩)]
        exact (hex s ⟨hs, he⟩).choose_spec.2.2
      exact hb.trans (Nat.le_max_right _ _)
    · rw [hold s (by omega)]
      exact (H.bound s hs (by omega)).trans (Nat.le_max_left _ _)

noncomputable def initial (X : CoboundaryExpanders.InfiniteChains.Complex V) (a : V) (ha : {a} ∈ X.faces) :
    BoundedCone X 0 1 where
  hom := rawCone a
  support := by
    intro s hs hn
    have he : s = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
    subst s
    simpa [rawCone_single] using
      (single_mem_supported (P := graded X.faces 1) ⟨ha, by simp⟩ (1 : k))
  contraction := by
    intro s _ _
    exact LinearMap.congr_fun (raw_contraction a) (Finsupp.single s 1)
  bound := by
    intro s _ _
    exact (size_rawCone_le _ _).trans (size_single_le _ _)

end BoundedCone

def vertices (c : Raw V) : Finset V := c.support.biUnion id

def allowed (X : CoboundaryExpanders.InfiniteChains.Complex V) (bad : V → Prop) (A : Finset V) : CoboundaryExpanders.InfiniteChains.Complex V where
  faces := {s | s ∈ X.faces ∧ ∀ v ∈ s, bad v → v ∈ A}
  empty_mem := ⟨X.empty_mem, by simp⟩
  downward := fun hs hts => ⟨X.downward hs.1 hts, fun v hv => hs.2 v (hts hv)⟩

omit [DecidableEq V] in
lemma relabel_size (f : V → W) (c : Raw V) : size (relabel f c) ≤ size c := by
  have h := size_map_le (relabel f) Set.univ 1 (fun s _ => by
    rw [relabel_single]; exact size_single_le _ _) c (by rw [mem_supported]; simp)
  simpa using h

omit [DecidableEq V] in
lemma relabel_supported (f : V → W) (P : Set (Finset V)) (Q : Set (Finset W))
    (h : ∀ s ∈ P, s.image f ∈ Q) (c : Raw V) (hc : c ∈ supported P) :
    relabel f c ∈ supported Q := by
  apply map_supported _ P Q _ c hc
  intro s hs a
  rw [relabel_single]
  exact single_mem_supported (h s hs) a

omit [DecidableEq V] in
lemma relabel_graded (f : V → W) (P : Set (Finset V)) (Q : Set (Finset W)) (r : ℕ)
    (h : ∀ s ∈ P, s.image f ∈ Q)
    (hinj : ∀ s ∈ P, Set.InjOn f (s : Set V))
    (c : Raw V) (hc : c ∈ supported (graded P r)) :
    relabel f c ∈ supported (graded Q r) := by
  apply relabel_supported f (graded P r) (graded Q r) _ c hc
  intro s hs
  exact ⟨h s hs.1, (Finset.card_image_of_injOn (hinj s hs.1)).trans hs.2⟩

lemma relabel_boundary (f : V → W) (hf : Function.Injective f) :
    rawBoundary.comp (relabel f) = (relabel f).comp rawBoundary := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, relabel_single,
    rawBoundary_single, map_sum, Finset.sum_image, hf.injOn]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.image_erase hf]

lemma relabel_retraction (f : V → W) (g : W → V) (P : Set (Finset W))
    (h : ∀ s ∈ P, ∀ w ∈ s, f (g w) = w)
    (c : Raw W) (hc : c ∈ supported P) : relabel f (relabel g c) = c := by
  apply linear_eq_on_supported ((relabel f).comp (relabel g)) LinearMap.id P _ c hc
  intro s hs
  simp only [LinearMap.comp_apply, relabel_single, LinearMap.id_apply]
  congr 1
  rw [Finset.image_image]
  calc
    s.image (f ∘ g) = s.image id := Finset.image_congr (fun w hw => h s hs w hw)
    _ = s := Finset.image_id

end CoboundaryExpanders.InfiniteChains.Cone

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.InfiniteChains.Cone
open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq W] in
lemma unlabel_size (f : V → W) (hf : Function.Injective f) (c : Raw W) :
    size (unlabel f hf c) ≤ size c := by
  have h := size_map_le (unlabel f hf) Set.univ 1 (fun s _ => by
    rw [unlabel_single]; exact size_single_le _ _) c (by rw [mem_supported]; simp)
  simpa using h

namespace FaceModel
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)

omit [DecidableEq V] in
lemma unlabel_face (t : Finset W) (ht : t ∈ Y.faces) :
    t.preimage M.vertex M.injective.injOn ∈ X.faces ∧
      (t.preimage M.vertex M.injective.injOn).image M.vertex = t ∧
        (t.preimage M.vertex M.injective.injOn).card = t.card := by
  obtain ⟨s,hs,he⟩ := M.cover t ht
  subst t
  rw [preimage_image M.vertex M.injective s]
  exact ⟨hs,rfl,(Finset.card_image_of_injective s M.injective).symm⟩

lemma unlabel_graded (r : ℕ) (c : Raw W) (hc : c ∈ supported (graded Y.faces r)) :
    unlabel M.vertex M.injective c ∈ supported (graded X.faces r) := by
  apply map_supported _ (graded Y.faces r) (graded X.faces r) _ c hc
  intro t ht a
  rw [unlabel_single]
  have hh := M.unlabel_face t ht.1
  exact single_mem_supported (P := graded X.faces r) ⟨hh.1,hh.2.2.trans ht.2⟩ a

lemma unlabel_boundary (c : Raw W) (hc : c ∈ supported Y.faces) :
    unlabel M.vertex M.injective (rawBoundary c) =
      rawBoundary (unlabel M.vertex M.injective c) := by
  apply linear_eq_on_supported ((unlabel M.vertex M.injective).comp rawBoundary)
    (rawBoundary.comp (unlabel M.vertex M.injective)) Y.faces _ c hc
  intro t ht
  obtain ⟨s,hs,he⟩ := M.cover t ht
  subst t
  rw [← relabel_single M.vertex s 1]
  change unlabel M.vertex M.injective (rawBoundary (relabel M.vertex (Finsupp.single s 1))) = _
  have hb := LinearMap.congr_fun (Cone.relabel_boundary M.vertex M.injective) (Finsupp.single s 1)
  change rawBoundary (relabel M.vertex (Finsupp.single s 1)) =
    relabel M.vertex (rawBoundary (Finsupp.single s 1)) at hb
  simp only [LinearMap.comp_apply] at *
  rw [hb,unlabel_relabel,unlabel_relabel]

def pullCone {n R : ℕ} (H : BoundedCone Y n R) : BoundedCone X n R where
  hom := (unlabel M.vertex M.injective).comp (H.hom.comp (relabel M.vertex))
  support := by
    intro s hs hn
    change unlabel M.vertex M.injective (H.hom (relabel M.vertex (Finsupp.single s 1))) ∈ _
    rw [relabel_single]
    have hc := Finset.card_image_of_injective s M.injective
    have hh := H.support (s.image M.vertex) ((M.face_iff s).mpr hs) (hc.trans_le hn)
    rw [hc] at hh
    exact M.unlabel_graded (s.card+1) _ hh
  contraction := by
    intro s hs hn
    have hc := Finset.card_image_of_injective s M.injective
    have hin := (M.face_iff s).mpr hs
    have hsupport := H.support (s.image M.vertex) hin (hc.trans_le hn)
    have hplain := supported_mono (P := graded Y.faces ((s.image M.vertex).card+1))
      (Q := Y.faces) (fun _ ht => ht.1) hsupport
    have hh := congrArg (unlabel M.vertex M.injective)
      (H.contraction (s.image M.vertex) hin (hc.trans_le hn))
    rw [map_add,M.unlabel_boundary _ hplain] at hh
    have hb := LinearMap.congr_fun (Cone.relabel_boundary M.vertex M.injective) (Finsupp.single s 1)
    change rawBoundary (relabel M.vertex (Finsupp.single s 1)) =
      relabel M.vertex (rawBoundary (Finsupp.single s 1)) at hb
    rw [relabel_single] at hb
    rw [hb,unlabel_single,preimage_image M.vertex M.injective s] at hh
    simpa only [LinearMap.comp_apply,relabel_single] using hh
  bound := by
    intro s hs hn
    change size (unlabel M.vertex M.injective (H.hom (relabel M.vertex (Finsupp.single s 1)))) ≤ _
    apply (unlabel_size _ _ _).trans
    rw [relabel_single]
    exact H.bound (s.image M.vertex) ((M.face_iff s).mpr hs)
      ((Finset.card_image_of_injective s M.injective).trans_le hn)

def pushCone {n R : ℕ} (H : BoundedCone X n R) : BoundedCone Y n R where
  hom := (relabel M.vertex).comp (H.hom.comp (unlabel M.vertex M.injective))
  support := by
    intro t ht hn
    obtain ⟨s,hs,he⟩ := M.cover t ht
    subst t
    rw [Finset.card_image_of_injective s M.injective] at hn ⊢
    change relabel M.vertex (H.hom (unlabel M.vertex M.injective (Finsupp.single (s.image M.vertex) 1))) ∈ _
    rw [unlabel_single,preimage_image M.vertex M.injective s]
    exact Cone.relabel_graded M.vertex X.faces Y.faces (s.card+1)
      (fun a ha => (M.face_iff a).mpr ha) (fun _ _ => M.injective.injOn)
      _ (H.support s hs hn)
  contraction := by
    intro t ht hn
    obtain ⟨s,hs,he⟩ := M.cover t ht
    subst t
    rw [Finset.card_image_of_injective s M.injective] at hn
    change rawBoundary (relabel M.vertex (H.hom (unlabel M.vertex M.injective (Finsupp.single (s.image M.vertex) 1)))) +
      relabel M.vertex (H.hom (unlabel M.vertex M.injective (rawBoundary (Finsupp.single (s.image M.vertex) 1)))) = _
    rw [←relabel_single,unlabel_relabel]
    have hb (c : Raw V) := LinearMap.congr_fun (Cone.relabel_boundary M.vertex M.injective) c
    change ∀ c : Raw V, rawBoundary (relabel M.vertex c) = relabel M.vertex (rawBoundary c) at hb
    rw [hb,hb,unlabel_relabel,←map_add,H.contraction s hs hn]
  bound := by
    intro t ht hn
    obtain ⟨s,hs,he⟩ := M.cover t ht
    subst t
    rw [Finset.card_image_of_injective s M.injective] at hn
    change size (relabel M.vertex (H.hom (unlabel M.vertex M.injective (Finsupp.single (s.image M.vertex) 1)))) ≤ _
    rw [unlabel_single,preimage_image M.vertex M.injective s]
    exact (relabel_size _ _).trans (H.bound s hs hn)

end FaceModel
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

def VertexPath (X : CoboundaryExpanders.InfiniteChains.Complex V) (x y : V) : Prop :=
  Relation.ReflTransGen (fun a b => ({a,b}:Finset V) ∈ X.faces) x y

end CoboundaryExpanders.InfiniteChains.Cone

end

open scoped Polynomial BigOperators

namespace CoboundaryExpanders.InfiniteChains.Cone

section
open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]

lemma relabel_boundary_on (f : V → W) (P : Set (Finset V))
    (hf : ∀ s ∈ P, Set.InjOn f (s : Set V))
    (c : Raw V) (hc : c ∈ supported P) :
    rawBoundary (relabel f c) = relabel f (rawBoundary c) := by
  apply linear_eq_on_supported (rawBoundary.comp (relabel f)) ((relabel f).comp rawBoundary) P _ c hc
  intro s hs
  simp only [LinearMap.comp_apply,relabel_single,rawBoundary_single,map_sum]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro v hv
    rw [image_erase_of_injOn f s (hf s hs) v hv]
  · exact hf s hs

noncomputable def BoundedCone.retract {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} {n R : ℕ}
    (H : BoundedCone Y n R) (f : V → W) (g : W → V)
    (hf : ∀ s ∈ X.faces, s.image f ∈ Y.faces)
    (hg : ∀ s ∈ Y.faces, s.image g ∈ X.faces)
    (hfi : ∀ s ∈ X.faces, Set.InjOn f (s : Set V))
    (hgi : ∀ s ∈ Y.faces, Set.InjOn g (s : Set W))
    (hret : ∀ s ∈ X.faces, ∀ v ∈ s, g (f v) = v) : BoundedCone X n R where
  hom := (relabel g).comp (H.hom.comp (relabel f))
  support := by
    intro s hs hn
    have hcard : (s.image f).card = s.card := Finset.card_image_of_injOn (hfi s hs)
    have hH := H.support (s.image f) (hf s hs) (hcard.trans_le hn)
    simpa only [LinearMap.comp_apply,relabel_single,hcard] using
      relabel_graded g Y.faces X.faces ((s.image f).card+1) hg hgi _ hH
  contraction := by
    intro s hs hn
    have hcard : (s.image f).card = s.card := Finset.card_image_of_injOn (hfi s hs)
    have hH := H.support (s.image f) (hf s hs) (hcard.trans_le hn)
    have hb := relabel_boundary_on g (graded Y.faces ((s.image f).card+1))
      (fun t ht => hgi t ht.1) _ hH
    have hc := congrArg (relabel g) (H.contraction (s.image f) (hf s hs) (hcard.trans_le hn))
    have hbf := relabel_boundary_on f X.faces hfi (Finsupp.single s 1) (single_mem_supported hs 1)
    simp only [LinearMap.comp_apply,relabel_single] at hbf ⊢
    rw [hb,← hbf,← map_add,hc]
    simpa only [relabel_single] using relabel_retraction g f X.faces hret _ (single_mem_supported hs 1)
  bound := by
    intro s hs hn
    simp only [LinearMap.comp_apply,relabel_single]
    apply (relabel_size g _).trans
    exact H.bound (s.image f) (hf s hs) ((Finset.card_image_of_injOn (hfi s hs)).trans_le hn)

end

open Attachment
end CoboundaryExpanders.InfiniteChains.Cone

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Joins
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction
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

def complex (X : CoboundaryExpanders.InfiniteChains.Complex W) (Y : CoboundaryExpanders.InfiniteChains.Complex V) : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V) where
  faces := {s | s.toLeft ∈ X.faces ∧ s.toRight ∈ Y.faces}
  empty_mem := by simpa [Finset.toLeft, Finset.toRight] using And.intro X.empty_mem Y.empty_mem
  downward := by
    intro s t hs ht
    exact ⟨X.downward hs.1 (by intro x hx; simpa using ht (by simpa using hx : Sum.inl x ∈ t)),
      Y.downward hs.2 (by intro x hx; simpa using ht (by simpa using hx : Sum.inr x ∈ t))⟩

end

open Attachment Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def truncated (X : CoboundaryExpanders.InfiniteChains.Complex W) (Y : CoboundaryExpanders.InfiniteChains.Complex V) (M : ℕ) : Set (Finset (W ⊕ V)) :=
  {s | s ∈ (complex X Y).faces ∧ s.toLeft.card ≤ M}

end CoboundaryExpanders.InfiniteChains.Join

namespace CoboundaryExpanders.InfiniteChains.Cone.BoundedCone
open Attachment
variable {V : Type} [DecidableEq V] {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ}

lemma cut_boundary (H : BoundedCone X n R) (s : Finset V) (hs : s.card ≤ n+1) :
    H.cut (rawBoundary (Finsupp.single s 1)) = H.hom (rawBoundary (Finsupp.single s 1)) := by
  simp only [rawBoundary_single, map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [cut_single, ite_eq_left]
  rw [Finset.card_erase_of_mem hv]
  omega

def normalize (H : BoundedCone X n R) : BoundedCone X n R where
  hom := H.cut
  support := by
    intro s hs hn
    rw [cut_single, ite_eq_left hn]
    exact H.support s hs hn
  contraction := by
    intro s hs hn
    rw [cut_single, ite_eq_left hn, cut_boundary H s (by omega)]
    exact H.contraction s hs hn
  bound := by
    intro s hs hn
    rw [cut_single, ite_eq_left hn]
    exact H.bound s hs hn

end CoboundaryExpanders.InfiniteChains.Cone.BoundedCone

namespace CoboundaryExpanders.InfiniteChains.Join

section
open Attachment Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
lemma cross_add_left (c e : Raw W) (d : Raw V) : cross (c+e) d = cross c d + cross e d := by
  simp [cross]
omit [DecidableEq V] [DecidableEq W] in
lemma cross_add_right (c : Raw W) (d e : Raw V) : cross c (d+e) = cross c d + cross c e := by
  simp [cross]
omit [DecidableEq V] [DecidableEq W] in
lemma cross_sum_left {ι : Type*} (I : Finset ι) (c : ι → Raw W) (d : Raw V) :
    cross (∑ i ∈ I, c i) d = ∑ i ∈ I, cross (c i) d := by simp [cross]
omit [DecidableEq V] [DecidableEq W] in
lemma cross_sum_right {ι : Type*} (I : Finset ι) (c : Raw W) (d : ι → Raw V) :
    cross c (∑ i ∈ I, d i) = ∑ i ∈ I, cross c (d i) := by simp [cross]

lemma cross_boundary (c : Raw W) (d : Raw V) :
    rawBoundary (cross c d) = cross (rawBoundary c) d + cross c (rawBoundary d) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c e hc he =>
    simp only [cross_add_left, map_add, hc, he]
    abel
  | single A a =>
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add d e hd he =>
      simp only [cross_add_right, map_add, hd, he]
      abel
    | single B b =>
      simp only [map_smul, rawBoundary_single, cross_single_right, cross_sum_right]
      simp [prepend_single, map_sum, Finset.smul_sum, mul_comm,
        erase_disjSum_inl, erase_disjSum_inr]

lemma cross_graded (X : CoboundaryExpanders.InfiniteChains.Complex W) (Y : CoboundaryExpanders.InfiniteChains.Complex V) (a b : ℕ) (c : Raw W) (d : Raw V)
    (hc : c ∈ supported (graded X.faces a)) (hd : d ∈ supported (graded Y.faces b)) :
    cross c d ∈ supported (graded (complex X Y).faces (a+b)) := by
  let T : Raw W →ₗ[k] Raw (W ⊕ V) := (LinearMap.applyₗ (R := k) d).comp crossLinear
  change T c ∈ _
  apply map_supported T _ _ _ c hc
  intro A hA z
  change cross (Finsupp.single A z) d ∈ _
  rw [cross_single_left]
  apply Submodule.smul_mem
  apply map_supported (append A) (graded Y.faces b) _ _ d hd
  intro B hB t
  rw [append_single]
  exact single_mem_supported (P := graded (complex X Y).faces (a+b)) ⟨⟨by simpa using hA.1, by simpa using hB.1⟩,
    by rw [Finset.card_disjSum, hA.2, hB.2]⟩ t

lemma cross_size (c : Raw W) (d : Raw V) : size (cross c d) ≤ size c * size d := by
  let T : Raw W →ₗ[k] Raw (W ⊕ V) := (LinearMap.applyₗ (R := k) d).comp crossLinear
  have hT (A : Finset W) (_ : A ∈ Set.univ) : size (T (Finsupp.single A 1)) ≤ size d := by
    change size (cross (Finsupp.single A 1) d) ≤ _
    rw [cross_single_left, one_smul]
    exact (size_map_le (append A) Set.univ 1 (fun B _ => by simpa using size_single_le (A.disjSum B) (1 : k))
      d (by rw [mem_supported]; simp)).trans_eq (by omega)
  exact (size_map_le T Set.univ (size d) hT c (by rw [mem_supported]; simp)).trans_eq (Nat.mul_comm _ _)

lemma operator_boundary (T : Raw W →ₗ[k] Raw W) (U : Raw V →ₗ[k] Raw V)
    (A : Finset W) (B : Finset V) :
    operator T U (rawBoundary (Finsupp.single (A.disjSum B) 1)) =
      cross (T (rawBoundary (Finsupp.single A 1))) (U (Finsupp.single B 1)) +
      cross (T (Finsupp.single A 1)) (U (rawBoundary (Finsupp.single B 1))) := by
  rw [boundary_disjSum_single, map_add, map_sum, map_sum]
  simp only [operator_single, rawBoundary_single, map_sum, cross_sum_left, cross_sum_right]

def residual (T : Raw V →ₗ[k] Raw V) : Raw V →ₗ[k] Raw V :=
  LinearMap.id + rawBoundary.comp T + T.comp rawBoundary

lemma residual_eq (T : Raw V →ₗ[k] Raw V) (c : Raw V) :
    residual T c = c + rawBoundary (T c) + T (rawBoundary c) := rfl

lemma residual_boundary (T : Raw V →ₗ[k] Raw V) (c : Raw V) :
    rawBoundary (residual T c) = residual T (rawBoundary c) := by
  have hh (x : Raw V) : rawBoundary (rawBoundary x) = 0 :=
    LinearMap.congr_fun (rawBoundary_squared (V := V)) x
  simp [residual_eq, map_add, hh]

def joinHom (T : Raw W →ₗ[k] Raw W) (U : Raw V →ₗ[k] Raw V) :
    Raw (W ⊕ V) →ₗ[k] Raw (W ⊕ V) :=
  operator T LinearMap.id + operator (residual T) U

lemma joinHom_contraction (T : Raw W →ₗ[k] Raw W) (U : Raw V →ₗ[k] Raw V)
    (A : Finset W) (B : Finset V) :
    rawBoundary (joinHom T U (Finsupp.single (A.disjSum B) 1)) +
      joinHom T U (rawBoundary (Finsupp.single (A.disjSum B) 1)) =
        Finsupp.single (A.disjSum B) 1 +
          cross (residual T (Finsupp.single A 1)) (residual U (Finsupp.single B 1)) := by
  simp only [joinHom, LinearMap.add_apply, operator_single, map_add, cross_boundary,
    LinearMap.id_apply, operator_boundary, residual_boundary]
  rw [residual_eq U, cross_add_right, cross_add_right]
  have he := residual_eq T (Finsupp.single A 1)
  have he' := congrArg (fun x => cross x (Finsupp.single B 1)) he
  rw [cross_add_left, cross_add_left] at he'
  have h0 : cross (Finsupp.single A 1) (Finsupp.single B 1) = Finsupp.single (A.disjSum B) 1 := by simp
  rw [h0] at he'
  have h2 (x : Raw (W ⊕ V)) : x+x = 0 := twice x
  rw [he']
  abel_nf
  simp only [two_smul ℤ, twice, zero_add, add_zero]

end

open Attachment Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]

lemma cut_boundary_high {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)
    (s : Finset V) (hs : n+1 < s.card) : H.cut (rawBoundary (Finsupp.single s 1)) = 0 := by
  rw [rawBoundary_single, map_sum]
  apply Finset.sum_eq_zero
  intro v hv
  rw [BoundedCone.cut_single, ite_eq_right]
  rw [Finset.card_erase_of_mem hv]
  omega

lemma residual_cut_low {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)
    (s : Finset V) (hs : s ∈ X.faces) (hn : s.card ≤ n) :
    residual H.cut (Finsupp.single s 1) = 0 := by
  rw [residual_eq, add_assoc]
  have he := H.normalize.contraction s hs hn
  change rawBoundary (H.cut (Finsupp.single s 1)) + H.cut (rawBoundary (Finsupp.single s 1)) = _ at he
  rw [he, twice]

lemma residual_cut_graded {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)
    (s : Finset V) (hs : s ∈ X.faces) :
    residual H.cut (Finsupp.single s 1) ∈ supported (graded X.faces s.card) := by
  by_cases hn : s.card ≤ n
  · rw [residual_cut_low H s hs hn]
    exact Submodule.zero_mem _
  rw [residual_eq, BoundedCone.cut_single, ite_eq_right hn, map_zero, add_zero]
  apply Submodule.add_mem _ (single_mem_supported (P := graded X.faces s.card) ⟨hs, rfl⟩ _)
  by_cases he : s.card = n+1
  · rw [H.cut_boundary s (by omega)]
    rw [he]
    apply H.map_graded n le_rfl
    apply boundary_graded X.faces (fun {_ _} ht h => X.downward ht h) n
    exact single_mem_supported (P := graded X.faces (n+1)) ⟨hs, he⟩ _
  · rw [cut_boundary_high H s (by omega)]
    exact Submodule.zero_mem _

lemma residual_cut_size {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)
    (s : Finset V) (hs : s ∈ X.faces) :
    size (residual H.cut (Finsupp.single s 1)) ≤ 1+R*(n+1) := by
  by_cases hn : s.card ≤ n
  · rw [residual_cut_low H s hs hn, size_zero]
    omega
  rw [residual_eq, BoundedCone.cut_single, ite_eq_right hn, map_zero, add_zero]
  by_cases he : s.card = n+1
  · have hb : rawBoundary (Finsupp.single s 1) ∈ supported (graded X.faces n) := by
      apply boundary_graded X.faces (fun {_ _} ht h => X.downward ht h) n
      exact single_mem_supported (P := graded X.faces (n+1)) ⟨hs, he⟩ _
    rw [H.cut_boundary s (by omega)]
    exact (size_add_le _ _).trans (Nat.add_le_add (size_single_le s (1 : k))
      ((H.size_apply n le_rfl _ hb).trans (Nat.mul_le_mul_left R (by simpa [he] using boundary_single_size s (1 : k)))))
  · rw [cut_boundary_high H s (by omega), add_zero]
    exact (size_single_le s (1 : k)).trans (by omega)

def boundedCone {X : CoboundaryExpanders.InfiniteChains.Complex W} {Y : CoboundaryExpanders.InfiniteChains.Complex V} {n m R S : ℕ}
    (H : BoundedCone X n R) (K : BoundedCone Y m S) :
    BoundedCone (complex X Y) (n+m+1) (max R ((1+R*(n+1))*S)) where
  hom := joinHom H.cut K.cut
  support := by
    intro s hs hn
    rw [← Finset.toLeft_disjSum_toRight (u := s)]
    simp only [joinHom, LinearMap.add_apply, operator_single, LinearMap.id_apply]
    by_cases hA : s.toLeft.card ≤ n
    · rw [residual_cut_low H s.toLeft hs.1 hA, cross_zero_left, add_zero]
      have hg := cross_graded X Y (s.toLeft.card+1) s.toRight.card
        (H.cut (Finsupp.single s.toLeft 1)) (Finsupp.single s.toRight 1)
        (H.normalize.support s.toLeft hs.1 hA) (single_mem_supported (P := graded Y.faces s.toRight.card) ⟨hs.2, rfl⟩ _)
      convert hg using 1
      all_goals try with_reducible_and_instances rfl
      simp [Finset.card_disjSum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · have hB : s.toRight.card ≤ m := by
        have hcard := Finset.card_toLeft_add_card_toRight (u := s)
        omega
      rw [BoundedCone.cut_single, ite_eq_right hA, cross_zero_left, zero_add]
      have hg := cross_graded X Y s.toLeft.card (s.toRight.card+1)
        (residual H.cut (Finsupp.single s.toLeft 1)) (K.cut (Finsupp.single s.toRight 1))
        (residual_cut_graded H s.toLeft hs.1) (K.normalize.support s.toRight hs.2 hB)
      convert hg using 1
      all_goals try with_reducible_and_instances rfl
      simp [Finset.card_disjSum, Nat.add_assoc]
  contraction := by
    intro s hs hn
    rw [← Finset.toLeft_disjSum_toRight (u := s), joinHom_contraction]
    by_cases hA : s.toLeft.card ≤ n
    · rw [residual_cut_low H s.toLeft hs.1 hA, cross_zero_left, add_zero]
    · have hB : s.toRight.card ≤ m := by
        have hcard := Finset.card_toLeft_add_card_toRight (u := s)
        omega
      rw [residual_cut_low K s.toRight hs.2 hB, cross_zero_right, add_zero]
  bound := by
    intro s hs hn
    rw [← Finset.toLeft_disjSum_toRight (u := s)]
    simp only [joinHom, LinearMap.add_apply, operator_single, LinearMap.id_apply]
    by_cases hA : s.toLeft.card ≤ n
    · rw [residual_cut_low H s.toLeft hs.1 hA, cross_zero_left, add_zero]
      exact ((cross_size _ _).trans (Nat.mul_le_mul
        (H.normalize.bound s.toLeft hs.1 hA) (size_single_le s.toRight (1 : k)))).trans
        (by simp)
    · have hB : s.toRight.card ≤ m := by
        have hcard := Finset.card_toLeft_add_card_toRight (u := s)
        omega
      rw [BoundedCone.cut_single, ite_eq_right hA, cross_zero_left, zero_add]
      exact ((cross_size _ _).trans (Nat.mul_le_mul (residual_cut_size H s.toLeft hs.1)
        (K.normalize.bound s.toRight hs.2 hB))).trans (Nat.le_max_right _ _)

end CoboundaryExpanders.InfiniteChains.Join

end

open scoped Polynomial BigOperators

namespace CoboundaryExpanders.InfiniteChains.Join

section
open Attachment Cone
open scoped BigOperators
variable {V : Type} [DecidableEq V]
def finiteComplex {L : ℕ} (X : Fin L → CoboundaryExpanders.InfiniteChains.Complex V) : InfiniteChains.Complex (Fin L × V) where
  faces := {s | ∀ i, fiber s i ∈ (X i).faces}
  empty_mem := by intro i; simpa only [fiber,Finset.filter_empty,Finset.image_empty] using (X i).empty_mem
  downward := by
    intro s t hs hts i
    apply (X i).downward (hs i)
    intro v hv
    rw [mem_fiber] at hv ⊢
    exact hts hv

end

open Attachment Cone
open scoped BigOperators
end CoboundaryExpanders.InfiniteChains.Join

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Basic
attribute [-instance] _root_.OAI.CoboundaryExpanders.Blocks.gammaNormal _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant
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

instance normalDeeper (p a m n : ℕ) : (deeperCongruence p a m n).Normal :=
  MonoidHom.normal_ker _

end

variable (p n : ℕ) [Fact p.Prime]

def uLocalEmbedding (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    uLocalGroup p n hn cut ↪ localGroup p n hn cut where
  toFun g := ⟨g.val.val, g.property⟩
  inj' := by
    intro g h he
    have hv : g.val.val = h.val.val := congrArg
      (fun x : localGroup p n hn cut => (x : Matrix.SpecialLinearGroup (Fin (n + 1)) (R p))) he
    exact Subtype.ext (Subtype.ext hv)

instance uLocalGroup_finite (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    Finite (uLocalGroup p n hn cut) :=
  Finite.of_injective (uLocalEmbedding p n hn cut) (uLocalEmbedding p n hn cut).injective

def reducedLocalMap (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n + 1)) :
    uLocalGroup p n hn cut → reducedLocalGroup p n hn m cut :=
  fun g => ⟨QuotientGroup.mk' (uReduction p (n + 1) m).ker g.val, ⟨g.val, g.property, rfl⟩⟩

def reducedRoot {a : ℕ} {i j : Fin a} (hij : i < j) (m : ℕ) (f : Trunc p m) :
    (uReduction p a m).range :=
  ⟨Matrix.SpecialLinearGroup.transvection hij.ne f, by
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective f
    refine ⟨⟨Matrix.SpecialLinearGroup.transvection hij.ne F,
      upper_transvection_mem_U p hij F⟩, ?_⟩
    change Matrix.SpecialLinearGroup.map _ _ = _
    exact map_transvection _ _ _⟩

end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Cosets
attribute [-instance] _root_.OAI.CoboundaryExpanders.TypedCosetFaces.complexInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.kernelInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexAction _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexMulAction
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

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.TypedCosetFaces

section
variable {G G' I I' : Type} [Group G] [Group G'] [DecidableEq I] [DecidableEq I']
  (H : I → Subgroup G) (H' : I' → Subgroup G')
  (e : G ≃* G') (r : I ≃ I')
  (he : ∀ i g, g ∈ H i ↔ e g ∈ H' (r i))

omit [DecidableEq I] [DecidableEq I'] in
lemma isoVertex_surjective : Function.Surjective (isoVertex H H' e r he) := by
  rintro ⟨i,q⟩
  induction q using Quotient.inductionOn with | h q =>
  refine ⟨vertex H (e.symm q) (r.symm i),?_⟩
  simp only [isoVertex_vertex,e.apply_symm_apply,r.apply_symm_apply]
  rfl

def vertexEquiv : Vertex H ≃ Vertex H' :=
  Equiv.ofBijective (isoVertex H H' e r he)
    ⟨isoVertex_injective H H' e r he,isoVertex_surjective H H' e r he⟩

end

open InfiniteChains InfiniteChains.Cone

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
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.TypedCosetFaces.complexInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.kernelInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexAction _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexMulAction
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

variable {N : ℕ}

namespace CompleteFlag
variable [FiniteDimensional K V]

lemma space_zero (F : CompleteFlag K V N) : F.space 0 = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  exact F.rank 0

lemma space_last (F : CompleteFlag K V N) : F.space (Fin.last N) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [F.rank, F.dimension]
  rfl

def Opposed (F : CompleteFlag K V N) (W : Submodule K V) : Prop :=
  IsCompl W (F.space ⟨N-finrank K W, by omega⟩)

def Good (F : CompleteFlag K V N) (W : Submodule K V) : Prop :=
  0 < finrank K W ∧ finrank K W < N ∧ F.Opposed W

def complex (F : CompleteFlag K V N) : InfiniteChains.Complex (Submodule K V) where
  faces := {s | (∀ W ∈ s, F.Good W) ∧ (s : Set (Submodule K V)).Pairwise (fun W W' => W ≤ W' ∨ W' ≤ W)}
  empty_mem := by simp
  downward := by
    intro s t hs hts
    exact ⟨fun W hW => hs.1 W (hts hW), hs.2.mono hts⟩

lemma rank_le (F : CompleteFlag K V N) (W : Submodule K V) : finrank K W ≤ N := by
  simpa [F.dimension] using Submodule.finrank_le W

lemma opposed_iff_disjoint (F : CompleteFlag K V N) (W : Submodule K V) :
    F.Opposed W ↔ Disjoint W (F.space ⟨N-finrank K W, by omega⟩) := by
  apply Submodule.isCompl_iff_disjoint
  rw [F.dimension, F.rank]
  dsimp
  have := F.rank_le W
  omega

lemma opposed_disjoint_below (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (i : Fin (N+1)) (hi : i.val ≤ N-finrank K W) :
    Disjoint W (F.space i) := by
  exact (F.opposed_iff_disjoint W).mp hW |>.mono_right (F.mono hi)

def forbidden (F : CompleteFlag K V N) (W : Submodule K V) : Submodule K V :=
  W ⊔ F.space ⟨N-finrank K W-1, by omega⟩

omit [FiniteDimensional K V] in
lemma opposed_sup_above (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (i : Fin (N+1)) (hi : N-finrank K W ≤ i.val) :
    W ⊔ F.space i = ⊤ := by
  apply top_unique
  rw [← hW.sup_eq_top]
  exact sup_le_sup_left (F.mono hi) W

lemma lower_rank (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (i : Fin (finrank K W+1)) :
    finrank K ((F.space ⟨N-finrank K W+i.val, by
      have := F.rank_le W
      omega⟩).comap W.subtype) = i.val := by
  rw [← Submodule.finrank_map_subtype_eq W, Submodule.map_comap_subtype]
  have he := Submodule.finrank_sup_add_finrank_inf_eq W
    (F.space ⟨N-finrank K W+i.val, by have := F.rank_le W; omega⟩)
  rw [F.opposed_sup_above W hW _ (by dsimp; omega), finrank_top,
    F.dimension, F.rank] at he
  dsimp only [Fin.val_mk] at he
  have := F.rank_le W
  omega

def lower (F : CompleteFlag K V N) (W : Submodule K V) (hW : F.Opposed W) :
    CompleteFlag K W (finrank K W) where
  space i := (F.space ⟨N-finrank K W+i.val, by have := F.rank_le W; omega⟩).comap W.subtype
  mono := by
    intro i j hij
    apply Submodule.comap_mono
    apply F.mono
    change N-finrank K W+i.val ≤ N-finrank K W+j.val
    omega
  dimension := rfl
  rank := F.lower_rank W hW

lemma opposed_lower_iff (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (A : Submodule K W) :
    (F.lower W hW).Opposed A ↔ F.Opposed (A.map W.subtype) := by
  rw [(F.lower W hW).opposed_iff_disjoint, F.opposed_iff_disjoint,
    disjoint_map_subtype_iff]
  have ha := Submodule.finrank_le A
  have hw := F.rank_le W
  have eqi : (⟨N-finrank K W+(⟨finrank K W-finrank K A, by omega⟩ :
        Fin (finrank K W+1)).val, by omega⟩ : Fin (N+1)) =
      ⟨N-finrank K (A.map W.subtype), by omega⟩ := by
    apply Fin.ext
    dsimp
    rw [Submodule.finrank_map_subtype_eq]
    omega
  change Disjoint A ((F.space _).comap W.subtype) ↔ _
  rw [eqi]

lemma face_has_greatest (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (hne : s.Nonempty) :
    ∃ W ∈ s, ∀ U ∈ s, U ≤ W := by
  obtain ⟨W, hW, hmax⟩ := s.exists_max_image (fun U => finrank K U) hne
  refine ⟨W, hW, fun U hU => ?_⟩
  by_cases he : U = W
  · exact he.le
  · rcases hs.2 hU hW he with h | h
    · exact h
    · exact (Submodule.eq_of_le_of_finrank_le h (hmax U hU)).ge

def safeComplex (F : CompleteFlag K V N) (v : V) :
    InfiniteChains.Complex (Submodule K V) where
  faces := {s | s ∈ F.complex.faces ∧
    ∀ W ∈ s, finrank K W + 1 < N ∧ v ∉ F.forbidden W}
  empty_mem := ⟨F.complex.empty_mem, by simp⟩
  downward := fun hs hts => ⟨F.complex.downward hs.1 hts, fun W hW => hs.2 W (hts hW)⟩

def carrierApex (_ : CompleteFlag K V N) (v : V) (s : Finset (Submodule K V)) :
    Submodule K V := s.sup id ⊔ Submodule.span K {v}

def carrier (F : CompleteFlag K V N) (v : V) (s : Finset (Submodule K V)) :
    Set (Finset (Submodule K V)) :=
  {t | t ∈ F.complex.faces ∧ ∀ W ∈ t, W ≤ F.carrierApex v s}

end CompleteFlag

end CoboundaryExpanders.SphericalOpposition

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

def TopBad (F : CompleteFlag K V N) (W : Submodule K V) : Prop :=
  F.Good W ∧ finrank K W = N-1

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

def Opposite (F E : CompleteFlag K V N) : Prop :=
  ∀ i : Fin (N+1), IsCompl (F.space i) (E.space ⟨N-i.val, by omega⟩)

omit [FiniteDimensional K V] in
lemma opposite_symm {F E : CompleteFlag K V N} (h : F.Opposite E) : E.Opposite F := by
  intro i
  have hh := (h ⟨N-i.val, by omega⟩).symm
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Fin.ext
  dsimp
  omega

lemma opposite_line_rank {F E : CompleteFlag K V N} (h : F.Opposite E) (i : Fin N) :
    finrank K (F.space i.succ ⊓ E.space ⟨N-i.val, by omega⟩ : Submodule K V) = 1 := by
  have hs : F.space i.succ ⊔ E.space ⟨N-i.val, by omega⟩ = ⊤ := by
    apply top_unique
    rw [← (h i.castSucc).sup_eq_top]
    exact sup_le_sup_right (F.mono (by simp [Fin.le_def])) _
  have hh := Submodule.finrank_sup_add_finrank_inf_eq (F.space i.succ)
    (E.space ⟨N-i.val, by omega⟩)
  rw [hs, finrank_top, F.dimension, F.rank, E.rank] at hh
  dsimp at hh
  omega

lemma opposite_line_vector {F E : CompleteFlag K V N} (h : F.Opposite E) (i : Fin N) :
    ∃ v : V, v ∈ F.space i.succ ∧ v ∈ E.space ⟨N-i.val, by omega⟩ ∧
      v ∉ F.space i.castSucc := by
  have hn : (F.space i.succ ⊓ E.space ⟨N-i.val, by omega⟩ : Submodule K V) ≠ ⊥ := by
    intro he
    have hh := opposite_line_rank h i
    rw [he, finrank_bot] at hh
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  refine ⟨v,hv.1,hv.2,?_⟩
  intro hvF
  have hz : v ∈ (F.space i.castSucc ⊓ E.space ⟨N-i.val, by omega⟩ : Submodule K V) :=
    ⟨hvF,hv.2⟩
  have hb : F.space i.castSucc ⊓ E.space ⟨N-i.val, by omega⟩ = ⊥ :=
    (h i.castSucc).inf_eq_bot
  rw [hb] at hz
  exact hv0 hz

lemma step_span (F : CompleteFlag K V N) (i : Fin N) {v : V}
    (hv : v ∈ F.space i.succ) (hnot : v ∉ F.space i.castSucc) :
    F.space i.succ = F.space i.castSucc ⊔ span K {v} := by
  have hv0 : v ≠ 0 := fun he => hnot (he ▸ (F.space i.castSucc).zero_mem)
  have hd : Disjoint (F.space i.castSucc) (span K {v}) := disjoint_span_singleton_of_notMem hnot
  apply (Submodule.eq_of_le_of_finrank_eq
    (sup_le (F.mono (by simp [Fin.le_def])) (span_le.mpr (by simpa using hv))) ?_).symm
  have hh := finrank_sup_add_finrank_inf_eq (F.space i.castSucc) (span K {v})
  rw [hd.eq_bot, finrank_bot, add_zero, finrank_span_singleton hv0, F.rank] at hh
  simpa only [F.rank, Fin.val_succ, Fin.val_castSucc] using hh

theorem exists_adapted_basis {F E : CompleteFlag K V N} (h : F.Opposite E) :
    ∃ b : Basis (Fin N) K V, ∀ i : Fin N,
      b i ∈ F.space i.succ ∧ b i ∈ E.space ⟨N-i.val, by omega⟩ := by
  choose v hvF hvE hvnot using opposite_line_vector h
  have hs : ∀ i : Fin (N+1), F.space i ≤ span K (Set.range v) := by
    intro i
    induction i using Fin.induction with
    | zero => rw [F.space_zero]; exact bot_le
    | succ i hi =>
      rw [F.step_span i (hvF i) (hvnot i)]
      exact sup_le hi (span_le.mpr (by
        intro x hx
        obtain rfl := Set.mem_singleton_iff.mp hx
        exact subset_span (Set.mem_range_self i)))
  have htop : ⊤ ≤ span K (Set.range v) := by simpa [F.space_last] using hs (Fin.last N)
  let b := basisOfTopLeSpanOfCardEqFinrank v htop (by simpa using F.dimension.symm)
  refine ⟨b, fun i => ?_⟩
  simpa [b] using And.intro (hvF i) (hvE i)

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

lemma adapted_suffix (E : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ j : Fin N, b j ∈ E.space ⟨N-j.val, by omega⟩) (i : Fin (N+1)) :
    span K (Set.range (fun j : Fin (N-i.val) => b (suffixIndex i j))) =
      E.space ⟨N-i.val, by omega⟩ := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact E.mono (by change N-(i.val+j.val) ≤ N-i.val; omega) (hb (suffixIndex i j))
  · simpa only [Function.comp_def, Fintype.card_fin, E.rank] using
      finrank_span_eq_card (b.linearIndependent.comp _ (suffixIndex_injective i))

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

lemma opposed_bot (F : CompleteFlag K V N) : F.Opposed ⊥ := by
  unfold Opposed
  simp only [finrank_bot, Nat.sub_zero]
  have hh : (⟨N, by omega⟩ : Fin (N+1)) = Fin.last N := rfl
  rw [hh, F.space_last]
  exact isCompl_bot_top

lemma opposed_top (F : CompleteFlag K V N) : F.Opposed ⊤ := by
  unfold Opposed
  simp only [finrank_top, F.dimension, Nat.sub_self]
  rw [show (⟨0, by omega⟩ : Fin (N+1)) = 0 from rfl, F.space_zero]
  exact isCompl_top_bot

lemma extend_opposed (F : CompleteFlag K V N) (A : Submodule K V) (hA : F.Opposed A)
    (j : ℕ) (hAj : finrank K A ≤ j) (hj : j ≤ N) :
    ∃ W : Submodule K V, A ≤ W ∧ finrank K W = j ∧ F.Opposed W := by
  have hd := F.opposed_disjoint_below A hA ⟨N-j, by omega⟩ (by dsimp; omega)
  obtain ⟨W,hAW,hW⟩ := hd.exists_isCompl
  have hr : finrank K W = j := by
    have hh := finrank_sup_add_finrank_inf_eq W (F.space ⟨N-j, by omega⟩)
    rw [hW.sup_eq_top, hW.inf_eq_bot, finrank_bot, add_zero, finrank_top,
      F.dimension, F.rank] at hh
    dsimp at hh
    omega
  refine ⟨W,hAW,hr,?_⟩
  unfold Opposed
  simpa only [hr] using hW

lemma interval_opposed (F : CompleteFlag K V N) (A B : Submodule K V)
    (hA : F.Opposed A) (hB : F.Opposed B) (hAB : A ≤ B)
    (j : ℕ) (hAj : finrank K A ≤ j) (hjB : j ≤ finrank K B) :
    ∃ W : Submodule K V, A ≤ W ∧ W ≤ B ∧ finrank K W = j ∧ F.Opposed W := by
  have hAc : (F.lower B hB).Opposed (A.comap B.subtype) := by
    rw [F.opposed_lower_iff B hB, map_comap_lower B A hAB]
    exact hA
  obtain ⟨W,hAW,hr,hW⟩ := (F.lower B hB).extend_opposed (A.comap B.subtype) hAc j
    (by simpa only [rank_comap_lower B A hAB] using hAj) hjB
  refine ⟨W.map B.subtype, ?_, Submodule.map_subtype_le B W, ?_,
    (F.opposed_lower_iff B hB W).mp hW⟩
  · rw [← map_comap_lower B A hAB]
    exact Submodule.map_mono hAW
  · simpa only [Submodule.finrank_map_subtype_eq] using hr

lemma rank_injective_on_face (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) : Set.InjOn (fun W : Submodule K V => finrank K W) s := by
  intro A hA B hB hr
  by_cases he : A = B
  · exact he
  · rcases hs.2 hA hB he with hAB | hBA
    · exact Submodule.eq_of_le_of_finrank_eq hAB hr
    · exact (Submodule.eq_of_le_of_finrank_eq hBA hr.symm).symm

lemma face_order_of_rank_le (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) {A B : Submodule K V} (hA : A ∈ s) (hB : B ∈ s)
    (hr : finrank K A ≤ finrank K B) : A ≤ B := by
  by_cases he : A = B
  · exact he.le
  · rcases hs.2 hA hB he with hAB | hBA
    · exact hAB
    · exact (Submodule.eq_of_le_of_finrank_le hBA hr).ge

lemma face_has_least (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (hne : s.Nonempty) :
    ∃ W ∈ s, ∀ U ∈ s, W ≤ U := by
  obtain ⟨W,hW,hmin⟩ := s.exists_min_image (fun U => finrank K U) hne
  exact ⟨W,hW,fun U hU => F.face_order_of_rank_le s hs hW hU (hmin U hU)⟩

lemma face_lower_bound_at (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (j : ℕ) (hj : 0 < j) :
    ∃ A : Submodule K V, F.Opposed A ∧ finrank K A < j ∧
      (∀ U ∈ s, finrank K U < j → U ≤ A) ∧ (∀ U ∈ s, j ≤ finrank K U → A ≤ U) ∧ (A = ⊥ ∨ A ∈ s) := by
  classical
  let t := s.filter (fun W : Submodule K V => finrank K W < j)
  by_cases ht : t.Nonempty
  · obtain ⟨A,hA,hmax⟩ := F.face_has_greatest t (F.complex.downward hs (Finset.filter_subset _ _)) ht
    obtain ⟨hAs,hAr⟩ := Finset.mem_filter.mp hA
    refine ⟨A,(hs.1 A hAs).2.2,hAr,fun U hU hr => hmax U (Finset.mem_filter.mpr ⟨hU,hr⟩),?_,Or.inr hAs⟩
    intro U hU hr
    exact F.face_order_of_rank_le s hs hAs hU (by omega)
  · refine ⟨⊥,F.opposed_bot, by simpa only [finrank_bot], ?_, fun _ _ _ => bot_le, Or.inl rfl⟩
    intro U hU hr
    exact False.elim (ht ⟨U,Finset.mem_filter.mpr ⟨hU,hr⟩⟩)

lemma face_upper_bound_at (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (j : ℕ) (hj : j < N) :
    ∃ B : Submodule K V, F.Opposed B ∧ j < finrank K B ∧
      (∀ U ∈ s, j < finrank K U → B ≤ U) ∧ (∀ U ∈ s, finrank K U ≤ j → U ≤ B) ∧ (B = ⊤ ∨ B ∈ s) := by
  classical
  let t := s.filter (fun W : Submodule K V => j < finrank K W)
  by_cases ht : t.Nonempty
  · obtain ⟨B,hB,hmin⟩ := F.face_has_least t (F.complex.downward hs (Finset.filter_subset _ _)) ht
    obtain ⟨hBs,hBr⟩ := Finset.mem_filter.mp hB
    refine ⟨B,(hs.1 B hBs).2.2,hBr,fun U hU hr => hmin U (Finset.mem_filter.mpr ⟨hU,hr⟩),?_,Or.inr hBs⟩
    intro U hU hr
    exact F.face_order_of_rank_le s hs hU hBs (by omega)
  · refine ⟨⊤,F.opposed_top, by simpa only [finrank_top,F.dimension], ?_, fun _ _ _ => le_top, Or.inl rfl⟩
    intro U hU hr
    exact False.elim (ht ⟨U,Finset.mem_filter.mpr ⟨hU,hr⟩⟩)

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

lemma insert_rank (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (j : ℕ) (hj0 : 0 < j) (hjN : j < N) :
    ∃ t : Finset (Submodule K V), t ∈ F.complex.faces ∧ s ⊆ t ∧
      ∃ W ∈ t, finrank K W = j := by
  classical
  by_cases hex : ∃ W ∈ s, finrank K W = j
  · exact ⟨s,hs,Finset.Subset.refl s,hex⟩
  obtain ⟨A,hA,hrA,hAl,hAu,hlocA⟩ := F.face_lower_bound_at s hs j hj0
  obtain ⟨B,hB,hrB,hBl,hBu,hlocB⟩ := F.face_upper_bound_at s hs j hjN
  have hAB : A ≤ B := by
    rcases hlocA with rfl | hAs
    · exact bot_le
    · exact hBu A hAs hrA.le
  obtain ⟨W,hAW,hWB,hrW,hW⟩ := F.interval_opposed A B hA hB hAB j hrA.le hrB.le
  have hcomp (U : Submodule K V) (hU : U ∈ s) : U ≤ W ∨ W ≤ U := by
    rcases lt_trichotomy (finrank K U) j with hr | hr | hr
    · exact Or.inl ((hAl U hU hr).trans hAW)
    · exact False.elim (hex ⟨U,hU,hr⟩)
    · exact Or.inr (hWB.trans (hBl U hU hr))
  refine ⟨insert W s,?_,Finset.subset_insert _ _,W,Finset.mem_insert_self _ _,hrW⟩
  constructor
  · intro U hU
    rcases Finset.mem_insert.mp hU with rfl | hU
    · exact ⟨by omega,by omega,hW⟩
    · exact hs.1 U hU
  · intro U hU U' hU' hne
    rcases Finset.mem_insert.mp hU with hUW | hUs
    · subst U
      rcases Finset.mem_insert.mp hU' with hU'W | hU's
      · subst U'; exact False.elim (hne rfl)
      · exact (hcomp U' hU's).symm
    · rcases Finset.mem_insert.mp hU' with hU'W | hU's
      · subst U'; exact hcomp U hUs
      · exact hs.2 hUs hU's hne

lemma exists_extend_ranks (F : CompleteFlag K V N) (I : Finset ℕ)
    (hI : ∀ j ∈ I, 0 < j ∧ j < N) (s : Finset (Submodule K V)) (hs : s ∈ F.complex.faces) :
    ∃ t : Finset (Submodule K V), t ∈ F.complex.faces ∧ s ⊆ t ∧
      ∀ j ∈ I, ∃ W ∈ t, finrank K W = j := by
  classical
  induction I using Finset.induction generalizing s with
  | empty => exact ⟨s,hs,Finset.Subset.refl s,by simp⟩
  | @insert a I ha ih =>
    obtain ⟨t,ht,hst,hfull⟩ := ih (fun j hj => hI j (Finset.mem_insert_of_mem hj)) s hs
    obtain ⟨u,hu,htu,hua⟩ := F.insert_rank t ht a
      (hI a (Finset.mem_insert_self _ _)).1 (hI a (Finset.mem_insert_self _ _)).2
    refine ⟨u,hu,hst.trans htu,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hua
    · obtain ⟨W,hW,hr⟩ := hfull j hj
      exact ⟨W,htu hW,hr⟩

def FullFace (F : CompleteFlag K V N) (s : Finset (Submodule K V)) : Prop :=
  s ∈ F.complex.faces ∧ ∀ j, 0 < j → j < N → ∃ W ∈ s, finrank K W = j

lemma exists_full_face (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) : ∃ t, F.FullFace t ∧ s ⊆ t := by
  obtain ⟨t,ht,hst,hfull⟩ := F.exists_extend_ranks (Finset.Ioo 0 N)
    (fun _ hj => Finset.mem_Ioo.mp hj) s hs
  exact ⟨t,⟨ht,fun j hj0 hjN => hfull j (Finset.mem_Ioo.mpr ⟨hj0,hjN⟩)⟩,hst⟩

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

lemma exists_flag_stages (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : F.FullFace s) (i : Fin (N+1)) :
    ∃ W : Submodule K V, finrank K W = i.val ∧ F.Opposed W ∧
      (0 < i.val → i.val < N → W ∈ s) := by
  by_cases hi0 : i.val = 0
  · exact ⟨⊥,by simp [hi0],F.opposed_bot,by omega⟩
  by_cases hiN : i.val = N
  · exact ⟨⊤,by simp [F.dimension,hiN],F.opposed_top,by omega⟩
  obtain ⟨W,hW,hr⟩ := hs.2 i.val (by omega) (by omega)
  exact ⟨W,hr,(hs.1.1 W hW).2.2,fun _ _ => hW⟩

theorem exists_flag_from_face (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : F.FullFace s) :
    ∃ E : CompleteFlag K V N, F.Opposite E ∧
      ∀ W : Submodule K V, W ∈ s ↔
        ∃ i : Fin (N+1), 0 < i.val ∧ i.val < N ∧ E.space i = W := by
  classical
  choose f hr ho hm using F.exists_flag_stages s hs
  have hmono : Monotone f := by
    intro i j hij
    by_cases hi : i.val = 0
    · have hh : f i = ⊥ := Submodule.finrank_eq_zero.mp ((hr i).trans hi)
      rw [hh]; exact bot_le
    by_cases hj : j.val = N
    · have hh : f j = ⊤ := Submodule.eq_top_of_finrank_eq ((hr j).trans (hj.trans F.dimension.symm))
      rw [hh]; exact le_top
    exact F.face_order_of_rank_le s hs.1 (hm i (by omega) (by omega))
      (hm j (by omega) (by omega)) (by rw [hr,hr]; exact hij)
  let E : CompleteFlag K V N := ⟨f,hmono,F.dimension,hr⟩
  refine ⟨E,?_,?_⟩
  · intro i
    have hh := (ho ⟨N-i.val, by omega⟩).symm
    simp only [hr] at hh
    have he : (⟨N-(N-i.val), by omega⟩ : Fin (N+1)) = i := by apply Fin.ext; dsimp; omega
    simpa only [he] using hh
  · intro W
    constructor
    · intro hW
      let i : Fin (N+1) := ⟨finrank K W, by have := (hs.1.1 W hW).2.1; omega⟩
      have hi0 : 0 < i.val := (hs.1.1 W hW).1
      have hiN : i.val < N := (hs.1.1 W hW).2.1
      exact ⟨i,hi0,hiN,F.rank_injective_on_face s hs.1 (hm i hi0 hiN) hW (hr i)⟩
    · rintro ⟨i,hi0,hiN,rfl⟩
      exact hm i hi0 hiN

open scoped Pointwise

lemma flagStabilizer_good (F : CompleteFlag K V N) (e : F.flagStabilizer) (W : Submodule K V)
    (hW : F.Good W) : F.Good (e • W) := by
  have he := (F.mem_flagStabilizer e.val).mp e.property
  change F.Good (W.map e.val.toLinearMap)
  refine ⟨by simpa only [e.val.finrank_map_eq] using hW.1,
    by simpa only [e.val.finrank_map_eq] using hW.2.1,?_⟩
  rw [F.opposed_iff_disjoint]
  simp only [e.val.finrank_map_eq]
  rw [← he]
  exact Submodule.disjoint_map e.val.injective hW.2.2.disjoint

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

omit [FiniteDimensional K V] in
lemma adapted_basis_not_mem_previous {F E : CompleteFlag K V N} (h : F.Opposite E)
    (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ F.space i.succ ∧ b i ∈ E.space ⟨N-i.val, by omega⟩)
    (i : Fin N) : b i ∉ F.space i.castSucc := by
  intro hi
  have hh : b i ∈ F.space i.castSucc ⊓ E.space ⟨N-i.val, by omega⟩ := ⟨hi,(hb i).2⟩
  have he : F.space i.castSucc ⊓ E.space ⟨N-i.val, by omega⟩ = ⊥ := by
    simpa only [Fin.val_castSucc] using (h i.castSucc).inf_eq_bot
  rw [he] at hh
  exact b.ne_zero i hh

lemma adapted_diagonal_ne_zero (F : CompleteFlag K V N)
    (b c : Basis (Fin N) K V) (hb : ∀ i : Fin N, b i ∈ F.space i.succ)
    (hc : ∀ i : Fin N, c i ∈ F.space i.succ)
    (hnot : ∀ i : Fin N, c i ∉ F.space i.castSucc) (i : Fin N) :
    b.repr (c i) i ≠ 0 := by
  intro hi
  apply hnot i
  apply (F.mem_flag_iff_repr b hb i.castSucc (c i)).mpr
  intro j hj
  by_cases hji : j = i
  · simpa [hji] using hi
  · apply (F.mem_flag_iff_repr b hb i.succ (c i)).mp (hc i) j
    change i.val+1 ≤ j.val
    change i.val ≤ j.val at hj
    have : j.val ≠ i.val := fun h => hji (Fin.ext h)
    omega

theorem exists_normalized_adapted_basis {F E : CompleteFlag K V N} (h : F.Opposite E)
    (b : Basis (Fin N) K V) (hb : ∀ i : Fin N, b i ∈ F.space i.succ) :
    ∃ c : Basis (Fin N) K V, ∀ i : Fin N,
      c i ∈ F.space i.succ ∧ c i ∈ E.space ⟨N-i.val, by omega⟩ ∧ b.repr (c i) i = 1 := by
  classical
  obtain ⟨c,hc⟩ := exists_adapted_basis h
  have hne := F.adapted_diagonal_ne_zero b c hb (fun i => (hc i).1)
    (adapted_basis_not_mem_previous h c hc)
  let u : Fin N → Kˣ := fun i => (Units.mk0 (b.repr (c i) i) (hne i))⁻¹
  refine ⟨c.unitsSMul u,?_⟩
  intro i
  simp only [Basis.unitsSMul_apply, Units.smul_def]
  refine ⟨(F.space i.succ).smul_mem _ (hc i).1,
    (E.space ⟨N-i.val, by omega⟩).smul_mem _ (hc i).2,?_⟩
  simp [u, map_smul, hne i]

theorem exists_unitriangular_equiv {F E E' : CompleteFlag K V N}
    (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ F.space i.succ ∧ b i ∈ E.space ⟨N-i.val, by omega⟩)
    (h' : F.Opposite E') :
    ∃ e : V ≃ₗ[K] V, Unitriangular b e ∧
      (∀ i, (F.space i).map e.toLinearMap = F.space i) ∧
      (∀ i, (E.space i).map e.toLinearMap = E'.space i) := by
  classical
  obtain ⟨c,hc⟩ := exists_normalized_adapted_basis h' b (fun i => (hb i).1)
  let e := b.equiv c (Equiv.refl _)
  refine ⟨e,?_,?_,?_⟩
  · intro i j hij
    dsimp [e]
    rw [Basis.equiv_apply, Equiv.refl_apply]
    by_cases hji : j = i
    · simpa [hji] using (hc i).2.2
    · rw [ite_eq_right hji]
      apply (F.mem_flag_iff_repr b (fun i => (hb i).1) i.succ (c i)).mp (hc i).1 j
      change i.val+1 ≤ j.val
      have : j.val ≠ i.val := fun h => hji (Fin.ext h)
      change i.val ≤ j.val at hij
      omega
  · intro i
    calc
      (F.space i).map e.toLinearMap =
          (span K (Set.range (fun j : Fin i.val => b (prefixIndex i j)))).map e.toLinearMap := by
        rw [adapted_prefix F b (fun i => (hb i).1)]
      _ = span K (Set.range (fun j : Fin i.val => c (prefixIndex i j))) :=
        basis_equiv_span_range b c _
      _ = F.space i := adapted_prefix F c (fun i => (hc i).1) i
  · intro i
    let k : Fin (N+1) := ⟨N-i.val, by omega⟩
    have he : (⟨N-k.val, by omega⟩ : Fin (N+1)) = i := by
      apply Fin.ext; dsimp [k]; omega
    rw [← he, ← adapted_suffix E b (fun i => (hb i).2) k,
      basis_equiv_span_range b c, adapted_suffix E' c (fun i => (hc i).2.1), he]

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

lemma mem_opposite_flag_iff_repr (E : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ j : Fin N, b j ∈ E.space ⟨N-j.val, by omega⟩) (i : Fin (N+1)) (v : V) :
    v ∈ E.space ⟨N-i.val, by omega⟩ ↔
      ∀ j : Fin N, j.val < i.val → b.repr v j = 0 := by
  rw [← E.adapted_suffix b hb i, suffix_span_image, b.mem_span_image]
  constructor
  · intro h j hj
    by_contra hn
    exact Nat.not_lt_of_ge (h (Finsupp.mem_support_iff.mpr hn)) hj
  · intro h j hj
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hj) (h j (Nat.lt_of_not_ge hn))

theorem unipotent_transitive {F E E' : CompleteFlag K V N}
    (h : F.Opposite E) (h' : F.Opposite E') :
    ∃ e : F.unipotentFlagStabilizer, ∀ i,
      (E.space i).map e.val.toLinearMap = E'.space i := by
  obtain ⟨b,hb⟩ := exists_adapted_basis h
  obtain ⟨e,he,heF,heE⟩ := exists_unitriangular_equiv b hb h'
  exact ⟨⟨e,(F.mem_flagStabilizer e).mpr heF,
    F.unitriangular_grading b (fun i => (hb i).1) e he⟩,heE⟩

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule TypedCosetFaces
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

open scoped Pointwise

omit [FiniteDimensional K V] in
lemma opposed_of_opposite {F E : CompleteFlag K V N} (h : F.Opposite E) (i : Fin (N+1)) :
    F.Opposed (E.space i) := by
  unfold Opposed
  simp only [E.rank]
  exact opposite_symm h i

omit [FiniteDimensional K V] in
lemma baseSpace_good {F E : CompleteFlag K V N} (h : F.Opposite E) (i : Fin (N-1)) :
    F.Good (E.baseSpace i) := by
  refine ⟨by simp,by simp; omega,opposed_of_opposite h _⟩

omit [FiniteDimensional K V] in
lemma cosetVertexMap_rank (F E : CompleteFlag K V N) (x : Vertex (F.vertexStabilizers E)) :
    finrank K (F.cosetVertexMap E x) = x.1.val+1 := by
  rcases x with ⟨i,x⟩
  induction x using Quotient.inductionOn with | h g =>
  change finrank K ((E.baseSpace i).map g.val.toLinearMap) = i.val+1
  rw [g.val.finrank_map_eq,baseSpace_rank]

omit [FiniteDimensional K V] in
lemma cosetVertexMap_injective (F E : CompleteFlag K V N) : Function.Injective (F.cosetVertexMap E) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ hxy
  have hr := congrArg (fun W : Submodule K V => finrank K W) hxy
  rw [cosetVertexMap_rank,cosetVertexMap_rank] at hr
  have hij : i = j := Fin.ext (by dsimp at hr; omega)
  subst j
  congr 1
  exact MulAction.injective_ofQuotientStabilizer F.unipotentFlagStabilizer (E.baseSpace i) hxy

lemma unipotent_good (F : CompleteFlag K V N) (g : F.unipotentFlagStabilizer)
    (W : Submodule K V) (hW : F.Good W) : F.Good (g • W) :=
  F.flagStabilizer_good ⟨g.val,g.property.1⟩ W hW

theorem cosetFace_opposed {F E : CompleteFlag K V N} (h : F.Opposite E)
    (s : Finset (Vertex (F.vertexStabilizers E))) (hs : IsFace (F.vertexStabilizers E) s) :
    s.image (F.cosetVertexMap E) ∈ F.complex.faces := by
  classical
  obtain ⟨g,A,rfl⟩ := hs
  have he : (face (F.vertexStabilizers E) g A).image (F.cosetVertexMap E) =
      A.image (fun i => g • E.baseSpace i) := by
    simp only [face,Finset.image_image,Function.comp_def,cosetVertexMap_vertex]
  rw [he]
  constructor
  · intro W hW
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hW
    exact F.unipotent_good g _ (baseSpace_good h i)
  · intro W hW W' hW' _
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hW'
    rcases le_total i j with hij | hji
    · exact Or.inl (Submodule.map_mono (E.mono (by change i.val+1 ≤ j.val+1; exact Nat.add_le_add_right hij 1)))
    · exact Or.inr (Submodule.map_mono (E.mono (by change j.val+1 ≤ i.val+1; exact Nat.add_le_add_right hji 1)))

theorem opposedFace_coset {F E : CompleteFlag K V N} (h : F.Opposite E)
    (s : Finset (Submodule K V)) (hs : s ∈ F.complex.faces) :
    ∃ g : F.unipotentFlagStabilizer, ∃ A : Finset (Fin (N-1)),
      (face (F.vertexStabilizers E) g A).image (F.cosetVertexMap E) = s := by
  classical
  obtain ⟨t,ht,hst⟩ := F.exists_full_face s hs
  obtain ⟨E',hE',htE'⟩ := F.exists_flag_from_face t ht
  obtain ⟨g,hg⟩ := unipotent_transitive h hE'
  let A := Finset.univ.filter (fun i : Fin (N-1) => E'.baseSpace i ∈ s)
  refine ⟨g,A,?_⟩
  simp only [face,Finset.image_image,Function.comp_def,cosetVertexMap_vertex]
  have hg' (i : Fin (N-1)) : g • E.baseSpace i = E'.baseSpace i := hg (properIndex (N:=N) i)
  simp_rw [hg']
  ext W
  constructor
  · intro hW
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hW
    exact (Finset.mem_filter.mp hi).2
  · intro hW
    obtain ⟨i,hi0,hiN,hiW⟩ := (htE' W).mp (hst hW)
    let j : Fin (N-1) := ⟨i.val-1,by omega⟩
    have hji : properIndex (N:=N) j = i := by apply Fin.ext; dsimp [properIndex,j]; omega
    have hjW : E'.baseSpace j = W := by rw [baseSpace,hji,hiW]
    exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hjW]; exact hW⟩,hjW⟩

theorem cosetFace_iff {F E : CompleteFlag K V N} (h : F.Opposite E)
    (s : Finset (Vertex (F.vertexStabilizers E))) :
    IsFace (F.vertexStabilizers E) s ↔ s.image (F.cosetVertexMap E) ∈ F.complex.faces := by
  classical
  constructor
  · exact cosetFace_opposed h s
  · intro hs
    obtain ⟨g,A,he⟩ := opposedFace_coset h _ hs
    refine ⟨g,A,?_⟩
    exact Finset.image_injective (F.cosetVertexMap_injective E) he

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

def oppositeBasisFlag (b : Basis (Fin N) K V) : CompleteFlag K V N where
  space i := span K (Set.range (fun j : Fin i.val => b (tailIndex i j)))
  mono := by
    intro i j hij
    apply span_mono
    rintro v ⟨k,rfl⟩
    refine ⟨⟨j.val-i.val+k.val,by omega⟩,?_⟩
    apply congrArg b
    apply Fin.ext
    dsimp [tailIndex]
    omega
  dimension := by simpa using Module.finrank_eq_card_basis b
  rank i := by
    have hi : Function.Injective (tailIndex i) := by
      intro j k he
      apply Fin.ext
      have hh := congrArg Fin.val he
      dsimp [tailIndex] at hh
      omega
    simpa only [Function.comp_def, Fintype.card_fin] using finrank_span_eq_card (b.linearIndependent.comp _ hi)

omit [FiniteDimensional K V] in
lemma oppositeBasisFlag_adapted (b : Basis (Fin N) K V) (i : Fin N) :
    b i ∈ (oppositeBasisFlag b).space ⟨N-i.val,by omega⟩ := by
  apply Submodule.subset_span
  refine ⟨⟨0,by change 0 < N-i.val; omega⟩,?_⟩
  apply congrArg b
  apply Fin.ext
  dsimp [tailIndex]
  omega

theorem basisFlags_opposite (b : Basis (Fin N) K V) :
    (basisFlag b).Opposite (oppositeBasisFlag b) := by
  intro i
  apply (Submodule.isCompl_iff_disjoint _ _ (by
    rw [(basisFlag b).rank,(oppositeBasisFlag b).rank,(basisFlag b).dimension]
    dsimp; omega)).mpr
  apply disjoint_def.mpr
  intro x hx hy
  apply b.repr.injective
  ext j
  rw [map_zero,Finsupp.zero_apply]
  by_cases hji : j.val < i.val
  · exact ((oppositeBasisFlag b).mem_opposite_flag_iff_repr b
      (oppositeBasisFlag_adapted b) i x).mp hy j hji
  · exact ((basisFlag b).mem_flag_iff_repr b (basisFlag_adapted b) i x).mp hx j (by omega)

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Patterns
attribute [-instance] _root_.OAI.CoboundaryExpanders.Blocks.gammaNormal _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant _root_.OAI.CoboundaryExpanders.MatrixOpposition.cutDecidableEq _root_.OAI.CoboundaryExpanders.MatrixOpposition.cutFinite _root_.OAI.CoboundaryExpanders.MatrixOpposition.cutFintype
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

variable (p : ℕ) [Fact p.Prime]

theorem localGroup_le_cutUpper (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    localGroup p n hn cut ≤ cutUpper p cut := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨j, hj, rfl⟩
  change cycleRoot p n hn j ∈ cutUpper p cut
  rw [cutUpper_iff]
  have hlt : cutRank cut (edgeSource n j) < cutRank cut j := by
    rw [cutRank_lt_iff _ _ _ (edgeSource_ne n hn j)]
    by_cases h0 : j = 0
    · subst j
      have hc : 0 < cut.val := by
        have : cut.val ≠ 0 := fun h => hj (Fin.ext h.symm)
        omega
      simp only [edgeSource, dite_eq_left rfl, Arc, Fin.val_last, Fin.val_zero,
        Nat.not_lt_zero, ite_false]
      omega
    · have hj0 : 0 < j.val := by
        have : j.val ≠ 0 := fun h => h0 (Fin.ext h)
        omega
      have hne : j.val ≠ cut.val := fun h => hj (Fin.ext h)
      simp only [edgeSource, dite_eq_right h0, Arc, Fin.val_mk,
        ite_eq_left (show j.val - 1 < j.val by omega)]
      omega
  intro a b hba
  change (Matrix.transvection (edgeSource n j) j _) a b = _
  have hne : ¬ (edgeSource n j = a ∧ j = b) := by
    rintro ⟨rfl, rfl⟩
    exact (not_lt_of_ge hba) hlt
  simp [Matrix.transvection, hne]

end

section
open CoboundaryExpanders.Construction CoboundaryExpanders.Elementary
variable (p n : ℕ) [Fact p.Prime]

def intersectionGroup (hn : 1 ≤ n) (J : Set (Fin (n + 1))) :
    Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)) :=
  ⨅ cut, ⨅ (_ : cut ∉ J), localGroup p n hn cut

omit [Fact p.Prime] in
theorem mem_intersectionGroup (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)) :
    g ∈ intersectionGroup p n hn J ↔ ∀ cut ∉ J, g ∈ localGroup p n hn cut := by
  simp [intersectionGroup]

omit [Fact p.Prime] in
theorem rootGroup_le_intersection (hn : 1 ≤ n) (J : Set (Fin (n + 1))) :
    rootGroup p n hn J ≤ intersectionGroup p n hn J := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨j, hj, rfl⟩
  change cycleRoot p n hn j ∈ intersectionGroup p n hn J
  rw [mem_intersectionGroup]
  intro cut hc
  exact Subgroup.subset_closure ⟨j, by intro he; subst cut; contradiction, rfl⟩

end

open CoboundaryExpanders.Construction CoboundaryExpanders.Elementary
variable (p n : ℕ) [Fact p.Prime]

theorem entry_nonzero_path (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) (R p))
    (hg : g ∈ intersectionGroup p n hn J) {a b : Fin (n + 1)} (hab : a ≠ b)
    (hne : g a b ≠ 0) : ∀ j, Arc a b j → j ∈ J := by
  intro j hj
  by_contra hjJ
  have hg' := (mem_intersectionGroup p n hn J g).mp hg j hjJ
  have hupper := (cutUpper_iff p j g).mp (localGroup_le_cutUpper p hn j hg')
  have hba : cutRank j b ≤ cutRank j a := by
    apply le_of_not_gt
    rwa [cutRank_lt_iff j a b hab, not_not]
  exact hne ((hupper a b hba).trans (Matrix.one_apply_ne hab))

theorem local_entry_coefficient (hn : 1 ≤ n) (cut : Fin (n + 1))
    (g : localGroup p n hn cut) {a b : Fin (n + 1)}
    (hlt : cutRank cut a < cutRank cut b) :
    ∃ c : ZMod p, g.val a b = pathCoefficient (p := p) (n := n) (a := a) (b := b) c := by
  obtain ⟨c, hc⟩ := localGroup_entry_equation p n hn cut g a b
  refine ⟨c, ?_⟩
  unfold cutPolynomial at hc
  unfold pathCoefficient
  change (if a.val < cut.val then a.val + (n + 1) - cut.val else a.val - cut.val) <
    (if b.val < cut.val then b.val + (n + 1) - cut.val else b.val - cut.val) at hlt
  by_cases ha : a.val < cut.val <;> by_cases hb : b.val < cut.val
  · rw [ite_eq_left ha, ite_eq_left hb] at hc
    have hab : a.val < b.val := by simp only [ite_eq_left ha, ite_eq_left hb] at hlt; omega
    rw [ite_eq_left hab, mul_one]
    apply mul_left_cancel₀ (Polynomial.X_ne_zero (R := ZMod p))
    simpa only [mul_comm Polynomial.X (Polynomial.C c)] using hc
  · simp only [ite_eq_left ha, ite_eq_right hb] at hlt
    omega
  · rw [ite_eq_right ha, ite_eq_left hb, one_mul] at hc
    rw [ite_eq_right (by omega : ¬ a.val < b.val)]
    exact hc
  · rw [ite_eq_right ha, ite_eq_right hb, one_mul, mul_one] at hc
    have hab : a.val < b.val := by simp only [ite_eq_right ha, ite_eq_right hb] at hlt; omega
    rw [ite_eq_left hab, mul_one]
    exact hc

theorem entry_root_mem (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    (cut : Fin (n + 1)) (hcut : cut ∉ J)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) (R p))
    (hg : g ∈ intersectionGroup p n hn J) {a b : Fin (n + 1)} (hab : a ≠ b) :
    E hab (g a b) ∈ rootGroup p n hn J := by
  by_cases hz : g a b = 0
  · simp [hz, E]
  · have hpath := entry_nonzero_path p n hn J g hg hab hz
    have hlt : cutRank cut a < cutRank cut b := by
      rw [cutRank_lt_iff cut a b hab]
      exact fun h => hcut (hpath cut h)
    have hg' := (mem_intersectionGroup p n hn J g).mp hg cut hcut
    obtain ⟨c, hc⟩ := local_entry_coefficient p n hn cut ⟨g, hg'⟩ hlt
    change g a b = _ at hc
    rw [hc]
    exact path_root_mem p n hn J hab hpath c

theorem rootGroup_eq_intersection (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    (hJ : ∃ cut, cut ∉ J) : rootGroup p n hn J = intersectionGroup p n hn J := by
  apply le_antisymm (rootGroup_le_intersection p n hn J)
  obtain ⟨cut, hcut⟩ := hJ
  let e := reindexSL (A := R p) (cutOrder cut)
  let P := (intersectionGroup p n hn J).map e.toMonoidHom
  let H := (rootGroup p n hn J).map e.toMonoidHom
  have hHP : H ≤ P := Subgroup.map_mono (rootGroup_le_intersection p n hn J)
  have hP : ∀ g ∈ P, Upper g := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' := (mem_intersectionGroup p n hn J g).mp hg cut hcut
    exact localGroup_le_cutUpper p hn cut hg'
  have hE : ∀ g ∈ P, ∀ i j (h : i < j), E h.ne (g i j) ∈ H := by
    rintro _ ⟨g, hg, rfl⟩ i j hij
    obtain ⟨a, rfl⟩ := (cutOrder cut).surjective i
    obtain ⟨b, rfl⟩ := (cutOrder cut).surjective j
    have hab : a ≠ b := fun he => hij.ne (congrArg (cutOrder cut) he)
    refine ⟨E hab (g a b), entry_root_mem p n hn J cut hcut g hg hab, ?_⟩
    change reindexSL (cutOrder cut) _ = _
    rw [reindexSL_E]
    congr 1
    exact (reindexSL_apply (cutOrder cut) g a b).symm
  have hPH := upper_subgroup_le P H hHP hP hE
  intro g hg
  have : e g ∈ H := hPH ⟨g, hg, rfl⟩
  obtain ⟨h, hh, he⟩ := this
  exact e.injective he ▸ hh

theorem rootGroup_inter (hn : 1 ≤ n) (J K : Set (Fin (n + 1)))
    (hJ : ∃ cut, cut ∉ J) (hK : ∃ cut, cut ∉ K) :
    rootGroup p n hn J ⊓ rootGroup p n hn K = rootGroup p n hn (J ∩ K) := by
  have hJK : ∃ cut, cut ∉ J ∩ K := by
    obtain ⟨cut, hc⟩ := hJ
    exact ⟨cut, fun h => hc h.1⟩
  rw [rootGroup_eq_intersection p n hn J hJ, rootGroup_eq_intersection p n hn K hK,
    rootGroup_eq_intersection p n hn (J ∩ K) hJK]
  ext g
  simp only [Subgroup.mem_inf, mem_intersectionGroup, Set.mem_inter_iff]
  constructor
  · rintro ⟨hJ', hK'⟩ cut hc
    by_cases h : cut ∈ J
    · exact hK' cut (fun hk => hc ⟨h, hk⟩)
    · exact hJ' cut h
  · intro h
    exact ⟨fun cut hc => h cut (fun hjk => hc hjk.1),
      fun cut hc => h cut (fun hjk => hc hjk.2)⟩

def standardLocalGroup (hn : 1 ≤ n) (J : Set (Fin (n + 1))) :
    Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) (ZMod p)) :=
  Subgroup.closure {g | ∃ j ∈ J, g = E (edgeSource_ne n hn j) (1 : ZMod p)}

theorem rootGroup_image_eq_standard (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    (cut : Fin (n + 1)) (hc : cut ∉ J) :
    (rootGroup p n hn J).map (cutConjugation p n cut) =
      (standardLocalGroup p n hn J).map (Matrix.SpecialLinearGroup.mapGL (Frac p)) := by
  rw [rootGroup, standardLocalGroup, MonoidHom.map_closure, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨E (edgeSource_ne n hn j) 1, ⟨j, hj, rfl⟩, ?_⟩
    have hjc : j ≠ cut := by intro he; subst cut; contradiction
    rw [cutConjugation_root p n hn cut j hjc]
    apply Matrix.GeneralLinearGroup.ext
    intro a b
    rfl
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨cycleRoot p n hn j, ⟨j, hj, rfl⟩, ?_⟩
    have hjc : j ≠ cut := by intro he; subst cut; contradiction
    rw [cutConjugation_root p n hn cut j hjc]
    apply Matrix.GeneralLinearGroup.ext
    intro a b
    rfl

def localStandardEquiv (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    (cut : Fin (n + 1)) (hc : cut ∉ J) :
    rootGroup p n hn J ≃* standardLocalGroup p n hn J :=
  ((rootGroup p n hn J).equivMapOfInjective (cutConjugation p n cut)
      (cutConjugation_injective p n cut)).trans
    ((MulEquiv.subgroupCongr (rootGroup_image_eq_standard p n hn J cut hc)).trans
      ((standardLocalGroup p n hn J).equivMapOfInjective
        (Matrix.SpecialLinearGroup.mapGL (Frac p)) Matrix.SpecialLinearGroup.mapGL_injective).symm)

end CoboundaryExpanders.Patterns

namespace CoboundaryExpanders.MatrixOpposition
open Module Submodule SphericalOpposition SphericalOpposition.CompleteFlag Elementary
open scoped Matrix Pointwise
variable {K : Type} [Field K] {N : ℕ}

abbrev oppFlag (K : Type) [Field K] (N : ℕ) : CompleteFlag K (Fin N → K) N :=
  oppositeBasisFlag (K:=K) (V:=Fin N → K) (Pi.basisFun K (Fin N))

lemma stdFlags_opposite : (stdFlag K N).Opposite (oppFlag K N) :=
  basisFlags_opposite _

def upperToFlag : upperGroup K N →* (stdFlag K N).unipotentFlagStabilizer :=
  { toFun := fun g => ⟨Matrix.SpecialLinearGroup.toLin' g.val,g.property⟩
    map_one' := by apply Subtype.ext; exact map_one _
    map_mul' := fun g h => by apply Subtype.ext; exact map_mul _ _ _ }

lemma upperToFlag_injective : Function.Injective (upperToFlag (K:=K) (N:=N)) := by
  intro g h he
  apply Subtype.ext
  exact Matrix.SpecialLinearGroup.toLin'_injective (congrArg Subtype.val he)

lemma upperToFlag_surjective : Function.Surjective (upperToFlag (K:=K) (N:=N)) := by
  intro e
  let M := LinearMap.toMatrix' e.val.toLinearMap
  have he : Unitriangular (Pi.basisFun K (Fin N)) e.val :=
    (mem_unipotent_iff_unitriangular _ _ (basisFlag_adapted _) _).mp e.property
  have hM (i j : Fin N) (hji : j ≤ i) : M i j = if i = j then 1 else 0 := by
    simpa only [M, LinearMap.toMatrix'_apply, Pi.basisFun_repr, Pi.basisFun_apply, LinearEquiv.coe_coe] using he j i hji
  have ht : M.IsUpperTriangular := by
    intro i j hji
    change j < i at hji
    rw [hM i j hji.le, ite_eq_right hji.ne.symm]
  have hd : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular ht]
    apply Finset.prod_eq_one
    intro i hi
    rw [hM i i le_rfl, ite_eq_left rfl]
  let g : Matrix.SpecialLinearGroup (Fin N) K := ⟨M,hd⟩
  have hge : Matrix.SpecialLinearGroup.toLin' g = e.val := by
    apply LinearEquiv.toLinearMap_injective
    change Matrix.toLin' (LinearMap.toMatrix' e.val.toLinearMap) = e.val.toLinearMap
    exact Matrix.toLin'_toMatrix' _
  have hg : g ∈ upperGroup K N := by
    rw [mem_upperGroup]
    intro i j hji
    change M i j = _
    simpa only [Matrix.one_apply] using hM i j hji
  exact ⟨⟨g,hg⟩,Subtype.ext hge⟩

def upperFlagEquiv : upperGroup K N ≃* (stdFlag K N).unipotentFlagStabilizer :=
  MulEquiv.ofBijective upperToFlag ⟨upperToFlag_injective, upperToFlag_surjective⟩

lemma upper_E {i j : Fin N} (hij : i < j) (c : K) : E hij.ne c ∈ upperGroup K N := by
  rw [mem_upperGroup]
  simpa only [mul_one] using upper_E_mul hij c (g:=1) (fun i j _ => rfl)

lemma preserves_suffix_iff (g : upperGroup K N) (k : Fin (N+1)) :
    ((oppFlag K N).space ⟨N-k.val,by omega⟩).map
      (Matrix.SpecialLinearGroup.toLin' g.val).toLinearMap =
      (oppFlag K N).space ⟨N-k.val,by omega⟩ ↔
    ∀ i j : Fin N, i.val < k.val → k.val ≤ j.val → g.val i j = 0 := by
  let e := Matrix.SpecialLinearGroup.toLin' g.val
  have hm := (oppFlag K N).mem_opposite_flag_iff_repr (Pi.basisFun K (Fin N))
    (oppositeBasisFlag_adapted _) k
  simp only [Pi.basisFun_repr] at hm
  constructor
  · intro h i j hi hj
    have hb : Pi.single j (1:K) ∈ (oppFlag K N).space ⟨N-k.val,by omega⟩ := by
      apply (hm _).mpr
      intro a ha
      simp only [Pi.single_apply, ite_eq_right (show a ≠ j by intro he; subst j; omega)]
    have he' : e (Pi.single j 1) ∈ (oppFlag K N).space ⟨N-k.val,by omega⟩ := by
      rw [← h]
      exact ⟨_,hb,rfl⟩
    have hh := (hm _).mp he' i hi
    simpa only [e, Matrix.SpecialLinearGroup.toLin'_apply,Matrix.toLin'_apply,
      Matrix.mulVec_single_one,Matrix.col_apply] using hh
  · intro h
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v,hv,rfl⟩
      apply (hm _).mpr
      intro i hi
      change (g.val.val *ᵥ v) i = 0
      rw [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hk : k.val ≤ j.val
      · rw [h i j hi hk,zero_mul]
      · rw [(hm v).mp hv j (by omega),mul_zero]
    · exact e.finrank_map_eq _

def suffixStabilizer (K : Type) [Field K] (k : Fin N) :
    Subgroup (Matrix.SpecialLinearGroup (Fin N) K) :=
  (MulAction.stabilizer ((Fin N → K) ≃ₗ[K] (Fin N → K))
    ((oppFlag K N).space ⟨N-k.val,by omega⟩)).comap Matrix.SpecialLinearGroup.toLin'

def patternGroup (K : Type) [Field K] (J : Set (Fin N)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin N) K) :=
  upperGroup K N ⊓ ⨅ k : Fin N, ⨅ (_ : k ∉ J), suffixStabilizer K k

lemma mem_suffixStabilizer (g : Matrix.SpecialLinearGroup (Fin N) K) (k : Fin N) :
    g ∈ suffixStabilizer K k ↔
    ((oppFlag K N).space ⟨N-k.val,by omega⟩).map
      (Matrix.SpecialLinearGroup.toLin' g).toLinearMap =
        (oppFlag K N).space ⟨N-k.val,by omega⟩ := by
  simp only [suffixStabilizer, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  rfl

lemma mem_patternGroup (J : Set (Fin N)) (g : Matrix.SpecialLinearGroup (Fin N) K) :
    g ∈ patternGroup K J ↔ Upper g ∧
      ∀ k : Fin N, k ∉ J → ∀ i j : Fin N,
        i.val < k.val → k.val ≤ j.val → g i j = 0 := by
  simp only [patternGroup,Subgroup.mem_inf,Subgroup.mem_iInf,mem_upperGroup]
  constructor
  · rintro ⟨hg,hs⟩
    refine ⟨hg,fun k hk => ?_⟩
    exact (preserves_suffix_iff ⟨g,(mem_upperGroup g).mpr hg⟩ k.castSucc).mp
      ((mem_suffixStabilizer g k).mp (hs k hk))
  · rintro ⟨hg,hs⟩
    refine ⟨hg,fun k hk => (mem_suffixStabilizer g k).mpr ?_⟩
    exact (preserves_suffix_iff ⟨g,(mem_upperGroup g).mpr hg⟩ k.castSucc).mpr (hs k hk)

def pathGroup (K : Type) [Field K] (J : Set (Fin N)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin N) K) :=
  Subgroup.closure {g | ∃ i j : Fin N, ∃ h : i.val+1 = j.val,
    j ∈ J ∧ g = E (show i ≠ j by intro he; subst j; omega) (1:K)}

lemma adjacent_mem_pathGroup (J : Set (Fin N)) {i j : Fin N}
    (h : i.val+1 = j.val) (hj : j ∈ J) :
    E (show i ≠ j by intro he; subst j; omega) (1:K) ∈ pathGroup K J :=
  Subgroup.subset_closure ⟨i,j,h,hj,rfl⟩

lemma pathGroup_le_pattern (J : Set (Fin N)) : pathGroup K J ≤ patternGroup K J := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i,j,h,hj,rfl⟩
  apply (mem_patternGroup J _).mpr
  refine ⟨(mem_upperGroup _).mp (upper_E (show i < j by change i.val < j.val; omega) 1),?_⟩
  intro k hk a b hak hkb
  have hab : a ≠ b := by intro he; subst b; omega
  have hn : ¬ (a = i ∧ b = j) := by
    rintro ⟨hai,hbj⟩
    have ha := congrArg Fin.val hai
    have hb := congrArg Fin.val hbj
    have he : k = j := by apply Fin.ext; omega
    exact hk (he.symm ▸ hj)
  have hn' : ¬ (i = a ∧ j = b) := fun h => hn ⟨h.1.symm,h.2.symm⟩
  change (1 + Matrix.single i j (1:K)) a b = 0
  simp [Matrix.add_apply,hab,hn']

lemma E_path_one_mem (J : Set (Fin N)) {i j : Fin N} (hij : i < j)
    (hpath : ∀ k : Fin N, i.val < k.val → k.val ≤ j.val → k ∈ J) :
    E hij.ne (1:K) ∈ pathGroup K J := by
  generalize hdiff : j.val-i.val = r
  induction r using Nat.strong_induction_on generalizing i j with
  | h r ih =>
    by_cases hadj : i.val+1 = j.val
    · exact adjacent_mem_pathGroup J hadj (hpath j hij le_rfl)
    · let c : Fin N := ⟨j.val-1,by omega⟩
      have hic : i < c := by change i.val < j.val-1; omega
      have hcj : c.val+1 = j.val := by dsimp [c]; omega
      have hcj' : c < j := by change c.val < j.val; omega
      have hc := ih (c.val-i.val) (by omega) hic
        (fun k hi hk => hpath k hi (hk.trans hcj'.le)) rfl
      simpa only [mul_one] using E_path_mem (pathGroup K J) hic.ne hcj'.ne hij.ne hc
        (adjacent_mem_pathGroup J hcj (hpath j hij le_rfl))

variable (p : ℕ) [Fact p.Prime]

lemma E_path_mem_coeff (J : Set (Fin N)) {i j : Fin N} (hij : i < j)
    (hpath : ∀ k : Fin N, i.val < k.val → k.val ≤ j.val → k ∈ J) (c : ZMod p) :
    E hij.ne c ∈ pathGroup (ZMod p) J := by
  have hc : E hij.ne c = E hij.ne (1:ZMod p) ^ c.val := by
    rw [← E_natCast_mul, ZMod.natCast_zmod_val, mul_one]
  rw [hc]
  exact (pathGroup (ZMod p) J).pow_mem (E_path_one_mem J hij hpath) _

theorem pathGroup_eq_pattern (J : Set (Fin N)) :
    pathGroup (ZMod p) J = patternGroup (ZMod p) J := by
  apply le_antisymm (pathGroup_le_pattern J)
  apply upper_subgroup_le _ _ (pathGroup_le_pattern J)
  · intro g hg
    exact ((mem_patternGroup J g).mp hg).1
  · intro g hg i j hij
    by_cases hzero : g i j = 0
    · rw [hzero]
      simpa only [E,Matrix.SpecialLinearGroup.transvection_coeff_zero] using (pathGroup (ZMod p) J).one_mem
    · apply E_path_mem_coeff p J hij
      intro k hik hkj
      by_contra hk
      exact hzero (((mem_patternGroup J g).mp hg).2 k hk i j hik hkj)

lemma pathGroup_inter (J L : Set (Fin N)) :
    pathGroup (ZMod p) J ⊓ pathGroup (ZMod p) L = pathGroup (ZMod p) (J ∩ L) := by
  simp only [pathGroup_eq_pattern]
  ext g
  simp only [Subgroup.mem_inf,mem_patternGroup,Set.mem_inter_iff,not_and_or]
  constructor
  · rintro ⟨⟨hu,hJ⟩,⟨_,hL⟩⟩
    exact ⟨hu,fun k hk => hk.elim (hJ k) (hL k)⟩
  · rintro ⟨hu,h⟩
    exact ⟨⟨hu,fun k hk => h k (Or.inl hk)⟩,⟨hu,fun k hk => h k (Or.inr hk)⟩⟩

lemma pathGroup_delete (k : Fin N) :
    pathGroup (ZMod p) ({k}ᶜ) = upperGroup (ZMod p) N ⊓ suffixStabilizer (ZMod p) k := by
  rw [pathGroup_eq_pattern]
  ext g
  simp [patternGroup]

end CoboundaryExpanders.MatrixOpposition

namespace CoboundaryExpanders.Patterns

section
open Construction Elementary MatrixOpposition SphericalOpposition.CompleteFlag
open scoped Matrix Pointwise
variable {n : ℕ}

lemma cutOrder_edgeSource (cut j : Fin (n+1)) (hj : j ≠ cut) :
    (cutOrder cut (edgeSource n j)).val + 1 = (cutOrder cut j).val := by
  have hjc : j.val ≠ cut.val := fun h => hj (Fin.ext h)
  by_cases hj0 : j = 0
  · subst j
    have hc : 0 < cut.val := Nat.pos_of_ne_zero (Ne.symm hjc)
    change (cutRank cut (Fin.last n)).val + 1 = (cutRank cut 0).val
    change (if n < cut.val then n+(n+1)-cut.val else n-cut.val)+1 =
      (if 0 < cut.val then 0+(n+1)-cut.val else 0-cut.val)
    rw [ite_eq_right (by omega),ite_eq_left hc]
    omega
  · have hjv : 0 < j.val := by apply Nat.pos_of_ne_zero; intro h; exact hj0 (Fin.ext h)
    change (cutRank cut (edgeSource n j)).val + 1 = (cutRank cut j).val
    simp only [edgeSource,dite_eq_right hj0,cutRank,Fin.val_mk]
    split_ifs <;> omega

variable (p n : ℕ) [Fact p.Prime]

theorem standard_reindex_eq_path (hn : 1 ≤ n) (J : Set (Fin (n+1)))
    (cut : Fin (n+1)) (hc : cut ∉ J) :
    (standardLocalGroup p n hn J).map (reindexSL (cutOrder cut)).toMonoidHom =
      pathGroup (ZMod p) ((cutOrder cut) '' J) := by
  rw [standardLocalGroup,MonoidHom.map_closure,pathGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨_,⟨j,hj,rfl⟩,rfl⟩
    have hjc : j ≠ cut := by intro he; exact hc (he ▸ hj)
    refine ⟨cutOrder cut (edgeSource n j),cutOrder cut j,cutOrder_edgeSource cut j hjc,
      ⟨j,hj,rfl⟩,?_⟩
    exact reindexSL_E _ _ _
  · rintro ⟨i,j,h,hj,rfl⟩
    obtain ⟨k,hk,rfl⟩ := hj
    have hkc : k ≠ cut := by intro he; exact hc (he ▸ hk)
    have hi : i = cutOrder cut (edgeSource n k) := by
      apply Fin.ext
      have := cutOrder_edgeSource cut k hkc
      omega
    refine ⟨E (edgeSource_ne n hn k) 1,⟨k,hk,rfl⟩,?_⟩
    change reindexSL (cutOrder cut) (E (edgeSource_ne n hn k) 1) = _
    subst i
    exact reindexSL_E _ _ _

lemma cutOrder_image_compl (cut : Fin (n+1)) :
    (cutOrder cut) '' ({cut}ᶜ : Set (Fin (n+1))) = ({0}ᶜ : Set (Fin (n+1))) := by
  ext j
  constructor
  · rintro ⟨i,hi,rfl⟩
    simpa only [Set.mem_compl_iff,Set.mem_singleton_iff,← cutOrder_cut cut,
      (cutOrder cut).injective.eq_iff] using hi
  · intro hj
    refine ⟨(cutOrder cut).symm j,?_,(cutOrder cut).apply_symm_apply j⟩
    intro hi
    have hh : j = 0 := by
      have he := congrArg (cutOrder cut) hi
      simpa using he
    exact hj hh

lemma pathGroup_compl_zero :
    pathGroup (ZMod p) ({(0:Fin (n+1))}ᶜ) = upperGroup (ZMod p) (n+1) := by
  rw [pathGroup_eq_pattern]
  ext g
  simp [mem_patternGroup]

theorem standard_max_reindex (hn : 1 ≤ n) (cut : Fin (n+1)) :
    (standardLocalGroup p n hn ({cut}ᶜ)).map (reindexSL (cutOrder cut)).toMonoidHom =
      upperGroup (ZMod p) (n+1) := by
  rw [standard_reindex_eq_path p n hn _ cut (by simp),cutOrder_image_compl,pathGroup_compl_zero]

def standardMaxFlagEquiv (hn : 1 ≤ n) (cut : Fin (n+1)) :
    standardLocalGroup p n hn ({cut}ᶜ) ≃*
      (stdFlag (ZMod p) (n+1)).unipotentFlagStabilizer :=
  ((standardLocalGroup p n hn ({cut}ᶜ)).equivMapOfInjective
    (reindexSL (cutOrder cut)).toMonoidHom (reindexSL (cutOrder cut)).injective).trans
      ((MulEquiv.subgroupCongr (standard_max_reindex p n hn cut)).trans upperFlagEquiv)

def localFlagEquiv (hn : 1 ≤ n) (cut : Fin (n+1)) :
    localGroup p n hn cut ≃* (stdFlag (ZMod p) (n+1)).unipotentFlagStabilizer :=
  (MulEquiv.subgroupCongr (rootGroup_compl_singleton p n hn cut)).symm.trans
    ((localStandardEquiv p n hn ({cut}ᶜ) cut (by simp)).trans
      (standardMaxFlagEquiv p n hn cut))

end

section
open Construction Elementary MatrixOpposition SphericalOpposition.CompleteFlag
open scoped Matrix Pointwise
variable (p n : ℕ) [Fact p.Prime]

lemma localStandardEquiv_equation (hn : 1 ≤ n) (J : Set (Fin (n+1)))
    (cut : Fin (n+1)) (hc : cut ∉ J) (g : rootGroup p n hn J) :
    Matrix.SpecialLinearGroup.mapGL (Frac p) (localStandardEquiv p n hn J cut hc g).val =
      cutConjugation p n cut g.val := by
  exact congrArg Subtype.val
    (((standardLocalGroup p n hn J).equivMapOfInjective
      (Matrix.SpecialLinearGroup.mapGL (Frac p)) Matrix.SpecialLinearGroup.mapGL_injective).apply_symm_apply _)

lemma localStandardEquiv_mem_iff (hn : 1 ≤ n) (J L : Set (Fin (n+1)))
    (cut : Fin (n+1)) (hcJ : cut ∉ J) (hcL : cut ∉ L)
    (g : rootGroup p n hn J) :
    (localStandardEquiv p n hn J cut hcJ g).val ∈ standardLocalGroup p n hn L ↔
      g.val ∈ rootGroup p n hn L := by
  have he := localStandardEquiv_equation p n hn J cut hcJ g
  have hm := rootGroup_image_eq_standard p n hn L cut hcL
  constructor
  · intro hg
    have hh : cutConjugation p n cut g.val ∈
        (standardLocalGroup p n hn L).map (Matrix.SpecialLinearGroup.mapGL (Frac p)) := by
      rw [← he]
      exact Subgroup.mem_map_of_mem _ hg
    rw [← hm] at hh
    obtain ⟨x,hx,hxg⟩ := hh
    have hxg' := cutConjugation_injective p n cut hxg
    exact hxg' ▸ hx
  · intro hg
    have hh : Matrix.SpecialLinearGroup.mapGL (Frac p)
        (localStandardEquiv p n hn J cut hcJ g).val ∈
        (rootGroup p n hn L).map (cutConjugation p n cut) := by
      rw [he]
      exact Subgroup.mem_map_of_mem _ hg
    rw [hm] at hh
    obtain ⟨x,hx,hxg⟩ := hh
    have hxg' := Matrix.SpecialLinearGroup.mapGL_injective hxg
    exact hxg' ▸ hx

lemma reindex_mem_iff (hn : 1 ≤ n) (J : Set (Fin (n+1))) (cut : Fin (n+1))
    (hc : cut ∉ J) (g : Matrix.SpecialLinearGroup (Fin (n+1)) (ZMod p)) :
    reindexSL (cutOrder cut) g ∈ pathGroup (ZMod p) ((cutOrder cut) '' J) ↔
      g ∈ standardLocalGroup p n hn J := by
  rw [← standard_reindex_eq_path p n hn J cut hc]
  constructor
  · rintro ⟨x,hx,hxg⟩
    exact ((reindexSL (cutOrder cut)).injective hxg) ▸ hx
  · intro hg
    exact Subgroup.mem_map_of_mem _ hg

lemma two_cuts_image (cut j : Fin (n+1)) :
    cutOrder cut '' (({cut}ᶜ ∩ {j}ᶜ : Set (Fin (n+1)))) =
      ({0}ᶜ ∩ {cutOrder cut j}ᶜ) := by
  rw [Set.image_inter (cutOrder cut).injective,cutOrder_image_compl]
  congr 1
  rw [Set.image_compl_eq (cutOrder cut).bijective,Set.image_singleton]

lemma pathGroup_delete_zero (k : Fin (n+1)) :
    pathGroup (ZMod p) (({0}ᶜ ∩ {k}ᶜ : Set (Fin (n+1)))) =
      upperGroup (ZMod p) (n+1) ⊓ suffixStabilizer (ZMod p) k := by
  rw [← pathGroup_inter,pathGroup_compl_zero,pathGroup_delete,inf_of_le_right inf_le_left]

lemma standardMaxFlagEquiv_value (hn : 1 ≤ n) (cut : Fin (n+1))
    (g : standardLocalGroup p n hn ({cut}ᶜ)) :
    (standardMaxFlagEquiv p n hn cut g).val =
      Matrix.SpecialLinearGroup.toLin' (reindexSL (cutOrder cut) g.val) := rfl

theorem standardMaxFlagEquiv_stabilizer (hn : 1 ≤ n) (cut j : Fin (n+1))
    (g : standardLocalGroup p n hn ({cut}ᶜ)) :
    (standardMaxFlagEquiv p n hn cut g).val ∈
      MulAction.stabilizer ((Fin (n+1) → ZMod p) ≃ₗ[ZMod p] (Fin (n+1) → ZMod p))
        ((oppFlag (ZMod p) (n+1)).space ⟨n+1-(cutOrder cut j).val,by omega⟩) ↔
      g.val ∈ standardLocalGroup p n hn ({cut}ᶜ ∩ {j}ᶜ) := by
  rw [standardMaxFlagEquiv_value]
  change reindexSL (cutOrder cut) g.val ∈ suffixStabilizer (ZMod p) (cutOrder cut j) ↔ _
  have hu : reindexSL (cutOrder cut) g.val ∈ upperGroup (ZMod p) (n+1) := by
    rw [← standard_max_reindex p n hn cut]
    exact Subgroup.mem_map_of_mem _ g.property
  rw [← reindex_mem_iff p n hn _ cut (by simp),two_cuts_image,pathGroup_delete_zero]
  exact (and_iff_right hu).symm

theorem localFlagEquiv_stabilizer (hn : 1 ≤ n) (cut j : Fin (n+1))
    (g : localGroup p n hn cut) :
    (localFlagEquiv p n hn cut g).val ∈
      MulAction.stabilizer ((Fin (n+1) → ZMod p) ≃ₗ[ZMod p] (Fin (n+1) → ZMod p))
        ((oppFlag (ZMod p) (n+1)).space ⟨n+1-(cutOrder cut j).val,by omega⟩) ↔
      g.val ∈ localGroup p n hn j := by
  let gg : rootGroup p n hn ({cut}ᶜ) :=
    (MulEquiv.subgroupCongr (rootGroup_compl_singleton p n hn cut)).symm g
  change (standardMaxFlagEquiv p n hn cut
    (localStandardEquiv p n hn ({cut}ᶜ) cut (by simp) gg)).val ∈ _ ↔ _
  rw [standardMaxFlagEquiv_stabilizer,
    localStandardEquiv_mem_iff p n hn _ _ cut (by simp) (by simp)]
  change g.val ∈ rootGroup p n hn ({cut}ᶜ ∩ {j}ᶜ) ↔ _
  rw [← rootGroup_inter p n hn ({cut}ᶜ) ({j}ᶜ) ⟨cut,by simp⟩ ⟨j,by simp⟩,
    rootGroup_compl_singleton,rootGroup_compl_singleton]
  exact and_iff_right g.property

end

variable {n : ℕ}

lemma cutOrder_pos (cut j : Fin (n+1)) (hj : j ≠ cut) : 0 < (cutOrder cut j).val := by
  by_contra h
  have he : cutOrder cut j = 0 := Fin.ext (Nat.eq_zero_of_not_pos h)
  rw [← cutOrder_cut cut] at he
  exact hj ((cutOrder cut).injective he)

def localTypeIndex (cut : Fin (n+1)) (j : {j : Fin (n+1) // j ≠ cut}) : Fin n :=
  ⟨n-(cutOrder cut j.val).val,by have := cutOrder_pos cut j.val j.property; omega⟩

lemma localTypeIndex_bijective (cut : Fin (n+1)) : Function.Bijective (localTypeIndex cut) := by
  constructor
  · intro i j he
    have h := congrArg Fin.val he
    apply Subtype.ext
    apply (cutOrder cut).injective
    apply Fin.ext
    dsimp [localTypeIndex] at h
    have hi := (cutOrder cut i.val).isLt
    have hj := (cutOrder cut j.val).isLt
    omega
  · intro i
    let k : Fin (n+1) := ⟨n-i.val,by omega⟩
    have hk : k ≠ 0 := by intro he; have h := congrArg Fin.val he; dsimp [k] at h; omega
    let j : Fin (n+1) := (cutOrder cut).symm k
    have hj : j ≠ cut := by
      intro he
      have hh := congrArg (cutOrder cut) he
      have hkj : cutOrder cut j = k := (cutOrder cut).apply_symm_apply k
      rw [hkj,cutOrder_cut] at hh
      exact hk hh
    refine ⟨⟨j,hj⟩,?_⟩
    apply Fin.ext
    change n-(cutOrder cut ((cutOrder cut).symm k)).val = i.val
    rw [(cutOrder cut).apply_symm_apply]
    dsimp [k]
    omega

def localTypeEquiv (cut : Fin (n+1)) : {j : Fin (n+1) // j ≠ cut} ≃ Fin n :=
  Equiv.ofBijective (localTypeIndex cut) (localTypeIndex_bijective cut)

lemma localTypeEquiv_rank (cut : Fin (n+1)) (j : {j : Fin (n+1) // j ≠ cut}) :
    (localTypeEquiv cut j).val+1 = n+1-(cutOrder cut j.val).val := by
  change n-(cutOrder cut j.val).val+1 = _
  have h := (cutOrder cut j.val).isLt
  omega

end CoboundaryExpanders.Patterns

namespace CoboundaryExpanders.MatrixOpposition

section
open Elementary
open scoped Matrix BigOperators
variable {K : Type} [Field K] {a b : ℕ}

lemma blockMatrix_upper (g : upperGroup K a) (h : upperGroup K b) :
    ∀ i j : Fin (a+b), j ≤ i → blockMatrix g.val.val h.val.val i j = (1 : Matrix _ _ K) i j := by
  have hg := (mem_upperGroup _).mp g.property
  have hh := (mem_upperGroup _).mp h.property
  intro i j
  induction i using Fin.addCases <;> induction j using Fin.addCases
  · intro hji
    simpa [Matrix.one_apply] using hg _ _ (by simpa only [Fin.le_def,Fin.val_castAdd,Fin.val_natAdd,Nat.add_le_add_iff_left] using hji)
  · intro hji
    have hv := Fin.le_iff_val_le_val.mp hji
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  · intro _
    rw [blockMatrix_rl,Matrix.one_apply,ite_eq_right]
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  · intro hji
    simpa [Matrix.one_apply] using hh _ _ (by simpa only [Fin.le_def,Fin.val_castAdd,Fin.val_natAdd,Nat.add_le_add_iff_left] using hji)

def blockUpper : upperGroup K a × upperGroup K b →* upperGroup K (a+b) where
  toFun gh := ⟨⟨blockMatrix gh.1.val.val gh.2.val.val,by
    rw [blockMatrix_det,gh.1.val.property,gh.2.val.property,mul_one]⟩,
    (mem_upperGroup _).mpr (blockMatrix_upper gh.1 gh.2)⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact blockMatrix_one
  map_mul' g h := by apply Subtype.ext; apply Subtype.ext; exact blockMatrix_mul _ _ _ _

lemma blockUpper_injective : Function.Injective (blockUpper (K:=K) (a:=a) (b:=b)) := by
  intro g h he
  have hh := congrArg (fun x : upperGroup K (a+b) => x.val.val) he
  change blockMatrix g.1.val.val g.2.val.val = blockMatrix h.1.val.val h.2.val.val at hh
  apply Prod.ext
  · apply Subtype.ext; apply Subtype.ext
    ext i j
    simpa only [blockMatrix_ll] using congrArg (fun M => M (i.castAdd b) (j.castAdd b)) hh
  · apply Subtype.ext; apply Subtype.ext
    ext i j
    simpa only [blockMatrix_rr] using congrArg (fun M => M (i.natAdd a) (j.natAdd a)) hh

lemma upper_submatrix {c : ℕ} (g : upperGroup K (a+b)) (e : Fin c ↪o Fin (a+b)) :
    ∃ h : upperGroup K c, h.val.val = g.val.val.submatrix e e := by
  let M := g.val.val.submatrix e e
  have hg := (mem_upperGroup _).mp g.property
  have hM (i j : Fin c) (hji : j ≤ i) : M i j = (1 : Matrix _ _ K) i j := by
    simpa [M,Matrix.submatrix_apply,Matrix.one_apply,e.injective.eq_iff] using hg (e i) (e j) (e.monotone hji)
  have ht : M.IsUpperTriangular := by
    intro i j hji
    change j < i at hji
    rw [hM i j hji.le,Matrix.one_apply,ite_eq_right hji.ne.symm]
  have hd : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular ht]
    apply Finset.prod_eq_one
    intro i _
    rw [hM i i le_rfl,Matrix.one_apply,ite_eq_left rfl]
  exact ⟨⟨⟨M,hd⟩,(mem_upperGroup _).mpr hM⟩,rfl⟩

theorem range_blockUpper (g : upperGroup K (a+b)) :
    g ∈ (blockUpper (K:=K) (a:=a) (b:=b)).range ↔
      ∀ i j : Fin (a+b), i.val < a → a ≤ j.val → g.val i j = 0 := by
  constructor
  · rintro ⟨⟨g,h⟩,rfl⟩ i j hi hj
    induction i using Fin.addCases <;> induction j using Fin.addCases
    · simp only [Fin.val_castAdd] at hj; omega
    · exact blockMatrix_lr _ _ _ _
    · simp only [Fin.val_natAdd] at hi; omega
    · simp only [Fin.val_natAdd] at hi; omega
  · intro hx
    let el : Fin a ↪o Fin (a+b) := ⟨⟨Fin.castAdd b,Fin.castAdd_injective a b⟩,by intro i j; rfl⟩
    let er : Fin b ↪o Fin (a+b) := ⟨⟨Fin.natAdd a,Fin.natAdd_injective b a⟩,by intro i j; simp⟩
    obtain ⟨gl,hgl⟩ := upper_submatrix g el
    obtain ⟨gr,hgr⟩ := upper_submatrix g er
    refine ⟨(gl,gr),?_⟩
    apply Subtype.ext; apply Subtype.ext
    ext i j
    change blockMatrix gl.val.val gr.val.val i j = g.val.val i j
    induction i using Fin.addCases <;> induction j using Fin.addCases
    · rw [blockMatrix_ll,hgl]; rfl
    · rw [blockMatrix_lr,hx _ _ (by simp) (by simp)]
    · rw [blockMatrix_rl,(mem_upperGroup _).mp g.property _ _ (by
        apply Fin.le_iff_val_le_val.mpr; simp only [Fin.val_natAdd,Fin.val_castAdd]; omega)]
      rw [Matrix.one_apply,ite_eq_right]
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    · rw [blockMatrix_rr,hgr]; rfl

def blockRangeEquiv : (upperGroup K a × upperGroup K b) ≃* (blockUpper (K:=K) (a:=a) (b:=b)).range :=
  MonoidHom.ofInjective blockUpper_injective

end

open Elementary SphericalOpposition SphericalOpposition.CompleteFlag
open scoped Matrix Pointwise
variable {K : Type} [Field K] {a b N : ℕ}

def suffixGroup (K : Type) [Field K] (N : ℕ) (cut : Fin (N+1)) : Subgroup (upperGroup K N) :=
  (MulAction.stabilizer ( (Fin N → K) ≃ₗ[K] (Fin N → K))
    ((oppFlag K N).space ⟨N-cut.val,by omega⟩)).comap
      (Matrix.SpecialLinearGroup.toLin'.comp (upperGroup K N).subtype)

@[simp] lemma mem_suffixGroup (g : upperGroup K N) (cut : Fin (N+1)) :
    g ∈ suffixGroup K N cut ↔
      ∀ i j : Fin N, i.val < cut.val → cut.val ≤ j.val → g.val i j = 0 := by
  change Matrix.SpecialLinearGroup.toLin' g.val •
    ((oppFlag K N).space ⟨N-cut.val,by omega⟩) = _ ↔ _
  exact preserves_suffix_iff g cut

lemma range_blockUpper_eq_suffixGroup :
    (blockUpper (K:=K) (a:=a) (b:=b)).range = suffixGroup K (a+b) ⟨a,by omega⟩ := by
  ext g
  rw [range_blockUpper,mem_suffixGroup]

def blockSuffixEquiv : (upperGroup K a × upperGroup K b) ≃*
    suffixGroup K (a+b) ⟨a,by omega⟩ :=
  blockRangeEquiv.trans (MulEquiv.subgroupCongr range_blockUpper_eq_suffixGroup)

@[simp] lemma blockSuffixEquiv_val (g : upperGroup K a × upperGroup K b) :
    (blockSuffixEquiv g).val = blockUpper g := rfl

lemma blockUpper_suffix_left (g : upperGroup K a × upperGroup K b) (cut : Fin (a+1)) :
    blockUpper g ∈ suffixGroup K (a+b) ⟨cut.val,by omega⟩ ↔
      g.1 ∈ suffixGroup K a cut := by
  simp only [mem_suffixGroup]
  constructor
  · intro h i j hi hj
    have he := h (i.castAdd b) (j.castAdd b) hi hj
    change blockMatrix g.1.val.val g.2.val.val (i.castAdd b) (j.castAdd b) = 0 at he
    simpa only [blockMatrix_ll] using he
  · intro h i j hi hj
    change blockMatrix g.1.val.val g.2.val.val i j = 0
    induction i using Fin.addCases <;> induction j using Fin.addCases
    · rw [blockMatrix_ll]
      exact h _ _ hi hj
    · exact blockMatrix_lr _ _ _ _
    · exact blockMatrix_rl _ _ _ _
    · simp only [Fin.val_natAdd] at hi
      omega

lemma blockUpper_suffix_right (g : upperGroup K a × upperGroup K b) (cut : Fin (b+1)) :
    blockUpper g ∈ suffixGroup K (a+b) ⟨a+cut.val,by omega⟩ ↔
      g.2 ∈ suffixGroup K b cut := by
  simp only [mem_suffixGroup]
  constructor
  · intro h i j hi hj
    have he := h (i.natAdd a) (j.natAdd a) (by simpa using hi) (by simpa using hj)
    change blockMatrix g.1.val.val g.2.val.val (i.natAdd a) (j.natAdd a) = 0 at he
    simpa only [blockMatrix_rr] using he
  · intro h i j hi hj
    change blockMatrix g.1.val.val g.2.val.val i j = 0
    induction i using Fin.addCases <;> induction j using Fin.addCases
    · simp only [Fin.val_castAdd] at hj
      omega
    · exact blockMatrix_lr _ _ _ _
    · exact blockMatrix_rl _ _ _ _
    · rw [blockMatrix_rr]
      exact h _ _ (by simpa using hi) (by simpa using hj)

def cutGroups (K : Type) [Field K] (N : ℕ) (c : Cut N) : Subgroup (upperGroup K N) :=
  suffixGroup K N ⟨c.val,by have h := c.property; omega⟩

def cutSplitEquiv : (Cut a ⊕ Cut b) ≃ {c : Cut (a+b) // c.val ≠ a} where
  toFun := fun c => match c with
    | Sum.inl c => ⟨⟨c.val,by have h := c.property; omega⟩,by change c.val ≠ a; have h := c.property; omega⟩
    | Sum.inr c => ⟨⟨a+c.val,by have h := c.property; omega⟩,by change a+c.val ≠ a; have h := c.property; omega⟩
  invFun := fun c => if h : c.val.val < a then
    Sum.inl ⟨c.val.val, c.val.property.1,h⟩
    else Sum.inr ⟨c.val.val-a,by have h' := c.val.property; have hn := c.property; omega⟩
  left_inv := by
    intro c
    cases c with
    | inl c =>
      simp only [c.property.2,dite_eq_left]
    | inr c =>
      dsimp only
      rw [dite_eq_right (by omega : ¬ a+c.val < a)]
      congr 1
      apply Subtype.ext
      dsimp
      omega
  right_inv := by
    intro c
    dsimp only
    split_ifs with h
    · rfl
    · apply Subtype.ext; apply Subtype.ext
      have h' := c.val.property
      have hn := c.property
      dsimp
      omega

lemma blockSuffix_system (g : upperGroup K a × upperGroup K b)
    (c : Cut a ⊕ Cut b) :
    blockSuffixEquiv g ∈ (cutGroups K (a+b) (cutSplitEquiv c).val).comap
      (suffixGroup K (a+b) ⟨a,Nat.lt_succ_of_le (Nat.le_add_right a b)⟩).subtype ↔
    match c with
    | Sum.inl c => g.1 ∈ cutGroups K a c
    | Sum.inr c => g.2 ∈ cutGroups K b c := by
  cases c with
  | inl c => exact blockUpper_suffix_left g ⟨c.val,by have h := c.property; omega⟩
  | inr c => exact blockUpper_suffix_right g ⟨c.val,by have h := c.property; omega⟩

end CoboundaryExpanders.MatrixOpposition

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Links
attribute [-instance] _root_.OAI.CoboundaryExpanders.Blocks.gammaNormal _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.TypedCosetFaces.complexInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.kernelInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexMulAction
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

def reducedFlagEquiv (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1)) :
    reducedLocalGroup p n hn m cut ≃*
      (stdFlag (ZMod p) (n+1)).unipotentFlagStabilizer :=
  (localReducedEquiv p n hn hm cut).symm.trans (localFlagEquiv p n hn cut)

lemma reducedFlagEquiv_stabilizer (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (cut j : Fin (n+1)) (q : reducedLocalGroup p n hn m cut) :
    (reducedFlagEquiv p n hn hm cut q).val ∈
      MulAction.stabilizer ((Fin (n+1) → ZMod p) ≃ₗ[ZMod p] (Fin (n+1) → ZMod p))
        ((oppFlag (ZMod p) (n+1)).space ⟨n+1-(cutOrder cut j).val,by omega⟩) ↔
      q.val ∈ reducedLocalGroup p n hn m j := by
  change (localFlagEquiv p n hn cut ((localReducedEquiv p n hn hm cut).symm q)).val ∈ _ ↔ _
  rw [localFlagEquiv_stabilizer]
  have he : (localReducedHom p n hn m cut ((localReducedEquiv p n hn hm cut).symm q)).val = q.val :=
    congrArg Subtype.val ((localReducedEquiv p n hn hm cut).apply_symm_apply q)
  exact (localReducedHom_mem_iff p n hn hm cut j
    ((localReducedEquiv p n hn hm cut).symm q)).symm.trans (by rw [he])

end

section
open Patterns MatrixOpposition TypedCosetFaces SphericalOpposition.CompleteFlag
open scoped Pointwise
variable (p n : ℕ) [Fact p.Prime]

lemma quotientLinkGroups_correspond (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (cut : Fin (n+1)) (j : {j : Fin (n+1) // j ≠ cut})
    (q : reducedLocalGroup p n hn m cut) :
    q ∈ quotientLinkGroups p n hn m cut j ↔
      reducedFlagEquiv p n hn hm cut q ∈
        (stdFlag (ZMod p) (n+1)).vertexStabilizers (oppFlag (ZMod p) (n+1))
          (localTypeEquiv cut j) := by
  change q.val ∈ reducedLocalGroup p n hn m j.val ↔
    reducedFlagEquiv p n hn hm cut q ∈ MulAction.stabilizer _
      ((oppFlag (ZMod p) (n+1)).baseSpace (localTypeEquiv cut j))
  have hr : properIndex (N:=n+1) (localTypeEquiv cut j) =
      (⟨n+1-(cutOrder cut j.val).val,by omega⟩ : Fin (n+2)) :=
    Fin.ext (localTypeEquiv_rank cut j)
  rw [baseSpace,hr]
  rw [MulAction.mem_stabilizer_iff]
  change q.val ∈ reducedLocalGroup p n hn m j.val ↔
    (reducedFlagEquiv p n hn hm cut q).val •
      (oppFlag (ZMod p) (n+1)).space ⟨n+1-(cutOrder cut j.val).val,by omega⟩ =
      (oppFlag (ZMod p) (n+1)).space ⟨n+1-(cutOrder cut j.val).val,by omega⟩
  exact (reducedFlagEquiv_stabilizer p n hn hm cut j.val q).symm

def quotientLinkVertexModel (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1)) :
    Vertex (quotientLinkGroups p n hn m cut) → Submodule (ZMod p) (Fin (n+1) → ZMod p) :=
  ((stdFlag (ZMod p) (n+1)).cosetVertexMap (oppFlag (ZMod p) (n+1))) ∘
    isoVertex (quotientLinkGroups p n hn m cut)
      ((stdFlag (ZMod p) (n+1)).vertexStabilizers (oppFlag (ZMod p) (n+1)))
      (reducedFlagEquiv p n hn hm cut) (localTypeEquiv cut)
      (quotientLinkGroups_correspond p n hn hm cut)

lemma quotientLinkVertexModel_injective (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1)) :
    Function.Injective (quotientLinkVertexModel p n hn hm cut) :=
  ((stdFlag (ZMod p) (n+1)).cosetVertexMap_injective (oppFlag (ZMod p) (n+1))).comp
    (isoVertex_injective _ _ _ _ _)

theorem quotientLinkFace_iff (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1))
    (s : Finset (Vertex (quotientLinkGroups p n hn m cut))) :
    IsFace (quotientLinkGroups p n hn m cut) s ↔
      s.image (quotientLinkVertexModel p n hn hm cut) ∈
        (stdFlag (ZMod p) (n+1)).complex.faces := by
  unfold quotientLinkVertexModel
  rw [← Finset.image_image,← cosetFace_iff stdFlags_opposite,isoFace_iff]

theorem quotientLinkFace_surjective (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1))
    (s : Finset (Submodule (ZMod p) (Fin (n+1) → ZMod p)))
    (hs : s ∈ (stdFlag (ZMod p) (n+1)).complex.faces) :
    ∃ t : Finset (Vertex (quotientLinkGroups p n hn m cut)),
      IsFace (quotientLinkGroups p n hn m cut) t ∧
      t.image (quotientLinkVertexModel p n hn hm cut) = s := by
  obtain ⟨g,A,hg⟩ := opposedFace_coset stdFlags_opposite s hs
  let e := reducedFlagEquiv p n hn hm cut
  let r := localTypeEquiv cut
  refine ⟨face (quotientLinkGroups p n hn m cut) (e.symm g) (A.image r.symm),⟨_,_,rfl⟩,?_⟩
  unfold quotientLinkVertexModel
  rw [← Finset.image_image,isoFace_image,e.apply_symm_apply]
  have hi : (A.image r.symm).image r = A := by ext j; simp
  rw [hi]
  exact hg

end

open InfiniteChains InfiniteChains.Cone TypedCosetFaces SphericalOpposition.CompleteFlag
open Patterns MatrixOpposition
variable (p n : ℕ) [Fact p.Prime]

def sphericalLinkModel (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1)) :
    FaceModel (TypedCosetFaces.complex (quotientLinkGroups p n hn m cut))
      (stdFlag (ZMod p) (n+1)).complex where
  vertex := quotientLinkVertexModel p n hn hm cut
  injective := quotientLinkVertexModel_injective p n hn hm cut
  face_iff := fun s => (quotientLinkFace_iff p n hn hm cut s).symm
  cover := fun t ht => quotientLinkFace_surjective p n hn hm cut t ht

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.InfiniteChains
namespace Complex
variable {V : Type} [DecidableEq V] (X : CoboundaryExpanders.InfiniteChains.Complex V)

def faceLink (s : Finset V) (hs : s ∈ X.faces) : CoboundaryExpanders.InfiniteChains.Complex V where
  faces := {a | Disjoint s a ∧ s ∪ a ∈ X.faces}
  empty_mem := ⟨Finset.disjoint_empty_right _,by simpa using hs⟩
  downward := by
    intro a b ha hb
    exact ⟨Finset.disjoint_left.mpr (fun v hv hv' => Finset.disjoint_left.mp ha.1 hv (hb hv')),
      X.downward ha.2 (Finset.union_subset_union (Finset.Subset.refl _) hb)⟩

end Complex

open Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]
attribute [local instance] Classical.propDecidable

namespace Cone.FaceModel
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)

def linkModel (s : Finset V) (hs : s ∈ X.faces) :
    FaceModel (X.faceLink s hs) (Y.faceLink (s.image M.vertex) ((M.face_iff s).mpr hs)) where
  vertex := M.vertex
  injective := M.injective
  face_iff := by
    intro a
    change Disjoint (s.image M.vertex) (a.image M.vertex) ∧
      s.image M.vertex ∪ a.image M.vertex ∈ Y.faces ↔
      Disjoint s a ∧ s ∪ a ∈ X.faces
    rw [←Finset.image_union,M.face_iff,Finset.disjoint_image M.injective]
  cover := by
    intro t ht
    obtain ⟨a,ha,he⟩ := M.cover t (Y.downward ht.2 Finset.subset_union_right)
    refine ⟨a,⟨?_,?_⟩,he⟩
    · rw [←Finset.disjoint_image M.injective,he]
      exact ht.1
    · apply (M.face_iff _).mp
      rw [Finset.image_union,he]
      exact ht.2

end Cone.FaceModel

namespace Join

def emptyLeftModel {X : CoboundaryExpanders.InfiniteChains.Complex W} {Y : CoboundaryExpanders.InfiniteChains.Complex V}
    (hX : ∀ s ∈ X.faces, s = ∅) : FaceModel Y (complex X Y) where
  vertex := Sum.inr
  injective := Sum.inr_injective
  face_iff := by
    intro s
    change (s.image Sum.inr).toLeft ∈ X.faces ∧ (s.image Sum.inr).toRight ∈ Y.faces ↔ _
    have hL : (s.image (Sum.inr : V → W ⊕ V)).toLeft = ∅ := by ext a; simp
    have hR : (s.image (Sum.inr : V → W ⊕ V)).toRight = s := by ext a; simp
    rw [hL,hR]
    simp only [X.empty_mem,true_and]
  cover := by
    intro t ht
    refine ⟨t.toRight,ht.2,?_⟩
    have he := Finset.toLeft_disjSum_toRight (u:=t)
    rw [hX t.toLeft ht.1] at he
    rw [Finset.empty_disjSum,Finset.map_eq_image] at he
    exact he

end Join
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.TypedCosetFaces
variable {G K I J : Type} [Group G] [Group K] [DecidableEq I] [DecidableEq J]
  (H : I → Subgroup G) (L : J → Subgroup K)

def embedLeft : Vertex H → Vertex (productGroups H L)
  | ⟨i,q⟩ => Quotient.lift (fun g : G => vertex (productGroups H L) (g,1) (Sum.inl i)) (by
      intro g h hgh
      refine Sigma.ext (by rfl) (heq_of_eq ?_)
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      exact ⟨QuotientGroup.leftRel_apply.mp hgh,Subgroup.mem_top _⟩) q

def embedRight : Vertex L → Vertex (productGroups H L)
  | ⟨j,q⟩ => Quotient.lift (fun g : K => vertex (productGroups H L) (1,g) (Sum.inr j)) (by
      intro g h hgh
      refine Sigma.ext (by rfl) (heq_of_eq ?_)
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      exact ⟨Subgroup.mem_top _,QuotientGroup.leftRel_apply.mp hgh⟩) q

def productVertexEquiv : Vertex (productGroups H L) ≃ Vertex H ⊕ Vertex L where
  toFun := productVertex H L
  invFun := Sum.elim (embedLeft H L) (embedRight H L)
  left_inv := by
    rintro ⟨i,q⟩
    cases i with
    | inl i =>
      induction q using Quotient.inductionOn with | h g =>
      refine Sigma.ext (by rfl) (heq_of_eq ?_)
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      change g.1⁻¹*g.1 ∈ H i ∧ _
      simp
    | inr j =>
      induction q using Quotient.inductionOn with | h g =>
      refine Sigma.ext (by rfl) (heq_of_eq ?_)
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      change _ ∧ g.2⁻¹*g.2 ∈ L j
      simp
  right_inv := by
    intro x
    cases x with
    | inl x =>
      rcases x with ⟨i,q⟩
      induction q using Quotient.inductionOn with | h g => rfl
    | inr x =>
      rcases x with ⟨j,q⟩
      induction q using Quotient.inductionOn with | h g => rfl

lemma productFace_image (g : G) (k : K) (A : Finset I) (B : Finset J) :
    (face (productGroups H L) (g,k) (A.image Sum.inl ∪ B.image Sum.inr)).image
      (productVertex H L) = (face H g A).image Sum.inl ∪ (face L k B).image Sum.inr := by
  simp only [face,Finset.image_union,Finset.image_image,Function.comp_def,
    productVertex_left,productVertex_right]

lemma productFace_image_general (g : G × K) (A : Finset (I ⊕ J)) :
    ∃ (B : Finset I) (C : Finset J),
      (face (productGroups H L) g A).image (productVertex H L) =
        (face H g.1 B).image Sum.inl ∪ (face L g.2 C).image Sum.inr := by
  refine ⟨A.toLeft,A.toRight,?_⟩
  have he : A.toLeft.image Sum.inl ∪ A.toRight.image Sum.inr = A := by ext x; cases x <;> simp
  calc
    _ = (face (productGroups H L) g (A.toLeft.image Sum.inl ∪ A.toRight.image Sum.inr)).image (productVertex H L) := by rw [he]
    _ = _ := productFace_image H L g.1 g.2 A.toLeft A.toRight

theorem productFace_iff (s : Finset (Vertex (productGroups H L))) :
    IsFace (productGroups H L) s ↔ ∃ (sL : Finset (Vertex H)) (sR : Finset (Vertex L)),
      IsFace H sL ∧ IsFace L sR ∧
      s.image (productVertex H L) = sL.image Sum.inl ∪ sR.image Sum.inr := by
  constructor
  · rintro ⟨g,A,rfl⟩
    obtain ⟨B,C,h⟩ := productFace_image_general H L g A
    exact ⟨face H g.1 B,face L g.2 C,⟨_,_,rfl⟩,⟨_,_,rfl⟩,h⟩
  · rintro ⟨sL,sR,⟨g,A,rfl⟩,⟨k,B,rfl⟩,he⟩
    refine ⟨(g,k),A.image Sum.inl ∪ B.image Sum.inr,?_⟩
    apply Finset.image_injective (productVertexEquiv H L).injective
    exact (productFace_image H L g k A B).trans he.symm

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.InfiniteChains.Cone.FaceModel
variable {V W Z : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Z]
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} {T : CoboundaryExpanders.InfiniteChains.Complex Z}
def trans (M : FaceModel X Y) (L : FaceModel Y T) : FaceModel X T where
  vertex := L.vertex ∘ M.vertex
  injective := L.injective.comp M.injective
  face_iff := by intro s; rw [←Finset.image_image,L.face_iff,M.face_iff]
  cover := by
    intro t ht
    obtain ⟨b,hb,he⟩ := L.cover t ht
    obtain ⟨a,ha,hf⟩ := M.cover b hb
    exact ⟨a,ha,by rw [←Finset.image_image,hf,he]⟩
end CoboundaryExpanders.InfiniteChains.Cone.FaceModel

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone
variable {G G' I I' : Type} [Group G] [Group G'] [DecidableEq I] [DecidableEq I']
variable (H : I → Subgroup G) (H' : I' → Subgroup G')
variable (e : G ≃* G') (r : I ≃ I') (he : ∀ i g, g ∈ H i ↔ e g ∈ H' (r i))

def isoModel : FaceModel (complex H) (complex H') where
  vertex := isoVertex H H' e r he
  injective := isoVertex_injective H H' e r he
  face_iff := isoFace_iff H H' e r he
  cover := by
    intro t ht
    let a := t.image (vertexEquiv H H' e r he).symm
    have ha : a.image (isoVertex H H' e r he) = t := by
      change a.image (vertexEquiv H H' e r he) = t
      simp only [a,Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,Finset.image_id']
    exact ⟨a,(isoFace_iff H H' e r he a).mp (by rwa [ha]),ha⟩

variable {K J : Type} [Group K] [DecidableEq J] (L : J → Subgroup K)
def productModel : FaceModel (complex (productGroups H L)) (Join.complex (complex H) (complex L)) where
  vertex := productVertex H L
  injective := (productVertexEquiv H L).injective
  face_iff := by
    intro s
    change IsFace H (s.image (productVertex H L)).toLeft ∧
      IsFace L (s.image (productVertex H L)).toRight ↔ IsFace (productGroups H L) s
    rw [productFace_iff]
    constructor
    · rintro ⟨hL,hR⟩
      refine ⟨_,_,hL,hR,?_⟩
      ext v
      cases v <;> simp
    · rintro ⟨a,b,ha,hb,he⟩
      rw [he]
      have hL : (a.image (Sum.inl : Vertex H → Vertex H ⊕ Vertex L) ∪ b.image Sum.inr).toLeft = a := by ext v; simp
      have hR : (a.image (Sum.inl : Vertex H → Vertex H ⊕ Vertex L) ∪ b.image Sum.inr).toRight = b := by ext v; simp
      exact ⟨by rwa [hL],by rwa [hR]⟩
  cover := by
    intro t ht
    let s := t.image (productVertexEquiv H L).symm
    have he : s.image (productVertex H L) = t := by
      change s.image (productVertexEquiv H L) = t
      simp only [s,Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,Finset.image_id']
    refine ⟨s,(productFace_iff H L s).mpr ⟨t.toLeft,t.toRight,ht.1,ht.2,?_⟩,he⟩
    rw [he]
    ext v
    cases v <;> simp
end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.MatrixOpposition
open SphericalOpposition SphericalOpposition.CompleteFlag TypedCosetFaces InfiniteChains Cone
open scoped Pointwise
variable {K : Type} [Field K] {N : ℕ}

lemma cutGroups_correspond (c : Cut N) (g : upperGroup K N) :
    upperFlagEquiv g ∈ (stdFlag K N).vertexStabilizers (oppFlag K N) (cutTypeEquiv c) ↔
      g ∈ cutGroups K N c := by
  change upperFlagEquiv g • (oppFlag K N).baseSpace (cutTypeEquiv c) = _ ↔ _
  have he : properIndex (N:=N) (cutTypeEquiv c) = (⟨N-c.val,by have h:=c.property; omega⟩:Fin (N+1)) := by
    apply Fin.ext
    have h:=c.property
    dsimp [properIndex,cutTypeEquiv]
    omega
  unfold baseSpace
  rw [he]
  rfl

def cutSphericalModel : FaceModel (TypedCosetFaces.complex (cutGroups K N)) (stdFlag K N).complex :=
  (isoModel (cutGroups K N) ((stdFlag K N).vertexStabilizers (oppFlag K N))
    upperFlagEquiv cutTypeEquiv (fun c g => (cutGroups_correspond c g).symm)).trans
    { vertex := (stdFlag K N).cosetVertexMap (oppFlag K N)
      injective := (stdFlag K N).cosetVertexMap_injective (oppFlag K N)
      face_iff := fun s => (cosetFace_iff stdFlags_opposite s).symm
      cover := fun s hs => by
        obtain ⟨g,A,he⟩ := opposedFace_coset stdFlags_opposite s hs
        exact ⟨_,⟨g,A,rfl⟩,he⟩ }

end CoboundaryExpanders.MatrixOpposition

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

lemma standard_face_mem (A : Finset I) : face H 1 A ∈ (complex H).faces := ⟨1,A,rfl⟩

def singleLinkModel (i : I) :
    FaceModel (complex (vertexLinkGroups H i)) (linkComplex H {i}) where
  vertex := vertexLinkEmbedding H i
  injective := vertexLinkEmbedding_injective H i
  face_iff := fun s => (vertexLinkFace_iff H i s).symm
  cover := fun t ht => vertexLinkFace_surjective H i t ht
end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.MatrixOpposition
open SphericalOpposition SphericalOpposition.CompleteFlag TypedCosetFaces InfiniteChains Cone
variable {K : Type} [Field K] {a b : ℕ}

def cutLinkTypes (ha : 0 < a) (hb : 0 < b) : Cut a ⊕ Cut b ≃
    {c : Cut (a+b) // c ≠ middleCut ha hb} := cutSplitEquiv.trans
  { toFun := fun c => ⟨c.val,fun h => c.property (congrArg Subtype.val h)⟩
    invFun := fun c => ⟨c.val,fun h => c.property (Subtype.ext h)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma cutLinkGroups_correspond (ha : 0 < a) (hb : 0 < b) (c : Cut a ⊕ Cut b)
    (g : upperGroup K a × upperGroup K b) :
    g ∈ productGroups (cutGroups K a) (cutGroups K b) c ↔
      blockSuffixEquiv g ∈ vertexLinkGroups (cutGroups K (a+b)) (middleCut ha hb) (cutLinkTypes ha hb c) := by
  have h := (blockSuffix_system g c).symm
  cases c with
  | inl c =>
    change (g.1 ∈ cutGroups K a c ∧ True) ↔
      (blockSuffixEquiv g).val ∈ cutGroups K (a+b) (cutSplitEquiv (Sum.inl c)).val
    rw [and_true]
    exact h
  | inr c =>
    change (True ∧ g.2 ∈ cutGroups K b c) ↔
      (blockSuffixEquiv g).val ∈ cutGroups K (a+b) (cutSplitEquiv (Sum.inr c)).val
    rw [true_and]
    exact h

def cutProductLinkModel (ha : 0 < a) (hb : 0 < b) :
    FaceModel (TypedCosetFaces.complex (productGroups (cutGroups K a) (cutGroups K b)))
      (TypedCosetFaces.complex (vertexLinkGroups (cutGroups K (a+b)) (middleCut ha hb))) :=
  isoModel _ _ blockSuffixEquiv (cutLinkTypes ha hb) (cutLinkGroups_correspond ha hb)

end CoboundaryExpanders.MatrixOpposition

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone
open scoped Pointwise
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

omit [DecidableEq I] in
lemma IsFace.smul {s : Finset (Vertex H)} (hs : IsFace H s) (g : G) : IsFace H (g • s) := by
  obtain ⟨h,A,rfl⟩ := hs
  rw [smul_face]
  exact ⟨g*h,A,rfl⟩

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.InfiniteChains

section
open Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]

namespace Cone.BoundedCone
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ}
def weaken (H : BoundedCone X n R) {m S : ℕ} (hm : m ≤ n) (hS : R ≤ S) : BoundedCone X m S where
  hom := H.hom
  support := fun s hs hn => H.support s hs (hn.trans hm)
  contraction := fun s hs hn => H.contraction s hs (hn.trans hm)
  bound := fun s hs hn => (H.bound s hs (hn.trans hm)).trans hS
end Cone.BoundedCone

def RankBound (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) : Prop := ∀ s ∈ X.faces, s.card ≤ N

def AllLinkCones (X : CoboundaryExpanders.InfiniteChains.Complex V) (N R : ℕ) : Prop :=
  ∀ s : Finset V, ∀ hs : s ∈ X.faces, s.card < N →
    Nonempty (BoundedCone (X.faceLink s hs) (N-s.card-1) R)

namespace Join

def emptyRightModel {X : CoboundaryExpanders.InfiniteChains.Complex W} {Y : CoboundaryExpanders.InfiniteChains.Complex V}
    (hY : ∀ s ∈ Y.faces, s = ∅) : FaceModel X (complex X Y) where
  vertex := Sum.inl
  injective := Sum.inl_injective
  face_iff := by
    intro s
    change (s.image Sum.inl).toLeft ∈ X.faces ∧ (s.image Sum.inl).toRight ∈ Y.faces ↔ _
    have hL : (s.image (Sum.inl : W → W ⊕ V)).toLeft = s := by ext a; simp
    have hR : (s.image (Sum.inl : W → W ⊕ V)).toRight = ∅ := by ext a; simp
    rw [hL,hR]
    simp only [Y.empty_mem,and_true]
  cover := by
    intro t ht
    refine ⟨t.toLeft,ht.1,?_⟩
    have he := Finset.toLeft_disjSum_toRight (u:=t)
    rw [hY t.toRight ht.2,Finset.disjSum_empty,Finset.map_eq_image] at he
    exact he

end Join
end

open Cone

end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone
open scoped Pointwise
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

def actionModel (g : G) : FaceModel (complex H) (complex H) where
  vertex := fun v => g • v
  injective := MulAction.injective g
  face_iff := by
    intro s
    change IsFace H (g • s) ↔ IsFace H s
    constructor
    · intro h
      have hh := h.smul H g⁻¹
      have he : g⁻¹ • (g • s) = s := inv_smul_smul g s
      rw [he] at hh
      exact hh
    · exact fun h => h.smul H g
  cover := by
    intro t ht
    refine ⟨g⁻¹ • t,ht.smul H g⁻¹,?_⟩
    change g • (g⁻¹ • t) = t
    exact smul_inv_smul g t

lemma standard_singleton_face (i : I) : {vertex H 1 i} ∈ (complex H).faces := by
  exact ⟨1,{i},by simp [face]⟩

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.InfiniteChains
open Cone
variable {V : Type} [DecidableEq V]

def ProperLinkCones (X : CoboundaryExpanders.InfiniteChains.Complex V) (N R : ℕ) : Prop :=
  ∀ s : Finset V, s.Nonempty → ∀ hs : s ∈ X.faces, s.card < N →
    Nonempty (BoundedCone (X.faceLink s hs) (N-s.card-1) R)

end CoboundaryExpanders.InfiniteChains

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_LinkSpectrum
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.TypedCosetFaces.complexInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.kernelInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexMulAction
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

namespace CoboundaryExpanders.RankTwoGeometry

section
open MatrixOpposition TypedCosetFaces Elementary
open scoped Matrix
variable {K : Type} [Field K]

def upper3 (a b c : K) : upperGroup K 3 :=
  ⟨⟨matrix3 a b c,matrix3_det a b c⟩,by
    apply (mem_upperGroup _).mpr
    intro i j hji
    fin_cases i <;> fin_cases j <;> norm_num [matrix3,Matrix.one_apply,Fin.le_iff_val_le_val] at *⟩

def ca (g : upperGroup K 3) : K := g.val 0 1
def cb (g : upperGroup K 3) : K := g.val 1 2
def cc (g : upperGroup K 3) : K := g.val 0 2

@[simp] lemma ca_upper3 (a b c : K) : ca (upper3 a b c) = a := rfl
@[simp] lemma cb_upper3 (a b c : K) : cb (upper3 a b c) = b := rfl
@[simp] lemma cc_upper3 (a b c : K) : cc (upper3 a b c) = c := rfl

lemma upper3_coords (g : upperGroup K 3) : upper3 (ca g) (cb g) (cc g) = g := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hg := (mem_upperGroup g.val).mp g.property
  change matrix3 (ca g) (cb g) (cc g) i j = g.val i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | rw [hg _ _ (by decide)]; rfl

@[ext] lemma upper_ext {g h : upperGroup K 3}
    (ha : ca g = ca h) (hb : cb g = cb h) (hc : cc g = cc h) : g = h := by
  rw [←upper3_coords g,←upper3_coords h,ha,hb,hc]

lemma upper3_mul (a b c a' b' c' : K) :
    upper3 a b c * upper3 a' b' c' = upper3 (a+a') (b+b') (c+c'+a*b') := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (matrix3 a b c * matrix3 a' b' c') i j = matrix3 (a+a') (b+b') (c+c'+a*b') i j
  fin_cases i <;> fin_cases j <;> simp [matrix3,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

@[simp] lemma ca_mul (g h : upperGroup K 3) : ca (g*h) = ca g+ca h := by
  rw [←upper3_coords g,←upper3_coords h,upper3_mul]; rfl
@[simp] lemma cb_mul (g h : upperGroup K 3) : cb (g*h) = cb g+cb h := by
  rw [←upper3_coords g,←upper3_coords h,upper3_mul]; rfl
@[simp] lemma cc_mul (g h : upperGroup K 3) : cc (g*h) = cc g+cc h+ca g*cb h := by
  rw [←upper3_coords g,←upper3_coords h,upper3_mul]; rfl
@[simp] lemma ca_one : ca (1 : upperGroup K 3) = 0 := by simp [ca]
@[simp] lemma cb_one : cb (1 : upperGroup K 3) = 0 := by simp [cb]
@[simp] lemma cc_one : cc (1 : upperGroup K 3) = 0 := by simp [cc]
@[simp] lemma ca_inv (g : upperGroup K 3) : ca g⁻¹ = -ca g := by
  have h := ca_mul g⁻¹ g
  simp only [inv_mul_cancel,ca_one] at h
  linear_combination -h
@[simp] lemma cb_inv (g : upperGroup K 3) : cb g⁻¹ = -cb g := by
  have h := cb_mul g⁻¹ g
  simp only [inv_mul_cancel,cb_one] at h
  linear_combination -h
@[simp] lemma cc_inv (g : upperGroup K 3) : cc g⁻¹ = -cc g+ca g*cb g := by
  have h := cc_mul g⁻¹ g
  simp only [inv_mul_cancel,cc_one,ca_inv] at h
  linear_combination -h

lemma mem_pointGroup (g : upperGroup K 3) :
    g ∈ cutGroups K 3 pointCut ↔ cb g = 0 ∧ cc g = 0 := by
  simp only [cutGroups,mem_suffixGroup,pointCut]
  refine ⟨fun h => ⟨h 1 2 (by decide) (by decide), h 0 2 (by decide) (by decide)⟩,?_⟩
  rintro ⟨hb,hc⟩ i j hi hj
  fin_cases i <;> fin_cases j <;> simp_all [cb,cc]
lemma mem_lineGroup (g : upperGroup K 3) :
    g ∈ cutGroups K 3 lineCut ↔ ca g = 0 ∧ cc g = 0 := by
  simp only [cutGroups,mem_suffixGroup,lineCut]
  refine ⟨fun h => ⟨h 0 1 (by decide) (by decide), h 0 2 (by decide) (by decide)⟩,?_⟩
  rintro ⟨ha,hc⟩ i j hi hj
  fin_cases i <;> fin_cases j <;> simp_all [ca,cc]

lemma point_rel (g h : upperGroup K 3) :
    g⁻¹*h ∈ cutGroups K 3 pointCut ↔ cb g = cb h ∧ cc g = cc h := by
  rw [mem_pointGroup]; simp only [cb_mul,cb_inv,cc_mul,cc_inv,ca_inv]
  constructor
  · rintro ⟨hb,hc⟩
    have he : cb g = cb h := by linear_combination -hb
    refine ⟨he,?_⟩
    rw [he] at hc
    linear_combination -hc
  · rintro ⟨hb,hc⟩; rw [hb,hc]; constructor <;> ring
lemma line_rel (g h : upperGroup K 3) :
    g⁻¹*h ∈ cutGroups K 3 lineCut ↔
      ca g = ca h ∧ cc g-ca g*cb g = cc h-ca h*cb h := by
  rw [mem_lineGroup]; simp only [ca_mul,ca_inv,cc_mul,cc_inv]
  constructor
  · rintro ⟨ha,hc⟩
    have he : ca g = ca h := by linear_combination -ha
    refine ⟨he,?_⟩
    rw [he] at hc ⊢
    linear_combination -hc
  · rintro ⟨ha,hc⟩; rw [ha]; constructor
    · ring
    · rw [ha] at hc; linear_combination -hc

end

open MatrixOpposition TypedCosetFaces InfiniteChains Cone
variable {K : Type} [Field K]

def cosetVertex : Vert K → Vertex (cutGroups K 3)
  | .inl P => vertex (cutGroups K 3) (upper3 0 P.1 P.2) pointCut
  | .inr L => vertex (cutGroups K 3) (upper3 L.1 0 L.2) lineCut

lemma point_vertex (g : upperGroup K 3) :
    cosetVertex (.inl (cb g,cc g)) = vertex (cutGroups K 3) g pointCut := by
  dsimp only [cosetVertex,vertex]
  apply congrArg (Sigma.mk _)
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  exact (point_rel _ _).mpr ⟨rfl,rfl⟩
lemma line_vertex (g : upperGroup K 3) :
    cosetVertex (.inr (ca g,cc g-ca g*cb g)) = vertex (cutGroups K 3) g lineCut := by
  dsimp only [cosetVertex,vertex]
  apply congrArg (Sigma.mk _)
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  apply (line_rel _ _).mpr
  simp

lemma cosetVertex_injective : Function.Injective (cosetVertex (K:=K)) := by
  intro x y h
  cases x with
  | inl P =>
    cases y with
    | inl Q =>
      have hh := QuotientGroup.leftRel_apply.mp
        (Quotient.exact (eq_of_heq (Sigma.mk.inj_iff.mp h).2))
      have he := (point_rel _ _).mp hh
      congr 1
      exact Prod.ext he.1 he.2
    | inr L =>
      have he := congrArg (fun v => v.1.val) h
      norm_num [cosetVertex,vertex,pointCut,lineCut] at he
  | inr L =>
    cases y with
    | inl P =>
      have he := congrArg (fun v => v.1.val) h
      norm_num [cosetVertex,vertex,pointCut,lineCut] at he
    | inr M =>
      have hh := QuotientGroup.leftRel_apply.mp
        (Quotient.exact (eq_of_heq (Sigma.mk.inj_iff.mp h).2))
      have he := (line_rel _ _).mp hh
      congr 1
      apply Prod.ext he.1
      simpa using he.2

lemma cosetVertex_surjective : Function.Surjective (cosetVertex (K:=K)) := by
  rintro ⟨i,q⟩
  induction q using Quotient.inductionOn with | h g =>
  rcases cuts3 i with rfl | rfl
  · exact ⟨.inl (cb g,cc g),point_vertex g⟩
  · exact ⟨.inr (ca g,cc g-ca g*cb g),line_vertex g⟩

def vertexEquiv : Vert K ≃ Vertex (cutGroups K 3) :=
  Equiv.ofBijective cosetVertex ⟨cosetVertex_injective,cosetVertex_surjective⟩

attribute [local instance] OAI.CoboundaryExpanders.RankTwoGeometry.instDecidableEq_solutions
def incidenceComplex (K : Type) [Field K] : CoboundaryExpanders.InfiniteChains.Complex (Vert K) where
  faces := {s | ∃ P L : K×K, incident P L ∧ s ⊆ {Sum.inl P,Sum.inr L}}
  empty_mem := ⟨(0,0),(0,0),by simp [incident],Finset.empty_subset _⟩
  downward := by
    rintro s t ⟨P,L,hPL,hs⟩ ht
    exact ⟨P,L,hPL,ht.trans hs⟩

lemma fullFace (g : upperGroup K 3) :
    ({Sum.inl (cb g,cc g),Sum.inr (ca g,cc g-ca g*cb g)} : Finset (Vert K)).image cosetVertex =
      face (cutGroups K 3) g {pointCut,lineCut} := by
  simp only [Finset.image_insert,Finset.image_singleton,point_vertex,line_vertex,face]

lemma face_subset_fullFace (g : upperGroup K 3) (A : Finset (Cut 3)) :
    face (cutGroups K 3) g A ⊆ face (cutGroups K 3) g {pointCut,lineCut} := by
  apply Finset.image_subset_image
  intro i _
  rcases cuts3 i with rfl | rfl <;> simp

lemma cosetVertex_face_iff (s : Finset (Vert K)) :
    s.image cosetVertex ∈ (TypedCosetFaces.complex (cutGroups K 3)).faces ↔
      s ∈ (incidenceComplex K).faces := by
  constructor
  · rintro ⟨g,A,hg⟩
    refine ⟨(cb g,cc g),(ca g,cc g-ca g*cb g),?_,?_⟩
    · dsimp [incident]; ring
    · apply (Finset.image_subset_image_iff cosetVertex_injective).mp
      rw [fullFace,←hg]
      exact face_subset_fullFace g A
  · rintro ⟨P,L,hPL,hs⟩
    have he : (ca (upper3 L.1 P.1 P.2),cc (upper3 L.1 P.1 P.2)-
        ca (upper3 L.1 P.1 P.2)*cb (upper3 L.1 P.1 P.2)) = L := by
      apply Prod.ext
      · rfl
      · change P.2-L.1*P.1 = L.2
        rw [hPL]; ring
    have hf := fullFace (upper3 L.1 P.1 P.2)
    simp only [ca_upper3,cb_upper3,cc_upper3] at he hf
    rw [he] at hf
    apply IsFace.downward (H:=cutGroups K 3) ⟨_,_,rfl⟩
    rw [←hf]
    exact Finset.image_subset_image hs

def incidenceModel : FaceModel (incidenceComplex K) (TypedCosetFaces.complex (cutGroups K 3)) where
  vertex := cosetVertex
  injective := cosetVertex_injective
  face_iff := cosetVertex_face_iff
  cover := by
    intro t ht
    let s := t.image vertexEquiv.symm
    have he : s.image cosetVertex = t := by
      change s.image vertexEquiv = t
      simp only [s,Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,Finset.image_id']
    exact ⟨s,by rwa [←cosetVertex_face_iff,he],he⟩

end CoboundaryExpanders.RankTwoGeometry

namespace CoboundaryExpanders.InfiniteChains
namespace FiniteWeights
variable {V : Type} [Fintype V] [DecidableEq V]

def cofaces (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (s : Finset V) : ℕ :=
  ((level X N).filter (fun t => s ⊆ t)).card

def Pure (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) : Prop :=
  (level X N).Nonempty ∧ ∀ s ∈ X.faces, ∃ t ∈ level X N, s ⊆ t

lemma cofaces_zero_of_not_face (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) {s : Finset V} (hs : s ∉ X.faces) :
    cofaces X N s = 0 := by
  unfold cofaces
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨ht,hst⟩ := Finset.mem_filter.mp ht
  exact hs (X.downward ((mem_level X N t).mp ht).1 hst)

end FiniteWeights

open FiniteWeights
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
attribute [local instance] Classical.propDecidable

namespace Cone.FaceModel
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)

lemma cofaces_image (N : ℕ) (s : Finset V) :
    cofaces Y N (s.image M.vertex) = cofaces X N s := by
  unfold cofaces
  symm
  apply Finset.card_bij (fun t _ => t.image M.vertex)
  · intro t ht
    obtain ⟨ht,hst⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht,hcard⟩ := (mem_level _ _ _).mp ht
    exact Finset.mem_filter.mpr ⟨(mem_level _ _ _).mpr
      ⟨(M.face_iff t).mpr ht,by rwa [Finset.card_image_of_injective t M.injective]⟩,
      Finset.image_subset_image hst⟩
  · intro t ht u hu he
    exact Finset.image_injective M.injective he
  · intro t ht
    obtain ⟨ht,hst⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht,hcard⟩ := (mem_level _ _ _).mp ht
    obtain ⟨u,hu,he⟩ := M.cover t ht
    refine ⟨u,Finset.mem_filter.mpr ⟨(mem_level _ _ _).mpr ⟨hu,?_⟩,?_⟩,he⟩
    · rw [←he,Finset.card_image_of_injective u M.injective] at hcard
      exact hcard
    · rw [←he] at hst
      exact (Finset.image_subset_image_iff M.injective).mp hst

omit [Fintype V] [Fintype W] [DecidableEq V] in
lemma vertex_in_range {y : W} (hy : ({y}:Finset W) ∈ Y.faces) : y ∈ Set.range M.vertex := by
  obtain ⟨s,hs,he⟩ := M.cover {y} hy
  have h : y ∈ s.image M.vertex := by rw [he]; simp
  obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp h
  exact ⟨x,hxy⟩

end Cone.FaceModel

namespace FiniteWeights

def edge (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (x y : V) : ℝ :=
  if x ≠ y then (cofaces X N {x,y}:ℝ) else 0
lemma edge_zero_of_not_face (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) {x : V} (hx : ({x}:Finset V) ∉ X.faces)
    (y : V) : edge X N x y = 0 := by
  unfold edge
  split_ifs
  · rw [cofaces_zero_of_not_face X N (fun h => hx (X.downward h (by simp))),Nat.cast_zero]
  · rfl

end FiniteWeights

namespace Cone.FaceModel
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)

def spectralEmbedding (N : ℕ) : EdgeMixing.Embedding (edge X N) (edge Y N) where
  vertex := M.vertex
  injective := M.injective
  edge_eq := by
    intro x y
    simp only [edge,M.injective.ne_iff]
    split_ifs
    · have h := M.cofaces_image N {x,y}
      simpa only [Finset.image_insert,Finset.image_singleton] using congrArg (fun a : ℕ => (a:ℝ)) h
    · rfl
  outside_zero := by
    intro y hy z
    apply edge_zero_of_not_face Y N
    exact fun h => hy (M.vertex_in_range h)

end Cone.FaceModel
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.InfiniteChains.FiniteWeights
variable {V : Type} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable
lemma cofaces_top (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (s : Finset V) (hs : s.card = N) :
    cofaces X N s = if s ∈ X.faces then 1 else 0 := by
  by_cases hf : s ∈ X.faces
  · rw [ite_eq_left hf]
    have he : (level X N).filter (fun t => s ⊆ t) = {s} := by
      ext t
      simp only [Finset.mem_filter,mem_level,Finset.mem_singleton]
      constructor
      · rintro ⟨⟨ht,hcard⟩,hst⟩
        exact (Finset.eq_of_subset_of_card_le hst (by omega)).symm
      · rintro rfl
        exact ⟨⟨hf,hs⟩,Finset.Subset.refl _⟩
    simp only [cofaces,he,Finset.card_singleton]
  · rw [ite_eq_right hf,cofaces_zero_of_not_face X N hf]
end CoboundaryExpanders.InfiniteChains.FiniteWeights

namespace CoboundaryExpanders.MatrixOpposition
open InfiniteChains FiniteWeights TypedCosetFaces
variable {K : Type} [Field K] [Fintype K]
noncomputable instance cutVertexFintype (N : ℕ) : Fintype (Vertex (cutGroups K N)) := Fintype.ofFinite _

end CoboundaryExpanders.MatrixOpposition

namespace CoboundaryExpanders.InfiniteChains.Join
open Cone FiniteWeights
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
attribute [local instance] Classical.propDecidable

abbrev TrueVertex (X : CoboundaryExpanders.InfiniteChains.Complex V) := {x : V // ({x}:Finset V) ∈ X.faces}

def rankOneEmbedding {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W}
    (hX : RankBound X 1) (hY : RankBound Y 1) :
    EdgeMixing.Embedding (EdgeMixing.bipartiteEdge (A:=TrueVertex X) (B:=TrueVertex Y))
      (edge (complex X Y) 2) where
  vertex := Sum.map Subtype.val Subtype.val
  injective := Sum.map_injective.mpr ⟨Subtype.val_injective,Subtype.val_injective⟩
  edge_eq := by
    intro x y
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        change edge (complex X Y) 2 (Sum.inl a.val) (Sum.inl b.val) = 0
        by_cases hab : a = b
        · subst b; simp [edge]
        · have hv : a.val ≠ b.val := fun h => hab (Subtype.ext h)
          have hne : Sum.inl a.val ≠ (Sum.inl b.val : V ⊕ W) := fun h => hv (Sum.inl.inj h)
          have hnot : ({Sum.inl a.val,Sum.inl b.val}:Finset (V ⊕ W)) ∉ (complex X Y).faces := by
            intro h
            have hh := hX {a.val,b.val} (by simpa [complex] using h.1)
            rw [Finset.card_pair hv] at hh
            omega
          simp [edge,hne,cofaces_zero_of_not_face _ _ hnot]
      | inr b =>
        change edge (complex X Y) 2 (Sum.inl a.val) (Sum.inr b.val) = 1
        rw [edge,ite_eq_left (by simp),cofaces_top _ _ _ (Finset.card_pair (by simp))]
        have hf : ({Sum.inl a.val,Sum.inr b.val}:Finset (V ⊕ W)) ∈ (complex X Y).faces := by
          simpa [complex] using And.intro a.property b.property
        simp [hf]
    | inr a =>
      cases y with
      | inl b =>
        change edge (complex X Y) 2 (Sum.inr a.val) (Sum.inl b.val) = 1
        rw [edge,ite_eq_left (by simp),cofaces_top _ _ _ (Finset.card_pair (by simp))]
        have hf : ({Sum.inr a.val,Sum.inl b.val}:Finset (V ⊕ W)) ∈ (complex X Y).faces := by
          simpa [complex] using And.intro b.property a.property
        simp [hf]
      | inr b =>
        change edge (complex X Y) 2 (Sum.inr a.val) (Sum.inr b.val) = 0
        by_cases hab : a = b
        · subst b; simp [edge]
        · have hv : a.val ≠ b.val := fun h => hab (Subtype.ext h)
          have hne : Sum.inr a.val ≠ (Sum.inr b.val : V ⊕ W) := fun h => hv (Sum.inr.inj h)
          have hnot : ({Sum.inr a.val,Sum.inr b.val}:Finset (V ⊕ W)) ∉ (complex X Y).faces := by
            intro h
            have hh := hY {a.val,b.val} (by simpa [complex] using h.2)
            rw [Finset.card_pair hv] at hh
            omega
          simp [edge,hne,cofaces_zero_of_not_face _ _ hnot]
  outside_zero := by
    intro x hx y
    apply edge_zero_of_not_face
    intro h
    cases x with
    | inl a =>
      have ha : ({a}:Finset V) ∈ X.faces := by simpa [complex] using h.1
      exact hx ⟨Sum.inl ⟨a,ha⟩,rfl⟩
    | inr b =>
      have hb : ({b}:Finset W) ∈ Y.faces := by simpa [complex] using h.2
      exact hx ⟨Sum.inr ⟨b,hb⟩,rfl⟩

end CoboundaryExpanders.InfiniteChains.Join

namespace CoboundaryExpanders.InfiniteChains
open Cone FiniteWeights
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def TopSpectral (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (lam : ℝ) : Prop :=
  ∀ s : Finset V, ∀ hs : s ∈ X.faces, s.card+2 = N →
    EdgeMixing.Rayleigh (edge (X.faceLink s hs) 2) lam

end CoboundaryExpanders.InfiniteChains

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Averaging
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction
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

namespace CoboundaryExpanders.InfiniteChains.Cone
open Attachment
variable {V : Type} [DecidableEq V]

def correction (T : Raw V →ₗ[k] Raw V) (f : Finset V → k) (s : Finset V) : k :=
  eval f (T (Finsupp.single s 1))

variable {G : Type} [Group G] [MulAction G V]
open scoped Pointwise

def movedCorrection (g : G) (T : Raw V →ₗ[k] Raw V) (f : Finset V → k) : Finset V → k :=
  pull g⁻¹ (correction T (pull g f))

end CoboundaryExpanders.InfiniteChains.Cone

namespace CoboundaryExpanders.InfiniteChains.FiniteWeights

section
open Attachment Cone Averaging
open scoped BigOperators Pointwise
variable {V : Type} [Fintype V] [DecidableEq V]

def weight (X : CoboundaryExpanders.InfiniteChains.Complex V) (N r : ℕ) (s : Finset V) : ℝ :=
  if s ∈ level X r then cofaces X N s / ((N.choose r : ℝ) * (level X N).card) else 0

end

open Attachment Cone Averaging
open scoped BigOperators Pointwise
variable {V : Type} [Fintype V] [DecidableEq V]

instance faceFintype (X : CoboundaryExpanders.InfiniteChains.Complex V) (r : ℕ) : Fintype (X.Face r) := Fintype.ofFinite _

end CoboundaryExpanders.InfiniteChains.FiniteWeights

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Lattices
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Affine and rational lattices, polynomial congruence actions, and lattice-chain geometry.
-/

noncomputable section


namespace CoboundaryExpanders.RationalLattices
open InfiniteChains InfiniteChains.Attachment
open scoped Polynomial
variable (K : Type) [Field K] (N : ℕ)

noncomputable abbrev building : InfiniteChains.Complex (Vertex K N) :=
  AffineLattices.complex (shift K N) (standard K N)

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
variable (K : Type) [Field K] (N : ℕ)

noncomputable def baseChamber : Finset (Vertex K N) :=
  Finset.univ.image (cutVertex K N)

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open Module
variable (K : Type) [Field K] (N : ℕ)

lemma residueMap_apply (A : Vertex K N) (v : A.val) (i : Fin N) :
    residueMap K N A v i = (((latticeBasis K N A).equivFun v) i).coeff 0 := rfl

lemma residueMap_surjective (A : Vertex K N) : Function.Surjective (residueMap K N A) := by
  intro v
  refine ⟨(latticeBasis K N A).equivFun.symm (fun i => Polynomial.C (v i)),?_⟩
  ext i
  simp only [residueMap_apply,LinearEquiv.apply_symm_apply,Polynomial.coeff_C_zero]

lemma residueMap_smul_polynomial (A : Vertex K N) (f : K[X]) (v : A.val) :
    residueMap K N A (f • v) = f.coeff 0 • residueMap K N A v := by
  ext i
  simp only [residueMap_apply,map_smul,Pi.smul_apply,smul_eq_mul]
  change Polynomial.constantCoeff (f * _) = Polynomial.constantCoeff f * Polynomial.constantCoeff _
  exact map_mul _ _ _

lemma residueMap_eq_zero_iff (A : Vertex K N) (v : A.val) :
    residueMap K N A v = 0 ↔ v.val ∈ shift K N A.val := by
  constructor
  · intro h
    have hz : ∀ i, Polynomial.X ∣ (latticeBasis K N A).equivFun v i := by
      intro i
      apply Polynomial.X_dvd_iff.mpr
      exact congr_fun h i
    choose f hf using hz
    let w : A.val := (latticeBasis K N A).equivFun.symm f
    have he : (Polynomial.X : K[X]) • w = v := by
      apply (latticeBasis K N A).equivFun.injective
      simp only [map_smul,LinearEquiv.apply_symm_apply,w]
      funext i
      exact (hf i).symm
    apply (mem_shift K N _ _).mpr
    refine ⟨w.val,w.property,?_⟩
    have hv := congrArg Subtype.val he
    change (Polynomial.X : K[X]) • w.val = v.val at hv
    simpa only [shiftLinear_eq_smul] using hv
  · intro hv
    obtain ⟨w,hw,he⟩ := (mem_shift K N _ _).mp hv
    have he' : (Polynomial.X : K[X]) • (⟨w,hw⟩ : A.val) = v := by
      apply Subtype.ext
      change (Polynomial.X : K[X]) • w = v.val
      simpa only [shiftLinear_eq_smul] using he
    rw [← he',residueMap_smul_polynomial]
    simp

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

noncomputable def polynomialLattice (A : Vertex K N) : Submodule K[X] (Fin N → K[X]) :=
  A.val.comap (polynomialEmbedding K N)

lemma polynomialLattice_map (A : Vertex K N) :
    (polynomialLattice K N A).map (polynomialEmbedding K N) = A.val := by
  apply le_antisymm
  · rintro v ⟨w,hw,rfl⟩
    exact hw
  · intro v hv
    obtain ⟨w,hw⟩ := (polynomialToStandard_bijective K N).2
      ⟨v,vertex_le (shift K N) (standard K N) A hv⟩
    refine ⟨w,?_,?_⟩
    · change polynomialEmbedding K N w ∈ A.val
      have he := congrArg Subtype.val hw
      change polynomialEmbedding K N w = v at he
      exact he.symm ▸ hv
    · exact congrArg Subtype.val hw

lemma polynomialLattice_bound (A : Vertex K N) :
    ∃ m : ℕ, ∀ i : Fin N, Pi.single i (Polynomial.X^m : K[X]) ∈ polynomialLattice K N A := by
  classical
  obtain ⟨m,hm⟩ := vertex_bounded (shift K N) (standard K N) A
  refine ⟨m,fun i => ?_⟩
  change polynomialEmbedding K N (Pi.single i (Polynomial.X^m : K[X])) ∈ A.val
  apply hm
  apply (mem_level K N _ _ _).mpr
  refine ⟨Pi.single i (1 : RatFunc K),(by intro j; exact ⟨(if j = i then 1 else 0 : K[X]),by split_ifs <;> simp_all⟩),?_⟩
  funext j
  by_cases hij : j = i
  · subst j; simp [Algebra.smul_def]
  · simp [hij,Algebra.smul_def]

lemma polynomialHasPivots (A : Vertex K N) :
    PolynomialVectors.HasPivots (polynomialLattice K N A) := by
  obtain ⟨m,hm⟩ := polynomialLattice_bound K N A
  exact PolynomialVectors.hasPivots_of_bound _ m hm

noncomputable def diagonalExponents (A : Vertex K N) : Fin N → ℕ :=
  PolynomialVectors.pivotDegree (polynomialLattice K N A) (polynomialHasPivots K N A)

noncomputable def exponentLattice (a : Fin N → ℕ) : LatticeSpace K N :=
  Submodule.span K[X] (Set.range fun i : Fin N => Pi.single i (uniformizer K ^ a i))

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices
variable (K : Type) [Field K] (N M : ℕ)

lemma polynomialLattice_mono {A B : Vertex K N} (hBA : B.val ≤ A.val) :
    polynomialLattice K N B ≤ polynomialLattice K N A :=
  Submodule.comap_mono hBA

lemma polynomialLattice_power_le {A B : Vertex K N}
    (hAB : level (shift K N) A.val 1 ≤ B.val) :
    PolynomialVectors.powerShift (polynomialLattice K N A) 1 ≤ polynomialLattice K N B := by
  rintro v ⟨w,hw,rfl⟩
  change polynomialEmbedding K N (PolynomialVectors.powerLinear 1 w) ∈ B.val
  apply hAB
  apply (mem_level K N _ _ _).mpr
  refine ⟨polynomialEmbedding K N w,hw,?_⟩
  funext i
  simp [PolynomialVectors.powerLinear,Algebra.smul_def]

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

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))

lemma terminal : C.stage (Fin.last N) = powerShift C.top 1 := by
  apply eq_of_le_same_pivots (C.hasStage (Fin.last N))
    (powerShift_hasPivots C.top C.hasTop 1) (C.lower (Fin.last N))
  intro i
  rw [C.stage_degree,pivotDegree_powerShift C.top C.hasTop]
  simp only [Fin.val_last,ite_eq_left (C.word.symm i).isLt]

noncomputable def length : ℕ := AffineWindow.inversion (N := N) (List.ofFn C.window)

end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable (K : Type) [Field K] (N : ℕ)

lemma polynomialLattice_injective : Function.Injective (polynomialLattice K N) := by
  intro A B he
  apply Subtype.ext
  have hh := congrArg (fun P => P.map (polynomialEmbedding K N)) he
  simpa only [polynomialLattice_map] using hh

lemma polynomialLattice_strict {A B : Vertex K N} (hBA : B.val < A.val) :
    polynomialLattice K N B < polynomialLattice K N A := by
  apply lt_of_le_of_ne (polynomialLattice_mono K N hBA.le)
  intro he
  exact hBA.ne (congrArg Subtype.val (polynomialLattice_injective K N he))

lemma polynomialLattice_power_map (A : Vertex K N) (m : ℕ) :
    (powerShift (polynomialLattice K N A) m).map (polynomialEmbedding K N) =
      level (shift K N) A.val m := by
  ext v
  constructor
  · rintro ⟨w,⟨z,hz,rfl⟩,rfl⟩
    apply (mem_level K N _ _ _).mpr
    exact ⟨polynomialEmbedding K N z,hz,by rw [← map_smul]; rfl⟩
  · intro hv
    obtain ⟨w,hw,rfl⟩ := (mem_level K N _ _ _).mp hv
    have hw' : w ∈ (polynomialLattice K N A).map (polynomialEmbedding K N) := by
      rwa [polynomialLattice_map]
    obtain ⟨z,hz,rfl⟩ := hw'
    exact ⟨powerLinear m z,⟨z,hz,rfl⟩,by change polynomialEmbedding K N ((Polynomial.X^m : K[X]) • z) = _; rw [map_smul]⟩

structure FullChamber (hN : 0 < N) where
  vertex : Fin N → Vertex K N
  strict : StrictAnti (fun r => (vertex r).val)
  lower : ∀ r, shift K N (vertex ⟨0,hN⟩).val ≤ (vertex r).val

namespace FullChamber
variable {K N} {hN : 0 < N} (C : FullChamber K N hN)

def topIndex (_C : FullChamber K N hN) : Fin N := ⟨0,hN⟩

noncomputable def stage (r : Fin (N+1)) : Submodule K[X] (PolynomialVectors.V K N) :=
  if hr : r.val < N then polynomialLattice K N (C.vertex ⟨r.val,hr⟩)
  else powerShift (polynomialLattice K N (C.vertex C.topIndex)) 1

lemma hasStage (r : Fin (N+1)) : HasPivots (C.stage r) := by
  unfold stage
  split_ifs
  · exact polynomialHasPivots K N _
  · exact powerShift_hasPivots _ (polynomialHasPivots K N _) 1

lemma lower_stage (r : Fin (N+1)) : powerShift (polynomialLattice K N (C.vertex C.topIndex)) 1 ≤ C.stage r := by
  unfold stage
  split_ifs
  · exact polynomialLattice_power_le K N (C.lower _)
  · exact le_rfl

lemma stage_strict : StrictAnti C.stage := by
  intro r s hrs
  have hrN : r.val < N := by have hs := s.isLt; change r.val < s.val at hrs; omega
  rw [show C.stage r = polynomialLattice K N (C.vertex ⟨r.val,hrN⟩) from dite_eq_left hrN]
  unfold stage
  split_ifs with hsN
  · exact polynomialLattice_strict K N (C.strict (show (⟨r.val,hrN⟩ : Fin N) < ⟨s.val,hsN⟩ from hrs))
  · apply lt_of_le_of_ne (polynomialLattice_power_le K N (C.lower _))
    intro he
    have hh := congrArg (fun P => P.map (polynomialEmbedding K N)) he
    rw [polynomialLattice_power_map,polynomialLattice_map] at hh
    have hle : (C.vertex ⟨r.val,hrN⟩).val ≤ shift K N (standard K N) := by
      rw [← hh]
      exact (shift K N).monotone (vertex_le (shift K N) (standard K N) _)
    exact vertex_normalized (shift K N) (standard K N) _ hle

noncomputable def polynomialChamber : ResidueChamber (K := K) (N := N) where
  top := polynomialLattice K N (C.vertex C.topIndex)
  hasTop := polynomialHasPivots K N _
  stage := C.stage
  hasStage := C.hasStage
  strict := C.stage_strict
  initial := by
    unfold stage
    split_ifs with h
    · rfl
    · exact False.elim (h hN)
  lower := C.lower_stage

noncomputable def length : ℕ := C.polynomialChamber.length

end FullChamber
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable (K : Type) [Field K] (N : ℕ)

lemma powerShift_map_embedding (P : Submodule K[X] (PolynomialVectors.V K N)) (m : ℕ) :
    (powerShift P m).map (polynomialEmbedding K N) =
      level (shift K N) (P.map (polynomialEmbedding K N)) m := by
  ext v
  constructor
  · rintro ⟨w,⟨z,hz,rfl⟩,rfl⟩
    apply (mem_level K N _ _ _).mpr
    refine ⟨polynomialEmbedding K N z,⟨z,hz,rfl⟩,?_⟩
    rw [← map_smul]
    rfl
  · intro hv
    obtain ⟨w,⟨z,hz,rfl⟩,rfl⟩ := (mem_level K N _ _ _).mp hv
    refine ⟨powerLinear m z,⟨z,hz,rfl⟩,?_⟩
    change polynomialEmbedding K N ((Polynomial.X^m : K[X]) • z) = _
    rw [map_smul]

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable (K : Type) [Field K] (N : ℕ)

def OpposedVertex (hN : 0 < N) (A : Vertex K N) : Prop :=
  ∃ g : Matrix.SpecialLinearGroup (Fin N) K[X],
    (∀ i j : Fin N, j ≤ i → (g i j).coeff 0 = (1 : Matrix (Fin N) (Fin N) K) i j) ∧
    ∃ cut : Fin N, A = actVertex K N hN g (cutVertex K N cut)

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
variable (K : Type) [Field K] (N : ℕ)
attribute [local irreducible] residueMap latticeBasis

abbrev ResidueInterval (A : Vertex K N) := Set.Icc (shift K N A.val) A.val

noncomputable def liftResidue (A : Vertex K N) (W : Submodule K (Fin N → K)) : LatticeSpace K N where
  carrier := {v | ∃ h : v ∈ A.val, residueMap K N A ⟨v,h⟩ ∈ W}
  zero_mem' := by
    refine ⟨A.val.zero_mem,?_⟩
    change residueMap K N A (0 : A.val) ∈ W
    rw [map_zero]
    exact W.zero_mem
  add_mem' := by
    rintro v w ⟨hv,hv'⟩ ⟨hw,hw'⟩
    refine ⟨A.val.add_mem hv hw,?_⟩
    change residueMap K N A ((⟨v,hv⟩ : A.val) + ⟨w,hw⟩) ∈ W
    exact ((residueMap K N A).map_add ⟨v,hv⟩ ⟨w,hw⟩).symm ▸ W.add_mem hv' hw'
  smul_mem' := by
    rintro f v ⟨hv,hv'⟩
    refine ⟨A.val.smul_mem f hv,?_⟩
    change residueMap K N A (f • (⟨v,hv⟩ : A.val)) ∈ W
    rw [residueMap_smul_polynomial]
    exact W.smul_mem _ hv'

lemma liftResidue_le (A : Vertex K N) (W : Submodule K (Fin N → K)) :
    liftResidue K N A W ≤ A.val := fun _ hv => hv.choose

lemma shift_le_liftResidue (A : Vertex K N) (W : Submodule K (Fin N → K)) :
    shift K N A.val ≤ liftResidue K N A W := by
  intro v hv
  have hvA := shift_le_self K N A.val hv
  refine ⟨hvA,?_⟩
  rw [(residueMap_eq_zero_iff K N A ⟨v,hvA⟩).mpr hv]
  exact W.zero_mem

lemma mem_liftResidue (A : Vertex K N) (W : Submodule K (Fin N → K)) (v : A.val) :
    v.val ∈ liftResidue K N A W ↔ residueMap K N A v ∈ W := by
  constructor
  · rintro ⟨hv,h⟩; exact h
  · intro h; exact ⟨v.property,h⟩

noncomputable def intervalSubspace (A : Vertex K N) (B : ResidueInterval K N A) : Submodule K (Fin N → K) :=
  (((B.val.restrictScalars K).comap (A.val.subtype.restrictScalars K)).map (residueMap K N A))

lemma mem_intervalSubspace (A : Vertex K N) (B : ResidueInterval K N A) (w : Fin N → K) :
    w ∈ intervalSubspace K N A B ↔ ∃ v : A.val, v.val ∈ B.val ∧ residueMap K N A v = w := Iff.rfl

lemma lift_intervalSubspace (A : Vertex K N) (B : ResidueInterval K N A) :
    liftResidue K N A (intervalSubspace K N A B) = B.val := by
  ext v
  constructor
  · rintro ⟨hv,hv'⟩
    obtain ⟨w,hw,he⟩ := (mem_intervalSubspace K N A B _).mp hv'
    have hz : residueMap K N A ((⟨v,hv⟩ : A.val) - w) = 0 := by rw [map_sub,he,sub_self]
    have hd : v - w.val ∈ B.val := B.property.1 ((residueMap_eq_zero_iff K N A _).mp hz)
    have hh := B.val.add_mem hd hw
    simpa only [sub_add_cancel] using hh
  · intro hv
    refine ⟨B.property.2 hv,?_⟩
    exact (mem_intervalSubspace K N A B _).mpr ⟨⟨v,B.property.2 hv⟩,hv,rfl⟩

lemma intervalSubspace_lift (A : Vertex K N) (W : Submodule K (Fin N → K)) :
    intervalSubspace K N A ⟨liftResidue K N A W,shift_le_liftResidue K N A W,liftResidue_le K N A W⟩ = W := by
  ext w
  rw [mem_intervalSubspace]
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact (mem_liftResidue K N A W v).mp hv
  · intro hw
    obtain ⟨v,rfl⟩ := residueMap_surjective K N A w
    exact ⟨v,(mem_liftResidue K N A W v).mpr hw,rfl⟩

noncomputable def residueIntervalIso (A : Vertex K N) :
    ResidueInterval K N A ≃o Submodule K (Fin N → K) where
  toFun := intervalSubspace K N A
  invFun W := ⟨liftResidue K N A W,shift_le_liftResidue K N A W,liftResidue_le K N A W⟩
  left_inv B := Subtype.ext (lift_intervalSubspace K N A B)
  right_inv := intervalSubspace_lift K N A
  map_rel_iff' := by
    intro B D
    constructor
    · intro h v hv
      have hvA := B.property.2 hv
      have hv' : residueMap K N A ⟨v,hvA⟩ ∈ intervalSubspace K N A D :=
        h ((mem_intervalSubspace K N A B _).mpr ⟨⟨v,hvA⟩,hv,rfl⟩)
      rw [← lift_intervalSubspace K N A D]
      exact ⟨hvA,hv'⟩
    · intro h w hw
      obtain ⟨v,hv,rfl⟩ := (mem_intervalSubspace K N A B w).mp hw
      exact (mem_intervalSubspace K N A D _).mpr ⟨v,h hv,rfl⟩

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)

lemma interval_exists_normalized (hN : 0 < N) (A : Vertex K N) (B : ResidueInterval K N A) :
    ∃ D : Vertex K N, Homothetic (shift K N) B.val D.val := by
  obtain ⟨m,hm⟩ := vertex_bounded (shift K N) (standard K N) A
  obtain ⟨D,j,_,hj⟩ := exists_normalized (shift K N) (standard K N)
    (shift_standard_le K N) (standard_not_le_shift K N hN) (m+1) B.val
    (B.property.2.trans (vertex_le _ _ A))
    ((shift K N).monotone hm |>.trans B.property.1) (shift_le_self K N B.val)
  exact ⟨D,0,j,hj⟩

noncomputable def intervalNormalize (hN : 0 < N) (A : Vertex K N) (B : ResidueInterval K N A) :
    Vertex K N := (interval_exists_normalized K N hN A B).choose

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)
namespace FullChamber
variable {K N} {hN : 0 < N} (C : FullChamber K N hN)
noncomputable def face : Finset (Vertex K N) := Finset.univ.image C.vertex
end FullChamber

def codistanceStage (hN : 0 < N) (m : ℕ) : Set (Finset (Vertex K N)) :=
  {s | ∃ C : FullChamber K N hN, C.length ≤ m ∧ s ⊆ C.face}

end CoboundaryExpanders.RationalLattices

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

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))
lemma rotateStage_strict (hN : 0 < N) : StrictAnti (C.rotateStage hN) := by
  intro r s hrs
  have hr : r.val < N := by have := s.isLt; change r.val < s.val at hrs; omega
  rw [show C.rotateStage hN r = C.stage ⟨r.val+1,by omega⟩ from dite_eq_left hr]
  unfold rotateStage
  split_ifs with hs
  · exact C.strict (show (⟨r.val+1,by omega⟩ : Fin (N+1)) < ⟨s.val+1,by omega⟩ by
      change r.val < s.val at hrs; change r.val+1 < s.val+1; omega)
  · have hlt : powerShift (C.stage (C.nextIndex hN)) 1 < powerShift C.top 1 := by
      rw [← C.initial]
      apply powerShift_strictMono 1
      exact C.strict (show (0 : Fin (N+1)) < C.nextIndex hN from by change 0 < 1; omega)
    rw [← C.terminal] at hlt
    exact hlt.trans_le (C.strict.antitone (Fin.le_last _))
noncomputable def rotate (hN : 0 < N) : ResidueChamber (K := K) (N := N) where
  top := C.stage (C.nextIndex hN)
  hasTop := C.hasStage _
  stage := C.rotateStage hN
  hasStage := C.rotateStage_has hN
  strict := C.rotateStage_strict hN
  initial := by
    apply (dite_eq_left hN).trans
    rfl
  lower := C.rotateStage_lower hN

end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {N : ℕ}

lemma polynomial_map_le_standard (A : Submodule K[X] (PolynomialVectors.V K N)) :
    A.map (polynomialEmbedding K N) ≤ standard K N := by
  rintro v ⟨w,hw,rfl⟩ i
  exact ⟨w i,rfl⟩

def PolyBounded (A : Submodule K[X] (PolynomialVectors.V K N)) : Prop :=
  ∃ m, level (shift K N) (standard K N) m ≤ A.map (polynomialEmbedding K N)

lemma PolyBounded.mono {A B : Submodule K[X] (PolynomialVectors.V K N)}
    (hA : PolyBounded A) (hAB : A ≤ B) : PolyBounded B := by
  obtain ⟨m,hm⟩ := hA
  exact ⟨m,hm.trans (Submodule.map_mono hAB)⟩

lemma PolyBounded.powerShift {A : Submodule K[X] (PolynomialVectors.V K N)}
    (hA : PolyBounded A) (r : ℕ) : PolyBounded (powerShift A r) := by
  obtain ⟨m,hm⟩ := hA
  refine ⟨m+r,?_⟩
  rw [powerShift_map_embedding,level_add]
  exact level_mono _ _ hm

lemma polyBounded_vertex (A : Vertex K N) : PolyBounded (polynomialLattice K N A) := by
  unfold PolyBounded
  rw [polynomialLattice_map]
  exact vertex_bounded _ _ A

lemma normalizedPolynomial_exists (hN : 0 < N)
    (A : Submodule K[X] (PolynomialVectors.V K N)) (hA : PolyBounded A) :
    ∃ B : Vertex K N, ∃ m, A.map (polynomialEmbedding K N) = level (shift K N) B.val m := by
  obtain ⟨m,hm⟩ := hA
  obtain ⟨B,j,_,hj⟩ := exists_normalized (shift K N) (standard K N)
    (shift_standard_le K N) (standard_not_le_shift K N hN) m
    (A.map (polynomialEmbedding K N)) (polynomial_map_le_standard A) hm (shift_le_self K N _)
  exact ⟨B,j,hj⟩

noncomputable def normalizedPolynomial (hN : 0 < N)
    (A : Submodule K[X] (PolynomialVectors.V K N)) (hA : PolyBounded A) : Vertex K N :=
  (normalizedPolynomial_exists hN A hA).choose

namespace BoundedChamber
variable (C : ResidueChamber (K := K) (N := N)) (hC : PolyBounded C.top)
include hC in
lemma stage_bounded (r : Fin (N+1)) : PolyBounded (C.stage r) :=
  (hC.powerShift 1).mono (C.lower r)

noncomputable def vertex (hN : 0 < N) (r : Fin N) : Vertex K N :=
  normalizedPolynomial hN (C.stage r.castSucc) (stage_bounded C hC r.castSucc)
noncomputable def face (hN : 0 < N) : Finset (Vertex K N) :=
  Finset.univ.image (vertex C hC hN)
end BoundedChamber
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial
variable {K : Type} [Field K] {N : ℕ}
noncomputable def reroot (C : ResidueChamber (K := K) (N := N)) (hN : 0 < N) (j : ℕ) :
    ResidueChamber (K := K) (N := N) := (fun D : ResidueChamber (K := K) (N := N) => D.rotate hN)^[j] C
@[simp] lemma reroot_zero (C : ResidueChamber (K := K) (N := N)) (hN : 0 < N) : C.reroot hN 0 = C := rfl
lemma reroot_succ (C : ResidueChamber (K := K) (N := N)) (hN : 0 < N) (j : ℕ) :
    C.reroot hN (j+1) = (C.reroot hN j).rotate hN := Function.iterate_succ_apply' _ _ _
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {N M : ℕ}
variable (C : ResidueChamber (K := K) (N := N)) (hC : PolyBounded C.top)
include hC in
lemma rotate_bounded (hN : 0 < N) : PolyBounded (C.rotate hN).top := stage_bounded C hC _
include hC in
lemma reroot_bounded (hN : 0 < N) (j : ℕ) : PolyBounded (C.reroot hN j).top := by
  induction j with
  | zero => exact hC
  | succ j ih => rw [C.reroot_succ]; exact rotate_bounded _ ih _

end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.FullChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
noncomputable def descentCore (E : FullChamber K (M+2) (by omega)) : Finset (Vertex K (M+2)) :=
  (AffineWindow.descents (by omega) E.polynomialChamber.window).image
    (fun r => E.vertex (finRotate (M+2) r))
end CoboundaryExpanders.RationalLattices.FullChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {N : ℕ}

noncomputable def descentCore {M : ℕ} (C : ResidueChamber (K := K) (N := M+2))
    (hC : PolyBounded C.top) : Finset (Vertex K (M+2)) :=
  (AffineWindow.descents (by omega) C.window).image
    (fun r => vertex C hC (by omega) (finRotate (M+2) r))
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
def codistanceBlock (m : ℕ) (A : Finset (Vertex K (M+2))) : Set (Finset (Vertex K (M+2))) :=
  {s | ∃ C : FullChamber K (M+2) (by omega), C.length = m+1 ∧ C.descentCore = A ∧ s ⊆ C.face}

def codistanceLink (m : ℕ) (A : Finset (Vertex K (M+2))) :
    Set (Finset (Vertex K (M+2))) := {s | Disjoint A s ∧ s ∈ codistanceBlock m A}
end CoboundaryExpanders.RationalLattices

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_ChamberCones
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite pivots, polynomial residue-chamber links, and exactness via finite joins.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N M : ℕ}

lemma constant_remainder_mem_diagonal (b : Fin N → V K N) (s : Finset (Fin N))
    (f : Fin N → K[X]) :
    (∑ i, (f i - if i ∈ s then Polynomial.C ((f i).coeff 0) else 0) • b i) ∈
      diagonalModule b s := by
  classical
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i ∈ s
  · simp only [ite_eq_left hi]
    have hd : Polynomial.X ∣ f i-Polynomial.C ((f i).coeff 0) := by
      apply Polynomial.X_dvd_iff.mpr
      simp
    obtain ⟨q,hq⟩ := hd
    rw [hq,mul_comm, mul_smul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i,by simp [diagonalFamily,hi]⟩
  · simp only [ite_eq_right hi,sub_zero]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i,by simp [diagonalFamily,hi]⟩

lemma selectedSection_mem_of_combination (b : Fin N → V K N) (σ : Fin M → Fin N)
    (hσ : Function.Injective σ) (D : Submodule K[X] (V K N))
    (hCD : diagonalModule b (Finset.univ.image σ) ≤ D)
    (f : Fin N → K[X]) (hf : (∑ i, f i • b i) ∈ D) :
    selectedSection b σ (fun r => (f (σ r)).coeff 0) ∈ D := by
  classical
  let s := Finset.univ.image σ
  let g (i : Fin N) : K[X] := if i ∈ s then Polynomial.C ((f i).coeff 0) else 0
  have hg : (∑ i, g i • b i) = selectedSection b σ (fun r => (f (σ r)).coeff 0) := by
    rw [selectedSection_polynomial]
    calc
      (∑ i, g i • b i) = ∑ i ∈ s, Polynomial.C ((f i).coeff 0) • b i := by
        simp only [g,ite_smul,zero_smul,← Finset.sum_filter]
        simp
      _ = ∑ r, Polynomial.C ((f (σ r)).coeff 0) • b (σ r) := Finset.sum_image hσ.injOn
  have hc : (∑ i, (f i-g i) • b i) ∈ D := hCD (constant_remainder_mem_diagonal b s f)
  have hh := D.sub_mem hf hc
  have he : (∑ i, f i • b i) - (∑ i, (f i-g i) • b i) = ∑ i, g i • b i := by
    simp only [sub_smul,Finset.sum_sub_distrib,sub_sub_cancel]
  rw [he,hg] at hh
  exact hh

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N M : ℕ}

lemma selectedSection_mem_diagonal_iff (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val)) (x : Fin M → K) :
    selectedSection b σ x ∈ diagonalModule b (Finset.univ.image σ) ↔ x = 0 := by
  classical
  constructor
  · intro hx
    by_contra hn
    obtain ⟨r,hr⟩ := FinitePivots.exists_leading hn
    have hl := selectedSection_leading b a hb σ hσ x r hr
    have hh := pivotDegree_min _ (diagonal_hasPivots b a hb (Finset.univ.image σ)) (σ r) hx hl
    rw [diagonal_pivotDegree b a hb] at hh
    have hm : σ r ∈ Finset.univ.image σ := Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
    simp only [ite_eq_left hm] at hh
    omega
  · rintro rfl
    rw [map_zero]
    exact Submodule.zero_mem _

lemma combination_sub_selected_mem (b : Fin N → V K N) (σ : Fin M → Fin N)
    (hσ : Function.Injective σ) (f : Fin N → K[X]) :
    (∑ i, f i • b i) - selectedSection b σ (fun r => (f (σ r)).coeff 0) ∈
      diagonalModule b (Finset.univ.image σ) := by
  classical
  let s := Finset.univ.image σ
  let g (i : Fin N) : K[X] := if i ∈ s then Polynomial.C ((f i).coeff 0) else 0
  have hg : (∑ i, g i • b i) = selectedSection b σ (fun r => (f (σ r)).coeff 0) := by
    rw [selectedSection_polynomial]
    calc
      (∑ i, g i • b i) = ∑ i ∈ s, Polynomial.C ((f i).coeff 0) • b i := by
        simp only [g,ite_smul,zero_smul,← Finset.sum_filter]
        simp
      _ = ∑ r, Polynomial.C ((f (σ r)).coeff 0) • b (σ r) := Finset.sum_image hσ.injOn
  rw [← hg,← Finset.sum_sub_distrib]
  simp only [← sub_smul]
  exact constant_remainder_mem_diagonal b s f

lemma selectedResidue_liftSelected (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val)) (W : Submodule K (Fin M → K)) :
    selectedResidue b σ (liftSelected b σ W) = W := by
  ext x
  constructor
  · rintro ⟨c,hc,y,hy,he⟩
    have hh : selectedSection b σ (x-y) = c := by rw [map_sub,he]; abel
    have hz := (selectedSection_mem_diagonal_iff b a hb σ hσ (x-y)).mp (hh ▸ hc)
    have hxy := sub_eq_zero.mp hz
    exact hxy ▸ hy
  · intro hx
    exact ⟨0,Submodule.zero_mem _,x,hx,by simp⟩

lemma liftSelected_selectedResidue (b : Fin N → V K N) (σ : Fin M → Fin N)
    (hσ : Function.Injective σ) (D : Submodule K[X] (V K N))
    (hCD : diagonalModule b (Finset.univ.image σ) ≤ D)
    (hDA : D ≤ Submodule.span K[X] (Set.range b)) :
    liftSelected b σ (selectedResidue b σ D) = D := by
  apply le_antisymm
  · rintro v ⟨c,hc,x,hx,rfl⟩
    exact D.add_mem (hCD hc) hx
  · intro v hv
    obtain ⟨f,hf⟩ := (Submodule.mem_span_range_iff_exists_fun K[X]).mp (hDA hv)
    let x := fun r => (f (σ r)).coeff 0
    refine ⟨v-selectedSection b σ x,?_,x,?_,by abel⟩
    · rw [← hf]
      exact combination_sub_selected_mem b σ hσ f
    · exact selectedSection_mem_of_combination b σ hσ D hCD f (hf ▸ hv)

noncomputable def selectedIntervalEquiv (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val)) :
    {D : Submodule K[X] (V K N) // diagonalModule b (Finset.univ.image σ) ≤ D ∧
      D ≤ Submodule.span K[X] (Set.range b)} ≃o Submodule K (Fin M → K) where
  toFun D := selectedResidue b σ D.val
  invFun W := ⟨liftSelected b σ W,diagonal_le_liftSelected b σ W,liftSelected_le_span b σ W⟩
  left_inv D := Subtype.ext (liftSelected_selectedResidue b σ
    (fun i j he => hσ.injective (congrArg (fun t => N*a t+t.val) he)) D.val D.property.1 D.property.2)
  right_inv W := selectedResidue_liftSelected b a hb σ hσ W
  map_rel_iff' := by
    intro D E
    constructor
    · intro h
      change D.val ≤ E.val
      rw [← liftSelected_selectedResidue b σ
        (fun i j he => hσ.injective (congrArg (fun t => N*a t+t.val) he)) D.val D.property.1 D.property.2]
      rintro v ⟨c,hc,x,hx,rfl⟩
      exact E.val.add_mem (E.property.1 hc) (h hx)
    · intro h x hx
      exact h hx

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.FinitePivots
open Module
variable {K : Type} [Field K] {N : ℕ}

noncomputable def prefixFlag (K : Type) [Field K] (N : ℕ) :
    SphericalOpposition.CompleteFlag K (Fin N → K) N where
  space i := prefSpace K N i.val
  mono := by intro i j hij v hv l hl; exact hv l (le_trans hij hl)
  dimension := by simp
  rank i := prefSpace_finrank i.val (by omega)

end CoboundaryExpanders.FinitePivots

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
open Module InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K : Type} [Field K] {N M : ℕ}

def prefixPatternComplex (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N) :
    InfiniteChains.Complex (SelectedInterval b σ) where
  faces := {s | (∀ D ∈ s, PrefixPattern b a hb σ D) ∧
    (s : Set (SelectedInterval b σ)).Pairwise (fun D E => D ≤ E ∨ E ≤ D)}
  empty_mem := by simp
  downward := by intro s t hs hts; exact ⟨fun D hD => hs.1 D (hts hD),hs.2.mono hts⟩

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))
noncomputable def blockBasis (b : Fin N → V K N) (a : Fin (N+1)) : Fin N → V K N :=
  diagonalFamily b (wordPrefix C.word a)
noncomputable def blockDegree (a : Fin (N+1)) (i : Fin N) : ℕ :=
  pivotDegree C.top C.hasTop i + if (C.word.symm i).val < a.val then 1 else 0
lemma blockBasis_leading (b : Fin N → V K N)
    (hb : ∀ i, Leading (b i) i (pivotDegree C.top C.hasTop i)) (a : Fin (N+1)) (i : Fin N) :
    Leading (C.blockBasis b a i) i (C.blockDegree a i) := by
  simpa only [blockBasis,blockDegree,wordPrefix,Finset.mem_filter,Finset.mem_univ,true_and] using
    diagonal_leading b _ hb (wordPrefix C.word a) i
lemma block_upper (b : Fin N → V K N)
    (hb : ∀ r, C.stage r = diagonalModule b (wordPrefix C.word r)) (a : Fin (N+1)) :
    Submodule.span K[X] (Set.range (C.blockBasis b a)) = C.stage a := (hb a).symm
lemma block_lower (b : Fin N → V K N)
    (hb : ∀ r, C.stage r = diagonalModule b (wordPrefix C.word r)) (a z : Fin (N+1)) (haz : a ≤ z) :
    diagonalModule (C.blockBasis b a) (Finset.univ.image (wordSlice C.word a z)) = C.stage z := by
  rw [blockBasis,diagonalModule_union b _ _ (wordPrefix_disjoint_slice C.word a z),
    wordPrefix_union_slice C.word a z haz,← hb z]
end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}
variable (C : ResidueChamber (K := K) (N := N))
def HasProfile (D : Submodule K[X] (V K N)) (r : Fin (N+1)) : Prop :=
  ∃ hD : HasPivots D, ∀ i, pivotDegree D hD i = pivotDegree C.top C.hasTop i +
    if (C.word.symm i).val < r.val then 1 else 0

lemma prefixPattern_iff_profile (b : Fin N → V K N)
    (hb : ∀ i, Leading (b i) i (pivotDegree C.top C.hasTop i))
    (a z : Fin (N+1)) (haz : a ≤ z)
    (D : SelectedInterval (C.blockBasis b a) (wordSlice C.word a z)) :
    PrefixPattern (C.blockBasis b a) (C.blockDegree a) (C.blockBasis_leading b hb a)
      (wordSlice C.word a z) D ↔
      ∃ r : Fin (N+1), a < r ∧ r < z ∧ C.HasProfile D.val r := by
  let hDP := selectedInterval_hasPivots (C.blockBasis b a) (C.blockDegree a)
    (C.blockBasis_leading b hb a) (wordSlice C.word a z) D
  constructor
  · rintro ⟨k,hk0,hkz,hpat⟩
    let r : Fin (N+1) := ⟨a.val+k,by have := z.isLt; omega⟩
    refine ⟨r,(by change a.val < a.val+k; omega),(by change a.val+k < z.val; omega),hDP,?_⟩
    intro i
    have hp := selected_pivot_bounds (C.blockBasis b a) (C.blockDegree a)
      (C.blockBasis_leading b hb a) (wordSlice C.word a z) D i
    by_cases hi : i ∈ Finset.univ.image (wordSlice C.word a z)
    · obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hi
      have he := hpat s
      have hb0 : C.blockDegree a (wordSlice C.word a z s) =
          pivotDegree C.top C.hasTop (wordSlice C.word a z s) := by
        simp only [blockDegree,wordSlice,Equiv.symm_apply_apply,Fin.val_mk]
        rw [ite_eq_right (by omega),Nat.add_zero]
      rw [hb0] at hp he
      have hm : wordSlice C.word a z s ∈ Finset.univ.image (wordSlice C.word a z) :=
        Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩
      simp only [hm,ite_true] at hp
      dsimp only [wordSlice] at hp he
      simp only [wordSlice,Equiv.symm_apply_apply,Fin.val_mk]
      change pivotDegree D.val hDP _ = pivotDegree C.top C.hasTop _ +
        if a.val+s.val < a.val+k then 1 else 0
      split_ifs <;> omega
    · have hn := (mem_wordSlice_image C.word a z i).not.mp hi
      simp only [hi,ite_false,Nat.add_zero] at hp
      have he := le_antisymm hp.2 hp.1
      rw [he]
      dsimp only [blockDegree,r]
      split_ifs <;> omega
  · rintro ⟨r,har,hrz,hprof⟩
    obtain ⟨hD,hdeg⟩ := hprof
    refine ⟨r.val-a.val,(by change a.val < r.val at har; omega),?_,?_⟩
    · change r.val < z.val at hrz
      change a.val < r.val at har
      omega
    · intro s
      rw [hdeg]
      simp only [wordSlice,blockDegree,Equiv.symm_apply_apply,Fin.val_mk]
      simp only [ite_eq_right (show ¬ a.val+s.val < a.val from by omega),Nat.add_zero]
      change a.val < r.val at har
      split_ifs <;> omega
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open InfiniteChains AffineWindow
variable {K : Type} [Field K] {N L : ℕ}
variable (C : ResidueChamber (K := K) (N := N))

noncomputable def fixedStages (c : Fin (L+1) → Fin (N+1)) : Finset (Submodule K[X] (V K N)) :=
  Finset.univ.image (fun j => C.stage (c j))

def IntervalProfile (c : Fin (L+1) → Fin (N+1)) (D : Submodule K[X] (V K N)) : Prop :=
  ∃ j : Fin L, C.stage (c j.succ) ≤ D ∧ D ≤ C.stage (c j.castSucc) ∧
    ∃ r : Fin (N+1), c j.castSucc < r ∧ r < c j.succ ∧ C.HasProfile D r

def rootedMinimumLink (c : Fin (L+1) → Fin (N+1)) : InfiniteChains.Complex (Submodule K[X] (V K N)) where
  faces := {s | Disjoint s (C.fixedStages c) ∧ ∃ E : ResidueChamber (K := K) (N := N),
    E.top = C.top ∧ E.length = C.length ∧ (∀ j, E.stage (c j) = C.stage (c j)) ∧
    ∀ D ∈ s, ∃ r, E.stage r = D}
  empty_mem := by exact ⟨Finset.disjoint_empty_left _,C,rfl,rfl,(fun _ => rfl),by simp⟩
  downward := by
    intro s t hs hts
    obtain ⟨hd,E,ht,hl,hfix,hface⟩ := hs
    exact ⟨hd.mono_left hts,E,ht,hl,hfix,fun D hD => hface D (hts hD)⟩

end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K : Type} [Field K] {N : ℕ}
variable (C : ResidueChamber (K := K) (N := N))
def ProfileBetween (a z : Fin (N+1)) (D : Submodule K[X] (V K N)) : Prop :=
  C.stage z ≤ D ∧ D ≤ C.stage a ∧ ∃ r : Fin (N+1), a < r ∧ r < z ∧ C.HasProfile D r
def profileIntervalComplex (a z : Fin (N+1)) : InfiniteChains.Complex (Submodule K[X] (V K N)) where
  faces := {s | (∀ D ∈ s, C.ProfileBetween a z D) ∧
    (s : Set (Submodule K[X] (V K N))).Pairwise (fun D E => D ≤ E ∨ E ≤ D)}
  empty_mem := by simp
  downward := by intro s t hs hts; exact ⟨fun D hD => hs.1 D (hts hD),hs.2.mono hts⟩
lemma profileInterval_faces_selected (b : Fin N → V K N)
    (hb : ∀ i, Leading (b i) i (pivotDegree C.top C.hasTop i))
    (hstage : ∀ r, C.stage r = diagonalModule b (wordPrefix C.word r))
    (a z : Fin (N+1)) (haz : a ≤ z)
    (s : Finset (SelectedInterval (C.blockBasis b a) (wordSlice C.word a z))) :
    s ∈ (prefixPatternComplex (C.blockBasis b a) (C.blockDegree a) (C.blockBasis_leading b hb a)
      (wordSlice C.word a z)).faces ↔ s.image Subtype.val ∈ (C.profileIntervalComplex a z).faces := by
  classical
  constructor
  · rintro ⟨hpat,hpair⟩
    constructor
    · intro D hD
      obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hD
      refine ⟨?_,?_,(C.prefixPattern_iff_profile b hb a z haz E).mp (hpat E hE)⟩
      · simpa only [C.block_lower b hstage a z haz] using E.property.1
      · simpa only [C.block_upper b hstage a] using E.property.2
    · intro D hD E hE hne
      obtain ⟨D,hDs,rfl⟩ := Finset.mem_image.mp hD
      obtain ⟨E,hEs,rfl⟩ := Finset.mem_image.mp hE
      exact hpair hDs hEs (fun hh => hne (congrArg Subtype.val hh))
  · rintro ⟨hprof,hpair⟩
    constructor
    · intro D hD
      exact (C.prefixPattern_iff_profile b hb a z haz D).mpr
        (hprof D.val (Finset.mem_image.mpr ⟨D,hD,rfl⟩)).2.2
    · intro D hD E hE hne
      exact hpair (Finset.mem_image.mpr ⟨D,hD,rfl⟩) (Finset.mem_image.mpr ⟨E,hE,rfl⟩)
        (fun hh => hne (Subtype.ext hh))
noncomputable def profileIntervalCone (b : Fin N → V K N)
    (hb : ∀ i, Leading (b i) i (pivotDegree C.top C.hasTop i))
    (hstage : ∀ r, C.stage r = diagonalModule b (wordPrefix C.word r))
    (a z : Fin (N+1)) (haz : a ≤ z) {n R : ℕ}
    (H : BoundedCone (prefixPatternComplex (C.blockBasis b a) (C.blockDegree a)
      (C.blockBasis_leading b hb a) (wordSlice C.word a z)) n R) :
    BoundedCone (C.profileIntervalComplex a z) n R := by
  classical
  let A := SelectedInterval (C.blockBasis b a) (wordSlice C.word a z)
  let d0 : A := ⟨C.stage a,by rw [C.block_lower b hstage a z haz]; exact C.strict.antitone haz,
    by rw [C.block_upper b hstage a]⟩
  let f : Submodule K[X] (V K N) → A := fun D =>
    if h : C.stage z ≤ D ∧ D ≤ C.stage a then
      ⟨D,by rw [C.block_lower b hstage a z haz]; exact h.1,
        by rw [C.block_upper b hstage a]; exact h.2⟩ else d0
  have hfval (D : Submodule K[X] (V K N)) (hD : C.stage z ≤ D ∧ D ≤ C.stage a) : (f D).val = D := by
    simp only [f,dite_eq_left hD]
  have hret (s) (hs : s ∈ (C.profileIntervalComplex a z).faces) (D) (hD : D ∈ s) : (f D).val = D :=
    hfval D ⟨(hs.1 D hD).1,(hs.1 D hD).2.1⟩
  have him (s) (hs : s ∈ (C.profileIntervalComplex a z).faces) : (s.image f).image Subtype.val = s := by
    rw [Finset.image_image]
    exact (Finset.image_congr (fun D hD => hret s hs D hD)).trans (Finset.image_id)
  refine H.retract f Subtype.val ?_ ?_ ?_ (fun _ _ => Subtype.val_injective.injOn) hret
  · intro s hs
    apply (C.profileInterval_faces_selected b hb hstage a z haz (s.image f)).mpr
    rwa [him s hs]
  · intro s hs
    exact (C.profileInterval_faces_selected b hb hstage a z haz s).mp hs
  · intro s hs D hD E hE hh
    have he := congrArg Subtype.val hh
    rwa [hret s hs D hD,hret s hs E hE] at he

end CoboundaryExpanders.PolynomialVectors.ResidueChamber

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Mixing
attribute [-instance] _root_.OAI.CoboundaryExpanders.Blocks.gammaNormal _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.complexInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.kernelInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexMulAction
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

open Elementary
variable (p n m : ℕ) [Fact p.Prime]

def truncatedIwahori (hm : 1 ≤ m) :
    Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) (Trunc p m)) :=
  (upperUnitriangular p (n + 1)).comap (Matrix.SpecialLinearGroup.map (residue p m hm))

def reducedGenerated (hn : 1 ≤ n) :=
  (cycleGenerated p n hn).map (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)))

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains FiniteWeights Cone
open scoped Pointwise
variable {G I : Type} [Group G] [Fintype G] [DecidableEq I] [Fintype I] (H : I → Subgroup G)
noncomputable instance vertexFintype : Fintype (Vertex H) := Fintype.ofFinite _

end CoboundaryExpanders.TypedCosetFaces

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Expansion
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.TypedCosetFaces.complexInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.kernelInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Local repairs, fat-ladder inequalities, and uniform raw cosystolic expansion.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.InfiniteChains
namespace FiniteWeights
open Cone Averaging
open scoped Pointwise
variable {V : Type} [DecidableEq V] [Fintype V]
attribute [local instance] Classical.propDecidable

def rawNorm (X : CoboundaryExpanders.InfiniteChains.Complex V) (N r : ℕ) (f : Finset V → k) : ℝ :=
  ∑ s ∈ level X r, if f s ≠ 0 then (cofaces X N s:ℝ) else 0

end FiniteWeights
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.TypedCosetFaces

section
open InfiniteChains
open scoped Pointwise
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

def faceStabilizer (s : Finset (Vertex H)) : Subgroup G := MulAction.stabilizer G s

end

open InfiniteChains FiniteWeights Cone
open scoped Pointwise

end CoboundaryExpanders.TypedCosetFaces

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Frames
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
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

namespace CoboundaryExpanders.InfiniteChains.BadSimplex
open Attachment
variable {W V : Type} [DecidableEq W] [DecidableEq V]

def stage (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (r : ℕ) : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V) where
  faces := {s | s ∈ X.faces ∧ s.toLeft.card ≤ r}
  empty_mem := ⟨X.empty_mem, by simp [Finset.toLeft]⟩
  downward := by
    intro s t hs ht
    exact ⟨X.downward hs.1 ht,
      (Finset.card_le_card (Finset.toLeft_subset_toLeft ht)).trans hs.2⟩

def goodLink (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (F : Finset W)
    (hF : F.disjSum (∅ : Finset V) ∈ X.faces) : CoboundaryExpanders.InfiniteChains.Complex V where
  faces := {t | F.disjSum t ∈ X.faces}
  empty_mem := hF
  downward := by
    intro s t hs ht
    exact X.downward hs (Finset.disjSum_mono (by rfl) ht)

abbrev BadFaces (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (r : ℕ) :=
  {F : Finset W // F.disjSum (∅ : Finset V) ∈ X.faces ∧ F.card = r+1}

end CoboundaryExpanders.InfiniteChains.BadSimplex

end

noncomputable section


namespace CoboundaryExpanders.InfiniteChains.ChainTransport
open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]
def relabel (f : V → W) : Raw V →ₗ[k] Raw W :=
  Finsupp.lmapDomain k k (Finset.image f)

omit [DecidableEq V] in
@[simp] lemma relabel_single (f : V → W) (s : Finset V) (a : k) :
    relabel f (Finsupp.single s a) = Finsupp.single (s.image f) a := by
  simp [relabel]

end CoboundaryExpanders.InfiniteChains.ChainTransport

end

noncomputable section


namespace CoboundaryExpanders.InfiniteChains.HeightReduction
open Attachment BadSimplex ChainTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type} [DecidableEq V]

def bounded (X : CoboundaryExpanders.InfiniteChains.Complex V) (h : V → ℕ) (H : ℕ) : CoboundaryExpanders.InfiniteChains.Complex V where
  faces := {s | s ∈ X.faces ∧ ∀ v ∈ s, h v ≤ H}
  empty_mem := ⟨X.empty_mem, by simp⟩
  downward := by
    intro s t hs ht
    exact ⟨X.downward hs.1 ht, fun v hv => hs.2 v (ht hv)⟩

def splitComplex (X : CoboundaryExpanders.InfiniteChains.Complex V) (h : V → ℕ) (H : ℕ) : CoboundaryExpanders.InfiniteChains.Complex (Bad h H ⊕ Good h H) where
  faces := {s | s.image (split h H) ∈ (bounded X h H).faces}
  empty_mem := by simpa using (bounded X h H).empty_mem
  downward := by
    intro s t hs ht
    exact (bounded X h H).downward hs (Finset.image_mono _ ht)

end CoboundaryExpanders.InfiniteChains.HeightReduction

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

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory

namespace CoboundaryExpanders.Transfer

section
open CategoryTheory Representation Finsupp
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

def barCoinvariantInclusion :
    CoinvariantModel.complex (k := k) (G := S) ⟶ subgroupChains S (Rep.barComplex k G) :=
  ((Rep.coinvariantsFunctor k S).mapHomologicalComplex _).map
    (BarComparison.inclusion (k := k) S)

end

open Representation
universe u

end CoboundaryExpanders.Transfer

namespace CoboundaryExpanders.Transfer
open Representation Finsupp
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

def barCoinvariantAdjusted (g : G) : CoinvariantModel.complex (k := k) (G := S) ⟶
    subgroupChains S (Rep.barComplex k G) :=
  ((Rep.coinvariantsFunctor k S).mapHomologicalComplex _).map
    (BarComparison.adjusted S g)

end CoboundaryExpanders.Transfer

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Coinvariants
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype _root_.OAI.CoboundaryExpanders.MatrixOpposition.cutVertexFintype _root_.OAI.CoboundaryExpanders.TypedCosetFaces.kernelInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexAction _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexFintype
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

namespace CoboundaryExpanders.FinsuppPermutation
open CategoryTheory
variable (k G A : Type) [CommRing k] [Group G] [MulAction G A]

def coeffIso : Rep.ofMulAction k G A ≅ rep k G A :=
  Rep.mkIso { MonoidAlgebra.coeffLinearEquiv k with
    isIntertwining' := by
      intro g
      apply MonoidAlgebra.lhom_ext'
      intro a
      apply LinearMap.ext
      intro r
      simp [ρ_single] }

end CoboundaryExpanders.FinsuppPermutation

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

instance basisMulAction (n : ℕ) : MulAction G (Basis H n) where
  smul g x := ⟨x.1, g • x.2⟩
  one_smul x := congrArg (Sigma.mk x.1) (one_smul G x.2)
  mul_smul g h x := congrArg (Sigma.mk x.1) (mul_smul g h x.2)

def gradedEquiv (n : ℕ) : Basis H n ≃ (complex H).Face n :=
  Equiv.ofBijective (gradedFace H n) (gradedFace_bijective H n)

lemma gradedFace_smul (n : ℕ) (g : G) (x : Basis H n) :
    gradedFace H n (g • x) = g • gradedFace H n x := by
  rcases x with ⟨A,x⟩
  induction x using Quotient.inductionOn with | h h =>
  apply Subtype.ext
  change face H (g*h) A.val = (face H h A.val).map (MulAction.toPerm g).toEmbedding
  exact (map_face H g h A.val).symm

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

def extend (H : Subgroup G) (A : Rep k G) (x : A)
    (hx : ∀ h : H, A.ρ h x = x) : permutation (k := k) H ⟶ A :=
  Rep.ofHom ⟨(Finsupp.linearCombination k (orbitVector H A x hx)).comp (MonoidAlgebra.coeffLinearEquiv k).toLinearMap, by
    intro g
    apply MonoidAlgebra.lhom_ext'
    intro q
    apply LinearMap.ext
    intro r
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply,
      Representation.ofMulAction_single]
    change (Finsupp.linearCombination k (orbitVector H A x hx)) (Finsupp.single (g • q) r) =
      A.ρ g ((Finsupp.linearCombination k (orbitVector H A x hx)) (Finsupp.single q r))
    simp only [Finsupp.linearCombination_single, map_smul, orbitVector_smul]⟩

@[simp] theorem extend_single (H : Subgroup G) (A : Rep k G) (x : A)
    (hx : ∀ h : H, A.ρ h x = x) (a : G) (r : k) :
    extend H A x hx (MonoidAlgebra.single (QuotientGroup.mk a) r) = r • A.ρ a x := by
  change (Finsupp.linearCombination k (orbitVector H A x hx))
    (Finsupp.single (QuotientGroup.mk a) r) = _
  rw [Finsupp.linearCombination_single, orbitVector_mk]

def base (H : Subgroup G) : Rep.trivial k H k ⟶ Rep.res H.subtype (permutation (k := k) H) :=
  Rep.ofHom ⟨MonoidAlgebra.lsingle (QuotientGroup.mk (1 : G)), by
    intro h
    apply LinearMap.ext
    intro r
    change MonoidAlgebra.single (QuotientGroup.mk (1 : G)) r =
      (Representation.ofMulAction k G (G ⧸ H)) h (MonoidAlgebra.single (QuotientGroup.mk (1 : G)) r)
    rw [Representation.ofMulAction_single]
    congr 1
    change (QuotientGroup.mk (1 : G) : G ⧸ H) = QuotientGroup.mk (h.val * 1)
    simp only [mul_one]
    apply Quotient.sound
    simpa only [QuotientGroup.leftRel_apply, inv_one, one_mul] using h.property⟩

theorem projective_permutation (H : Subgroup G) [Projective (Rep.trivial k H k)] :
    Projective (permutation (k := k) H) where
  factors {E X} f e he := by
    let f₀ : Rep.trivial k H k ⟶ Rep.res H.subtype X :=
      base H ≫ (Rep.resFunctor (k := k) H.subtype).map f
    let e₀ : Rep.res H.subtype E ⟶ Rep.res H.subtype X :=
      (Rep.resFunctor (k := k) H.subtype).map e
    have : Epi e₀ := by
      apply (Rep.epi_iff_surjective e₀).mpr
      exact (Rep.epi_iff_surjective e).mp he
    let l := Projective.factorThru f₀ e₀
    let x : E := l 1
    have hx : ∀ h : H, E.ρ h x = x := by
      intro h
      have hh := Rep.hom_comm_apply l h 1
      simpa [x] using hh.symm
    refine ⟨extend H E x hx, ?_⟩
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro q
    apply LinearMap.ext
    intro r
    induction q using Quotient.inductionOn with | h a =>
      have hbase : e x = f (MonoidAlgebra.single (QuotientGroup.mk (1 : G)) (1 : k)) := by
        have hh := congrArg (fun z => z 1) (Projective.factorThru_comp f₀ e₀)
        exact hh
      change e (extend H E x hx (MonoidAlgebra.single (QuotientGroup.mk a) r)) =
        f (MonoidAlgebra.single (QuotientGroup.mk a) r)
      rw [extend_single, map_smul, Rep.hom_comm_apply, hbase]
      have hf := Rep.hom_comm_apply f a (MonoidAlgebra.single (QuotientGroup.mk (1 : G)) (1 : k))
      rw [← hf]
      simp only [Representation.ofMulAction_single]
      change r • f (MonoidAlgebra.single (QuotientGroup.mk (a * 1)) 1) = _
      rw [mul_one, ← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

theorem projective_permutation_of_invertible_order (H : Subgroup G)
    [Finite H] [NeZero (Nat.card H : k)] : Projective (permutation (k := k) H) := by
  let A := Rep.trivial k H k
  let M := Rep.toModuleMonoidAlgebra.obj A
  let : Module.Projective (MonoidAlgebra k H) M :=
    Module.projective_of_isSemisimpleRing _ _
  have : Projective M := inferInstance
  have : Projective A :=
    Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective A
      (inferInstance : Projective M)
  exact projective_permutation H

end

theorem projective_permutation_of_odd_order {G : Type} [Group G]
    (H : Subgroup G) [Finite H] (hH : Odd (Nat.card H)) :
    Projective (permutation (k := ZMod 2) H) := by
  have hc : (Nat.card H : ZMod 2) = 1 := by
    rcases hH with ⟨r, hr⟩
    rw [hr]
    have htwo : (2 : ZMod 2) = 0 := by decide
    simp [Nat.cast_add, Nat.cast_mul, htwo]
  let : NeZero (Nat.card H : ZMod 2) := ⟨by rw [hc]; exact one_ne_zero⟩
  exact projective_permutation_of_invertible_order H
end CoboundaryExpanders.CosetModules

namespace CoboundaryExpanders.CosetSums
variable {k G I : Type} [Field k] [Group G] (H : I → Subgroup G)

def inclusion (i : I) : CosetModules.permutation (k := k) (H i) ⟶ permutation (k := k) H :=
  Rep.ofHom ⟨(Finsupp.linearCombination k (fun q : G ⧸ H i =>
    MonoidAlgebra.single (⟨i,q⟩ : Basis H) (1 : k))).comp
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap, by
    intro g
    apply MonoidAlgebra.lhom_ext'
    intro q
    apply LinearMap.ext
    intro r
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply,
      Representation.ofMulAction_single]
    change Finsupp.linearCombination _ _ (Finsupp.single (g • q) r) =
      (Representation.ofMulAction k G (Basis H)) g
        (Finsupp.linearCombination _ _ (Finsupp.single q r))
    simp [Representation.ofMulAction_single]
    rfl⟩

@[simp] theorem inclusion_single (i : I) (q : G ⧸ H i) (r : k) :
    inclusion (k := k) H i (MonoidAlgebra.single q r) =
      MonoidAlgebra.single (⟨i,q⟩ : Basis H) r := by
  change Finsupp.linearCombination _ _ (Finsupp.single q r) = _
  simp

def descend (A : Rep k G) (f : ∀ i, CosetModules.permutation (k := k) (H i) ⟶ A) :
    permutation (k := k) H ⟶ A :=
  Rep.ofHom ⟨(Finsupp.linearCombination k (fun x : Basis H =>
    f x.1 (MonoidAlgebra.single x.2 (1 : k)))).comp
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap, by
    intro g
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext
    intro r
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply,
      Representation.ofMulAction_single]
    change Finsupp.linearCombination _ _ (Finsupp.single (g • x) r) =
      A.ρ g (Finsupp.linearCombination _ _ (Finsupp.single x r))
    simp only [Finsupp.linearCombination_single, map_smul]
    congr 1
    change (f x.1).hom (MonoidAlgebra.single (g • x.2) (1 : k)) =
      A.ρ g ((f x.1).hom (MonoidAlgebra.single x.2 (1 : k)))
    have hh := Rep.hom_comm_apply (f x.1) g (MonoidAlgebra.single x.2 (1 : k))
    rw [Representation.ofMulAction_single] at hh
    exact hh⟩

@[simp] theorem descend_single (A : Rep k G)
    (f : ∀ i, CosetModules.permutation (k := k) (H i) ⟶ A)
    (x : Basis H) (r : k) :
    descend H A f (MonoidAlgebra.single x r) = f x.1 (MonoidAlgebra.single x.2 r) := by
  change Finsupp.linearCombination _ _ (Finsupp.single x r) = _
  simp [← map_smul]

theorem projective [∀ i, Projective (CosetModules.permutation (k := k) (H i))] :
    Projective (permutation (k := k) H) where
  factors {E X} f e he := by
    let l := fun i => Projective.factorThru (inclusion H i ≫ f) e
    refine ⟨descend H E l, ?_⟩
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext
    intro r
    change e (descend H E l (MonoidAlgebra.single x r)) = f (MonoidAlgebra.single x r)
    rw [descend_single]
    have hh := congrArg (fun z => z (MonoidAlgebra.single x.2 r))
      (Projective.factorThru_comp (inclusion H x.1 ≫ f) e)
    change e (l x.1 (MonoidAlgebra.single x.2 r)) =
      f (inclusion H x.1 (MonoidAlgebra.single x.2 r)) at hh
    exact hh.trans (congrArg (fun z => f z) (inclusion_single H x.1 x.2 r))

theorem projective_of_odd_order [∀ i, Finite (H i)] (hH : ∀ i, Odd (Nat.card (H i))) :
    Projective (permutation (k := ZMod 2) H) := by
  let _ : ∀ i, Projective (CosetModules.permutation (k := ZMod 2) (H i)) :=
    fun i => CosetModules.projective_permutation_of_odd_order (H i) (hH i)
  exact projective H
end CoboundaryExpanders.CosetSums

namespace CoboundaryExpanders.TypedCosetFaces

section
open CategoryTheory
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

def chainsIso (n : ℕ) :
    CosetSums.permutation (k := ZMod 2) (fun A : Types (I := I) n => stabilizer H A.val) ≅
      (complex H).chainsRep (G := G) n :=
  FinsuppPermutation.coeffIso _ _ _ ≪≫ Rep.mkIso {
    (Finsupp.domLCongr (gradedEquiv H n) : _ ≃ₗ[ZMod 2] _) with
    isIntertwining' := by
      intro g
      apply Finsupp.lhom_ext'
      intro x
      apply LinearMap.ext
      intro r
      change (Finsupp.domLCongr (gradedEquiv H n) : _ ≃ₗ[ZMod 2] _)
        (FinsuppPermutation.ρ (ZMod 2) G _ g (Finsupp.single x r)) =
        FinsuppPermutation.ρ (ZMod 2) G _ g
          ((Finsupp.domLCongr (gradedEquiv H n) : _ ≃ₗ[ZMod 2] _) (Finsupp.single x r))
      simp only [FinsuppPermutation.ρ_single, Finsupp.domLCongr_single]
      exact congrArg (fun s => Finsupp.single s r) (gradedFace_smul H n g x) }

end

open InfiniteChains
open CategoryTheory
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

lemma face_orbit_base (n : ℕ) (s : (complex H).Face n) :
    ∃ g : G, g • baseFace H n (typeFace H n s) = s := by
  obtain ⟨g,A,hA⟩ := s.property.1
  refine ⟨g, Subtype.ext ?_⟩
  change (face H 1 (types H s.val)).map (MulAction.toPerm g).toEmbedding = s.val
  rw [map_face, mul_one, ← hA, types_face]

lemma fromTypes_toTypes (n : ℕ) : (fromTypes H n).comp (toTypes H n) = LinearMap.id := by
  apply Representation.Coinvariants.hom_ext
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  change fromTypes H n (typeMap H n (Finsupp.single s r)) =
    Representation.Coinvariants.mk (FinsuppPermutation.ρ k G ((complex H).Face n))
      (Finsupp.single s r)
  rw [typeMap_single, fromTypes_single]
  obtain ⟨g,hg⟩ := face_orbit_base H n s
  have hh := (Representation.Coinvariants.mk_self_apply
    (FinsuppPermutation.ρ k G ((complex H).Face n)) g
    (Finsupp.single (baseFace H n (typeFace H n s)) r)).symm
  simpa only [FinsuppPermutation.ρ_single, hg] using hh

lemma toTypes_fromTypes (n : ℕ) : (toTypes H n).comp (fromTypes H n) = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro A
  apply LinearMap.ext
  intro r
  simp

def typesEquiv (n : ℕ) : CoinvariantChains H n ≃ₗ[k] (Simplex (I := I)).Chains n :=
  LinearEquiv.ofLinearMap (toTypes H n) (fromTypes H n)
    (toTypes_fromTypes H n) (fromTypes_toTypes H n)

lemma types_erase_vertex (g : G) (A : Finset I) (i : I) :
    types H ((face H g A).erase (vertex H g i)) = A.erase i := by
  rw [face, ← Finset.image_erase (vertex_injective H g)]
  exact types_face H g (A.erase i)

lemma typeMap_boundary (n : ℕ) :
    (typeMap H n).comp ((complex H).boundary n) =
      (Simplex (I := I)).boundary n ∘ₗ typeMap H (n+1) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  apply (Simplex (I := I)).embed_injective n
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, CoboundaryExpanders.InfiniteChains.Complex.boundary_single,
    map_sum, typeMap_single, CoboundaryExpanders.InfiniteChains.Complex.embed_single]
  change (∑ v : ↥s.val, Finsupp.single (types H (s.val.erase v.val)) r) =
    ∑ i : ↥(types H s.val), Finsupp.single ((types H s.val).erase i.val) r
  rw [Finset.sum_coe_sort s.val (fun v => Finsupp.single (types H (s.val.erase v)) r),
    Finset.sum_coe_sort (types H s.val) (fun i => Finsupp.single ((types H s.val).erase i) r)]
  obtain ⟨g,A,hA⟩ := s.property.1
  rw [← hA, types_face]
  change (∑ i ∈ A.image (vertex H g),
    Finsupp.single (types H ((face H g A).erase i)) r) = _
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [types_erase_vertex]
  · exact fun _ _ _ _ he => vertex_injective H g he

def coinvariantBoundary (n : ℕ) : CoinvariantChains H (n+1) →ₗ[k] CoinvariantChains H n :=
  Representation.Coinvariants.map _ _ ((complex H).boundaryRep (G := G) n).hom

lemma toTypes_boundary (n : ℕ) :
    (toTypes H n).comp (coinvariantBoundary H n) =
      (Simplex (I := I)).boundary n ∘ₗ toTypes H (n+1) := by
  apply Representation.Coinvariants.hom_ext
  exact typeMap_boundary H n

abbrev coinvariantComplex : ChainComplex (ModuleCat k) ℕ :=
  ((Rep.coinvariantsFunctor k G).mapHomologicalComplex _).obj ((complex H).repComplex (G := G))

def coinvariantSimplexIso : coinvariantComplex H ≅ (Simplex (I := I)).chainComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => (typesEquiv H (j+1)).toModuleIso) (by
      intro i j hij
      have he : i=j+1 := by simpa using hij.symm
      subst i
      apply ModuleCat.hom_ext
      change ((Simplex (I := I)).chainComplex.d (j+1) j).hom.comp (toTypes H (j+2)) = _
      rw [CoboundaryExpanders.InfiniteChains.Complex.chainComplex_d]
      change (Simplex (I := I)).boundary (j+1) ∘ₗ toTypes H (j+2) =
        (toTypes H (j+1)).comp
          (Representation.Coinvariants.map _ _ (((complex H).repComplex (G := G)).d (j+1) j).hom)
      rw [CoboundaryExpanders.InfiniteChains.Complex.repComplex_d]
      exact (toTypes_boundary H (j+1)).symm)

end CoboundaryExpanders.TypedCosetFaces

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Resolution
attribute [-instance] _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype _root_.OAI.CoboundaryExpanders.MatrixOpposition.cutVertexFintype _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexFintype
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

namespace CoboundaryExpanders.TypedCosetFaces

section
open InfiniteChains CategoryTheory
attribute [local instance 1100] InfiniteChains.Complex.faceMulAction
variable {G Q I : Type} [Group G] [Group Q] [DecidableEq I]
variable (H : I → Subgroup G) (f : G →* Q)
variable (hf : Function.Surjective f)
variable (hinter : ∀ A : Finset I, (stabilizer H A).map f = stabilizer (imageGroups H f) A)

lemma toQuotient_boundary (n : ℕ) :
    (toQuotient H f n).comp (kernelCoinvariantBoundary H f n) =
      (complex (imageGroups H f)).boundary n ∘ₗ toQuotient H f (n+1) := by
  apply Representation.Coinvariants.hom_ext
  exact quotientChainMap_boundary H f n

def kernelCoinvariantQuotientIso :
    kernelCoinvariantComplex H f ≅ (complex (imageGroups H f)).chainComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => (quotientChainsEquiv H f hf hinter (j+1)).toModuleIso) (by
      intro i j hij
      have he : i=j+1 := by simpa using hij.symm
      subst i
      apply ModuleCat.hom_ext
      change ((complex (imageGroups H f)).chainComplex.d (j+1) j).hom.comp
        (toQuotient H f (j+2)) = _
      rw [CoboundaryExpanders.InfiniteChains.Complex.chainComplex_d]
      change (complex (imageGroups H f)).boundary (j+1) ∘ₗ toQuotient H f (j+2) =
        (toQuotient H f (j+1)).comp
          (Representation.Coinvariants.map _ _ (((complex H).repComplex (G := f.ker)).d (j+1) j).hom)
      rw [CoboundaryExpanders.InfiniteChains.Complex.repComplex_d]
      exact (toQuotient_boundary H f (j+1)).symm)

end

open InfiniteChains CategoryTheory
attribute [local instance 1100] InfiniteChains.Complex.faceMulAction
variable {G Q I : Type} [Group G] [Group Q] [DecidableEq I]
variable (H : I → Subgroup G) (f : G →* Q)

theorem kernel_face_stabilizer (hlocal : ∀ i, Set.InjOn f (H i))
    (n : ℕ) (s : (complex H).Face (n+1)) :
    MulAction.stabilizer f.ker s = ⊥ := by
  obtain ⟨⟨A,q⟩,rfl⟩ := (gradedFace_bijective H (n+1)).2 s
  induction q using Quotient.inductionOn with | h g =>
  obtain ⟨i,hi⟩ : A.val.Nonempty := Finset.card_pos.mp (by rw [A.property]; omega)
  have hi' : Set.InjOn f (stabilizer H A.val) := by
    intro a ha b hb hab
    exact hlocal i ((mem_stabilizer H A.val a).mp ha i hi)
      ((mem_stabilizer H A.val b).mp hb i hi) hab
  apply le_antisymm _ bot_le
  intro x hx
  have hfix : x • gradedFace H (n+1) ⟨A,QuotientGroup.mk g⟩ =
      gradedFace H (n+1) ⟨A,QuotientGroup.mk g⟩ := hx
  rw [kernel_smul_graded] at hfix
  have he := (gradedFace_bijective H (n+1)).1 hfix
  have hekk : x • (QuotientGroup.mk g : G ⧸ stabilizer H A.val) = QuotientGroup.mk g :=
    eq_of_heq (Sigma.mk.inj_iff.mp he).2
  have hx' : x ∈ MulAction.stabilizer f.ker (QuotientGroup.mk g : G ⧸ stabilizer H A.val) := hekk
  rw [KernelCosetOrbits.stabilizer_eq_bot f (stabilizer H A.val) hi'] at hx'
  exact hx'

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.PermutationProjectivity
open CategoryTheory
variable {k G X : Type} [Field k] [Group G] [MulAction G X]

def orbitBasis : CosetSums.Basis (orbitStabilizer (G := G) (X := X)) ≃ X :=
  (MulAction.selfEquivSigmaOrbitsQuotientStabilizer G X).symm

lemma orbitBasis_apply (x : CosetSums.Basis (orbitStabilizer (G := G) (X := X))) :
    orbitBasis x = MulAction.ofQuotientStabilizer G x.1.out x.2 := rfl

lemma orbitBasis_smul (g : G) (x : CosetSums.Basis (orbitStabilizer (G := G) (X := X))) :
    orbitBasis (g • x) = g • orbitBasis x := by
  rw [orbitBasis_apply, orbitBasis_apply]
  exact MulAction.ofQuotientStabilizer_smul G x.1.out g x.2

def chainsIso :
    CosetSums.permutation (k := k) (orbitStabilizer (G := G) (X := X)) ≅
      FinsuppPermutation.rep k G X :=
  FinsuppPermutation.coeffIso _ _ _ ≪≫ Rep.mkIso {
    (Finsupp.domLCongr orbitBasis : _ ≃ₗ[k] _) with
    isIntertwining' := by
      intro g
      apply Finsupp.lhom_ext'
      intro x
      apply LinearMap.ext
      intro r
      change (Finsupp.domLCongr orbitBasis : _ ≃ₗ[k] _)
        (FinsuppPermutation.ρ k G _ g (Finsupp.single x r)) =
        FinsuppPermutation.ρ k G _ g
          ((Finsupp.domLCongr orbitBasis : _ ≃ₗ[k] _) (Finsupp.single x r))
      simp only [FinsuppPermutation.ρ_single, Finsupp.domLCongr_single]
      exact congrArg (fun s => Finsupp.single s r) (orbitBasis_smul g x) }

theorem projective_of_odd [∀ x : X, Finite (MulAction.stabilizer G x)]
    (hodd : ∀ x : X, Odd (Nat.card (MulAction.stabilizer G x))) :
    Projective (FinsuppPermutation.rep (ZMod 2) G X) := by
  let _ : ∀ q : Orbit (G := G) (X := X), Finite (orbitStabilizer q) :=
    fun q => (inferInstance : Finite (MulAction.stabilizer G q.out))
  have hP := CosetSums.projective_of_odd_order
    (orbitStabilizer (G := G) (X := X)) (fun q => hodd q.out)
  exact Projective.of_iso (chainsIso (k := ZMod 2) (G := G) (X := X)) hP

theorem projective_of_free (hfree : ∀ x : X, MulAction.stabilizer G x = ⊥) :
    Projective (FinsuppPermutation.rep (ZMod 2) G X) := by
  let _ : ∀ x : X, Finite (MulAction.stabilizer G x) := fun x => by
    rw [hfree x]
    infer_instance
  apply projective_of_odd
  intro x
  rw [hfree x]
  simp

end CoboundaryExpanders.PermutationProjectivity

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains CategoryTheory
attribute [local instance 1100] InfiniteChains.Complex.faceMulAction
variable {G Q I : Type} [Group G] [Group Q] [DecidableEq I] [Nonempty I]
variable (H : I → Subgroup G) (f : G →* Q)

omit [Nonempty I] in
lemma kernel_projective_chains (hlocal : ∀ i, Set.InjOn f (H i)) (n : ℕ) :
    Projective (((complex H).repComplex (G := f.ker)).X n) :=
  PermutationProjectivity.projective_of_free (kernel_face_stabilizer H f hlocal n)

def kernelHomologyQuotientIso (hf : Function.Surjective f)
    (hinter : ∀ A : Finset I, (stabilizer H A).map f = stabilizer (imageGroups H f) A)
    (hlocal : ∀ i, Set.InjOn f (H i)) (h : ℕ)
    (hexact : ∀ n, n < h → (complex H).chainComplex.ExactAt (n+1))
    (hzero : Function.Exact ((complex H).boundary 1) ((complex H).sumCoefficients 1))
    (j : ℕ) (hj : j ≤ h) :
    groupHomology (Rep.trivial k f.ker k) j ≅ (complex (imageGroups H f)).chainComplex.homology j := by
  classical
  let a : I := Classical.choice inferInstance
  let _ : Nonempty ((complex H).Face 1) :=
    ⟨⟨face H 1 {a}, ⟨1,{a},rfl⟩, by simp⟩⟩
  let ε : ((complex H).repComplex (G := f.ker)).X 0 ⟶ Rep.trivial k f.ker k :=
    (complex H).augmentationRep
  let _ : Epi ε := (complex H).augmentationRep_epi
  have hε : ((complex H).repComplex (G := f.ker)).d 1 0 ≫ ε = 0 := by
    change (complex H).boundaryRep 1 ≫ (complex H).augmentationRep = 0
    exact (complex H).augmentationRep_boundary
  have hz : (ShortComplex.mk (((complex H).repComplex (G := f.ker)).d 1 0)
      ε hε).Exact := by
    change (ShortComplex.mk ((complex H).boundaryRep 1)
      (complex H).augmentationRep _).Exact
    exact (complex H).augmentationRep_exact hzero
  exact CoinvariantHomology.homologyIso k f.ker ((complex H).repComplex (G := f.ker)) h
    ε hε
    (fun n _ => kernel_projective_chains H f hlocal n)
    (fun n hn => (complex H).repComplex_exactAt n (hexact n hn)) hz j hj ≪≫
      (HomologicalComplex.homologyFunctor _ _ j).mapIso (kernelCoinvariantQuotientIso H f hf hinter)

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction
open CategoryTheory TypedCosetFaces
variable (p n : ℕ) [Fact p.Prime]

def matrixKernelHomologyIso (hn : 2 ≤ n) (m : ℕ) (hm : 2 ≤ m)
    (hL : OppositionAcyclic p n (by omega)) (j : ℕ) (hj : j < n-1) :
    groupHomology (Rep.trivial (ZMod 2) (quotientProjection p n m).ker (ZMod 2)) j ≅
      (quotientTypedComplex p n (by omega) m).chainComplex.homology j := by
  classical
  apply TypedCosetFaces.kernelHomologyQuotientIso (uLocalGroup p n (by omega))
    (quotientProjection p n m) (QuotientGroup.mk'_surjective _)
    (quotientProjection_intersections p n (by omega) hm)
    (fun i a ha b hb he => quotientProjection_cross_injective p n (by omega) hm i i a b ha hb he)
    (n-2)
  · intro r hr
    exact hL.2 (r+1) (by omega) (by omega)
  · exact hL.1
  · omega

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

abbrev Walk (H : Fin (n + 1) → Subgroup G)
    (v w : Fin (Fintype.card (Vertex H))) : Prop :=
  Relation.ReflTransGen (fun a b => a ≠ b ∧ {a, b} ∈ (complex H).faces) v w

end

end CoboundaryExpanders.CosetConstruction

namespace CoboundaryExpanders.InfiniteChains.Complex
variable {V : Type} [DecidableEq V] [Finite V] (X : InfiniteChains.Complex V)

instance finiteFaceFintype (n : ℕ) : Fintype (X.Face n) := Fintype.ofFinite _

lemma boundary_single_subfaces (n : ℕ) (s : X.Face (n+1)) (r : k) :
    X.boundary n (Finsupp.single s r) =
      ∑ t : X.Face n, if t.val ⊆ s.val then Finsupp.single t r else 0 := by
  classical
  rw [boundary_single, ← Finset.sum_filter]
  apply Finset.sum_bij (fun (v : ↥s.val) _ => X.erase n s v)
  · intro v _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.erase_subset _ _
  · intro a _ b _ he
    apply Subtype.ext
    exact (Finset.erase_inj s.val a.property).mp (congrArg Subtype.val he)
  · intro t ht
    have hsub : t.val ⊆ s.val := (Finset.mem_filter.mp ht).2
    have hcard : (s.val \ t.val).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, s.property.2,t.property.2]
      omega
    obtain ⟨v,hv,he⟩ := (Finset.covBy_iff_card_sdiff_eq_one.mpr ⟨hsub,hcard⟩).exists_finset_erase
    exact ⟨⟨v,hv⟩,Finset.mem_univ _,Subtype.ext he⟩
  · intro _ _
    rfl
end CoboundaryExpanders.InfiniteChains.Complex

namespace CoboundaryExpanders.CosetConstruction
open CategoryTheory
variable {G : Type} [Group G] [Fintype G] {n : ℕ}
variable (H : Fin (n+1) → Subgroup G)

lemma typedFaceEquiv_subset (i j : ℕ)
    (s : (TypedCosetFaces.complex H).Face (i+1))
    (t : (TypedCosetFaces.complex H).Face (j+1)) :
    (typedFaceEquiv H i s).val ⊆ (typedFaceEquiv H j t).val ↔ s.val ⊆ t.val := by
  change s.val.image (labelEquiv H) ⊆ t.val.image (labelEquiv H) ↔ _
  exact Finset.image_subset_image_iff (labelEquiv H).injective

local instance instFintypeFace_rce28bb_1 (X : CoboundaryExpanders.Complex) (i : ℕ) : Fintype (X.Face i) := X.instFintypeFace i
lemma typedChainEquiv_boundary (i : ℕ) :
    (typedChainEquiv H i).toLinearMap.comp ((TypedCosetFaces.complex H).boundary (i+1)) =
      ((complex H).boundaryLinear i).comp (typedChainEquiv H (i+1)).toLinearMap := by
  classical
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply,
    InfiniteChains.Complex.boundary_single_subfaces, map_sum,
    LinearEquiv.coe_coe, typedChainEquiv_single, map_smul,
    Complex.boundary_on_face, Finset.smul_sum]
  apply @Fintype.sum_equiv _ _ _ _ ((complex H).instFintypeFace_2 i) _ (typedFaceEquiv H i)
  intro t
  by_cases ht : t.val ⊆ s.val
  · have hlt := (typedFaceEquiv_subset H i (i+1) t s).mpr ht
    simp only [ite_eq_left ht,ite_eq_left hlt,typedChainEquiv_single]
  · have hlt := mt (typedFaceEquiv_subset H i (i+1) t s).mp ht
    simp only [ite_eq_right ht,ite_eq_right hlt,map_zero,smul_zero]

def typedChainIso : (TypedCosetFaces.complex H).chainComplex ≅ (complex H).chainComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (typedChainEquiv H i).toModuleIso)
    (by
      intro i j hij
      have hij' : j+1 = i := by simpa using hij
      subst i
      rw [InfiniteChains.Complex.chainComplex_d, CoboundaryExpanders.Complex.chainComplex_d]
      apply ModuleCat.hom_ext
      exact (typedChainEquiv_boundary H j).symm)

end CoboundaryExpanders.CosetConstruction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_ProStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Positive exactness, coefficient change, Bockstein groups, integral pro-stability support, and F2 reductions.
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

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

def singletonFace (g : G) (i : I) : (complex H).Face 1 :=
  ⟨{vertex H g i}, ⟨g,{i},by simp [face]⟩, Finset.card_singleton _⟩

def pairFace (g : G) (i j : I) (hij : i ≠ j) : (complex H).Face 2 :=
  ⟨{vertex H g i,vertex H g j}, ⟨g,{i,j},by simp [face]⟩, by
    have hv : vertex H g i ≠ vertex H g j := fun h => hij (vertex_injective H g h)
    simp [hv]⟩

abbrev Components := (complex H).Chains 1 ⧸ LinearMap.range ((complex H).boundary 1)

def component (g : G) (i : I) : Components H :=
  (LinearMap.range ((complex H).boundary 1)).mkQ (Finsupp.single (singletonFace H g i) 1)

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.ProCoefficientChange

attribute [instance] Tower.ab Tower.mod

end CoboundaryExpanders.ProCoefficientChange

namespace CoboundaryExpanders.GroupProStability
open ProCoefficientChange
attribute [local instance 2000] Rep.hV2
attribute [local instance 3000] ModuleCat.isModule

attribute [instance] Groups.grp

end CoboundaryExpanders.GroupProStability

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_LatticeCones
attribute [-instance] _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant
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

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
variable (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top)
def RootInterval (D : Submodule K[X] (PolynomialVectors.V K (M+2))) : Prop :=
  powerShift C.top 1 ≤ D ∧ D ≤ C.top ∧ D ≠ powerShift C.top 1
noncomputable def normalizeModule (D : Submodule K[X] (PolynomialVectors.V K (M+2))) : Vertex K (M+2) := by
  classical
  exact if hD : PolyBounded D then normalizedPolynomial (by omega) D hD
  else normalizedPolynomial (by omega) C.top hC
noncomputable def liftModule (v : Vertex K (M+2)) : Submodule K[X] (PolynomialVectors.V K (M+2)) := by
  classical
  exact if h : ∃ D, RootInterval C D ∧ normalizeModule C hC D = v then h.choose else C.top
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.Construction
open CoboundaryExpanders.RationalLattices CoboundaryExpanders.AffineLattices
variable (p n : ℕ) [Fact p.Prime]

noncomputable def oppositionVertex (hn : 1 ≤ n) :
    TypedCosetFaces.Vertex (uLocalGroup p n hn) → RationalLattices.Vertex (ZMod p) (n+1) :=
  fun x => Quotient.lift (fun g : U p (n+1) =>
    actVertex (ZMod p) (n+1) (by omega) g.val (cutVertex (ZMod p) (n+1) x.1))
    (fun g h he => (act_cut_eq_iff p n hn g h x.1 x.1).mpr
      ⟨rfl,QuotientGroup.leftRel_apply.mp he⟩) x.2

@[simp] lemma oppositionVertex_mk (hn : 1 ≤ n) (g : U p (n+1)) (c : Fin (n+1)) :
    oppositionVertex p n hn (TypedCosetFaces.vertex (uLocalGroup p n hn) g c) =
      actVertex (ZMod p) (n+1) (by omega) g.val (cutVertex (ZMod p) (n+1) c) := rfl

def opposition : InfiniteChains.Complex (RationalLattices.Vertex (ZMod p) (n+1)) where
  faces := {s | ∃ g : U p (n+1), ∃ A : Finset (Fin (n+1)),
    A.image (fun c => actVertex (ZMod p) (n+1) (by omega) g.val (cutVertex (ZMod p) (n+1) c)) = s}
  empty_mem := ⟨1,∅,Finset.image_empty _⟩
  downward := by
    rintro s t ⟨g,A,rfl⟩ ht
    obtain ⟨B,hB,he⟩ := Finset.subset_image_iff.mp ht
    exact ⟨g,B,he⟩

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

namespace OrbitParam
variable (P : OrbitParam G X Y)

def H0Equiv : groupHomology (rep k G X) 0 ≃ₗ[k] (Y →₀ k) :=
  (groupHomology.H0Iso (rep k G X)).toLinearEquiv.trans P.coinEquiv

end OrbitParam
end CoboundaryExpanders.FinsuppPermutation


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

namespace CoboundaryExpanders.QuotientCoinvariants
open QuotientBarAugmentation
variable {G : Type} [Group G] [DecidableEq G] (N : Subgroup G) [N.Normal]
variable [DecidableEq (G ⧸ N)]
variable (H : ∀ s : Finset N, ∃ S : Subgroup N, Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S)

theorem quotientBar_augmentation :
    quotientBar N ≫ (Rep.barResolution (ZMod 2) (G ⧸ N)).π = (quotientResolution N H).π := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    apply (homEquiv N _ _).injective
    apply Rep.free_ext
    intro x
    change ((Rep.barResolution (ZMod 2) (G ⧸ N)).π.f 0).hom
      ((quotientBarF N 0).hom (single x (.single 1 1))) =
      ((Rep.barResolution (ZMod 2) G).π.f 0).hom (single x (.single 1 1))
    rw [quotientBarF_single,bar_augmentation_single,bar_augmentation_single]
  | succ n =>
    apply Limits.IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_single_obj_X (V := Rep (ZMod 2) (G ⧸ N))
      (ComplexShape.down ℕ) 0 (Rep.trivial (ZMod 2) (G ⧸ N) (ZMod 2)) (n + 1) (by omega)

noncomputable def quotientBarHomotopy : Homotopy (quotientBar N)
    ((quotientResolution N H).homotopyEquiv (Rep.barResolution (ZMod 2) (G ⧸ N))).hom :=
  ProjectiveResolution.liftHomotopy
    (P := quotientResolution N H) (Q := Rep.barResolution (ZMod 2) (G ⧸ N))
    (𝟙 _) (quotientBar N)
    ((quotientResolution N H).homotopyEquiv (Rep.barResolution (ZMod 2) (G ⧸ N))).hom
    (by rw [CategoryTheory.Functor.map_id,Category.comp_id]; exact quotientBar_augmentation N H)
    (by rw [CategoryTheory.Functor.map_id,Category.comp_id]; exact ProjectiveResolution.homotopyEquiv_hom_π _ _)

noncomputable def quotientBarEquiv : HomotopyEquiv
    ((L N).mapHomologicalComplex _ |>.obj (Rep.barComplex (ZMod 2) G))
    (Rep.barComplex (ZMod 2) (G ⧸ N)) where
  hom := quotientBar N
  inv := ((quotientResolution N H).homotopyEquiv (Rep.barResolution (ZMod 2) (G ⧸ N))).inv
  homotopyHomInvId := ((quotientBarHomotopy N H).compRight _).trans
    ((quotientResolution N H).homotopyEquiv (Rep.barResolution (ZMod 2) (G ⧸ N))).homotopyHomInvId
  homotopyInvHomId := ((quotientBarHomotopy N H).compLeft _).trans
    ((quotientResolution N H).homotopyEquiv (Rep.barResolution (ZMod 2) (G ⧸ N))).homotopyInvHomId

end CoboundaryExpanders.QuotientCoinvariants

end

section
open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp
open CategoryTheory CategoryTheory.Limits Representation Finsupp Rep TensorProduct
open CategoryTheory Finsupp MonoidalCategory

namespace CoboundaryExpanders.QuotientCoinvariants
open Representation
variable {G : Type} [Group G] [DecidableEq G] (N : Subgroup G) [N.Normal] [DecidableEq (G ⧸ N)]

variable (H : ∀ s : Finset N, ∃ S : Subgroup N, Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S)

noncomputable def coinvariantQuotientEquiv : HomotopyEquiv
    (QuotientCoinvariantModel.complex (k := ZMod 2) (G := G))
    (QuotientCoinvariantModel.complex (k := ZMod 2) (G := G ⧸ N)) :=
  (HomotopyEquiv.ofIso
    (((NatIso.mapHomologicalComplex (totalCoinvariantsIso N) _).app (Rep.barComplex (ZMod 2) G)).symm)).trans
      ((Rep.coinvariantsFunctor (ZMod 2) (G ⧸ N)).mapHomotopyEquiv (quotientBarEquiv N H))

end CoboundaryExpanders.QuotientCoinvariants

end

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp
open CategoryTheory CategoryTheory.Limits Representation Finsupp Rep TensorProduct
open CategoryTheory Finsupp MonoidalCategory
open CategoryTheory

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Parabolic
attribute [-instance] _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Actual parabolic stabilizers, F2 homological stability maps, and matrix duality.
-/


section
open CategoryTheory
open scoped Matrix

namespace CoboundaryExpanders.MatrixDual
variable {A B : Type*} [CommRing A] [CommRing B]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

open Construction
variable (p a m : ℕ)

lemma dual_mem_gamma (x : Gamma p a m) : dual x.val ∈ Gamma p a m := by
  change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) (dual x.val) = 1
  rw [map_dual, x.property, map_one]

def gammaDual : MulAut (Gamma p a m) where
  toFun x := ⟨dual x.val, dual_mem_gamma p a m x⟩
  invFun x := ⟨dual x.val, dual_mem_gamma p a m x⟩
  left_inv x := Subtype.ext (dual_dual x.val)
  right_inv x := Subtype.ext (dual_dual x.val)
  map_mul' _ _ := Subtype.ext (map_mul dual _ _)

end CoboundaryExpanders.MatrixDual

namespace CoboundaryExpanders.MatrixDual
open Construction F2Stability
variable (p a m : ℕ)
local instance gammaNormal : (Gamma p a m).Normal := by unfold Gamma; infer_instance

end CoboundaryExpanders.MatrixDual

end

open CategoryTheory

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_CongruenceFrames
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

def sectionHom : Matrix.SpecialLinearGroup (Fin a) A →* fixed A a b where
  toFun g := ofBlocks A a b g 0
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact Matrix.fromBlocks_one
  map_mul' g h := by
    apply Subtype.ext; apply Subtype.ext
    change Matrix.fromBlocks (g.val*h.val) 0 0 (1 : Matrix (Fin b) (Fin b) A) =
      Matrix.fromBlocks g.val 0 0 1 * Matrix.fromBlocks h.val 0 0 1
    simp [Matrix.fromBlocks_multiply]

end CoboundaryExpanders.RowParabolic

end

namespace CoboundaryExpanders.MultiParabolic
open scoped Matrix BigOperators

open Construction RowParabolic CategoryTheory
variable (p a b m : ℕ)

def toFixed : group p a b m →* fixed (R p) a b :=
  Subgroup.inclusion inf_le_left

def project : group p a b m →* Gamma p a m :=
  ((RowParabolic.project (R p) a b).comp (toFixed p a b m)).codRestrict _ (by
    intro A
    have h := A.property.2
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have he := congrArg (fun B : Matrix.SpecialLinearGroup (Idx a b) (R p ⧸ powerIdeal p m) =>
      B (Sum.inl i) (Sum.inl j)) h
    change Ideal.Quotient.mk (powerIdeal p m) (A.val.val (Sum.inl i) (Sum.inl j)) =
      (1 : Matrix (Fin a) (Fin a) (R p ⧸ powerIdeal p m)) i j
    simpa [Matrix.one_apply] using he)

def sectionValue (A : Gamma p a m) : group p a b m :=
  ⟨(RowParabolic.sectionHom (R p) a b A.val).val, by
    constructor
    · exact (RowParabolic.sectionHom (R p) a b A.val).property
    · apply Matrix.SpecialLinearGroup.ext
      intro i j
      have h := A.property
      change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) A.val = 1 at h
      have hh (i j : Fin a) := congrArg (fun B : Matrix.SpecialLinearGroup (Fin a)
        (R p ⧸ powerIdeal p m) => B i j) h
      change Ideal.Quotient.mk (powerIdeal p m)
        (Matrix.fromBlocks A.val.val (0 : Matrix (Fin a) (Fin b) (R p)) 0 1 i j) =
          (1 : Matrix (Idx a b) (Idx a b) (R p ⧸ powerIdeal p m)) i j
      cases i with
      | inl i => cases j with
        | inl j => simpa [Matrix.one_apply, Matrix.SpecialLinearGroup.map_apply_coe] using hh i j
        | inr j => simp
      | inr i => cases j with
        | inl j => simp
        | inr j => simp [Matrix.one_apply]⟩

lemma kernel_form (A : (project p a b m).ker) : A.val.val.val =
    Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) (R p))
      (Matrix.toBlocks₁₂ A.val.val.val) 0 1 := by
  have he := congrArg (fun x : Gamma p a m => x.val.val) A.property
  change Matrix.toBlocks₁₁ A.val.val.val = 1 at he
  have hh := RowParabolic.block_form (R p) a b (toFixed p a b m A.val)
  change A.val.val.val = Matrix.fromBlocks (Matrix.toBlocks₁₁ A.val.val.val)
    (Matrix.toBlocks₁₂ A.val.val.val) 0 1 at hh
  rw [he] at hh
  exact hh

def kernelBlock : (project p a b m).ker →* Multiplicative (Matrix (Fin a) (Fin b) (R p)) where
  toFun A := Multiplicative.ofAdd (Matrix.toBlocks₁₂ A.val.val.val)
  map_one' := by
    change Matrix.toBlocks₁₂ (1 : Matrix (Idx a b) (Idx a b) (R p)) = 0
    funext i j
    change (1 : Matrix (Idx a b) (Idx a b) (R p)) (Sum.inl i) (Sum.inr j) = 0
    simp
  map_mul' A B := by
    change Matrix.toBlocks₁₂ (A.val.val.val * B.val.val.val) =
      Matrix.toBlocks₁₂ A.val.val.val + Matrix.toBlocks₁₂ B.val.val.val
    rw [kernel_form p a b m A, kernel_form p a b m B, Matrix.fromBlocks_multiply]
    simp [add_comm]

end CoboundaryExpanders.MultiParabolic


open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_FrameHomology
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Shapiro comparison, frame resolution homology, augmentation ranges, and triviality of conjugation.
-/


section
open CategoryTheory CategoryTheory.Limits Rep Representation Finsupp

namespace CoboundaryExpanders.CosetModules
variable {k G : Type} [Field k] [Group G] [DecidableEq G] (S : Subgroup G)

omit [DecidableEq G] in
lemma hom_ext_base {A : Rep k G} {f g : permutation (k := k) S ⟶ A}
    (h : base S ≫ (resFunctor S.subtype).map f = base S ≫ (resFunctor S.subtype).map g) : f = g := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro q
  apply LinearMap.ext
  intro r
  induction q using Quotient.inductionOn with | h a =>
    have hh := congrArg (fun f => f.hom r) h
    have hf := Rep.hom_comm_apply f a (MonoidAlgebra.single (QuotientGroup.mk (1 : G)) r)
    have hg := Rep.hom_comm_apply g a (MonoidAlgebra.single (QuotientGroup.mk (1 : G)) r)
    rw [Representation.ofMulAction_single] at hf hg
    change f.hom (MonoidAlgebra.single (QuotientGroup.mk (a*1)) r) = _ at hf
    change g.hom (MonoidAlgebra.single (QuotientGroup.mk (a*1)) r) = _ at hg
    simp only [mul_one] at hf hg
    change f.hom (MonoidAlgebra.single (QuotientGroup.mk a) r) =
      g.hom (MonoidAlgebra.single (QuotientGroup.mk a) r)
    rw [hf, hg]
    exact congrArg (A.ρ a) hh

def indToCoset : Rep.ind S.subtype (Rep.trivial k S k) ⟶ permutation (k := k) S :=
  (Rep.indResHomEquiv S.subtype _ _).symm (base S)

omit [DecidableEq G] in
lemma indBase_comp_toCoset :
    ActualShapiro.indBase S (Rep.trivial k S k) ≫ (resFunctor S.subtype).map (indToCoset S) = base S :=
  (Rep.indResHomEquiv S.subtype _ _).apply_symm_apply (base S)

omit [DecidableEq G] in
lemma indBase_fixed (h : S) :
    (Rep.ind S.subtype (Rep.trivial k S k)).ρ h
      ((ActualShapiro.indBase S (Rep.trivial k S k)).hom (1 : k)) =
      (ActualShapiro.indBase S (Rep.trivial k S k)).hom (1 : k) := by
  have hh := Rep.hom_comm_apply (ActualShapiro.indBase S (Rep.trivial k S k)) h (1 : k)
  exact hh.symm

def cosetToInd : permutation (k := k) S ⟶ Rep.ind S.subtype (Rep.trivial k S k) :=
  extend S _ ((ActualShapiro.indBase S (Rep.trivial k S k)).hom 1) (indBase_fixed S)

omit [DecidableEq G] in
lemma base_comp_toInd : base S ≫ (resFunctor S.subtype).map (cosetToInd (k := k) S) =
    ActualShapiro.indBase S (Rep.trivial k S k) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro r
  change extend S _ _ _ (MonoidAlgebra.single (QuotientGroup.mk (1 : G)) r) = _
  rw [extend_single]
  simp only [map_one, Module.End.one_apply]
  change r • ((ActualShapiro.indBase S (Rep.trivial k S k)).hom 1) =
    (ActualShapiro.indBase S (Rep.trivial k S k)).hom r
  rw [← map_smul]
  simp

def indCosetIso : Rep.ind S.subtype (Rep.trivial k S k) ≅ permutation (k := k) S where
  hom := indToCoset S
  inv := cosetToInd S
  hom_inv_id := by
    apply (Rep.indResHomEquiv S.subtype _ _).injective
    change ActualShapiro.indBase S (Rep.trivial k S k) ≫
      (resFunctor S.subtype).map (indToCoset S ≫ cosetToInd S) = _
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, indBase_comp_toCoset, base_comp_toInd]
    rfl
  inv_hom_id := by
    apply hom_ext_base S
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, base_comp_toInd, indBase_comp_toCoset,
      CategoryTheory.Functor.map_id, Category.comp_id]

end CoboundaryExpanders.CosetModules

open CategoryTheory CategoryTheory.Limits Rep Representation Finsupp
open scoped BigOperators
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.CosetSums
variable {k G I : Type} [Field k] [Group G] (H : I → Subgroup G)

def projection (i : I) : permutation (k := k) H ⟶ CosetModules.permutation (k := k) (H i) :=
  Rep.ofHom ⟨(MonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap.comp
    ((Finsupp.lcomapDomain (fun q : G ⧸ H i => (⟨i,q⟩ : Basis H)) (by intro a b h; exact eq_of_heq (Sigma.mk.inj h).2)).comp
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap), by
    intro g
    apply LinearMap.ext
    intro f
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro q
    change ((Representation.ofMulAction k G (Basis H)) g f).coeff ⟨i,q⟩ =
      ((Representation.ofMulAction k G (G ⧸ H i)) g _).coeff q
    rw [Representation.coeff_ofMulAction, Representation.coeff_ofMulAction]
    rfl⟩

@[simp] lemma projection_coeff (i : I) (f : permutation (k := k) H) (q : G ⧸ H i) :
    (projection H i f).coeff q = f.coeff ⟨i,q⟩ := rfl

open groupHomology

end CoboundaryExpanders.CosetSums

end

section
open CategoryTheory CategoryTheory.Limits

namespace CoboundaryExpanders.MultiParabolic
open Construction F2Stability RowFrames
variable (p a b m : ℕ)
def sectionHom : Gamma p a m →* group p a b m where
  toFun := sectionValue p a b m
  map_one' := by
    apply Subtype.ext
    change (RowParabolic.sectionHom (R p) a b 1).val = 1
    exact congrArg Subtype.val (map_one (RowParabolic.sectionHom (R p) a b))
  map_mul' A B := by
    apply Subtype.ext
    change (RowParabolic.sectionHom (R p) a b (A.val*B.val)).val =
      (RowParabolic.sectionHom (R p) a b A.val).val * (RowParabolic.sectionHom (R p) a b B.val).val
    exact congrArg Subtype.val (map_mul (RowParabolic.sectionHom (R p) a b) A.val B.val)

def inclusion : group p a b m →* Gamma p (a+b) m where
  toFun A := ⟨Blocks.reindexSL finSumFinEquiv A.val, by
    change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) _ = 1
    rw [Blocks.reindexSL_map,A.property.2,map_one]⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' A B := by apply Subtype.ext; exact map_mul _ _ _

end CoboundaryExpanders.MultiParabolic

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.InfiniteChains.Complex
variable {V G : Type} [DecidableEq V] [Group G] [MulAction G V]
    (X : CoboundaryExpanders.InfiniteChains.Complex V) [Fact (X.Invariant (G := G))]

def augmentedData : HomologyEdge.AugmentedData (k := k) (G := G) where
  D | 0 => Rep.trivial k G k
    | s+1 => X.chainsRep (G := G) (s+1)
  d | 0 => X.augmentationRep
    | s+1 => X.boundaryRep (s+1)
  square s := by
    cases s with
    | zero => exact X.augmentationRep_boundary
    | succ s => exact X.boundaryRep_squared (s+1)

end CoboundaryExpanders.InfiniteChains.Complex

end

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

end

end OAI
end


