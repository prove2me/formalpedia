-- Prove2me | Definitions.Def_OAIQ043T007
-- name    : OAIQ043T007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T09:53:35.795985+00:00
-- url     : https://prove2.me/theorems/a6f4fe18-2650-4e85-9f4b-8fca48746769
-- title:
--   Definitions bundle OAIQ043T007 of the split of OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Thomason.main` and `OAI.Thomason.nerveDetection_allDimensions`, carved from OpenAI's openai/math development (OpenAI, *Thomason Model Structures in Every Strict Higher Dimension (result family 317)*, OpenAI Math Release, September 25, 2026, result family 317, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 106 declarations of OpenAI's Lean: 19 definitions and 87 theorems. The definitions and types are `OAI.Thomason.DirectedComplex.PartialHom.extendOriental`, `OAI.Thomason.DirectedComplex.PartialHom.image`, `OAI.Thomason.DirectedComplex.PartialHom.oneStep`, `OAI.Thomason.DirectedComplex.PartialHom.table`, `OAI.Thomason.KanQuillen.geometricModel`, `OAI.Thomason.NormalizedChains.cutHom`, `OAI.Thomason.NormalizedChains.cutTotal`, `OAI.Thomason.NormalizedChains.homVertexOrderHom`, `OAI.Thomason.PartialNormalized.cutHom`, `OAI.Thomason.PartialNormalized.cutTotal`, `OAI.Thomason.PartialNormalized.finiteCut`, `OAI.Thomason.PartialNormalized.homVertexOrderHom`, `OAI.Thomason.finitePosetTableNerveMap`, `OAI.Thomason.finiteTableCut`, `OAI.Thomason.liftedPartial`, `OAI.Thomason.tableNerveCutCylinder`, `OAI.Thomason.tableNerveCutHomotopy`, `OAI.Thomason.tableNerveCutSimplex`, `OAI.Thomason.tableNerveVertexMap`.
--
--   **Sources.** They come from these modules of lean/OAI/CategoryTheory/Thomason, in whole or in part: [`Thomason_BoundaryQuotients`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/BoundaryQuotients.lean), [`Thomason_KanQuillen`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/KanQuillen.lean), [`Thomason_PartialPrisms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/PartialPrisms.lean), [`Thomason_PartialTables`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/PartialTables.lean), [`Thomason_PosetComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/PosetComparison.lean), [`Thomason_SieveAttachments`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/SieveAttachments.lean).
--
--   **Imports.** It imports the published bundle `Def_ThomasonModelStructures`; the bundles `OAIQ043T004` and `OAIQ043T005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ043T008` and `OAIQ043T009`.
-- source:
--   OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 317; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/CategoryTheory/Thomason at commit adc7f12

import Mathlib
import Definitions.Def_ThomasonModelStructures
import Definitions.Def_OAIQ043T004
import Definitions.Def_OAIQ043T005

section
-- module Solutions.OAIQ043_TH.Thomason_BoundaryQuotients
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Quotients. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex
open Table OmegaCategory

namespace PartialHom
variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {n : ℕ}

def table (f : PartialHom K L n) (x : Table K) : Table L where
  row p b := if p < n then f.map p (x.row p b) else
    if p = n then f.map p (x.row p false) else 0
  positive p b := by
    split_ifs with h h
    · exact f.map_positive p _ (x.positive p b)
    · exact f.map_positive p _ (x.positive p false)
    · exact (L.positive p).zero_mem
  boundary p b := by
    by_cases hp : p < n
    · by_cases hp' : p+1 < n
      · simp only [hp,hp',ite_true]
        rw [← f.map_d p hp,x.boundary,map_sub]
      · have he : p+1 = n := by omega
        simp only [hp,ite_true,ite_false,he,lt_self_iff_false]
        rw [← f.map_d p hp,x.boundary,map_sub]
    · have hp' : ¬p+1 < n := by omega
      have he' : p+1 ≠ n := by omega
      simp only [hp,hp',he',ite_false,map_zero]
      split <;> simp
  augmentation b := by
    by_cases hn : 0 < n
    · simp only [hn,ite_true]; rw [f.map_augmentation,x.augmentation]
    · have he : n = 0 := by omega
      simp only [he,lt_self_iff_false,ite_false,ite_true]
      rw [f.map_augmentation,x.augmentation]
  bounded := ⟨n,fun p hp b => by simp [show ¬p<n by omega,show p ≠ n by omega]⟩

lemma table_bounded (f : PartialHom K L n) (x : Table K) :
    truncate n false (f.table x) = f.table x := by
  apply dimension_of_rows_above_zero
  intro p hp b
  simp [table,show ¬p<n by omega,show p≠n by omega]

lemma table_source (f : PartialHom K L n) (k : ℕ) (x : Table K) :
    f.table (truncate k false x) = truncate k false (f.table x) := by
  ext p b
  simp only [table,truncate_row]
  split_ifs <;> simp_all only [map_zero]

lemma table_target_lt (f : PartialHom K L n) (k : ℕ) (hk : k<n) (x : Table K) :
    f.table (truncate k true x) = truncate k true (f.table x) := by
  ext p b
  simp only [table,truncate_row]
  split_ifs <;> simp_all only [map_zero, not_true_eq_false]

lemma table_composable (f : PartialHom K L n) {k : ℕ} (hk : k<n) {x y : Table K}
    (h : truncate k true x = truncate k false y) :
    truncate k true (f.table x) = truncate k false (f.table y) := by
  rw [← f.table_target_lt k hk,← f.table_source,h]

lemma table_comp_lt (f : PartialHom K L n) {k : ℕ} (hk : k<n) (x y : Table K)
    (h : truncate k true x = truncate k false y) :
    f.table (comp k x y h) = comp k (f.table x) (f.table y) (f.table_composable hk h) := by
  ext p b
  simp only [table,comp_row]
  cases b <;> split_ifs <;> simp_all only [map_add, add_zero, not_true_eq_false]

lemma table_source_n (f : PartialHom K L n) (x : Table K) :
    f.table (truncate n false x) = f.table x := by
  rw [f.table_source,f.table_bounded]

end PartialHom
end Thomason.DirectedComplex

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PosetComparison
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poset Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]

lemma homTotal_boundary (f : Hom (complex E) (complex D)) (c : Chains E) :
    homTotal f (boundary c) = boundary (homTotal f c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add w z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single w z = z • bracket w.val := by
      rw [bracket_of_pairwise w.property]; simp
    rw [hz]
    simp only [map_smul]
    congr 1
    obtain ⟨l,hl⟩ := w
    cases l with
    | nil => simp [homTotal_bracket,homWord,boundary_bracket]
    | cons a l =>
      cases l with
      | nil =>
        rw [homTotal_bracket]
        change homTotal f (boundary (bracket [a])) =
          boundary (f.map 0 ⟨bracket [a],bracket_mem_grade [a]⟩).val
        rw [grade_zero_eq_empty (boundary_mem_grade
          (f.map 0 ⟨bracket [a],bracket_mem_grade [a]⟩).property)]
        have hau := f.map_augmentation ⟨bracket [a], bracket_mem_grade [a]⟩
        change emptyCoefficient (boundary (f.map 0 _).val) =
          emptyCoefficient (boundary (bracket [a])) at hau
        rw [hau, boundary_bracket (by simp), wordBoundary_cons,
          wordBoundary_nil, map_zero, sub_zero, homTotal_bracket]
        simp [homWord]
      | cons b l =>
        let x : (complex E).Chain (l.length+1) :=
          ⟨bracket (a::b::l),bracket_mem_grade (a::b::l)⟩
        have hd := congrArg Subtype.val (f.map_d l.length x)
        change homTotal f ((complex E).d l.length x).val =
          boundary (homTotal f x.val)
        rw [homTotal_map,homTotal_map]
        exact hd

lemma homTotal_vertex (f : Hom (complex E) (complex D)) (a : E) :
    homTotal f (bracket [a]) = bracket [homVertex f a] :=
  (homTotal_vertex_exists f a).choose_spec

lemma homVertex_monotone (f : Hom (complex E) (complex D)) : Monotone (homVertex f) := by
  intro a b hab
  apply table_source_le_target_partial (f.table (edgeTable a b hab))
  · exact (homTotal_map f 0 ⟨bracket [a],bracket_mem_grade [a]⟩).symm.trans
      (homTotal_vertex f a)
  · exact (homTotal_map f 0 ⟨bracket [b],bracket_mem_grade [b]⟩).symm.trans
      (homTotal_vertex f b)

def homVertexOrderHom (f : Hom (complex E) (complex D)) : E →o D :=
  ⟨homVertex f, homVertex_monotone f⟩

lemma homTotal_bracket_supportedOn_lower (f : Hom (complex E) (complex D))
    (S : Set D) (hS : IsLowerSet S) (l : List E) (hl : l.Pairwise (· ≤ ·))
    (hs : ∀ a ∈ l, homVertex f a ∈ S) : homTotal f (bracket l) ∈ supportedOn S := by
  induction hlen : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
    cases l with
    | nil =>
      rw [homTotal_bracket]
      exact bracket_mem_supportedOn (by simp)
    | cons a l =>
      cases l with
      | nil =>
        rw [homTotal_vertex]
        exact bracket_mem_supportedOn (by simpa using hs)
      | cons b l =>
        apply positive_supportedOn_of_boundary_partial hS
          (homTotal_grade f (bracket_mem_grade (a::b::l)))
          (homTotal_positive f (bracket_positive _))
        rw [← homTotal_boundary, boundary_bracket hl, ← faces_bracket]
        change (homTotal f).toAddMonoidHom (faces bracket (a::b::l)) ∈ _
        rw [faces_hom]
        apply faces_mem_submodule_length
        intro m hm hmlen
        exact ih m.length (by simp only [List.length_cons] at hmlen hlen; omega)
          m (hl.sublist hm) (fun a ha => hs a (hm.subset ha)) rfl

lemma cutWord_append (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (l : List E) (a : E) : cutWord f θ (l++[a]) =
      if θ a = 0 then homTotal f (bracket (l++[a])) else append (homVertex f a) (cutWord f θ l) :=
  by unfold cutWord; rw [List.reverseRecOn_concat]

lemma cutWord_of_all_zero (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (l : List E) (h : ∀ a ∈ l, θ a = 0) : cutWord f θ l = homTotal f (bracket l) := by
  cases l using List.reverseRecOn with
  | nil => rw [cutWord_nil, homTotal_bracket]; rfl
  | append_singleton l a => rw [cutWord_append, ite_eq_left (h a (by simp))]

lemma cutWord_positive (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (l : List E) : Positive (cutWord f θ l) := by
  induction l using List.reverseRecOn with
  | nil => rw [cutWord_nil]; exact bracket_positive []
  | append_singleton l a ih =>
    rw [cutWord_append]
    split
    · exact homTotal_positive f (bracket_positive _)
    · exact append_positive _ ih

lemma cutWord_grade (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (l : List E) : cutWord f θ l ∈ grade l.length := by
  induction l using List.reverseRecOn with
  | nil => rw [cutWord_nil]; exact bracket_mem_grade []
  | append_singleton l a ih =>
    rw [cutWord_append]
    split
    · exact homTotal_grade f (bracket_mem_grade _)
    · simpa only [List.length_append,List.length_singleton] using append_mem_grade _ ih

lemma cutWord_supportedOn_lower (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (S : Set D) (hS : IsLowerSet S) (l : List E) (hl : l.Pairwise (· ≤ ·))
    (hs : ∀ a ∈ l, homVertex f a ∈ S) : cutWord f θ l ∈ supportedOn S := by
  induction l using List.reverseRecOn with
  | nil => rw [cutWord_nil]; exact bracket_mem_supportedOn (by simp)
  | append_singleton l a ih =>
    rw [cutWord_append]
    split
    · exact homTotal_bracket_supportedOn_lower f S hS _ hl hs
    · exact append_mem_supportedOn (hs a (by simp))
        (ih (List.pairwise_append.mp hl).1 (fun b hb => hs b (List.mem_append_left _ hb)))

lemma cutWord_boundary (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (l : List E) (hl : l.Pairwise (· ≤ ·)) :
    boundary (cutWord f θ l) = faces (cutWord f θ) l := by
  induction l using List.reverseRecOn with
  | nil => simp [boundary_bracket]
  | append_singleton l a ih =>
    rw [cutWord_append]
    by_cases hθ : θ a = 0
    · rw [ite_eq_left hθ, ← homTotal_boundary, boundary_bracket hl, ← faces_bracket]
      change (homTotal f).toAddMonoidHom (faces bracket (l++[a])) = _
      rw [faces_hom]
      apply faces_congr
      intro m hm
      apply (cutWord_of_all_zero f θ m ?_).symm
      intro b hb
      have hba : b ≤ a := by
        rcases List.mem_append.mp (hm.subset hb) with hb | hb
        · exact (List.pairwise_append.mp hl).2.2 b hb a (by simp)
        · simpa using (show b = a by simpa using hb).le
      have hle := θ.monotone hba
      rw [hθ] at hle
      exact le_antisymm hle (Fin.zero_le _)
    · rw [ite_eq_right hθ, boundary_append_supported _ (cutWord_grade f θ l)
        (cutWord_supportedOn_lower f θ _ (isLowerSet_Iic _) l
          (List.pairwise_append.mp hl).1 (fun b hb =>
            homVertex_monotone f ((List.pairwise_append.mp hl).2.2 b hb a (by simp)))),
        ih (List.pairwise_append.mp hl).1, faces_append_singleton]
      congr 1
      change (append (homVertex f a)).toAddMonoidHom (faces (cutWord f θ) l) = _
      rw [faces_hom]
      apply faces_congr
      intro m _
      rw [cutWord_append,ite_eq_right hθ]
      rfl

lemma cutWord_eq_zero_of_not_pairwise (f : Hom (complex E) (complex D))
    (θ : E →o Fin 2) (l : List E) (hl : l.Pairwise (· ≤ ·))
    (hn : ¬l.Pairwise (· < ·)) : cutWord f θ l = 0 := by
  induction l using List.reverseRecOn with
  | nil => exact (hn (by simp)).elim
  | append_singleton l a ih =>
    rw [cutWord_append]
    split
    · rw [bracket_of_not_pairwise hn,map_zero]
    · rename_i hθ
      by_cases hp : l.Pairwise (· < ·)
      · cases l using List.reverseRecOn with
        | nil => exact (hn (by simp)).elim
        | append_singleton r b =>
          have hba : b ≤ a := (List.pairwise_append.mp hl).2.2 b (by simp) a (by simp)
          have he : b = a := by
            by_contra he
            have hba' : b < a := lt_of_le_of_ne hba he
            apply hn
            apply List.pairwise_append.mpr
            refine ⟨hp, by simp, ?_⟩
            intro c hc d hd
            have hed : d = a := by simpa using hd
            subst d
            rcases List.mem_append.mp hc with hc | hc
            · exact lt_trans ((List.pairwise_append.mp hp).2.2 c hc b (by simp)) hba'
            · have hec : c = b := by simpa using hc
              simpa [hec] using hba'
          subst b
          rw [cutWord_append,ite_eq_right hθ,append_append_self]
      · rw [ih (List.pairwise_append.mp hl).1 hp,map_zero]

def cutTotal (f : Hom (complex E) (complex D)) (θ : E →o Fin 2) :
    Chains E →ₗ[ℤ] Chains D := Finsupp.linearCombination ℤ (fun w => cutWord f θ w.val)

lemma cutTotal_bracket (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (l : List E) (hl : l.Pairwise (· ≤ ·)) : cutTotal f θ (bracket l) = cutWord f θ l := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    change Finsupp.linearCombination ℤ _ (Finsupp.single _ 1) = _
    rw [Finsupp.linearCombination_single,one_smul]
  · rw [bracket_of_not_pairwise hs,map_zero,cutWord_eq_zero_of_not_pairwise f θ l hl hs]

lemma cutTotal_grade (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    {k : ℕ} {c : Chains E} (hc : c ∈ grade k) : cutTotal f θ c ∈ grade k := by
  apply linearCombination_mem_grade _ k k _ hc
  intro w hw
  simpa only [← hw] using cutWord_grade f θ w.val

lemma cutTotal_positive (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    {c : Chains E} (hc : Positive c) : Positive (cutTotal f θ c) :=
  linearCombination_positive _ (fun w => cutWord_positive f θ w.val) hc

lemma cutTotal_wordBoundary (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (l : List E) (hl : l.Pairwise (· ≤ ·)) :
    cutTotal f θ (wordBoundary l) = faces (cutWord f θ) l := by
  rw [← faces_bracket]
  change (cutTotal f θ).toAddMonoidHom (faces bracket l) = _
  rw [faces_hom]
  apply faces_congr
  intro m hm
  exact cutTotal_bracket f θ m (hl.sublist hm)

lemma cutTotal_boundary (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (c : Chains E) : cutTotal f θ (boundary c) = boundary (cutTotal f θ c) := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [boundary_bracket (w.property.imp le_of_lt),
    cutTotal_bracket f θ w.val (w.property.imp le_of_lt),
    cutWord_boundary f θ w.val (w.property.imp le_of_lt),
    cutTotal_wordBoundary f θ w.val (w.property.imp le_of_lt)]

lemma cutTotal_empty (f : Hom (complex E) (complex D)) (θ : E →o Fin 2) :
    cutTotal f θ (bracket []) = bracket [] := by
  rw [cutTotal_bracket f θ [] (by simp),cutWord_nil]

lemma cutTotal_augmentation (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    {c : Chains E} (hc : c ∈ grade 1) :
    emptyCoefficient (boundary (cutTotal f θ c)) = emptyCoefficient (boundary c) := by
  rw [← cutTotal_boundary, grade_zero_eq_empty (boundary_mem_grade hc), map_smul,
    cutTotal_empty]
  simp only [map_smul,emptyCoefficient_bracket,smul_eq_mul]

def cutHom (f : Hom (complex E) (complex D)) (θ : E →o Fin 2) :
    Hom (complex E) (complex D) where
  map _p :=
    { toFun := fun c => ⟨cutTotal f θ c.val, cutTotal_grade f θ c.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x.val y.val) }
  map_d _ x := Subtype.ext (cutTotal_boundary f θ x.val)
  map_augmentation x := cutTotal_augmentation f θ x.property
  map_positive _ _ hc := cutTotal_positive f θ hc

variable {B : Type w} [PartialOrder B]

lemma homTotal_comp (f : Hom (complex E) (complex D)) (g : Hom (complex D) (complex B))
    (c : Chains E) : homTotal (Hom.comp f g) c = homTotal g (homTotal f c) := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  obtain ⟨l,hl⟩ := w
  cases l with
  | nil => simp only [homTotal_bracket,homWord]
  | cons a l =>
    rw [homTotal_map (Hom.comp f g) l.length ⟨bracket (a::l),bracket_mem_grade _⟩,
      homTotal_map f l.length ⟨bracket (a::l),bracket_mem_grade _⟩,
      homTotal_map g l.length (f.map l.length ⟨bracket (a::l),bracket_mem_grade _⟩)]
    rfl

lemma homTotal_complexMap (a : E →o D) (c : Chains E) :
    homTotal (complexMap a) c = map a c := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  obtain ⟨l,hl⟩ := w
  cases l with
  | nil => rw [homTotal_bracket,map_bracket a (by simp)]; rfl
  | cons b l =>
    rw [homTotal_map (complexMap a) l.length ⟨bracket (b::l),bracket_mem_grade _⟩]
    rfl

lemma homVertex_complexMap (a : E →o D) (b : E) : homVertex (complexMap a) b = a b := by
  apply bracket_singleton_injective
  change bracket [homVertex (complexMap a) b] = bracket [a b]
  rw [← homTotal_vertex,homTotal_complexMap,map_bracket a (by simp)]
  rfl

lemma homVertex_precomp (a : B →o E) (f : Hom (complex E) (complex D)) (b : B) :
    homVertex (Hom.comp (complexMap a) f) b = homVertex f (a b) := by
  apply bracket_singleton_injective
  change bracket [homVertex (Hom.comp (complexMap a) f) b] = bracket [homVertex f (a b)]
  rw [← homTotal_vertex,homTotal_comp,homTotal_complexMap,map_bracket a (by simp)]
  exact homTotal_vertex f (a b)

lemma cutWord_precomp (a : B →o E) (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (l : List B) (hl : l.Pairwise (· ≤ ·)) :
    cutWord (Hom.comp (complexMap a) f) (θ.comp a) l = cutWord f θ (l.map a) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l b ih =>
    rw [List.map_append,List.map_singleton,cutWord_append,cutWord_append]
    change (if θ (a b) = 0 then _ else _) = (if θ (a b) = 0 then _ else _)
    split
    · rw [homTotal_comp,homTotal_complexMap,map_bracket a hl,List.map_append,List.map_singleton]
    · rw [homVertex_precomp,ih (List.pairwise_append.mp hl).1]

lemma cutTotal_precomp (a : B →o E) (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (c : Chains B) :
    cutTotal (Hom.comp (complexMap a) f) (θ.comp a) c = cutTotal f θ (map a c) := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [cutTotal_bracket _ _ w.val (w.property.imp le_of_lt),
    map_bracket a (w.property.imp le_of_lt),
    cutTotal_bracket _ _ (w.val.map a)
      (List.pairwise_map.mpr (w.property.imp (fun h => a.monotone h.le)))]
  exact cutWord_precomp a f θ w.val (w.property.imp le_of_lt)

lemma cutHom_precomp (a : B →o E) (f : Hom (complex E) (complex D)) (θ : E →o Fin 2) :
    cutHom (Hom.comp (complexMap a) f) (θ.comp a) = Hom.comp (complexMap a) (cutHom f θ) := by
  ext p x
  exact Subtype.ext (cutTotal_precomp a f θ x.val)

lemma cutWord_const_one (f : Hom (complex E) (complex D)) (l : List E) :
    cutWord f (OrderHom.const E (1 : Fin 2)) l = bracket (l.map (homVertex f)) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [cutWord_append,ite_eq_right (by change (1 : Fin 2) ≠ 0; decide),ih,append_bracket,
      List.map_append,List.map_singleton]

lemma cutTotal_const_zero (f : Hom (complex E) (complex D)) (c : Chains E) :
    cutTotal f (OrderHom.const E (0 : Fin 2)) c = homTotal f c := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [cutTotal_bracket _ _ w.val (w.property.imp le_of_lt)]
  exact cutWord_of_all_zero f _ w.val (by simp)

lemma cutTotal_const_one (f : Hom (complex E) (complex D)) (c : Chains E) :
    cutTotal f (OrderHom.const E (1 : Fin 2)) c = map (homVertexOrderHom f) c := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [cutTotal_bracket _ _ w.val (w.property.imp le_of_lt),cutWord_const_one,
    map_bracket (homVertexOrderHom f) (w.property.imp le_of_lt)]
  rfl

lemma cutHom_const_zero (f : Hom (complex E) (complex D)) :
    cutHom f (OrderHom.const E (0 : Fin 2)) = f := by
  ext p c
  apply Subtype.ext
  exact (cutTotal_const_zero f c.val).trans (homTotal_map f p c)

lemma cutHom_const_one (f : Hom (complex E) (complex D)) :
    cutHom f (OrderHom.const E (1 : Fin 2)) = complexMap (homVertexOrderHom f) := by
  ext p c
  exact Subtype.ext (cutTotal_const_one f c.val)

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Opposite Simplicial MonoidalCategory DirectedComplex NormalizedChains

noncomputable def tableNerveVertexMap (P : Type u) [PartialOrder P] :
    streetNerve (complex P).nu ⟶ nerve P where
  app m := ↾fun F => (homVertexOrderHom (orientalChain m.unop.len F)).monotone.functor
  naturality m n a := by
    apply ConcreteCategory.hom_ext
    intro F
    apply nerve.ext_of_isThin
    funext i
    change homVertex (orientalChain n.unop.len
      (OmegaCategory.Functor.comp (complexMap a.unop.toOrderHom).nu F)) i =
        homVertex (orientalChain m.unop.len F) (a.unop.toOrderHom i)
    erw [orientalChain_natural,homVertex_precomp]

lemma posetTableNerveMap_vertex (P : Type u) [PartialOrder P] :
    posetTableNerveMap P ≫ tableNerveVertexMap P = 𝟙 (nerve P) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  change homVertex (orientalChain m.unop.len (complexMap (posetSimplexOrder s)).nu) i = s.obj i
  rw [orientalChain_of_nu,homVertex_complexMap]
  rfl

noncomputable def tableNerveCutSimplex (P : Type u) [PartialOrder P] (m : ℕ)
    (F : OmegaCategory.Functor (Oriental m) (complex P).nu)
    (θ : Fin (m+1) →o Fin 2) : OmegaCategory.Functor (Oriental m) (complex P).nu :=
  (cutHom (orientalChain m F) θ).nu

lemma tableNerveCutSimplex_natural (P : Type u) [PartialOrder P] {m n : ℕ}
    (a : Fin (m+1) →o Fin (n+1))
    (F : OmegaCategory.Functor (Oriental n) (complex P).nu) (θ : Fin (n+1) →o Fin 2) :
    tableNerveCutSimplex P m (OmegaCategory.Functor.comp (complexMap a).nu F) (θ.comp a) =
      OmegaCategory.Functor.comp (complexMap a).nu (tableNerveCutSimplex P n F θ) := by
  unfold tableNerveCutSimplex
  rw [orientalChain_natural,cutHom_precomp]
  rfl

noncomputable def tableNerveCutCylinder (P : Type u) [PartialOrder P] :
    streetNerve (complex P).nu ⊗ Δ[1] ⟶ streetNerve (complex P).nu where
  app m := ↾fun z => tableNerveCutSimplex P m.unop.len z.1
    (SSet.stdSimplex.objEquiv z.2).toOrderHom
  naturality m n a := by
    apply ConcreteCategory.hom_ext
    intro z
    exact tableNerveCutSimplex_natural P a.unop.toOrderHom z.1
      (SSet.stdSimplex.objEquiv z.2).toOrderHom

noncomputable def tableNerveCutHomotopy (P : Type u) [PartialOrder P] :
    SSet.Homotopy (𝟙 (streetNerve (complex P).nu))
      (tableNerveVertexMap P ≫ posetTableNerveMap P) where
  h := tableNerveCutCylinder P
  h₀ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    change (cutHom (orientalChain m.unop.len F) (OrderHom.const _ (0 : Fin 2))).nu = F
    rw [cutHom_const_zero]
    exact orientalChain_nu _ F
  h₁ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    change (cutHom (orientalChain m.unop.len F) (OrderHom.const _ (1 : Fin 2))).nu =
      (complexMap (homVertexOrderHom (orientalChain m.unop.len F))).nu
    rw [cutHom_const_one]
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x,hx⟩,θ⟩
    exact False.elim hx

lemma tableNerveVertexMap_weakEquivalence (P : Type u) [PartialOrder P] :
    simplicialWeakEquivalences (tableNerveVertexMap P) :=
  simplicialWeakEquivalence_of_simplicial_retract _ (posetTableNerveMap P)
    (posetTableNerveMap_vertex P) (tableNerveCutHomotopy P)

lemma posetTableNerveMap_weakEquivalence (P : Type u) [PartialOrder P] :
    simplicialWeakEquivalences (posetTableNerveMap P) := by
  apply simplicialWeakEquivalences.of_postcomp _ (tableNerveVertexMap P)
    (tableNerveVertexMap_weakEquivalence P)
  rw [posetTableNerveMap_vertex]
  exact simplicialWeakEquivalences.id_mem _

lemma posetCategorificationUnit_tableMap (P : Type u) [PartialOrder P] :
    categorificationAdjunction.unit.app (nerve P) ≫
      streetNerveMap (posetCategorificationTableMap P) = posetTableNerveMap P := by
  exact (categorificationAdjunction.homEquiv _ _).apply_symm_apply (posetTableNerveMap P)

theorem posetCategorificationUnit_weakEquivalence (P : Type u) [PartialOrder P] :
    simplicialWeakEquivalences (categorificationAdjunction.unit.app (nerve P)) := by
  have : IsIso (streetNerveMap (posetCategorificationTableMap P)) := by
    change IsIso (streetNerveFunctor.map (posetCategorificationTableMap P))
    infer_instance
  apply simplicialWeakEquivalences.of_postcomp _ (streetNerveMap (posetCategorificationTableMap P))
    (simplicialWeakEquivalences.of_isIso _)
  erw [posetCategorificationUnit_tableMap]
  exact posetTableNerveMap_weakEquivalence P

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PartialTables
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial Tables. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.PartialHom
open Table OmegaCategory NormalizedChains
variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {n : ℕ}

def image (f : PartialHom K L n) (x : Table K) : (truncation n L.nu).val.Cell :=
  (truncationUnit n L.nu).map (f.table x)

lemma image_source (f : PartialHom K L n) (k : ℕ) (x : Table K) :
    f.image (truncate k false x) = (truncation n L.nu).val.source k (f.image x) := by
  change (truncationUnit n L.nu).map (f.table (truncate k false x)) = _
  rw [f.table_source]
  exact (truncationUnit n L.nu).map_source k _

lemma image_source_n (f : PartialHom K L n) (x : Table K) :
    f.image (truncate n false x) = f.image x := by
  exact congrArg (truncationUnit n L.nu).map (f.table_source_n x)

lemma image_target_lt (f : PartialHom K L n) (k : ℕ) (hk : k<n) (x : Table K) :
    f.image (truncate k true x) = (truncation n L.nu).val.target k (f.image x) := by
  change (truncationUnit n L.nu).map (f.table (truncate k true x)) = _
  rw [f.table_target_lt k hk]
  exact (truncationUnit n L.nu).map_target k _

lemma image_composable (f : PartialHom K L n) {k : ℕ} (hk : k<n) {x y : Table K}
    (h : truncate k true x = truncate k false y) :
    (truncation n L.nu).val.target k (f.image x) = (truncation n L.nu).val.source k (f.image y) := by
  rw [← f.image_target_lt k hk,← f.image_source,h]

lemma image_comp_lt (f : PartialHom K L n) {k : ℕ} (hk : k<n) (x y : Table K)
    (h : truncate k true x = truncate k false y) :
    f.image (comp k x y h) = (truncation n L.nu).val.comp k (f.image x) (f.image y)
      (f.image_composable hk h) := by
  change (truncationUnit n L.nu).map (f.table (comp k x y h)) = _
  rw [f.table_comp_lt hk]
  exact (truncationUnit n L.nu).map_comp k _ _ (f.table_composable hk h) (f.image_composable hk h)

lemma image_boundary_of_bounded (f : PartialHom K L n) (x : Table K)
    (hx : truncate n false x = x) : f.image x = f.image (truncate n true x) := by
  exact congrArg f.image (K.nu.target_eq_self_of_source_eq_self hx).symm

lemma image_boundary_comp (f : PartialHom K L n) (k : ℕ) (x y : Table K)
    (h : truncate k true x = truncate k false y)
    (hx : f.image x = f.image (truncate n true x))
    (hy : f.image y = f.image (truncate n true y)) :
    f.image (comp k x y h) = f.image (truncate n true (comp k x y h)) := by
  by_cases hk : k<n
  · erw [truncate_comp_gt n k hk true x y h (K.nu.target_composable hk h),
      f.image_comp_lt hk,f.image_comp_lt hk]
    congr 1
  · have hkn : n ≤ k := by omega
    rw [← f.image_source_n (comp k x y h),source_comp_le n k hkn,
      target_comp_le n k hkn,f.image_source_n]
    by_cases he : n = k
    · subst k
      exact hx.trans ((congrArg f.image h).trans ((f.image_source_n y).trans hy))
    · have hn : n < k := by omega
      have hh := congrArg (truncate n false) h
      rw [truncate_truncate,ite_eq_left hn,truncate_truncate,ite_eq_left hn] at hh
      exact ((f.image_source_n x).symm.trans
        ((congrArg f.image hh).trans (f.image_source_n y))).trans hy

variable {N : ℕ}

lemma image_boundary_of_atoms (f : PartialHom (complex (Fin (N+1))) L n)
    (hatom : ∀ (a : Fin (N+1)) (l : List (Fin (N+1))) (ha : (a::l).Pairwise (· < ·)),
      l.length = n+1 → f.image (simplexAtom a l (ha.imp le_of_lt)).table =
        f.image (truncate n true (simplexAtom a l (ha.imp le_of_lt)).table))
    (x : Table (complex (Fin (N+1)))) :
    f.image x = f.image (truncate n true x) := by
  have hb (z : Table (complex (Fin (N+1))))
      (hz : truncate (n+1) false z = z) :
      f.image z = f.image (truncate n true z) := by
    induction oriental_all_atomic z with
    | atom a l ha =>
      have hl := simplexAtom_dimension_le a l ha hz
      by_cases he : l.length = n+1
      · exact hatom a l ha he
      · apply f.image_boundary_of_bounded
        exact (complex (Fin (N+1))).nu.source_fixed_upwards (i := l.length) (by omega)
          (by exact (simplexAtom a l (ha.imp le_of_lt)).dimension)
    | compose k x y h hx hy ihx ihy =>
      obtain ⟨hx',hy'⟩ := comp_dimension_factors x y h hz
      exact f.image_boundary_comp k x y h (ihx hx') (ihy hy')
  have hh := hb (truncate (n+1) false x) (by simp only [truncate_truncate,lt_self_iff_false,ite_false])
  have hf : f.image (truncate (n+1) false x) = f.image x := by
    rw [← f.image_source_n (truncate (n+1) false x),truncate_truncate,
      ite_eq_left (by omega : n < n+1),f.image_source_n]
  rw [hf,truncate_truncate,ite_eq_left (by omega : n < n+1)] at hh
  exact hh

def extendOriental (f : PartialHom (complex (Fin (N+1))) L n)
    (hatom : ∀ (a : Fin (N+1)) (l : List (Fin (N+1))) (ha : (a::l).Pairwise (· < ·)),
      l.length = n+1 → f.image (simplexAtom a l (ha.imp le_of_lt)).table =
        f.image (truncate n true (simplexAtom a l (ha.imp le_of_lt)).table)) :
    OmegaCategory.Functor (Oriental N) (truncation n L.nu).val where
  map := f.image
  map_source := f.image_source
  map_target k x := by
    change f.image (truncate k true x) = (truncation n L.nu).val.target k (f.image x)
    by_cases hk : k<n
    · exact f.image_target_lt k hk x
    · have hkn : n ≤ k := by omega
      have ht : (truncation n L.nu).val.target k (f.image x) = f.image x :=
        (truncation n L.nu).val.target_eq_self_of_source_eq_self
          ((truncation n L.nu).val.source_fixed_upwards hkn ((truncation n L.nu).property _))
      rw [ht,← f.image_source_n (truncate k true x)]
      by_cases he : n = k
      · subst k
        erw [truncate_truncate,ite_eq_right (Nat.lt_irrefl n)]
        exact (f.image_boundary_of_atoms hatom x).symm
      · erw [truncate_truncate,ite_eq_left (by omega : n<k),f.image_source_n]
  map_comp k x y h h' := by
    change f.image (comp k x y h) = (truncation n L.nu).val.comp k (f.image x) (f.image y) h'
    by_cases hk : k<n
    · exact f.image_comp_lt hk x y h
    · have hkn : n ≤ k := by omega
      erw [← f.image_source_n (comp k x y h),source_comp_le n k hkn,f.image_source_n]
      have hxf : (truncation n L.nu).val.source k (f.image x) = f.image x :=
        (truncation n L.nu).val.source_fixed_upwards hkn ((truncation n L.nu).property _)
      have hyf : (truncation n L.nu).val.source k (f.image y) = f.image y :=
        (truncation n L.nu).val.source_fixed_upwards hkn ((truncation n L.nu).property _)
      have he : f.image x = f.image y := by
        rw [(truncation n L.nu).val.target_eq_self_of_source_eq_self hxf,hyf] at h'
        exact h'
      have hh := (truncation n L.nu).val.unit_left k (f.image y)
        ((truncation n L.nu).val.target_source_self k _)
      have hc := comp_congr_cells (truncation n L.nu).val k
        ((truncation n L.nu).val.target_source_self k _) h'
        (hyf.trans he.symm) rfl
      exact he.trans (hh.symm.trans hc)

end Thomason.DirectedComplex.PartialHom

end

noncomputable section
universe u v w z


namespace Thomason.PartialNormalized
open DirectedComplex NormalizedChains
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D] {n : ℕ}

lemma homTotal_boundary (f : PartialHom (complex E) (complex D) n)
    {k : ℕ} (hk : k ≤ n+1) (c : Chains E) (hc : c ∈ grade k) :
    homTotal f (boundary c) = boundary (homTotal f c) := by
  apply grade_induction (M := fun c _ => homTotal f (boundary c) = boundary (homTotal f c))
    ?_ ?_ ?_ ?_ c hc
  · rintro ⟨l,hl⟩ hlen
    cases l with
    | nil => simp [homTotal_bracket,homWord,boundary_bracket]
    | cons a l =>
      cases l with
      | nil =>
        rw [homTotal_bracket]
        change homTotal f (boundary (bracket [a])) =
          boundary (f.map 0 ⟨bracket [a],bracket_mem_grade [a]⟩).val
        rw [grade_zero_eq_empty (boundary_mem_grade
          (f.map 0 ⟨bracket [a],bracket_mem_grade [a]⟩).property)]
        have hau := f.map_augmentation ⟨bracket [a], bracket_mem_grade [a]⟩
        change emptyCoefficient (boundary (f.map 0 _).val) =
          emptyCoefficient (boundary (bracket [a])) at hau
        rw [hau, boundary_bracket (by simp), wordBoundary_cons,
          wordBoundary_nil, map_zero, sub_zero, homTotal_bracket]
        simp [homWord]
      | cons b l =>
        let x : (complex E).Chain (l.length+1) :=
          ⟨bracket (a::b::l),bracket_mem_grade (a::b::l)⟩
        have hp : l.length < n := by simp only [List.length_cons] at hlen; omega
        have hd := congrArg Subtype.val (f.map_d l.length hp x)
        change homTotal f ((complex E).d l.length x).val =
          boundary (homTotal f x.val)
        rw [homTotal_map,homTotal_map]
        exact hd
  · simp only [map_zero]
  · intro c d hc hd ihc ihd; simp only [map_add,ihc,ihd]
  · intro r c hc ih; simp only [map_smul,ih]

lemma homTotal_vertex (f : PartialHom (complex E) (complex D) n) (a : E) :
    homTotal f (bracket [a]) = bracket [homVertex f a] :=
  (homTotal_vertex_exists f a).choose_spec

lemma homVertex_monotone (f : PartialHom (complex E) (complex D) n) (hn : 0<n) : Monotone (homVertex f) := by
  intro a b hab
  apply table_source_le_target_partial (f.table (edgeTable a b hab))
  · simp only [PartialHom.table,hn,ite_true]
    exact (homTotal_map f 0 ⟨bracket [a],bracket_mem_grade [a]⟩).symm.trans
      (homTotal_vertex f a)
  · simp only [PartialHom.table,hn,ite_true]
    exact (homTotal_map f 0 ⟨bracket [b],bracket_mem_grade [b]⟩).symm.trans
      (homTotal_vertex f b)

def homVertexOrderHom (f : PartialHom (complex E) (complex D) n) (hn : 0<n) : E →o D :=
  ⟨homVertex f, homVertex_monotone f hn⟩

lemma homTotal_bracket_supportedOn_lower (f : PartialHom (complex E) (complex D) n)
    (S : Set D) (hS : IsLowerSet S) (l : List E) (hl : l.Pairwise (· ≤ ·))
    (hs : ∀ a ∈ l, homVertex f a ∈ S) (hln : l.length ≤ n+1) : homTotal f (bracket l) ∈ supportedOn S := by
  induction hlen : l.length using Nat.strong_induction_on generalizing l with
  | h z ih =>
    cases l with
    | nil =>
      rw [homTotal_bracket]
      exact bracket_mem_supportedOn (by simp)
    | cons a l =>
      cases l with
      | nil =>
        rw [homTotal_vertex]
        exact bracket_mem_supportedOn (by simpa using hs)
      | cons b l =>
        apply positive_supportedOn_of_boundary_partial hS
          (homTotal_grade f (bracket_mem_grade (a::b::l)))
          (homTotal_positive f (bracket_positive _))
        rw [← homTotal_boundary f hln _ (bracket_mem_grade _), boundary_bracket hl, ← faces_bracket]
        change (homTotal f).toAddMonoidHom (faces bracket (a::b::l)) ∈ _
        rw [faces_hom]
        apply faces_mem_submodule_length
        intro m hm hmlen
        exact ih m.length (by simp only [List.length_cons] at hmlen hlen; omega)
          m (hl.sublist hm) (fun a ha => hs a (hm.subset ha)) (by omega) rfl

lemma cutWord_append (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    (l : List E) (a : E) : cutWord f θ (l++[a]) =
      if θ a = 0 then homTotal f (bracket (l++[a])) else append (homVertex f a) (cutWord f θ l) :=
  by unfold cutWord; rw [List.reverseRecOn_concat]

lemma cutWord_of_all_zero (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    (l : List E) (h : ∀ a ∈ l, θ a = 0) : cutWord f θ l = homTotal f (bracket l) := by
  cases l using List.reverseRecOn with
  | nil => rw [cutWord_nil, homTotal_bracket]; rfl
  | append_singleton l a => rw [cutWord_append, ite_eq_left (h a (by simp))]

lemma cutWord_positive (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    (l : List E) : Positive (cutWord f θ l) := by
  induction l using List.reverseRecOn with
  | nil => rw [cutWord_nil]; exact bracket_positive []
  | append_singleton l a ih =>
    rw [cutWord_append]
    split
    · exact homTotal_positive f (bracket_positive _)
    · exact append_positive _ ih

lemma cutWord_grade (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    (l : List E) : cutWord f θ l ∈ grade l.length := by
  induction l using List.reverseRecOn with
  | nil => rw [cutWord_nil]; exact bracket_mem_grade []
  | append_singleton l a ih =>
    rw [cutWord_append]
    split
    · exact homTotal_grade f (bracket_mem_grade _)
    · simpa only [List.length_append,List.length_singleton] using append_mem_grade _ ih

lemma cutWord_supportedOn_lower (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    (S : Set D) (hS : IsLowerSet S) (l : List E) (hl : l.Pairwise (· ≤ ·))
    (hs : ∀ a ∈ l, homVertex f a ∈ S) (hln : l.length ≤ n+1) : cutWord f θ l ∈ supportedOn S := by
  induction l using List.reverseRecOn with
  | nil => rw [cutWord_nil]; exact bracket_mem_supportedOn (by simp)
  | append_singleton l a ih =>
    rw [cutWord_append]
    split
    · exact homTotal_bracket_supportedOn_lower f S hS _ hl hs hln
    · exact append_mem_supportedOn (hs a (by simp))
        (ih (List.pairwise_append.mp hl).1 (fun b hb => hs b (List.mem_append_left _ hb))
          (by simp only [List.length_append,List.length_singleton] at hln; omega))

lemma cutWord_boundary (f : PartialHom (complex E) (complex D) n) (hn : 0<n) (θ : E →o Fin 2)
    (l : List E) (hl : l.Pairwise (· ≤ ·)) (hln : l.length ≤ n+1) :
    boundary (cutWord f θ l) = faces (cutWord f θ) l := by
  induction l using List.reverseRecOn with
  | nil => simp [boundary_bracket]
  | append_singleton l a ih =>
    rw [cutWord_append]
    by_cases hθ : θ a = 0
    · rw [ite_eq_left hθ, ← homTotal_boundary f hln _ (bracket_mem_grade _), boundary_bracket hl, ← faces_bracket]
      change (homTotal f).toAddMonoidHom (faces bracket (l++[a])) = _
      rw [faces_hom]
      apply faces_congr
      intro m hm
      apply (cutWord_of_all_zero f θ m ?_).symm
      intro b hb
      have hba : b ≤ a := by
        rcases List.mem_append.mp (hm.subset hb) with hb | hb
        · exact (List.pairwise_append.mp hl).2.2 b hb a (by simp)
        · simpa using (show b = a by simpa using hb).le
      have hle := θ.monotone hba
      rw [hθ] at hle
      exact le_antisymm hle (Fin.zero_le _)
    · rw [ite_eq_right hθ, boundary_append_supported _ (cutWord_grade f θ l)
        (cutWord_supportedOn_lower f θ _ (isLowerSet_Iic _) l
          (List.pairwise_append.mp hl).1 (fun b hb =>
            homVertex_monotone f hn ((List.pairwise_append.mp hl).2.2 b hb a (by simp)))
          (by simp only [List.length_append,List.length_singleton] at hln; omega)),
        ih (List.pairwise_append.mp hl).1
          (by simp only [List.length_append,List.length_singleton] at hln; omega), faces_append_singleton]
      congr 1
      change (append (homVertex f a)).toAddMonoidHom (faces (cutWord f θ) l) = _
      rw [faces_hom]
      apply faces_congr
      intro m _
      rw [cutWord_append,ite_eq_right hθ]
      rfl

lemma cutWord_eq_zero_of_not_pairwise (f : PartialHom (complex E) (complex D) n)
    (θ : E →o Fin 2) (l : List E) (hl : l.Pairwise (· ≤ ·))
    (hn : ¬l.Pairwise (· < ·)) : cutWord f θ l = 0 := by
  induction l using List.reverseRecOn with
  | nil => exact (hn (by simp)).elim
  | append_singleton l a ih =>
    rw [cutWord_append]
    split
    · rw [bracket_of_not_pairwise hn,map_zero]
    · rename_i hθ
      by_cases hp : l.Pairwise (· < ·)
      · cases l using List.reverseRecOn with
        | nil => exact (hn (by simp)).elim
        | append_singleton r b =>
          have hba : b ≤ a := (List.pairwise_append.mp hl).2.2 b (by simp) a (by simp)
          have he : b = a := by
            by_contra he
            have hba' : b < a := lt_of_le_of_ne hba he
            apply hn
            apply List.pairwise_append.mpr
            refine ⟨hp, by simp, ?_⟩
            intro c hc d hd
            have hed : d = a := by simpa using hd
            subst d
            rcases List.mem_append.mp hc with hc | hc
            · exact lt_trans ((List.pairwise_append.mp hp).2.2 c hc b (by simp)) hba'
            · have hec : c = b := by simpa using hc
              simpa [hec] using hba'
          subst b
          rw [cutWord_append,ite_eq_right hθ,append_append_self]
      · rw [ih (List.pairwise_append.mp hl).1 hp,map_zero]

def cutTotal (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2) :
    Chains E →ₗ[ℤ] Chains D := Finsupp.linearCombination ℤ (fun w => cutWord f θ w.val)

lemma cutTotal_bracket (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    (l : List E) (hl : l.Pairwise (· ≤ ·)) : cutTotal f θ (bracket l) = cutWord f θ l := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    change Finsupp.linearCombination ℤ _ (Finsupp.single _ 1) = _
    rw [Finsupp.linearCombination_single,one_smul]
  · rw [bracket_of_not_pairwise hs,map_zero,cutWord_eq_zero_of_not_pairwise f θ l hl hs]

lemma cutTotal_grade (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    {k : ℕ} {c : Chains E} (hc : c ∈ grade k) : cutTotal f θ c ∈ grade k := by
  apply linearCombination_mem_grade _ k k _ hc
  intro w hw
  simpa only [← hw] using cutWord_grade f θ w.val

lemma cutTotal_positive (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    {c : Chains E} (hc : Positive c) : Positive (cutTotal f θ c) :=
  linearCombination_positive _ (fun w => cutWord_positive f θ w.val) hc

lemma cutTotal_wordBoundary (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    (l : List E) (hl : l.Pairwise (· ≤ ·)) :
    cutTotal f θ (wordBoundary l) = faces (cutWord f θ) l := by
  rw [← faces_bracket]
  change (cutTotal f θ).toAddMonoidHom (faces bracket l) = _
  rw [faces_hom]
  apply faces_congr
  intro m hm
  exact cutTotal_bracket f θ m (hl.sublist hm)

lemma cutTotal_boundary (f : PartialHom (complex E) (complex D) n) (hn : 0<n) (θ : E →o Fin 2)
    {k : ℕ} (hk : k ≤ n+1) (c : Chains E) (hc : c ∈ grade k) :
    cutTotal f θ (boundary c) = boundary (cutTotal f θ c) := by
  apply grade_induction (M := fun c _ => cutTotal f θ (boundary c) = boundary (cutTotal f θ c))
    ?_ ?_ ?_ ?_ c hc
  · intro w hw
    rw [boundary_bracket (w.property.imp le_of_lt),
      cutTotal_bracket f θ w.val (w.property.imp le_of_lt),
      cutWord_boundary f hn θ w.val (w.property.imp le_of_lt) (by omega),
      cutTotal_wordBoundary f θ w.val (w.property.imp le_of_lt)]
  · simp only [map_zero]
  · intro c d hc hd ihc ihd; simp only [map_add,ihc,ihd]
  · intro r c hc ih; simp only [map_smul,ih]

lemma cutTotal_empty (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2) :
    cutTotal f θ (bracket []) = bracket [] := by
  rw [cutTotal_bracket f θ [] (by simp),cutWord_nil]

lemma cutTotal_augmentation (f : PartialHom (complex E) (complex D) n) (hn : 0<n) (θ : E →o Fin 2)
    {c : Chains E} (hc : c ∈ grade 1) :
    emptyCoefficient (boundary (cutTotal f θ c)) = emptyCoefficient (boundary c) := by
  rw [← cutTotal_boundary f hn θ (by omega) _ hc, grade_zero_eq_empty (boundary_mem_grade hc), map_smul,
    cutTotal_empty]
  simp only [map_smul,emptyCoefficient_bracket,smul_eq_mul]

def cutHom (f : PartialHom (complex E) (complex D) n) (hn : 0<n) (θ : E →o Fin 2) :
    PartialHom (complex E) (complex D) n where
  map _p :=
    { toFun := fun c => ⟨cutTotal f θ c.val, cutTotal_grade f θ c.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x.val y.val) }
  map_d p hp x := Subtype.ext (cutTotal_boundary f hn θ (by omega) x.val x.property)
  map_augmentation x := cutTotal_augmentation f hn θ x.property
  map_positive _ _ hc := cutTotal_positive f θ hc

end Thomason.PartialNormalized

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.PartialHom
open Table OmegaCategory
variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {n : ℕ}

def oneStep (f : PartialHom K L n) (x : Table K)
    (hx : truncate (n+1) false x = x)
    (hd : ∀ b, f.map n (K.d n (x.row (n+1) b)) = L.d n (f.map (n+1) (x.row (n+1) b))) : Table L where
  row p b := f.map p (x.row p b)
  positive p b := f.map_positive p _ (x.positive p b)
  boundary p b := by
    by_cases hp : p<n
    · rw [← f.map_d p hp,x.boundary,map_sub]
    · by_cases he : p=n
      · subst p; rw [← hd b,x.boundary,map_sub]
      · have hnp : n+1 ≤ p := by omega
        have hx' := K.nu.source_fixed_upwards hnp hx
        rw [row_above_fixed x hx (by omega : n+1 < p+1) b,map_zero,map_zero]
        have heq : x.row p true = x.row p false := by
          have hh := congrArg (fun t : Table K => t.row p true) hx'
          change (truncate p false x).row p true = x.row p true at hh
          rw [truncate_top_row] at hh
          exact hh.symm
        rw [heq,sub_self]
  augmentation b := by rw [f.map_augmentation,x.augmentation]
  bounded := ⟨n+1,fun p hp b => by rw [row_above_fixed x hx hp b,map_zero]⟩

lemma table_eq_oneStep_source (f : PartialHom K L n) (x : Table K)
    (hx : truncate (n+1) false x = x)
    (hd : ∀ b, f.map n (K.d n (x.row (n+1) b)) = L.d n (f.map (n+1) (x.row (n+1) b))) :
    f.table x = truncate n false (f.oneStep x hx hd) := by
  ext p b
  simp only [table,oneStep,truncate_row]

lemma table_target_eq_oneStep_target (f : PartialHom K L n) (x : Table K)
    (hx : truncate (n+1) false x = x)
    (hd : ∀ b, f.map n (K.d n (x.row (n+1) b)) = L.d n (f.map (n+1) (x.row (n+1) b))) :
    f.table (truncate n true x) = truncate n true (f.oneStep x hx hd) := by
  ext p b
  simp only [table,oneStep,truncate_row]
  split_ifs <;> simp_all only

lemma image_boundary_of_oneStep (f : PartialHom K L n) (x : Table K)
    (hx : truncate (n+1) false x = x)
    (hd : ∀ b, f.map n (K.d n (x.row (n+1) b)) = L.d n (f.map (n+1) (x.row (n+1) b))) :
    f.image x = f.image (truncate n true x) := by
  change (truncationUnit n L.nu).map (f.table x) =
    (truncationUnit n L.nu).map (f.table (truncate n true x))
  rw [f.table_eq_oneStep_source x hx hd,f.table_target_eq_oneStep_target x hx hd]
  exact ((truncationUnit n L.nu).map_source n _).trans
    (((truncation n L.nu).property _).trans
      (((truncation n L.nu).val.target_eq_self_of_source_eq_self
        ((truncation n L.nu).property _)).symm.trans
          ((truncationUnit n L.nu).map_target n _).symm))

end Thomason.DirectedComplex.PartialHom

end

noncomputable section
universe u v w z


namespace Thomason
open DirectedComplex DirectedComplex.Table NormalizedChains OmegaCategory
variable {C : OmegaCategory.{u}} {n N : ℕ}

lemma liftedChainMap_d_below (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) (hp : p<n) (x : (complex (Fin (N+1))).Chain (p+1)) :
    liftedChainMap F p ((complex (Fin (N+1))).d p x) =
      C.lambdaD p (liftedChainMap F (p+1) x) := by
  apply truncationUnit_lambdaMap_injective C n p hp
  rw [liftedChainMap_unit]
  have hd := (simplexCounitInverse N).map_d p x
  change atomCounitInverse p ((complex (Fin (N+1))).d p x) =
    (Oriental N).lambdaD p (atomCounitInverse (p+1) x) at hd
  rw [hd]
  exact (LinearMap.congr_fun (F.lambdaMap_d p) _).trans
    ((congrArg ((truncation n C).val.lambdaD p) (liftedChainMap_unit F (p+1) x).symm).trans
      (LinearMap.congr_fun ((truncationUnit n C).lambdaMap_d p) _).symm)

variable {K : DirectedComplex.{u}}

def liftedPartial (F : OmegaCategory.Functor (Oriental N) (truncation n K.nu).val) :
    PartialHom (complex (Fin (N+1))) K n where
  map p := (K.lambdaCounit.map p).comp (liftedChainMap F p).toAddMonoidHom
  map_d p hp x := by
    change K.lambdaCounit.map p (liftedChainMap F p ((complex (Fin (N+1))).d p x)) = _
    rw [liftedChainMap_d_below F p hp]
    exact K.lambdaCounit.map_d p _
  map_augmentation x := (K.lambdaCounit.map_augmentation _).trans (liftedChainMap_aug F x)
  map_positive p x hx := K.lambdaCounit.map_positive p _ (liftedChainMap_positive F p x hx)

lemma liftedMap_atom_row
    (F : OmegaCategory.Functor (Oriental N) (truncation n K.nu).val)
    (a : Fin (N+1)) (l : List (Fin (N+1))) (ha : (a::l).Pairwise (· < ·))
    (hlen : l.length ≤ n) (p : ℕ) (b : Bool) :
    K.lambdaCounitMap p (liftedChainMap F p ((simplexAtom a l (ha.imp le_of_lt)).table.row p b)) =
      (truncationCellLift K.nu n l.length
        (F.onCells l.length ⟨(simplexAtom a l (ha.imp le_of_lt)).table,
          by exact (simplexAtom a l (ha.imp le_of_lt)).dimension⟩)).val.row p b := by
  let A := simplexAtom a l (ha.imp le_of_lt)
  have hd : truncate l.length false A.table = A.table := by
    simpa only [List.length_cons,Nat.add_sub_cancel] using A.dimension
  let L := truncationCellLift K.nu n l.length (F.onCells l.length ⟨A.table,hd⟩)
  have hL : (truncationUnit n K.nu).map L.val = F.map A.table :=
    truncationCellLift_map K.nu n l.length _
  by_cases hp : p < l.length
  · have hl : liftedChainMap F p (A.table.row p b) = K.nu.lambdaGen
        (if b then K.nu.targetCell p L.val else K.nu.sourceCell p L.val) := by
      apply truncationUnit_lambdaMap_injective K.nu n p (by omega)
      rw [liftedChainMap_unit,atomCounitInverse_row]
      cases b <;> simp only [Bool.false_eq_true,↓reduceIte]
      · erw [OmegaCategory.Functor.lambdaMap_gen,OmegaCategory.Functor.lambdaMap_gen]
        congr 1
        apply Subtype.ext
        change F.map (truncate p false A.table) =
          (truncationUnit n K.nu).map (truncate p false L.val)
        exact (F.map_source p A.table).trans
          ((congrArg ((truncation n K.nu).val.source p) hL.symm).trans
            ((truncationUnit n K.nu).map_source p L.val).symm)
      · erw [OmegaCategory.Functor.lambdaMap_gen,OmegaCategory.Functor.lambdaMap_gen]
        congr 1
        apply Subtype.ext
        change F.map (truncate p true A.table) =
          (truncationUnit n K.nu).map (truncate p true L.val)
        exact (F.map_target p A.table).trans
          ((congrArg ((truncation n K.nu).val.target p) hL.symm).trans
            ((truncationUnit n K.nu).map_target p L.val).symm)
    rw [hl]
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte]
    · rw [K.lambdaCounitMap_gen]
      exact truncate_top_row p false L.val false
    · rw [K.lambdaCounitMap_gen]
      exact truncate_top_row p true L.val false
  · by_cases he : p = l.length
    · subst p
      have ht : A.table.row l.length b =
          (⟨bracket (a::l),bracket_mem_grade (a::l)⟩ : (complex (Fin (N+1))).Chain l.length) := by
        apply Subtype.ext
        have ht := A.top b
        have he : (a::l).length-1 = l.length := by simp
        rw [he] at ht
        exact ht
      rw [ht,liftedChainMap_bracket F l.length ⟨a::l,ha⟩ rfl,
        liftedBasis_cons F l.length a l ha rfl hd]
      rw [K.lambdaCounitMap_gen]
      change L.val.row l.length false = L.val.row l.length b
      have h := congrArg (fun t : Table K => t.row l.length b) L.property
      change (truncate l.length false L.val).row l.length b = L.val.row l.length b at h
      erw [truncate_top_row] at h
      exact h
    · have hlt : l.length < p := by omega
      rw [row_above_fixed A.table hd hlt b,map_zero,map_zero,
        row_above_fixed L.val L.property hlt b]

lemma liftedPartial_table_atom
    (F : OmegaCategory.Functor (Oriental N) (truncation n K.nu).val)
    (a : Fin (N+1)) (l : List (Fin (N+1))) (ha : (a::l).Pairwise (· < ·))
    (hlen : l.length ≤ n) :
    (liftedPartial F).table (simplexAtom a l (ha.imp le_of_lt)).table =
      (truncationCellLift K.nu n l.length
        (F.onCells l.length ⟨(simplexAtom a l (ha.imp le_of_lt)).table,
          by exact (simplexAtom a l (ha.imp le_of_lt)).dimension⟩)).val := by
  let L := truncationCellLift K.nu n l.length
    (F.onCells l.length ⟨(simplexAtom a l (ha.imp le_of_lt)).table,
      by exact (simplexAtom a l (ha.imp le_of_lt)).dimension⟩)
  have hL : truncate n false L.val = L.val := K.nu.source_fixed_upwards hlen L.property
  have table_eq : (liftedPartial F).table (simplexAtom a l (ha.imp le_of_lt)).table =
      truncate n false L.val := by
    ext p b
    simp only [PartialHom.table]
    erw [truncate_row]
    split_ifs
    · exact liftedMap_atom_row F a l ha hlen p b
    · exact liftedMap_atom_row F a l ha hlen p false
    · rfl
  exact table_eq.trans hL

lemma liftedPartial_image (F : OmegaCategory.Functor (Oriental N) (truncation n K.nu).val)
    (x : Table (complex (Fin (N+1)))) : (liftedPartial F).image x = F.map x := by
  have hb (y : Table (complex (Fin (N+1)))) (hbound : truncate n false y = y) :
      (liftedPartial F).image y = F.map y := by
    induction oriental_all_atomic y with
    | atom a l ha =>
      have hl := simplexAtom_dimension_le a l ha hbound
      change (truncationUnit n K.nu).map ((liftedPartial F).table _) = _
      rw [liftedPartial_table_atom F a l ha hl]
      exact truncationCellLift_map K.nu n l.length _
    | compose k x y h hx hy ihx ihy =>
      obtain ⟨hx',hy'⟩ := comp_dimension_factors x y h hbound
      by_cases hk : k<n
      · rw [(liftedPartial F).image_comp_lt hk]
        exact (comp_congr_cells (truncation n K.nu).val k _ (F.map_composable h)
          (ihx hx') (ihy hy')).trans (F.map_comp k x y h (F.map_composable h)).symm
      · have hc := (complex (Fin (N+1))).nu.comp_of_left_source_fixed k x y h
          ((complex (Fin (N+1))).nu.source_fixed_upwards (by omega : n≤k) hx')
        change Table.comp k x y h = y at hc
        rw [hc]
        exact ihy hy'
  rw [← (liftedPartial F).image_source_n x,hb _ (by simp only [truncate_truncate,lt_self_iff_false,ite_false])]
  exact (F.map_source n x).trans ((truncation n K.nu).property _)

lemma oriental_functor_ext_truncated {D : OmegaCategory.{v}} (hD : D.IsTruncated n)
    (F G : OmegaCategory.Functor (Oriental N) D)
    (h : ∀ (a : Fin (N+1)) (l : List (Fin (N+1))) (ha : (a::l).Pairwise (· < ·)),
      l.length ≤ n → F.map (simplexAtom a l (ha.imp le_of_lt)).table =
        G.map (simplexAtom a l (ha.imp le_of_lt)).table) : F = G := by
  have hb (x : Table (complex (Fin (N+1)))) (hx : truncate n false x = x) :
      F.map x = G.map x := by
    induction oriental_all_atomic x with
    | atom a l ha => exact h a l ha (simplexAtom_dimension_le a l ha hx)
    | compose k x y hab hax hay ihx ihy =>
      obtain ⟨hx',hy'⟩ := comp_dimension_factors x y hab hx
      exact (F.map_comp k x y hab (F.map_composable hab)).trans
        ((comp_congr_cells D k _ _ (ihx hx') (ihy hy')).trans
          (G.map_comp k x y hab (G.map_composable hab)).symm)
  apply OmegaCategory.Functor.ext
  funext x
  exact (hD _).symm.trans ((F.map_source n x).symm.trans
    ((hb (truncate n false x) (by erw [truncate_truncate,ite_eq_right (Nat.lt_irrefl n)])).trans
      ((G.map_source n x).trans (hD _))))

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.PartialNormalized
open DirectedComplex NormalizedChains
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D] {n : ℕ}

lemma cutWord_boundary_append_one (f : PartialHom (complex E) (complex D) n)
    (hn : 0<n) (θ : E →o Fin 2) (l : List E) (a : E)
    (hl : (l++[a]).Pairwise (· ≤ ·)) (hln : l.length ≤ n+1) (hθ : θ a ≠ 0) :
    boundary (cutWord f θ (l++[a])) = faces (cutWord f θ) (l++[a]) := by
  rw [cutWord_append,ite_eq_right hθ, boundary_append_supported _ (cutWord_grade f θ l)
    (cutWord_supportedOn_lower f θ _ (isLowerSet_Iic _) l
      (List.pairwise_append.mp hl).1 (fun b hb =>
        homVertex_monotone f hn ((List.pairwise_append.mp hl).2.2 b hb a (by simp))) hln),
    cutWord_boundary f hn θ l (List.pairwise_append.mp hl).1 hln,faces_append_singleton]
  congr 1
  change (append (homVertex f a)).toAddMonoidHom (faces (cutWord f θ) l) = _
  rw [faces_hom]
  apply faces_congr
  intro m _
  rw [cutWord_append,ite_eq_right hθ]
  rfl

lemma cutTotal_eq_homTotal_of_supported (f : PartialHom (complex E) (complex D) n)
    (θ : E →o Fin 2) (c : Chains E) (hc : c ∈ supportedOn {a | θ a = 0}) :
    cutTotal f θ c = homTotal f c := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  rw [cutTotal_bracket f θ w.val (w.property.imp le_of_lt),homTotal_bracket]
  exact (cutWord_of_all_zero f θ w.val
    ((mem_supportedOn_iff _ c).mp hc w (Finsupp.mem_support_iff.mp hw))).trans
      (homTotal_bracket f w.val)

lemma cutHom_table_of_supported (f : PartialHom (complex E) (complex D) n)
    (hn : 0<n) (θ : E →o Fin 2) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn {a | θ a = 0}) :
    (cutHom f hn θ).table x = f.table x := by
  ext p b
  simp only [PartialHom.table]
  split_ifs
  · apply Subtype.ext
    exact (cutTotal_eq_homTotal_of_supported f θ _ (hx p b)).trans (homTotal_map f p _)
  · apply Subtype.ext
    exact (cutTotal_eq_homTotal_of_supported f θ _ (hx p false)).trans (homTotal_map f p _)
  · rfl

lemma cutHom_image_of_supported (f : PartialHom (complex E) (complex D) n)
    (hn : 0<n) (θ : E →o Fin 2) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn {a | θ a = 0}) :
    (cutHom f hn θ).image x = f.image x :=
  congrArg (OmegaCategory.truncationUnit n (complex D).nu).map
    (cutHom_table_of_supported f hn θ x hx)

lemma truncate_supported {S : Set E} (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn S) (k : ℕ) (e : Bool) :
    ∀ p b, ((Table.truncate k e x).row p b).val ∈ supportedOn S := by
  intro p b
  simp only [Table.truncate_row]
  split_ifs
  · exact hx p b
  · exact hx p e
  · exact (supportedOn S).zero_mem

end Thomason.PartialNormalized

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PartialPrisms
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.OneCat.oneUnitCatIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial Prisms. -/

noncomputable section
universe u v w z


namespace Thomason.PartialNormalized
open DirectedComplex DirectedComplex.Table NormalizedChains OmegaCategory
variable {D : Type u} [PartialOrder D] {n N : ℕ}

lemma cutAtom_boundary (f : PartialHom (complex (Fin (N+1))) (complex D) n)
    (F : OmegaCategory.Functor (Oriental N) (truncation n (complex D).nu).val)
    (hf : ∀ x, f.image x = F.map x) (hn : 0<n) (θ : Fin (N+1) →o Fin 2)
    (a : Fin (N+1)) (l : List (Fin (N+1))) (ha : (a::l).Pairwise (· < ·))
    (hl : l.length = n+1) :
    (cutHom f hn θ).image (simplexAtom a l (ha.imp le_of_lt)).table =
      (cutHom f hn θ).image (truncate n true (simplexAtom a l (ha.imp le_of_lt)).table) := by
  cases l using List.reverseRecOn with
  | nil => simp at hl
  | append_singleton l b =>
    let A := simplexAtom a (l++[b]) (ha.imp le_of_lt)
    have hpw : ((a::l)++[b]).Pairwise (· ≤ ·) := ha.imp le_of_lt
    by_cases hθ : θ b = 0
    · have hz : ∀ z ∈ a::(l++[b]), θ z = 0 := by
        intro z hz
        have hz' : z ∈ (a::l)++[b] := hz
        have hzb : z ≤ b := by
          rcases List.mem_append.mp hz' with hz' | hz'
          · exact (List.pairwise_append.mp hpw).2.2 z hz' b (by simp)
          · have he : z=b := by simpa using hz'
            exact he.le
        have he := θ.monotone hzb
        rw [hθ] at he
        exact le_antisymm he (Fin.zero_le _)
      have hs : ∀ p e, (A.table.row p e).val ∈ supportedOn {z | θ z = 0} :=
        fun p e => supportedOn_mono hz (A.supported p e)
      calc
        _ = f.image A.table := cutHom_image_of_supported f hn θ A.table hs
        _ = F.map A.table := hf _
        _ = F.map (truncate n true A.table) :=
          ((truncation n (complex D).nu).val.target_eq_self_of_source_eq_self
            ((truncation n (complex D).nu).property _)).symm.trans (F.map_target n A.table).symm
        _ = f.image (truncate n true A.table) := (hf _).symm
        _ = _ := (cutHom_image_of_supported f hn θ _ (truncate_supported A.table hs n true)).symm
    · apply PartialHom.image_boundary_of_oneStep
      · exact hl ▸ A.dimension
      · intro e
        have ht : A.table.row (n+1) e =
            (⟨bracket (a::(l++[b])), by
              simpa only [List.length_cons,hl] using (bracket_mem_grade (a::(l++[b])))⟩ : (complex (Fin (N+1))).Chain (n+1)) := by
          apply Subtype.ext
          have h := A.top e
          have he : (a::(l++[b])).length-1 = n+1 := by
            rw [List.length_cons,hl]; omega
          rw [he] at h
          exact h
        change (cutHom f hn θ).map n ((complex (Fin (N+1))).d n (A.table.row (n+1) e)) = _
        rw [ht]
        apply Subtype.ext
        change cutTotal f θ (boundary (bracket (a::(l++[b])))) =
          boundary (cutTotal f θ (bracket (a::(l++[b]))))
        rw [boundary_bracket (ha.imp le_of_lt),cutTotal_wordBoundary f θ _ (ha.imp le_of_lt),
          cutTotal_bracket f θ _ (ha.imp le_of_lt)]
        exact (cutWord_boundary_append_one f hn θ (a::l) b hpw
          (by simp only [List.length_append,List.length_singleton] at hl
              simp only [List.length_cons]; omega) hθ).symm

def finiteCut (f : PartialHom (complex (Fin (N+1))) (complex D) n)
    (F : OmegaCategory.Functor (Oriental N) (truncation n (complex D).nu).val)
    (hf : ∀ x, f.image x = F.map x) (hn : 0<n) (θ : Fin (N+1) →o Fin 2) :
    OmegaCategory.Functor (Oriental N) (truncation n (complex D).nu).val :=
  (cutHom f hn θ).extendOriental (cutAtom_boundary f F hf hn θ)

end Thomason.PartialNormalized

end

noncomputable section
universe u v w z


namespace Thomason
open DirectedComplex NormalizedChains OmegaCategory PartialNormalized
variable {P : Type u} [PartialOrder P] {n : ℕ}

def finiteTableCut (hn : 0<n) {N : ℕ}
    (F : OmegaCategory.Functor (Oriental N) (truncation n (complex P).nu).val)
    (θ : Fin (N+1) →o Fin 2) :
    OmegaCategory.Functor (Oriental N) (truncation n (complex P).nu).val :=
  finiteCut (liftedPartial F) F (liftedPartial_image F) hn θ

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Opposite Simplicial MonoidalCategory DirectedComplex NormalizedChains OmegaCategory

noncomputable def finitePosetTableNerveMap (n : ℕ) (P : Type u) [PartialOrder P] :
    nerve P ⟶ streetNerve (truncation n (complex P).nu).val :=
  posetTableNerveMap P ≫ streetNerveMap (truncationUnit n (complex P).nu)

lemma posetCategorificationFiniteUnit_tableMap (n : ℕ) (P : Type u) [PartialOrder P] :
    (categorificationFiniteAdjunction n).unit.app (nerve P) ≫
      streetNerveMap ((truncationFunctor n).map (posetCategorificationTableMap P)) =
        finitePosetTableNerveMap n P := by
  change (categorificationAdjunction.unit.app (nerve P) ≫
    streetNerveMap (truncationUnit n (categorification.obj (nerve P)))) ≫ _ = _
  erw [Category.assoc]
  have he : streetNerveMap (truncationUnit n (categorification.obj (nerve P))) ≫
      streetNerveMap ((truncationFunctor n).map (posetCategorificationTableMap P)) =
      streetNerveMap (posetCategorificationTableMap P) ≫ streetNerveMap (truncationUnit n (complex P).nu) := rfl
  erw [he,← Category.assoc,posetCategorificationUnit_tableMap]
  rfl

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SieveAttachments
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sieve Attachments. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables

lemma interval_vertex_mem_new {P : Type u} [PartialOrder P] {Y : OmegaCategory.{u}}
    (i : categorification.obj (nerve P) ⟶ Y) (η : Y ⟶ interval) (l : P →o Fin 2)
    (hi : i ≫ η = posetCategorificationLabel l)
    (x : (categorification.obj (nerve P)).Objects) (e : Fin 2)
    (he : l (NormalizedChains.tableObjectsEquiv ((posetCategorificationTableMap P).objects x)) = e) :
    i.objects x ∈ intervalFiberObjects η e := by
  change η.objects (i.objects x) = intervalVertex e
  exact (congrArg (fun f : categorification.obj (nerve P) ⟶ interval => f.objects x) hi).trans
    ((posetLabel_objects l x).trans (congrArg intervalVertex he))

lemma labelled_objects_cover {P : Type u} [PartialOrder P] {A : Set P}
    {X Y : OmegaCategory.{u}} {a : categorification.obj (nerve A) ⟶ X}
    {h : X ⟶ Y} {i : categorification.obj (nerve P) ⟶ Y}
    (H : IsPushout a
      (categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i)
    (η₁ η₂ : Y ⟶ interval) (l₁ l₂ : P →o Fin 2) (e : Fin 2)
    (hh : h ≫ η₁ = constantLabel X e ∨ h ≫ η₂ = constantLabel X e)
    (hi₁ : i ≫ η₁ = posetCategorificationLabel l₁)
    (hi₂ : i ≫ η₂ = posetCategorificationLabel l₂)
    (hl : ∀ p, l₁ p = e ∨ l₂ p = e) :
    intervalFiberObjects η₁ e ∪ intervalFiberObjects η₂ e = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  rcases Types.eq_or_eq_of_isPushout (H.map objectsFunctor) y with ⟨x,rfl⟩ | ⟨x,rfl⟩
  · rcases hh with hh | hh
    · exact Or.inl (interval_vertex_mem_old h η₁ e hh x)
    · exact Or.inr (interval_vertex_mem_old h η₂ e hh x)
  · rcases hl (NormalizedChains.tableObjectsEquiv ((posetCategorificationTableMap P).objects x)) with hx | hx
    · exact Or.inl (interval_vertex_mem_new i η₁ l₁ hi₁ x e hx)
    · exact Or.inr (interval_vertex_mem_new i η₂ l₂ hi₂ x e hx)

end Thomason.Attachments

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_KanQuillen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kan Quillen. -/

noncomputable section
universe u v w z
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace Thomason.KanQuillen
open SSet.modelCategoryQuillen

lemma first_wfs : IsWeakFactorizationSystem
    (monomorphisms SSet.{u} ⊓ simplicialWeakEquivalences) simplicialFibrations := by
  rw [← anodyne_class]; exact horn_weakFactorization

lemma second_wfs : IsWeakFactorizationSystem
    (monomorphisms SSet.{u}) (simplicialFibrations ⊓ simplicialWeakEquivalences) := by
  rw [← GeometricRecognition.boundary_right_class]; exact boundary_weakFactorization

def geometricModel : KanQuillenModel.{u} := by
  letI : CategoryWithWeakEquivalences SSet.{u} := ⟨simplicialWeakEquivalences⟩
  letI : CategoryWithFibrations SSet.{u} := ⟨simplicialFibrations⟩
  letI : CategoryWithCofibrations SSet.{u} := ⟨monomorphisms SSet⟩
  letI : IsWeakFactorizationSystem (trivialCofibrations SSet.{u}) (fibrations SSet) := first_wfs
  letI : IsWeakFactorizationSystem (cofibrations SSet.{u}) (trivialFibrations SSet) := second_wfs
  letI : (weakEquivalences SSet.{u}).HasTwoOutOfThreeProperty :=
    simplicialWeakEquivalences_hasTwoOutOfThreeProperty
  exact ⟨ModelCategory.mk' SSet,rfl,rfl,rfl⟩
end Thomason.KanQuillen

end

noncomputable section
universe u v w z


namespace Thomason.DependentPosets
open CategoryTheory Limits Opposite
attribute [-instance] CategoryTheory.Sigma.sigma

open Attachments AttachmentComparison
end Thomason.DependentPosets

end

noncomputable section
universe u v w z


namespace Thomason.TransferAcyclicity
open CategoryTheory Limits Simplicial PartialOrder
open AttachmentComparison Attachments HornAttachments SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

attribute [instance] PosetAttachment.order

end Thomason.TransferAcyclicity

end

noncomputable section
universe u v w z


namespace Thomason.TransferAcyclicity
open CategoryTheory Limits Simplicial
open AttachmentComparison Attachments HornAttachments SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

end Thomason.TransferAcyclicity

end

end OAI
end


