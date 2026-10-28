-- Prove2me | Definitions.Def_OAIQ043T009
-- name    : OAIQ043T009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T09:59:43.431435+00:00
-- url     : https://prove2.me/theorems/557f2da8-e133-4b31-aeec-711afc160993
-- title:
--   Definitions bundle OAIQ043T009 of the split of OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Thomason.main` and `OAI.Thomason.nerveDetection_allDimensions`, carved from OpenAI's openai/math development (OpenAI, *Thomason Model Structures in Every Strict Higher Dimension (result family 317)*, OpenAI Math Release, September 25, 2026, result family 317, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 38 declarations of OpenAI's Lean: 7 definitions and 31 theorems. The definitions and types are `OAI.Thomason.DirectedComplex.PartialHom.precomp`, `OAI.Thomason.NormalizedChains.complexFinIso`, `OAI.Thomason.NormalizedChains.complexOrderIso`, `OAI.Thomason.OmegaAttachmentComparison.posetObj`, `OAI.Thomason.RightIntervalExtensionExists`, `OAI.Thomason.finiteTableNerveCutCylinder`, `OAI.Thomason.finiteTableNerveVertexMap`.
--
--   **Sources.** They come from these modules of lean/OAI/CategoryTheory/Thomason, in whole or in part: [`Thomason_AttachmentComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/AttachmentComparison.lean), [`Thomason_DimensionOne`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/DimensionOne.lean), [`Thomason_FiniteGluing`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/FiniteGluing.lean), [`Thomason_GrayGenerators`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/GrayGenerators.lean), [`Thomason_PartialPrisms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/PartialPrisms.lean), [`Thomason_PrismBasis`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/PrismBasis.lean), [`Thomason_StandardComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/StandardComparison.lean).
--
--   **Imports.** It imports the published bundle `Def_ThomasonModelStructures`; the bundles `OAIQ043T006` and `OAIQ043T007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ043T010` and `OAIQ043T011`.
-- source:
--   OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 317; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/CategoryTheory/Thomason at commit adc7f12

import Mathlib
import Definitions.Def_ThomasonModelStructures
import Definitions.Def_OAIQ043T006
import Definitions.Def_OAIQ043T007

section
-- module Solutions.OAIQ043_TH.Thomason_PartialPrisms
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial Prisms. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.PartialHom
open Table
variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {M : DirectedComplex.{w}} {n : ℕ}

def precomp (f : PartialHom L M n) (a : Hom K L) : PartialHom K M n where
  map p := (f.map p).comp (a.map p)
  map_d p hp x := by
    change f.map p (a.map p (K.d p x)) = _
    rw [a.map_d,f.map_d p hp]
    rfl
  map_augmentation x := (f.map_augmentation _).trans (a.map_augmentation x)
  map_positive p x hx := f.map_positive p _ (a.map_positive p x hx)

lemma precomp_table (f : PartialHom L M n) (a : Hom K L) (x : Table K) :
    (f.precomp a).table x = f.table (a.table x) := by
  ext p b
  simp only [table,precomp]
  split_ifs <;> rfl

lemma precomp_image (f : PartialHom L M n) (a : Hom K L) (x : Table K) :
    (f.precomp a).image x = f.image (a.table x) :=
  congrArg (OmegaCategory.truncationUnit n M.nu).map (f.precomp_table a x)

end Thomason.DirectedComplex.PartialHom

end

noncomputable section
universe u v w z


namespace Thomason.PartialNormalized
open DirectedComplex NormalizedChains
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]
variable {B : Type w} [PartialOrder B] {n : ℕ}

lemma homTotal_precomp (a : B →o E) (f : PartialHom (complex E) (complex D) n)
    (c : Chains B) : homTotal (f.precomp (complexMap a)) c = homTotal f (map a c) := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  obtain ⟨l,hl⟩ := w
  cases l with
  | nil => rw [homTotal_bracket,map_bracket a (by simp),homTotal_bracket]; rfl
  | cons b l =>
    have h := homTotal_map f l.length ((complexMap a).map l.length
      ⟨bracket (b::l),bracket_mem_grade _⟩)
    exact (homTotal_map (f.precomp (complexMap a)) l.length
      ⟨bracket (b::l),bracket_mem_grade _⟩).trans h.symm

lemma homVertex_precomp (a : B →o E) (f : PartialHom (complex E) (complex D) n) (b : B) :
    homVertex (f.precomp (complexMap a)) b = homVertex f (a b) := by
  apply bracket_singleton_injective
  change bracket [homVertex (f.precomp (complexMap a)) b] = bracket [homVertex f (a b)]
  rw [← homTotal_vertex,homTotal_precomp,map_bracket a (by simp)]
  exact homTotal_vertex f (a b)

lemma cutWord_precomp (a : B →o E) (f : PartialHom (complex E) (complex D) n)
    (θ : E →o Fin 2) (l : List B) (hl : l.Pairwise (· ≤ ·)) :
    cutWord (f.precomp (complexMap a)) (θ.comp a) l = cutWord f θ (l.map a) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l b ih =>
    rw [List.map_append,List.map_singleton,cutWord_append,cutWord_append]
    change (if θ (a b) = 0 then _ else _) = (if θ (a b) = 0 then _ else _)
    split
    · rw [homTotal_precomp,map_bracket a hl,List.map_append,List.map_singleton]
    · rw [homVertex_precomp,ih (List.pairwise_append.mp hl).1]

lemma cutTotal_precomp (a : B →o E) (f : PartialHom (complex E) (complex D) n)
    (θ : E →o Fin 2) (c : Chains B) :
    cutTotal (f.precomp (complexMap a)) (θ.comp a) c = cutTotal f θ (map a c) := by
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

lemma cutHom_precomp (a : B →o E) (f : PartialHom (complex E) (complex D) n)
    (hn : 0<n) (θ : E →o Fin 2) :
    cutHom (f.precomp (complexMap a)) hn (θ.comp a) = (cutHom f hn θ).precomp (complexMap a) := by
  apply PartialHom.ext
  intro p
  apply AddMonoidHom.ext
  intro x
  exact Subtype.ext (cutTotal_precomp a _ θ x.val)

end Thomason.PartialNormalized

end

noncomputable section
universe u v w z


namespace Thomason
open DirectedComplex DirectedComplex.Table NormalizedChains OmegaCategory
variable {K : DirectedComplex.{u}} {n M N : ℕ}

lemma simplexInverse_natural (a : Fin (M+1) →o Fin (N+1)) (p : ℕ)
    (x : (complex (Fin (M+1))).Chain p) :
    atomCounitInverse p ((complexMap a).map p x) =
      (complexMap a).nu.lambdaMap p (atomCounitInverse p x) := by
  apply oriental_lambdaCounit_injective p
  rw [counit_atomInverse]
  have hh := lambdaNu_left_inv (Hom.comp (complex (Fin (M+1))).lambdaCounit (complexMap a))
  rw [lambdaNuForward_counit] at hh
  have h := congrArg (fun H => H.map p (atomCounitInverse p x)) hh
  change (complex (Fin (N+1))).lambdaCounitMap p
    ((complexMap a).nu.lambdaMap p (atomCounitInverse p x)) =
      (complexMap a).map p ((complex (Fin (M+1))).lambdaCounitMap p (atomCounitInverse p x)) at h
  rw [counit_atomInverse] at h
  exact h.symm

lemma liftedPartial_natural_below (a : Fin (M+1) →o Fin (N+1))
    (F : OmegaCategory.Functor (Oriental N) (truncation n K.nu).val)
    (p : ℕ) (hp : p<n) :
    (liftedPartial (OmegaCategory.Functor.comp (complexMap a).nu F)).map p =
      ((liftedPartial F).precomp (complexMap a)).map p := by
  apply AddMonoidHom.ext
  intro x
  change K.lambdaCounitMap p (liftedChainMap (OmegaCategory.Functor.comp (complexMap a).nu F) p x) =
    K.lambdaCounitMap p (liftedChainMap F p ((complexMap a).map p x))
  congr 1
  apply truncationUnit_lambdaMap_injective K.nu n p hp
  rw [liftedChainMap_unit,liftedChainMap_unit]
  exact (LinearMap.congr_fun (OmegaCategory.Functor.lambdaMap_comp (complexMap a).nu F p) _).trans
    (congrArg (F.lambdaMap p) (simplexInverse_natural a p x).symm)

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.PartialNormalized
open DirectedComplex DirectedComplex.Table NormalizedChains OmegaCategory
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D] {n : ℕ}

lemma homWord_congr_low (f g : PartialHom (complex E) (complex D) n)
    (hfg : ∀ p, p<n → f.map p = g.map p) (l : List E) (hl : l.length ≤ n) :
    homWord f l = homWord g l := by
  cases l with
  | nil => rfl
  | cons a l =>
    change (f.map l.length _).val = (g.map l.length _).val
    rw [hfg l.length (by simp only [List.length_cons] at hl; omega)]

lemma homTotal_congr_low (f g : PartialHom (complex E) (complex D) n)
    (hfg : ∀ p, p<n → f.map p = g.map p) {k : ℕ} (hk : k≤n)
    (c : Chains E) (hc : c ∈ grade k) : homTotal f c = homTotal g c := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  rw [homTotal_bracket,homTotal_bracket]
  exact homWord_congr_low f g hfg _ (by
    have he := (mem_grade_iff k c).mp hc w (Finsupp.mem_support_iff.mp hw)
    omega)

lemma homVertex_congr_low (f g : PartialHom (complex E) (complex D) n)
    (hfg : ∀ p, p<n → f.map p = g.map p) (hn : 0<n) (a : E) :
    homVertex f a = homVertex g a := by
  apply bracket_singleton_injective
  change bracket [homVertex f a] = bracket [homVertex g a]
  rw [← homTotal_vertex,← homTotal_vertex]
  exact homTotal_congr_low f g hfg (by change 1 ≤ n; omega) _ (bracket_mem_grade [a])

lemma cutWord_congr_low (f g : PartialHom (complex E) (complex D) n)
    (hfg : ∀ p, p<n → f.map p = g.map p) (hn : 0<n)
    (θ : E →o Fin 2) (l : List E) (hl : l.length ≤ n) :
    cutWord f θ l = cutWord g θ l := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [cutWord_append,cutWord_append]
    split
    · exact homTotal_congr_low f g hfg hl _ (bracket_mem_grade _)
    · rw [homVertex_congr_low f g hfg hn a,
        ih (by simp only [List.length_append,List.length_singleton] at hl; omega)]

lemma cutTotal_congr_low (f g : PartialHom (complex E) (complex D) n)
    (hfg : ∀ p, p<n → f.map p = g.map p) (hn : 0<n)
    (θ : E →o Fin 2) {k : ℕ} (hk : k≤n) (c : Chains E) (hc : c ∈ grade k) :
    cutTotal f θ c = cutTotal g θ c := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  rw [cutTotal_bracket _ _ _ (w.property.imp le_of_lt),cutTotal_bracket _ _ _ (w.property.imp le_of_lt)]
  exact cutWord_congr_low f g hfg hn θ _ (by
    have he := (mem_grade_iff k c).mp hc w (Finsupp.mem_support_iff.mp hw)
    omega)

lemma cutWord_congr_append_one (f g : PartialHom (complex E) (complex D) n)
    (hfg : ∀ p, p<n → f.map p = g.map p) (hn : 0<n)
    (θ : E →o Fin 2) (l : List E) (a : E) (hl : l.length ≤ n) (ha : θ a ≠ 0) :
    cutWord f θ (l++[a]) = cutWord g θ (l++[a]) := by
  rw [cutWord_append,cutWord_append,ite_eq_right ha,ite_eq_right ha,
    homVertex_congr_low f g hfg hn a,cutWord_congr_low f g hfg hn θ l hl]

lemma cutTable_atom_congr (f g : PartialHom (complex E) (complex D) n)
    (hfg : ∀ p, p<n → f.map p = g.map p) (hn : 0<n)
    (θ : E →o Fin 2) (a : E) (l : List E) (ha : (a::l).Pairwise (· < ·))
    (hl : l.length ≤ n) (r : List E) (b : E) (he : a::l = r++[b]) (hb : θ b ≠ 0) :
    (cutHom f hn θ).table (simplexAtom a l (ha.imp le_of_lt)).table =
      (cutHom g hn θ).table (simplexAtom a l (ha.imp le_of_lt)).table := by
  let A := simplexAtom a l (ha.imp le_of_lt)
  ext p e
  simp only [PartialHom.table]
  split_ifs with hpn hpe
  · apply Subtype.ext
    exact cutTotal_congr_low f g hfg hn θ (by omega) _ (A.table.row p e).property
  · subst p
    by_cases hln : l.length < n
    · rw [row_above_fixed A.table A.dimension hln false,map_zero,map_zero]
    · have hlen : l.length = n := by omega
      have ht : (A.table.row n false).val = bracket (a::l) := by
        have ht := A.top false
        have he : (a::l).length-1 = n := by rw [List.length_cons,hlen]; omega
        rw [he] at ht
        exact ht
      apply Subtype.ext
      change cutTotal f θ (A.table.row n false).val = cutTotal g θ (A.table.row n false).val
      rw [ht,cutTotal_bracket _ _ _ (ha.imp le_of_lt),cutTotal_bracket _ _ _ (ha.imp le_of_lt),he]
      apply cutWord_congr_append_one f g hfg hn θ r b _ hb
      have h := congrArg List.length he
      simp only [List.length_cons,List.length_append] at h
      omega
  · rfl

end Thomason.PartialNormalized

end

noncomputable section
universe u v w z


namespace Thomason.PartialNormalized
open DirectedComplex DirectedComplex.Table NormalizedChains OmegaCategory
variable {D : Type u} [PartialOrder D] {n N : ℕ}

lemma finiteCut_congr
    (f g : PartialHom (complex (Fin (N+1))) (complex D) n)
    (F : OmegaCategory.Functor (Oriental N) (truncation n (complex D).nu).val)
    (hf : ∀ x, f.image x = F.map x) (hg : ∀ x, g.image x = F.map x)
    (hfg : ∀ p, p<n → f.map p = g.map p) (hn : 0<n) (θ : Fin (N+1) →o Fin 2) :
    finiteCut f F hf hn θ = finiteCut g F hg hn θ := by
  apply oriental_functor_ext_truncated (truncation n (complex D).nu).property
  intro a l ha hl
  change (cutHom f hn θ).image (simplexAtom a l (ha.imp le_of_lt)).table =
    (cutHom g hn θ).image (simplexAtom a l (ha.imp le_of_lt)).table
  have hlast : ∃ r b, a::l = r++[b] := by
    cases l using List.reverseRecOn with
    | nil => exact ⟨[],a,rfl⟩
    | append_singleton r b => exact ⟨a::r,b,rfl⟩
  obtain ⟨r,b,he⟩ := hlast
  by_cases hb : θ b = 0
  · have hpw : (r++[b]).Pairwise (· ≤ ·) := he ▸ ha.imp le_of_lt
    have hz : ∀ z ∈ a::l, θ z = 0 := by
      intro z hz
      rw [he] at hz
      have hzb : z ≤ b := by
        rcases List.mem_append.mp hz with hz | hz
        · exact (List.pairwise_append.mp hpw).2.2 z hz b (by simp)
        · have he' : z=b := by simpa using hz
          exact he'.le
      have h := θ.monotone hzb
      rw [hb] at h
      exact le_antisymm h (Fin.zero_le _)
    have hs : ∀ p e, ((simplexAtom a l (ha.imp le_of_lt)).table.row p e).val ∈
        supportedOn {z | θ z = 0} := fun p e =>
      supportedOn_mono hz ((simplexAtom a l (ha.imp le_of_lt)).supported p e)
    rw [cutHom_image_of_supported f hn θ _ hs,cutHom_image_of_supported g hn θ _ hs,hf,hg]
  · exact congrArg (truncationUnit n (complex D).nu).map
      (cutTable_atom_congr f g hfg hn θ a l ha hl r b he hb)

end Thomason.PartialNormalized

end

noncomputable section
universe u v w z


namespace Thomason
open DirectedComplex NormalizedChains OmegaCategory PartialNormalized
variable {P : Type u} [PartialOrder P] {n : ℕ}

lemma finiteTableCut_natural (hn : 0<n) {M N : ℕ}
    (a : Fin (M+1) →o Fin (N+1))
    (F : OmegaCategory.Functor (Oriental N) (truncation n (complex P).nu).val)
    (θ : Fin (N+1) →o Fin 2) :
    finiteTableCut hn (OmegaCategory.Functor.comp (complexMap a).nu F) (θ.comp a) =
      OmegaCategory.Functor.comp (complexMap a).nu (finiteTableCut hn F θ) := by
  let g := (liftedPartial F).precomp (complexMap a)
  have hg : ∀ x, g.image x = (OmegaCategory.Functor.comp (complexMap a).nu F).map x := by
    intro x
    exact ((liftedPartial F).precomp_image (complexMap a) x).trans (liftedPartial_image F _)
  calc
    _ = finiteCut g (OmegaCategory.Functor.comp (complexMap a).nu F) hg hn (θ.comp a) :=
      finiteCut_congr _ g _ (liftedPartial_image _) hg
        (liftedPartial_natural_below a F) hn (θ.comp a)
    _ = _ := by
      apply OmegaCategory.Functor.ext
      funext x
      change (PartialNormalized.cutHom ((liftedPartial F).precomp (complexMap a)) hn (θ.comp a)).image x = _
      erw [PartialNormalized.cutHom_precomp,PartialHom.precomp_image]
      rfl

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.PartialNormalized
open DirectedComplex NormalizedChains
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D] {n : ℕ}

lemma cutWord_const_one (f : PartialHom (complex E) (complex D) n) (l : List E) :
    cutWord f (OrderHom.const E (1 : Fin 2)) l = bracket (l.map (homVertex f)) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [cutWord_append,ite_eq_right (by change (1 : Fin 2) ≠ 0; decide),ih,append_bracket,
      List.map_append,List.map_singleton]

lemma cutTotal_const_zero (f : PartialHom (complex E) (complex D) n) (c : Chains E) :
    cutTotal f (OrderHom.const E (0 : Fin 2)) c = homTotal f c := by
  apply cutTotal_eq_homTotal_of_supported
  apply (mem_supportedOn_iff _ c).mpr
  simp

lemma cutTotal_const_one (f : PartialHom (complex E) (complex D) n) (hn : 0<n) (c : Chains E) :
    cutTotal f (OrderHom.const E (1 : Fin 2)) c = map (homVertexOrderHom f hn) c := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [cutTotal_bracket _ _ w.val (w.property.imp le_of_lt),cutWord_const_one,
    map_bracket (homVertexOrderHom f hn) (w.property.imp le_of_lt)]
  rfl

lemma cutHom_const_zero (f : PartialHom (complex E) (complex D) n) (hn : 0<n) :
    cutHom f hn (OrderHom.const E (0 : Fin 2)) = f := by
  apply PartialHom.ext
  intro p
  apply AddMonoidHom.ext
  intro c
  apply Subtype.ext
  exact (cutTotal_const_zero f c.val).trans (homTotal_map f p c)

end Thomason.PartialNormalized

end

noncomputable section
universe u v w z


namespace Thomason
open DirectedComplex NormalizedChains OmegaCategory
variable {K : DirectedComplex.{u}} {n N : ℕ}

lemma liftedPartial_of_nu_below (f : Hom (complex (Fin (N+1))) K) (p : ℕ) (hp : p<n) :
    (liftedPartial (OmegaCategory.Functor.comp f.nu (truncationUnit n K.nu))).map p = f.map p := by
  apply AddMonoidHom.ext
  intro x
  have he : liftedChainMap (OmegaCategory.Functor.comp f.nu (truncationUnit n K.nu)) p x =
      f.nu.lambdaMap p (atomCounitInverse p x) := by
    apply truncationUnit_lambdaMap_injective K.nu n p hp
    erw [liftedChainMap_unit,OmegaCategory.Functor.lambdaMap_comp]
    rfl
  change K.lambdaCounitMap p (liftedChainMap
    (OmegaCategory.Functor.comp f.nu (truncationUnit n K.nu)) p x) = _
  rw [he]
  change (orientalChain N f.nu).map p x = f.map p x
  rw [orientalChain_of_nu]

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Opposite Simplicial MonoidalCategory DirectedComplex NormalizedChains OmegaCategory

noncomputable def finiteTableNerveVertexMap (n : ℕ) (hn : 0<n) (P : Type u) [PartialOrder P] :
    streetNerve (truncation n (complex P).nu).val ⟶ nerve P where
  app m := ↾fun F => (PartialNormalized.homVertexOrderHom (liftedPartial F) hn).monotone.functor
  naturality m k a := by
    apply ConcreteCategory.hom_ext
    intro F
    apply nerve.ext_of_isThin
    funext i
    change PartialNormalized.homVertex
        (liftedPartial (OmegaCategory.Functor.comp (complexMap a.unop.toOrderHom).nu F)) i =
      PartialNormalized.homVertex (liftedPartial F) (a.unop.toOrderHom i)
    rw [PartialNormalized.homVertex_congr_low _ _ (liftedPartial_natural_below a.unop.toOrderHom F) hn]
    exact PartialNormalized.homVertex_precomp a.unop.toOrderHom (liftedPartial F) i

lemma finiteTableCut_const_zero {n N : ℕ} (hn : 0<n) (P : Type u) [PartialOrder P]
    (F : OmegaCategory.Functor (Oriental N) (truncation n (complex P).nu).val) :
    finiteTableCut hn F (OrderHom.const _ (0 : Fin 2)) = F := by
  apply OmegaCategory.Functor.ext
  funext x
  change (PartialNormalized.cutHom (liftedPartial F) hn (OrderHom.const _ (0 : Fin 2))).image x = _
  rw [PartialNormalized.cutHom_const_zero]
  exact liftedPartial_image F x

noncomputable def finiteTableNerveCutCylinder (n : ℕ) (hn : 0<n) (P : Type u) [PartialOrder P] :
    streetNerve (truncation n (complex P).nu).val ⊗ Δ[1] ⟶
      streetNerve (truncation n (complex P).nu).val where
  app m := ↾fun z => finiteTableCut hn z.1 (SSet.stdSimplex.objEquiv z.2).toOrderHom
  naturality m k a := by
    apply ConcreteCategory.hom_ext
    intro z
    exact finiteTableCut_natural hn a.unop.toOrderHom z.1 (SSet.stdSimplex.objEquiv z.2).toOrderHom

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_DimensionOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension One. -/

noncomputable section
universe u v w z


namespace Thomason.BoundaryProperness
open CategoryTheory Limits Simplicial PartialOrder
open AttachmentComparison Attachments HornAttachments SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

attribute [instance] PosetAttachment.order

end Thomason.BoundaryProperness

end

noncomputable section
universe u v w z


namespace Thomason.BoundaryProperness
open CategoryTheory Limits Simplicial
open AttachmentComparison Attachments HornAttachments SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

end Thomason.BoundaryProperness

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason

def RightIntervalExtensionExists : Prop := Nonempty RightIntervalExtension.{u}

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex
open CategoryTheory DirectedComplex DirectedComplex.Table

lemma faceMap_faceMap (n k j : ℕ) (hjk : j < k) (a b : Bool) :
    Hom.comp (faceMap.{u} k j a) (faceMap n k b) = faceMap n j a := by
  apply hom_ext
  change (faceMap n k b).nu.map ((faceMap k j a).nu.map (topTable j)) = _
  rw [faceMap_top]
  change (faceMap n k b).table (truncate j a (topTable k)) = _
  rw [Hom.table_truncate]
  change truncate j a ((faceMap n k b).nu.map (topTable k)) = _
  rw [faceMap_top, faceMap_top, truncate_truncate, ite_eq_left hjk]

end Thomason.GlobeComplex

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_GrayGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gray Generators. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

lemma join_interchange (C : OmegaCategory.{u}) (k l : ℕ) (hkl : k < l)
    (a b c d : C.Cell)
    (hab : C.target l a = C.source l b) (hcd : C.target l c = C.source l d)
    (hac : C.target k a = C.source k c) (hbd : C.target k b = C.source k d) :
    C.join k (C.join l a b) (C.join l c d) =
      C.join l (C.join k a c) (C.join k b d) := by
  have h₁ : C.target k (C.comp l a b hab) = C.source k (C.comp l c d hcd) := by
    rw [C.target_comp_le k l (by omega), C.source_comp_le k l (by omega)]
    have he : C.target k a = C.target k b := by
      have hh := congrArg (C.target k) hab
      simpa only [C.target_target, min_eq_left (le_of_lt hkl),
        C.target_source, ite_eq_left hkl] using hh
    exact he.symm.trans hac
  have h₂ : C.target l (C.comp k a c hac) = C.source l (C.comp k b d hbd) := by
    rw [C.target_comp_gt l k hkl a c hac (C.target_composable hkl hac),
      C.source_comp_gt l k hkl b d hbd (C.source_composable hkl hbd)]
    simp only [hab, hcd]
  rw [C.join_eq l a b hab, C.join_eq l c d hcd,
    C.join_eq k a c hac, C.join_eq k b d hbd,
    C.join_eq k _ _ h₁, C.join_eq l _ _ h₂]
  exact C.interchange k l hkl a b c d _ _ _ _ _ _

lemma join_whisker_right (C : OmegaCategory.{u}) (k l : ℕ) (hkl : k < l)
    (a b c : C.Cell) (hc : C.source l c = c)
    (hab : C.target l a = C.source l b)
    (hac : C.target k a = C.source k c) (hbc : C.target k b = C.source k c) :
    C.join k (C.join l a b) c = C.join l (C.join k a c) (C.join k b c) := by
  have hcc : C.target l c = C.source l c := (C.target_eq_self_of_source_eq_self hc).trans hc.symm
  have h' := C.join_interchange k l hkl a b c c hab hcc hac hbc
  rw [C.join_left_unit l c c hc hcc] at h'
  exact h'

lemma join_whisker_left (C : OmegaCategory.{u}) (k l : ℕ) (hkl : k < l)
    (a b c : C.Cell) (ha : C.source l a = a)
    (hbc : C.target l b = C.source l c)
    (hab : C.target k a = C.source k b) (hac : C.target k a = C.source k c) :
    C.join k a (C.join l b c) = C.join l (C.join k a b) (C.join k a c) := by
  have haa : C.target l a = C.source l a := (C.target_eq_self_of_source_eq_self ha).trans ha.symm
  have h' := C.join_interchange k l hkl a a b c haa hbc hab hac
  rw [C.join_left_unit l a a ha haa] at h'
  exact h'

lemma Functor.map_join {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) (k : ℕ) (x y : C.Cell)
    (h : C.target k x = C.source k y) :
    F.map (C.join k x y) = D.join k (F.map x) (F.map y) := by
  rw [C.join_eq k x y h, D.join_eq k _ _ (F.map_composable h), F.map_comp]

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_AttachmentComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Attachment Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaAttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments Couniversality
open AttachmentComparison (upward)

abbrev posetObj (P : Type u) [PartialOrder P] := categorification.obj (nerve P)

end Thomason.OmegaAttachmentComparison

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_StandardComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Standard Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains
open CategoryTheory DirectedComplex

def complexOrderIso {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (e : P ≃o Q) : complex P ≅ complex Q where
  hom := complexMap (e : P →o Q)
  inv := complexMap (e.symm : Q →o P)
  hom_inv_id := by
    change Hom.comp (complexMap (e : P →o Q)) (complexMap (e.symm : Q →o P)) = _
    rw [← complexMap_comp]
    have he : (e.symm : Q →o P).comp (e : P →o Q) = OrderHom.id := by
      ext x
      exact e.symm_apply_apply x
    rw [he, complexMap_id]
    rfl
  inv_hom_id := by
    change Hom.comp (complexMap (e.symm : Q →o P)) (complexMap (e : P →o Q)) = _
    rw [← complexMap_comp]
    have he : (e : P →o Q).comp (e.symm : Q →o P) = OrderHom.id := by
      ext x
      exact e.apply_symm_apply x
    rw [he, complexMap_id]
    rfl

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains
open CategoryTheory DirectedComplex

def complexFinIso (P : Type u) [LinearOrder P] [Fintype P]
    {k : ℕ} (h : Fintype.card P = k) :
    complex (ULift.{u} (Fin k)) ≅ complex P :=
  complexOrderIso (ULift.orderIso.trans (Fintype.orderIsoFinOfCardEq P h))

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PrismBasis
attribute [-instance] _root_.OAI.Thomason.NormalizedChains.Prism.Word.finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prism Basis. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.Prism
open DirectedComplex DirectedComplex.Table

namespace Word
variable {N : ℕ}

lemma dim_eq_of_coefficient {p : ℕ} (x : (complex (Fin (N+1))).Chain p)
    (w : Word N) (hw : x.val w.val ≠ 0) : w.dim = p := by
  have h := (mem_grade_iff (p+1) x.val).mp x.property w.val hw
  simp only [dim,h,Nat.add_sub_cancel]

end Word

end Thomason.NormalizedChains.Prism

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_FiniteGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Gluing. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains
open DirectedComplex

lemma complexMap_orderIso_inverse {P : Type u} {Q : Type v}
    [PartialOrder P] [PartialOrder Q] (e : P ≃o Q) :
    Hom.comp (complexMap (e : P →o Q)) (complexMap (e.symm : Q →o P)) = Hom.id (complex P) := by
  rw [← complexMap_comp]
  have he : (e.symm : Q →o P).comp (e : P →o Q) = OrderHom.id := by
    ext x; exact e.symm_apply_apply x
  rw [he,complexMap_id]

end Thomason.NormalizedChains

end

end OAI
end


