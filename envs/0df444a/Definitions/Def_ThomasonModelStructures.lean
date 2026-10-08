-- Prove2me | Definitions.Def_ThomasonModelStructures
-- name    : ThomasonModelStructures
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:29.338732+00:00
-- url     : https://prove2.me/theorems/b549034d-05f2-447a-8a28-d9fa45009edc
-- statement:
--   This file builds the machinery for the Thomason model structures on strict ω-categories and defines the proposition that they are exact Quillen-equivalent model endpoints of simplicial sets. An OmegaCategory is a type of cells with, for each natural number k, source and target operations satisfying the globular identities, a partially defined k-composition comp(k,x,y) when target k x = source k y, compatibility of sources and targets with composition, unit, associativity and interchange laws, and the finiteness condition that every cell equals its own k-source for some k. Functors preserve sources, targets and compositions; ω-categories form a category, and NCategory(n) is the full subcategory where every cell equals its own n-source. A DirectedComplex is a chain complex of abelian groups with augmentation to ℤ vanishing on boundaries and a chosen additive submonoid of positive chains in each degree. Its ν-construction takes ‘tables’, which assign to each degree p and Bool a positive chain with boundary row(p+1,b) ↦ row(p,true) − row(p,false), augmentation 1 in degree 0, and vanishing above some bound, and makes them the cells of an ω-category; this is functorial. For a partial order E, NormalizedChains builds a directed complex from strictly increasing lists with the usual alternating boundary, and sending the simplex categories to these complexes then applying ν gives the orientals Δ → OmegaCategory, universe-raised to raisedOrientals. Presentations by generators, dimensions and relations have free cell terms, a validity relation, a quotient ω-category and an evaluation into any ω-category interpreting the generators; these give colimits of ω-categories. Left Kan extension along the orientals defines categorification SSet → OmegaCategory, and the Street nerve sends C to the simplicial set of functors from orientals into C. These form the adjunction categorificationAdjunction. Composing with two subdivisions SSet.sd and two SSet.ex gives thomasonLeft, thomasonRight and thomasonAdjunction. Truncation to n-categories is left adjoint to the inclusion, yielding finite versions of all these functors and adjunctions for each n. Weak homotopy equivalences of spaces are maps bijective on components and on all homotopy groups indexed by Fin(n+1) at every basepoint; simplicial weak equivalences are their pullback along geometric realization, and simplicial fibrations are the right lifting class of Quillen's generating horn inclusions. KanQuillenModel is a model structure on SSet with exactly these weak equivalences and fibrations and monomorphisms as cofibrations. LeftProperFor, RightProperFor, FibrantFor, boundaryImages and hornImages are defined as the usual pushout/pullback properness conditions, fibrancy over a terminal object, and images of boundary and horn inclusions. ExactModelEndpoint for an adjunction L ⊣ R is a model category on the target with weak equivalences and fibrations created by R, cofibrations the left lifting class of the trivial fibrations, the stated generating (trivial) cofibration lifting characterizations, both weak factorization systems, completeness, cocompleteness, local presentability, left and right properness, a left-Quillen condition on monomorphisms, and a Quillen-equivalence criterion for fibrant targets. FullMain is the defined proposition, not an established theorem, asserting that a KanQuillenModel exists, an ExactModelEndpoint exists for the Thomason adjunction, and for every n ≥ 1 one exists for the n-truncated Thomason adjunction. Thomason weak equivalences are morphisms whose image under thomasonRight, or its finite analogue, is a simplicial weak equivalence.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThomasonModelStructures.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThomasonModelStructures.lean; bytes 16..135763
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

/-! Definitions for the Thomason model structures and their Street-nerve detection statement. -/

noncomputable section
universe u v w

section
namespace OAI.Thomason


structure OmegaCategory where
  Cell : Type u
  source : ℕ → Cell → Cell
  target : ℕ → Cell → Cell
  source_source (i j : ℕ) (x : Cell) : source i (source j x) = source (min i j) x
  target_target (i j : ℕ) (x : Cell) : target i (target j x) = target (min i j) x
  source_target (i j : ℕ) (x : Cell) :
    source i (target j x) = if i < j then source i x else target j x
  target_source (i j : ℕ) (x : Cell) :
    target i (source j x) = if i < j then target i x else source j x
  comp (k : ℕ) (x y : Cell) : target k x = source k y → Cell
  source_comp_le (i k : ℕ) (hik : i ≤ k) (x y : Cell)
      (h : target k x = source k y) : source i (comp k x y h) = source i x
  target_comp_le (i k : ℕ) (hik : i ≤ k) (x y : Cell)
      (h : target k x = source k y) : target i (comp k x y h) = target i y
  source_comp_gt (i k : ℕ) (hki : k < i) (x y : Cell)
      (h : target k x = source k y)
      (hs : target k (source i x) = source k (source i y)) :
    source i (comp k x y h) = comp k (source i x) (source i y) hs
  target_comp_gt (i k : ℕ) (hki : k < i) (x y : Cell)
      (h : target k x = source k y)
      (ht : target k (target i x) = source k (target i y)) :
    target i (comp k x y h) = comp k (target i x) (target i y) ht
  unit_left (k : ℕ) (x : Cell) (h : target k (source k x) = source k x) :
    comp k (source k x) x h = x
  unit_right (k : ℕ) (x : Cell) (h : target k x = source k (target k x)) :
    comp k x (target k x) h = x
  assoc (k : ℕ) (x y z : Cell)
      (hxy : target k x = source k y) (hyz : target k y = source k z)
      (hxy_z : target k (comp k x y hxy) = source k z)
      (hx_yz : target k x = source k (comp k y z hyz)) :
    comp k (comp k x y hxy) z hxy_z = comp k x (comp k y z hyz) hx_yz
  interchange (k l : ℕ) (hkl : k < l) (a b c d : Cell)
      (hab : target l a = source l b) (hcd : target l c = source l d)
      (hac : target k a = source k c) (hbd : target k b = source k d)
      (hab_cd : target k (comp l a b hab) = source k (comp l c d hcd))
      (hac_bd : target l (comp k a c hac) = source l (comp k b d hbd)) :
    comp k (comp l a b hab) (comp l c d hcd) hab_cd =
      comp l (comp k a c hac) (comp k b d hbd) hac_bd
  finite_dimension (x : Cell) : ∃ k, source k x = x


end OAI.Thomason
end

section
namespace OAI.Thomason.OmegaCategory
variable (C : OmegaCategory.{u})

@[ext]
structure Functor (C : OAI.Thomason.OmegaCategory.{u}) (D : OAI.Thomason.OmegaCategory.{v}) where
  map : C.Cell → D.Cell
  map_source (k : ℕ) (x : C.Cell) : map (C.source k x) = D.source k (map x)
  map_target (k : ℕ) (x : C.Cell) : map (C.target k x) = D.target k (map x)
  map_comp (k : ℕ) (x y : C.Cell) (h : C.target k x = C.source k y)
      (h' : D.target k (map x) = D.source k (map y)) :
    map (C.comp k x y h) = D.comp k (map x) (map y) h'


end OAI.Thomason.OmegaCategory
end

section
namespace OAI.Thomason.OmegaCategory.Functor
variable (C : OmegaCategory.{u})
variable {C : OmegaCategory.{u}} {D : OmegaCategory.{v}} {B : OmegaCategory.{w}}

noncomputable def id (C : OAI.Thomason.OmegaCategory.{u}) : OAI.Thomason.OmegaCategory.Functor C C where
  map x := x
  map_source _ _ := rfl
  map_target _ _ := rfl
  map_comp _ _ _ _ _ := rfl

noncomputable def comp (F : OAI.Thomason.OmegaCategory.Functor C D) (G : OAI.Thomason.OmegaCategory.Functor D B) : OAI.Thomason.OmegaCategory.Functor C B := by
  classical
  have proof_map_composable_0 {C : OAI.Thomason.OmegaCategory.{u}} {D : OAI.Thomason.OmegaCategory.{v}}  (F : OAI.Thomason.OmegaCategory.Functor C D) {k : ℕ} {x y : C.Cell}
      (h : C.target k x = C.source k y) :
      D.target k (F.map x) = D.source k (F.map y) := by
    rw [← F.map_target, ← F.map_source, h]
  exact {
    map x := G.map (F.map x)
    map_source k x := by rw [F.map_source, G.map_source]
    map_target k x := by rw [F.map_target, G.map_target]
    map_comp k x y h h' := by
      rw [F.map_comp k x y h (proof_map_composable_0 F h), G.map_comp]
  }


end OAI.Thomason.OmegaCategory.Functor
end

section
namespace OAI.Thomason.OmegaCategory
variable (C : OmegaCategory.{u})

noncomputable instance : CategoryTheory.Category OAI.Thomason.OmegaCategory.{u} where
  Hom C D := OAI.Thomason.OmegaCategory.Functor C D
  id := OAI.Thomason.OmegaCategory.Functor.id
  comp := OAI.Thomason.OmegaCategory.Functor.comp

noncomputable def IsTruncated (n : ℕ) : Prop := ∀ x : C.Cell, C.source n x = x

noncomputable def NCategory (n : ℕ) := {C : OAI.Thomason.OmegaCategory.{u} // C.IsTruncated n}

noncomputable instance (n : ℕ) : CategoryTheory.Category (OAI.Thomason.OmegaCategory.NCategory.{u} n) where
  Hom C D := OAI.Thomason.OmegaCategory.Functor C.val D.val
  id C := OAI.Thomason.OmegaCategory.Functor.id C.val
  comp := OAI.Thomason.OmegaCategory.Functor.comp


end OAI.Thomason.OmegaCategory
end

section
namespace OAI.Thomason


structure DirectedComplex where
  Chain : ℕ → Type u
  group : ∀ p, AddCommGroup (Chain p)
  d : (p : ℕ) → Chain (p+1) →+ Chain p
  d_d (p : ℕ) (x : Chain (p+2)) : d p (d (p+1) x) = 0
  augmentation : Chain 0 →+ ℤ
  augmentation_d (x : Chain 1) : augmentation (d 0 x) = 0
  positive : (p : ℕ) → AddSubmonoid (Chain p)

end OAI.Thomason
end

attribute [instance] OAI.Thomason.DirectedComplex.group

section
namespace OAI.Thomason.DirectedComplex


@[ext]
structure Hom (K : OAI.Thomason.DirectedComplex.{u}) (L : OAI.Thomason.DirectedComplex.{v}) where
  map (p : ℕ) : K.Chain p →+ L.Chain p
  map_d (p : ℕ) (x : K.Chain (p+1)) : map p (K.d p x) = L.d p (map (p+1) x)
  map_augmentation (x : K.Chain 0) : L.augmentation (map 0 x) = K.augmentation x
  map_positive (p : ℕ) (x : K.Chain p) : x ∈ K.positive p → map p x ∈ L.positive p


end OAI.Thomason.DirectedComplex
end

section
namespace OAI.Thomason.DirectedComplex.Hom
variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {M : DirectedComplex.{w}}

noncomputable def id (K : OAI.Thomason.DirectedComplex.{u}) : OAI.Thomason.DirectedComplex.Hom K K where
  map _ := AddMonoidHom.id _
  map_d _ _ := rfl
  map_augmentation _ := rfl
  map_positive _ _ h := h

noncomputable def comp (f : OAI.Thomason.DirectedComplex.Hom K L) (g : OAI.Thomason.DirectedComplex.Hom L M) : OAI.Thomason.DirectedComplex.Hom K M where
  map p := (g.map p).comp (f.map p)
  map_d p x := by simp only [AddMonoidHom.comp_apply, f.map_d, g.map_d]
  map_augmentation x := by simp only [AddMonoidHom.comp_apply,
    g.map_augmentation, f.map_augmentation]
  map_positive p x hx := g.map_positive p _ (f.map_positive p x hx)


end OAI.Thomason.DirectedComplex.Hom
end

section
namespace OAI.Thomason.DirectedComplex


noncomputable instance : CategoryTheory.Category OAI.Thomason.DirectedComplex.{u} where
  Hom := OAI.Thomason.DirectedComplex.Hom
  id := OAI.Thomason.DirectedComplex.Hom.id
  comp := OAI.Thomason.DirectedComplex.Hom.comp

@[ext]
structure Table (K : OAI.Thomason.DirectedComplex.{u}) where
  row : (p : ℕ) → Bool → K.Chain p
  positive (p : ℕ) (b : Bool) : row p b ∈ K.positive p
  boundary (p : ℕ) (b : Bool) :
    K.d p (row (p+1) b) = row p true - row p false
  augmentation (b : Bool) : K.augmentation (row 0 b) = 1
  bounded : ∃ k, ∀ p, k < p → ∀ b, row p b = 0


end OAI.Thomason.DirectedComplex
end

section
namespace OAI.Thomason.DirectedComplex.Table
variable {K : DirectedComplex.{u}}

noncomputable def truncate (k : ℕ) (e : Bool) (x : OAI.Thomason.DirectedComplex.Table K) : OAI.Thomason.DirectedComplex.Table K where
  row p b := if p < k then x.row p b else if p = k then x.row p e else 0
  positive p b := by
    split_ifs <;> first | exact x.positive _ _ | exact (K.positive _).zero_mem
  boundary p b := by
    by_cases hp : p < k
    · by_cases hp' : p+1 < k
      · simp only [hp, hp', ite_eq_left]
        exact x.boundary p b
      · have he : p+1 = k := by omega
        simp only [ite_eq_left hp, ite_eq_right hp', ite_eq_left he]
        exact x.boundary p e
    · by_cases he : p = k
      · have hp' : ¬p+1 < k := by omega
        have he' : ¬p+1 = k := by omega
        simp only [ite_eq_right hp, ite_eq_right hp', ite_eq_right he', ite_eq_left he, map_zero, sub_self]
      · have hp' : ¬p+1 < k := by omega
        have he' : ¬p+1 = k := by omega
        simp only [hp, hp', he', he, ite_false, map_zero, sub_self]
  augmentation b := by
    by_cases hk : k = 0
    · subst k
      simpa using x.augmentation e
    · have hk' : 0 < k := Nat.pos_of_ne_zero hk
      simpa only [hk', ite_eq_left] using x.augmentation b
  bounded := by
    refine ⟨k, ?_⟩
    intro p hp b
    simp only [show ¬p < k by omega, show ¬p = k by omega, ite_false]

noncomputable def comp (k : ℕ) (x y : OAI.Thomason.DirectedComplex.Table K)
    (h : OAI.Thomason.DirectedComplex.Table.truncate k true x = OAI.Thomason.DirectedComplex.Table.truncate k false y) : OAI.Thomason.DirectedComplex.Table K := by
  classical
  have proof_truncate_row_3 {K : OAI.Thomason.DirectedComplex.{u}}  (k : ℕ) (e : Bool) (x : OAI.Thomason.DirectedComplex.Table K) (p : ℕ) (b : Bool) :
      (OAI.Thomason.DirectedComplex.Table.truncate k e x).row p b =
        if p < k then x.row p b else if p = k then x.row p e else 0 := rfl
  have proof_lower_rows_eq_1 {K : OAI.Thomason.DirectedComplex.{u}}  {k : ℕ} {x y : OAI.Thomason.DirectedComplex.Table K}
      (h : OAI.Thomason.DirectedComplex.Table.truncate k true x = OAI.Thomason.DirectedComplex.Table.truncate k false y) {p : ℕ} (hp : p < k) (b : Bool) :
      x.row p b = y.row p b := by
    have hr := congrArg (fun z : OAI.Thomason.DirectedComplex.Table K => z.row p b) h
    simpa only [OAI.Thomason.DirectedComplex.Table.truncate, hp, ite_eq_left] using hr
  have proof_matching_row_eq_2 {K : OAI.Thomason.DirectedComplex.{u}}  {k : ℕ} {x y : OAI.Thomason.DirectedComplex.Table K}
      (h : OAI.Thomason.DirectedComplex.Table.truncate k true x = OAI.Thomason.DirectedComplex.Table.truncate k false y) : x.row k true = y.row k false := by
    have hr := congrArg (fun z : OAI.Thomason.DirectedComplex.Table K => z.row k false) h
    simpa [OAI.Thomason.DirectedComplex.Table.truncate] using hr
  exact {
    row p b := if p < k then x.row p b else if p = k then
      (if b then y.row p true else x.row p false) else x.row p b + y.row p b
    positive p b := by
      split_ifs <;> first
        | exact x.positive _ _
        | exact y.positive _ _
        | exact (K.positive _).add_mem (x.positive _ _) (y.positive _ _)
    boundary p b := by
      by_cases hp : p < k
      · by_cases hp' : p+1 < k
        · simp only [ite_eq_left hp, ite_eq_left hp']
          exact x.boundary p b
        · have he : p+1 = k := by omega
          simp only [ite_eq_left hp, ite_eq_right hp', ite_eq_left he]
          cases b with
          | false => exact x.boundary p false
          | true =>
            change K.d p (y.row (p+1) true) = x.row p true - x.row p false
            rw [y.boundary, proof_lower_rows_eq_1 h hp true, proof_lower_rows_eq_1 h hp false]
      · by_cases he : p = k
        · subst p
          have hp' : ¬k+1 < k := by omega
          have he' : ¬k+1 = k := by omega
          simp only [ite_eq_right (Nat.lt_irrefl k), ite_eq_right hp', ite_eq_right he',
            ↓reduceIte, map_add, x.boundary, y.boundary]
          rw [proof_matching_row_eq_2 h]
          abel_nf
          exact add_comm _ _
        · have hp' : ¬p+1 < k := by omega
          have he' : ¬p+1 = k := by omega
          simp only [ite_eq_right hp, ite_eq_right hp', ite_eq_right he', ite_eq_right he, map_add,
            x.boundary, y.boundary]
          abel
    augmentation b := by
      by_cases hk : 0 < k
      · simp only [ite_eq_left hk]
        exact x.augmentation b
      · have he : 0 = k := by omega
        simp only [ite_eq_right hk, ite_eq_left he]
        cases b <;> first | exact x.augmentation _ | exact y.augmentation _
    bounded := by
      obtain ⟨nx, hx⟩ := x.bounded
      obtain ⟨ny, hy⟩ := y.bounded
      refine ⟨max nx ny, ?_⟩
      intro p hp b
      have hx' := hx p (lt_of_le_of_lt (le_max_left _ _) hp)
      have hy' := hy p (lt_of_le_of_lt (le_max_right _ _) hp)
      split_ifs <;> simp only [hx', hy', zero_add]
  }


end OAI.Thomason.DirectedComplex.Table
end

section
namespace OAI.Thomason.DirectedComplex


noncomputable def nu (K : OAI.Thomason.DirectedComplex.{u}) : OAI.Thomason.OmegaCategory.{u} := by
  classical
  have proof_truncate_row_3 {K : OAI.Thomason.DirectedComplex.{u}}  (k : ℕ) (e : Bool) (x : OAI.Thomason.DirectedComplex.Table K) (p : ℕ) (b : Bool) :
      (OAI.Thomason.DirectedComplex.Table.truncate k e x).row p b =
        if p < k then x.row p b else if p = k then x.row p e else 0 := rfl
  have proof_truncate_truncate_5 {K : OAI.Thomason.DirectedComplex.{u}}  (i j : ℕ) (e f : Bool) (x : OAI.Thomason.DirectedComplex.Table K) :
      OAI.Thomason.DirectedComplex.Table.truncate i e (OAI.Thomason.DirectedComplex.Table.truncate j f x) =
        if i < j then OAI.Thomason.DirectedComplex.Table.truncate i e x else OAI.Thomason.DirectedComplex.Table.truncate j f x := by
    ext p b
    by_cases hij : i < j
    · simp only [hij, ite_eq_left, OAI.Thomason.DirectedComplex.Table.truncate]
      by_cases hpi : p < i
      · have hpj : p < j := lt_trans hpi hij
        simp [hpi, hpj]
      · by_cases hpe : p = i
        · subst p
          simp [hij]
        · simp [hpi, hpe]
    · simp only [hij, ite_false, OAI.Thomason.DirectedComplex.Table.truncate]
      by_cases hpj : p < j
      · have hpi : p < i := by omega
        simp [hpj, hpi]
      · by_cases hpje : p = j
        · subst p
          by_cases hji : j < i
          · simp [hji]
          · have hi : i = j := by omega
            subst i
            simp []
        · by_cases hpi : p < i
          · simp [hpi, hpj, hpje]
          · by_cases hpie : p = i
            · subst p
              simp [hij]
            · simp [hpi, hpie, hpj, hpje]
  have proof_truncate_truncate_same_4 {K : OAI.Thomason.DirectedComplex.{u}}  (i j : ℕ) (e : Bool) (x : OAI.Thomason.DirectedComplex.Table K) :
      OAI.Thomason.DirectedComplex.Table.truncate i e (OAI.Thomason.DirectedComplex.Table.truncate j e x) = OAI.Thomason.DirectedComplex.Table.truncate (min i j) e x := by
    rw [proof_truncate_truncate_5]
    split_ifs with h
    · rw [min_eq_left (le_of_lt h)]
    · rw [min_eq_right (le_of_not_gt h)]
  have proof_comp_row_14 {K : OAI.Thomason.DirectedComplex.{u}}  (k : ℕ) (x y : OAI.Thomason.DirectedComplex.Table K)
      (h : OAI.Thomason.DirectedComplex.Table.truncate k true x = OAI.Thomason.DirectedComplex.Table.truncate k false y) (p : ℕ) (b : Bool) :
      (OAI.Thomason.DirectedComplex.Table.comp k x y h).row p b = if p < k then x.row p b else if p = k then
        (if b then y.row p true else x.row p false) else x.row p b + y.row p b := rfl
  have proof_source_comp_le_6 {K : OAI.Thomason.DirectedComplex.{u}}  (i k : ℕ) (hik : i ≤ k) (x y : OAI.Thomason.DirectedComplex.Table K)
      (h : OAI.Thomason.DirectedComplex.Table.truncate k true x = OAI.Thomason.DirectedComplex.Table.truncate k false y) :
      OAI.Thomason.DirectedComplex.Table.truncate i false (OAI.Thomason.DirectedComplex.Table.comp k x y h) = OAI.Thomason.DirectedComplex.Table.truncate i false x := by
    ext p b
    by_cases hpi : p < i
    · have hpk : p < k := lt_of_lt_of_le hpi hik
      simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp, hpi, hpk]
    · by_cases hpe : p = i
      · subst p
        by_cases hik' : i < k
        · simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp, hik']
        · have he : i = k := by omega
          subst i
          simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp]
      · simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp, hpi, hpe]
  have proof_lower_rows_eq_1 {K : OAI.Thomason.DirectedComplex.{u}}  {k : ℕ} {x y : OAI.Thomason.DirectedComplex.Table K}
      (h : OAI.Thomason.DirectedComplex.Table.truncate k true x = OAI.Thomason.DirectedComplex.Table.truncate k false y) {p : ℕ} (hp : p < k) (b : Bool) :
      x.row p b = y.row p b := by
    have hr := congrArg (fun z : OAI.Thomason.DirectedComplex.Table K => z.row p b) h
    simpa only [OAI.Thomason.DirectedComplex.Table.truncate, hp, ite_eq_left] using hr
  have proof_target_comp_le_7 {K : OAI.Thomason.DirectedComplex.{u}}  (i k : ℕ) (hik : i ≤ k) (x y : OAI.Thomason.DirectedComplex.Table K)
      (h : OAI.Thomason.DirectedComplex.Table.truncate k true x = OAI.Thomason.DirectedComplex.Table.truncate k false y) :
      OAI.Thomason.DirectedComplex.Table.truncate i true (OAI.Thomason.DirectedComplex.Table.comp k x y h) = OAI.Thomason.DirectedComplex.Table.truncate i true y := by
    ext p b
    by_cases hpi : p < i
    · have hpk : p < k := lt_of_lt_of_le hpi hik
      simp only [OAI.Thomason.DirectedComplex.Table.truncate, ite_eq_left hpi, OAI.Thomason.DirectedComplex.Table.comp, ite_eq_left hpk]
      exact proof_lower_rows_eq_1 h hpk b
    · by_cases hpe : p = i
      · subst p
        by_cases hik' : i < k
        · simpa [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp, hik'] using proof_lower_rows_eq_1 h hik' true
        · have he : i = k := by omega
          subst i
          simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp]
      · simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp, hpi, hpe]
  have proof_truncate_comp_gt_8 {K : OAI.Thomason.DirectedComplex.{u}}  (i k : ℕ) (hki : k < i) (e : Bool) (x y : OAI.Thomason.DirectedComplex.Table K)
      (h : OAI.Thomason.DirectedComplex.Table.truncate k true x = OAI.Thomason.DirectedComplex.Table.truncate k false y)
      (h' : OAI.Thomason.DirectedComplex.Table.truncate k true (OAI.Thomason.DirectedComplex.Table.truncate i e x) = OAI.Thomason.DirectedComplex.Table.truncate k false (OAI.Thomason.DirectedComplex.Table.truncate i e y)) :
      OAI.Thomason.DirectedComplex.Table.truncate i e (OAI.Thomason.DirectedComplex.Table.comp k x y h) = OAI.Thomason.DirectedComplex.Table.comp k (OAI.Thomason.DirectedComplex.Table.truncate i e x) (OAI.Thomason.DirectedComplex.Table.truncate i e y) h' := by
    ext p b
    by_cases hpk : p < k
    · have hpi : p < i := lt_trans hpk hki
      simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp, hpk, hpi]
    · by_cases hpe : p = k
      · subst p
        simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp, hki]
      · by_cases hpi : p < i
        · simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp, hpk, hpe, hpi]
        · by_cases hpie : p = i
          · subst p
            have hik : ¬i < k := by omega
            have hie : ¬i = k := by omega
            simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp, hik, hie]
          · simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp, hpk, hpe, hpi, hpie]
  have proof_unit_left_9 {K : OAI.Thomason.DirectedComplex.{u}}  (k : ℕ) (x : OAI.Thomason.DirectedComplex.Table K)
      (h : OAI.Thomason.DirectedComplex.Table.truncate k true (OAI.Thomason.DirectedComplex.Table.truncate k false x) = OAI.Thomason.DirectedComplex.Table.truncate k false x) :
      OAI.Thomason.DirectedComplex.Table.comp k (OAI.Thomason.DirectedComplex.Table.truncate k false x) x h = x := by
    ext p b
    by_cases hp : p < k
    · simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp, hp]
    · by_cases he : p = k
      · subst p
        cases b <;> simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp]
      · simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp, hp, he]
  have proof_unit_right_10 {K : OAI.Thomason.DirectedComplex.{u}}  (k : ℕ) (x : OAI.Thomason.DirectedComplex.Table K)
      (h : OAI.Thomason.DirectedComplex.Table.truncate k true x = OAI.Thomason.DirectedComplex.Table.truncate k false (OAI.Thomason.DirectedComplex.Table.truncate k true x)) :
      OAI.Thomason.DirectedComplex.Table.comp k x (OAI.Thomason.DirectedComplex.Table.truncate k true x) h = x := by
    ext p b
    by_cases hp : p < k
    · simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp, hp]
    · by_cases he : p = k
      · subst p
        cases b <;> simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp]
      · simp [OAI.Thomason.DirectedComplex.Table.truncate, OAI.Thomason.DirectedComplex.Table.comp, hp, he]
  have proof_assoc_11 {K : OAI.Thomason.DirectedComplex.{u}}  (k : ℕ) (x y z : OAI.Thomason.DirectedComplex.Table K)
      (hxy : OAI.Thomason.DirectedComplex.Table.truncate k true x = OAI.Thomason.DirectedComplex.Table.truncate k false y)
      (hyz : OAI.Thomason.DirectedComplex.Table.truncate k true y = OAI.Thomason.DirectedComplex.Table.truncate k false z)
      (hxy_z : OAI.Thomason.DirectedComplex.Table.truncate k true (OAI.Thomason.DirectedComplex.Table.comp k x y hxy) = OAI.Thomason.DirectedComplex.Table.truncate k false z)
      (hx_yz : OAI.Thomason.DirectedComplex.Table.truncate k true x = OAI.Thomason.DirectedComplex.Table.truncate k false (OAI.Thomason.DirectedComplex.Table.comp k y z hyz)) :
      OAI.Thomason.DirectedComplex.Table.comp k (OAI.Thomason.DirectedComplex.Table.comp k x y hxy) z hxy_z = OAI.Thomason.DirectedComplex.Table.comp k x (OAI.Thomason.DirectedComplex.Table.comp k y z hyz) hx_yz := by
    ext p b
    by_cases hp : p < k
    · simp [OAI.Thomason.DirectedComplex.Table.comp, hp]
    · by_cases he : p = k
      · subst p
        cases b <;> simp [OAI.Thomason.DirectedComplex.Table.comp]
      · simp [OAI.Thomason.DirectedComplex.Table.comp, hp, he, add_assoc]
  have proof_interchange_12 {K : OAI.Thomason.DirectedComplex.{u}}  (k l : ℕ) (hkl : k < l) (a b c d : OAI.Thomason.DirectedComplex.Table K)
      (hab : OAI.Thomason.DirectedComplex.Table.truncate l true a = OAI.Thomason.DirectedComplex.Table.truncate l false b)
      (hcd : OAI.Thomason.DirectedComplex.Table.truncate l true c = OAI.Thomason.DirectedComplex.Table.truncate l false d)
      (hac : OAI.Thomason.DirectedComplex.Table.truncate k true a = OAI.Thomason.DirectedComplex.Table.truncate k false c)
      (hbd : OAI.Thomason.DirectedComplex.Table.truncate k true b = OAI.Thomason.DirectedComplex.Table.truncate k false d)
      (hab_cd : OAI.Thomason.DirectedComplex.Table.truncate k true (OAI.Thomason.DirectedComplex.Table.comp l a b hab) = OAI.Thomason.DirectedComplex.Table.truncate k false (OAI.Thomason.DirectedComplex.Table.comp l c d hcd))
      (hac_bd : OAI.Thomason.DirectedComplex.Table.truncate l true (OAI.Thomason.DirectedComplex.Table.comp k a c hac) = OAI.Thomason.DirectedComplex.Table.truncate l false (OAI.Thomason.DirectedComplex.Table.comp k b d hbd)) :
      OAI.Thomason.DirectedComplex.Table.comp k (OAI.Thomason.DirectedComplex.Table.comp l a b hab) (OAI.Thomason.DirectedComplex.Table.comp l c d hcd) hab_cd =
        OAI.Thomason.DirectedComplex.Table.comp l (OAI.Thomason.DirectedComplex.Table.comp k a c hac) (OAI.Thomason.DirectedComplex.Table.comp k b d hbd) hac_bd := by
    ext p e
    by_cases hpk : p < k
    · have hpl : p < l := lt_trans hpk hkl
      simp [OAI.Thomason.DirectedComplex.Table.comp, hpk, hpl]
    · by_cases hpe : p = k
      · subst p
        cases e <;> simp [OAI.Thomason.DirectedComplex.Table.comp, hkl]
      · by_cases hpl : p < l
        · simp [OAI.Thomason.DirectedComplex.Table.comp, hpk, hpe, hpl]
        · by_cases hple : p = l
          · subst p
            have hlk : ¬l < k := by omega
            have hlke : ¬l = k := by omega
            cases e <;> simp [OAI.Thomason.DirectedComplex.Table.comp, hlk, hlke]
          · simp only [OAI.Thomason.DirectedComplex.Table.comp, ite_eq_right hpk, ite_eq_right hpe, ite_eq_right hpl, ite_eq_right hple]
            abel
  have proof_finite_dimension_13 {K : OAI.Thomason.DirectedComplex.{u}}  (x : OAI.Thomason.DirectedComplex.Table K) : ∃ k, OAI.Thomason.DirectedComplex.Table.truncate k false x = x := by
    obtain ⟨k, hk⟩ := x.bounded
    have ht : x.row k true = x.row k false := by
      have hb := x.boundary k false
      rw [hk (k+1) (by omega) false, map_zero] at hb
      exact sub_eq_zero.mp hb.symm
    refine ⟨k, ?_⟩
    ext p b
    by_cases hp : p < k
    · simp [OAI.Thomason.DirectedComplex.Table.truncate, hp]
    · by_cases he : p = k
      · subst p
        cases b <;> simp [OAI.Thomason.DirectedComplex.Table.truncate, ht]
      · have hkp : k < p := by omega
        simp [OAI.Thomason.DirectedComplex.Table.truncate, hp, he, hk p hkp b]
  exact {
    Cell := OAI.Thomason.DirectedComplex.Table K
    source k := OAI.Thomason.DirectedComplex.Table.truncate k false
    target k := OAI.Thomason.DirectedComplex.Table.truncate k true
    source_source i j x := proof_truncate_truncate_same_4 i j false x
    target_target i j x := proof_truncate_truncate_same_4 i j true x
    source_target i j x := proof_truncate_truncate_5 i j false true x
    target_source i j x := proof_truncate_truncate_5 i j true false x
    comp := OAI.Thomason.DirectedComplex.Table.comp
    source_comp_le := proof_source_comp_le_6
    target_comp_le := proof_target_comp_le_7
    source_comp_gt i k hki x y h hs := proof_truncate_comp_gt_8 i k hki false x y h hs
    target_comp_gt i k hki x y h ht := proof_truncate_comp_gt_8 i k hki true x y h ht
    unit_left := proof_unit_left_9
    unit_right := proof_unit_right_10
    assoc := proof_assoc_11
    interchange := proof_interchange_12
    finite_dimension := proof_finite_dimension_13
  }


end OAI.Thomason.DirectedComplex
end

section
namespace OAI.Thomason.DirectedComplex.Hom
variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {M : DirectedComplex.{w}}

noncomputable def table (f : OAI.Thomason.DirectedComplex.Hom K L) (x : OAI.Thomason.DirectedComplex.Table K) : OAI.Thomason.DirectedComplex.Table L where
  row p b := f.map p (x.row p b)
  positive p b := f.map_positive p _ (x.positive p b)
  boundary p b := by rw [← f.map_d, x.boundary, map_sub]
  augmentation b := by rw [f.map_augmentation, x.augmentation]
  bounded := by
    obtain ⟨k, hk⟩ := x.bounded
    refine ⟨k, ?_⟩
    intro p hp b
    rw [hk p hp b, map_zero]

noncomputable def nu (f : OAI.Thomason.DirectedComplex.Hom K L) : OAI.Thomason.OmegaCategory.Functor K.nu L.nu := by
  classical
  have proof_table_row_17 {K : OAI.Thomason.DirectedComplex.{u}} {L : OAI.Thomason.DirectedComplex.{v}}  (f : OAI.Thomason.DirectedComplex.Hom K L) (x : OAI.Thomason.DirectedComplex.Table K) (p : ℕ) (b : Bool) :
      (f.table x).row p b = f.map p (x.row p b) := rfl
  have proof_truncate_row_3 {K : OAI.Thomason.DirectedComplex.{u}}  (k : ℕ) (e : Bool) (x : OAI.Thomason.DirectedComplex.Table K) (p : ℕ) (b : Bool) :
      (OAI.Thomason.DirectedComplex.Table.truncate k e x).row p b =
        if p < k then x.row p b else if p = k then x.row p e else 0 := rfl
  have proof_table_truncate_15 {K : OAI.Thomason.DirectedComplex.{u}} {L : OAI.Thomason.DirectedComplex.{v}}  (f : OAI.Thomason.DirectedComplex.Hom K L) (k : ℕ) (b : Bool) (x : OAI.Thomason.DirectedComplex.Table K) :
      f.table (OAI.Thomason.DirectedComplex.Table.truncate k b x) = OAI.Thomason.DirectedComplex.Table.truncate k b (f.table x) := by
    ext p e
    simp only [OAI.Thomason.DirectedComplex.Hom.table, OAI.Thomason.DirectedComplex.Table.truncate]
    split_ifs <;> simp only [map_zero]
  have proof_comp_row_14 {K : OAI.Thomason.DirectedComplex.{u}}  (k : ℕ) (x y : OAI.Thomason.DirectedComplex.Table K)
      (h : OAI.Thomason.DirectedComplex.Table.truncate k true x = OAI.Thomason.DirectedComplex.Table.truncate k false y) (p : ℕ) (b : Bool) :
      (OAI.Thomason.DirectedComplex.Table.comp k x y h).row p b = if p < k then x.row p b else if p = k then
        (if b then y.row p true else x.row p false) else x.row p b + y.row p b := rfl
  have proof_table_comp_16 {K : OAI.Thomason.DirectedComplex.{u}} {L : OAI.Thomason.DirectedComplex.{v}}  (f : OAI.Thomason.DirectedComplex.Hom K L) (k : ℕ) (x y : OAI.Thomason.DirectedComplex.Table K)
      (h : OAI.Thomason.DirectedComplex.Table.truncate k true x = OAI.Thomason.DirectedComplex.Table.truncate k false y)
      (h' : OAI.Thomason.DirectedComplex.Table.truncate k true (f.table x) = OAI.Thomason.DirectedComplex.Table.truncate k false (f.table y)) :
      f.table (OAI.Thomason.DirectedComplex.Table.comp k x y h) = OAI.Thomason.DirectedComplex.Table.comp k (f.table x) (f.table y) h' := by
    ext p e
    simp only [OAI.Thomason.DirectedComplex.Hom.table, OAI.Thomason.DirectedComplex.Table.comp]
    split_ifs <;> simp only [map_add]
  exact {
    map := f.table
    map_source k x := (proof_table_truncate_15 f k Bool.false x)
    map_target k x := (proof_table_truncate_15 f k Bool.true x)
    map_comp := (proof_table_comp_16 f)
  }


end OAI.Thomason.DirectedComplex.Hom
end

section
namespace OAI.Thomason.DirectedComplex


noncomputable def nuFunctor : CategoryTheory.Functor OAI.Thomason.DirectedComplex.{u} OAI.Thomason.OmegaCategory.{u} where
  obj := OAI.Thomason.DirectedComplex.nu
  map := OAI.Thomason.DirectedComplex.Hom.nu
  map_id K := by
    change OAI.Thomason.DirectedComplex.Hom.nu (OAI.Thomason.DirectedComplex.Hom.id K) = OAI.Thomason.OmegaCategory.Functor.id K.nu
    ext x
    rfl
  map_comp f g := by
    change OAI.Thomason.DirectedComplex.Hom.nu (OAI.Thomason.DirectedComplex.Hom.comp f g) = OAI.Thomason.OmegaCategory.Functor.comp f.nu g.nu
    ext x
    rfl


end OAI.Thomason.DirectedComplex
end

section
namespace OAI.Thomason.NormalizedChains
variable {E : Type u} [PartialOrder E]

noncomputable abbrev Word (E : Type u) [PartialOrder E] :=
  {l : List E // l.Pairwise (· < ·)}

noncomputable abbrev Chains (E : Type u) [PartialOrder E] := OAI.Thomason.NormalizedChains.Word E →₀ ℤ

noncomputable def bracket (l : List E) : OAI.Thomason.NormalizedChains.Chains E := by
  classical
  exact if h : l.Pairwise (· < ·) then Finsupp.single ⟨l, h⟩ 1 else 0

noncomputable def prepend (a : E) : OAI.Thomason.NormalizedChains.Chains E →ₗ[ℤ] OAI.Thomason.NormalizedChains.Chains E :=
  Finsupp.linearCombination ℤ (fun l : OAI.Thomason.NormalizedChains.Word E => OAI.Thomason.NormalizedChains.bracket (a :: l.val))

noncomputable def wordBoundary : List E → OAI.Thomason.NormalizedChains.Chains E
  | [] => 0
  | a :: l => OAI.Thomason.NormalizedChains.bracket l - OAI.Thomason.NormalizedChains.prepend a (wordBoundary l)

noncomputable def boundary : OAI.Thomason.NormalizedChains.Chains E →ₗ[ℤ] OAI.Thomason.NormalizedChains.Chains E :=
  Finsupp.linearCombination ℤ (fun l : OAI.Thomason.NormalizedChains.Word E => OAI.Thomason.NormalizedChains.wordBoundary l.val)


end OAI.Thomason.NormalizedChains
end

section
namespace OAI.Thomason.NormalizedChains
variable {E : Type u} [PartialOrder E]
omit [PartialOrder E]
variable {M : Type v} [AddCommGroup M]

noncomputable def faces (H : List E → M) : List E → M
  | [] => 0
  | a :: l => H l - faces (fun m => H (a :: m)) l


end OAI.Thomason.NormalizedChains
end

section
namespace OAI.Thomason.NormalizedChains
variable {E : Type u} [PartialOrder E]

noncomputable def grade (k : ℕ) : Submodule ℤ (OAI.Thomason.NormalizedChains.Chains E) :=
  Finsupp.supported ℤ ℤ {w : OAI.Thomason.NormalizedChains.Word E | w.val.length = k}

noncomputable def emptyWord : OAI.Thomason.NormalizedChains.Word E := ⟨[], List.Pairwise.nil⟩

noncomputable def emptyCoefficient : OAI.Thomason.NormalizedChains.Chains E →ₗ[ℤ] ℤ := Finsupp.lapply OAI.Thomason.NormalizedChains.emptyWord

noncomputable def Positive (c : OAI.Thomason.NormalizedChains.Chains E) : Prop := ∀ l, 0 ≤ c l

noncomputable def positiveGrade (p : ℕ) : AddSubmonoid (OAI.Thomason.NormalizedChains.grade (E := E) (p+1)) where
  carrier := {c | Positive c.val}
  zero_mem' _ := le_rfl
  add_mem' ha hb w := add_nonneg (ha w) (hb w)

noncomputable def complex (E : Type u) [PartialOrder E] : OAI.Thomason.DirectedComplex.{u} := by
  classical
  have proof_mem_grade_iff_20 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (k : ℕ) (c : OAI.Thomason.NormalizedChains.Chains E) :
      c ∈ OAI.Thomason.NormalizedChains.grade k ↔ ∀ w, c w ≠ 0 → w.val.length = k := by
    simp only [OAI.Thomason.NormalizedChains.grade, Finsupp.mem_supported, Set.subset_def, Finsupp.mem_support_iff,
      Finset.mem_coe, Set.mem_ofPred_eq]
  have proof_linearCombination_mem_grade_21 {E : Type u} [instLocal1 : PartialOrder.{u} E]  {D : Type u} [PartialOrder D]
      (H : OAI.Thomason.NormalizedChains.Word E → OAI.Thomason.NormalizedChains.Chains D) (k j : ℕ)
      (hH : ∀ w, w.val.length = k → H w ∈ OAI.Thomason.NormalizedChains.grade j)
      {c : OAI.Thomason.NormalizedChains.Chains E} (hc : c ∈ OAI.Thomason.NormalizedChains.grade k) :
      Finsupp.linearCombination ℤ H c ∈ OAI.Thomason.NormalizedChains.grade j := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro w hw
    exact Submodule.smul_mem _ _ (hH w ((proof_mem_grade_iff_20 k c).mp hc w
      (Finsupp.mem_support_iff.mp hw)))
  have proof_bracket_of_pairwise_22 {E : Type u} [instLocal1 : PartialOrder.{u} E]  {l : List E} (h : l.Pairwise (· < ·)) :
      OAI.Thomason.NormalizedChains.bracket l = Finsupp.single ⟨l, h⟩ 1 := by
    classical
    simp [OAI.Thomason.NormalizedChains.bracket, h]
  have proof_bracket_of_not_pairwise_23 {E : Type u} [instLocal1 : PartialOrder.{u} E]  {l : List E} (h : ¬l.Pairwise (· < ·)) :
      OAI.Thomason.NormalizedChains.bracket l = 0 := by
    classical
    simp [OAI.Thomason.NormalizedChains.bracket, h]
  have proof_bracket_mem_grade_24 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (l : List E) : OAI.Thomason.NormalizedChains.bracket l ∈ OAI.Thomason.NormalizedChains.grade l.length := by
    classical
    by_cases h : l.Pairwise (· < ·)
    · rw [proof_bracket_of_pairwise_22 h]
      exact Finsupp.single_mem_supported ℤ 1 rfl
    · rw [proof_bracket_of_not_pairwise_23 h]
      exact Submodule.zero_mem _
  have proof_wordBoundary_nil_25 {E : Type u} [instLocal1 : PartialOrder.{u} E]  : OAI.Thomason.NormalizedChains.wordBoundary ([] : List E) = 0 := rfl
  have proof_wordBoundary_cons_26 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (a : E) (l : List E) :
      OAI.Thomason.NormalizedChains.wordBoundary (a :: l) = OAI.Thomason.NormalizedChains.bracket l - OAI.Thomason.NormalizedChains.prepend a (OAI.Thomason.NormalizedChains.wordBoundary l) := rfl
  have proof_prepend_bracket_27 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (a : E) (l : List E) :
      OAI.Thomason.NormalizedChains.prepend a (OAI.Thomason.NormalizedChains.bracket l) = OAI.Thomason.NormalizedChains.bracket (a :: l) := by
    classical
    by_cases h : l.Pairwise (· < ·)
    · rw [proof_bracket_of_pairwise_22 h]
      change Finsupp.linearCombination ℤ (fun l : OAI.Thomason.NormalizedChains.Word E => OAI.Thomason.NormalizedChains.bracket (a :: l.val))
        (Finsupp.single (⟨l, h⟩ : OAI.Thomason.NormalizedChains.Word E) 1) = _
      rw [Finsupp.linearCombination_single]
      simp
    · have h' : ¬(a :: l).Pairwise (· < ·) := fun hw => h hw.tail
      simp [proof_bracket_of_not_pairwise_23 h, proof_bracket_of_not_pairwise_23 h']
  have proof_prepend_mem_grade_28 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (a : E) {k : ℕ} {c : OAI.Thomason.NormalizedChains.Chains E} (hc : c ∈ OAI.Thomason.NormalizedChains.grade k) :
      OAI.Thomason.NormalizedChains.prepend a c ∈ OAI.Thomason.NormalizedChains.grade (k+1) := by
    apply proof_linearCombination_mem_grade_21 _ k (k+1) _ hc
    intro w hw
    simpa only [List.length_cons, hw] using proof_bracket_mem_grade_24 (a :: w.val)
  have proof_wordBoundary_mem_grade_29 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (l : List E) : OAI.Thomason.NormalizedChains.wordBoundary l ∈ OAI.Thomason.NormalizedChains.grade (l.length-1) := by
    induction l with
    | nil => exact Submodule.zero_mem _
    | cons a l ih =>
      cases l with
      | nil => simpa [proof_wordBoundary_nil_25, proof_wordBoundary_cons_26, proof_prepend_bracket_27, OAI.Thomason.NormalizedChains.wordBoundary] using proof_bracket_mem_grade_24 ([] : List E)
      | cons b l =>
        rw [proof_wordBoundary_cons_26]
        apply Submodule.sub_mem
        · simpa [proof_wordBoundary_nil_25, proof_wordBoundary_cons_26, proof_prepend_bracket_27] using proof_bracket_mem_grade_24 (b :: l)
        · simpa [proof_wordBoundary_nil_25, proof_wordBoundary_cons_26, proof_prepend_bracket_27] using proof_prepend_mem_grade_28 a ih
  have proof_boundary_mem_grade_18 {E : Type u} [instLocal1 : PartialOrder.{u} E]  {k : ℕ} {c : OAI.Thomason.NormalizedChains.Chains E} (hc : c ∈ OAI.Thomason.NormalizedChains.grade (k+1)) :
      OAI.Thomason.NormalizedChains.boundary c ∈ OAI.Thomason.NormalizedChains.grade k := by
    apply proof_linearCombination_mem_grade_21 _ (k+1) k _ hc
    intro w hw
    simpa only [hw, Nat.add_sub_cancel] using proof_wordBoundary_mem_grade_29 w.val
  have proof_prepend_prepend_self_30 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (a : E) (c : OAI.Thomason.NormalizedChains.Chains E) : OAI.Thomason.NormalizedChains.prepend a (OAI.Thomason.NormalizedChains.prepend a c) = 0 := by
    classical
    induction c using Finsupp.induction with
    | zero => simp []
    | @single_add l z c _ _ ih =>
      simp only [map_add, ih, add_zero]
      have hz : Finsupp.single l z = z • OAI.Thomason.NormalizedChains.bracket l.val := by
        rw [proof_bracket_of_pairwise_22 l.property]
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hz]
      simp only [map_smul, proof_prepend_bracket_27]
      have h : ¬(a :: a :: l.val).Pairwise (· < ·) := by simp []
      simp [proof_bracket_of_not_pairwise_23 h]
  have proof_wordBoundary_repeated_31 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (a : E) (l : List E) :
      OAI.Thomason.NormalizedChains.wordBoundary (a :: a :: l) = 0 := by
    simp [proof_prepend_bracket_27, OAI.Thomason.NormalizedChains.wordBoundary, map_sub, proof_prepend_prepend_self_30]
  have proof_wordBoundary_eq_zero_of_not_pairwise_32 {E : Type u} [instLocal1 : PartialOrder.{u} E]  {l : List E}
      (h : l.Pairwise (· ≤ ·)) (hn : ¬l.Pairwise (· < ·)) : OAI.Thomason.NormalizedChains.wordBoundary l = 0 := by
    induction l with
    | nil => exact (hn (by simp)).elim
    | cons a l ih =>
      by_cases hl : l.Pairwise (· < ·)
      · cases l with
        | nil => exact (hn (by simp)).elim
        | cons b l =>
          have hab : a ≤ b := (List.pairwise_cons.mp h).1 b (by simp)
          have hab' : ¬a < b := by
            intro hab'
            exact hn (List.Pairwise.cons_cons_of_trans hab' hl)
          have heq : a = b := (lt_or_eq_of_le hab).resolve_left hab'
          subst b
          exact proof_wordBoundary_repeated_31 a l
      · simp [OAI.Thomason.NormalizedChains.wordBoundary, proof_bracket_of_not_pairwise_23 hl, ih h.tail hl]
  have proof_boundary_bracket_33 {E : Type u} [instLocal1 : PartialOrder.{u} E]  {l : List E} (h : l.Pairwise (· ≤ ·)) :
      OAI.Thomason.NormalizedChains.boundary (OAI.Thomason.NormalizedChains.bracket l) = OAI.Thomason.NormalizedChains.wordBoundary l := by
    classical
    by_cases hs : l.Pairwise (· < ·)
    · rw [proof_bracket_of_pairwise_22 hs]
      change Finsupp.linearCombination ℤ (fun l : OAI.Thomason.NormalizedChains.Word E => OAI.Thomason.NormalizedChains.wordBoundary l.val)
        (Finsupp.single (⟨l, hs⟩ : OAI.Thomason.NormalizedChains.Word E) 1) = _
      rw [Finsupp.linearCombination_single]
      simp []
    · simp [proof_bracket_of_not_pairwise_23 hs, proof_wordBoundary_eq_zero_of_not_pairwise_32 h hs]
  have proof_faces_nil_34 {E : Type u} {M : Type u} [instLocal2 : AddCommGroup.{u} M]  (H : List E → M) : OAI.Thomason.NormalizedChains.faces H [] = 0 := rfl
  have proof_faces_cons_35 {E : Type u} {M : Type u} [instLocal2 : AddCommGroup.{u} M]  (H : List E → M) (a : E) (l : List E) :
      OAI.Thomason.NormalizedChains.faces H (a :: l) = H l - OAI.Thomason.NormalizedChains.faces (fun m => H (a :: m)) l := rfl
  have proof_faces_hom_36 {E : Type u} {M : Type u} [instLocal2 : AddCommGroup.{u} M]  {M' : Type u} [AddCommGroup M'] (q : M →+ M')
      (H : List E → M) (l : List E) :
      q (OAI.Thomason.NormalizedChains.faces H l) = OAI.Thomason.NormalizedChains.faces (fun m => q (H m)) l := by
    induction l generalizing H with
    | nil => simp only [OAI.Thomason.NormalizedChains.faces, map_zero]
    | cons a l ih => simp only [OAI.Thomason.NormalizedChains.faces, map_sub, ih]
  have proof_faces_bracket_37 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (l : List E) : OAI.Thomason.NormalizedChains.faces OAI.Thomason.NormalizedChains.bracket l = OAI.Thomason.NormalizedChains.wordBoundary l := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [proof_faces_cons_35, proof_wordBoundary_cons_26]
      have h := proof_faces_hom_36 (OAI.Thomason.NormalizedChains.prepend a).toAddMonoidHom OAI.Thomason.NormalizedChains.bracket l
      simp only [LinearMap.toAddMonoidHom_coe, proof_prepend_bracket_27] at h
      rw [← h, ih]
  have proof_faces_congr_38 {E : Type u} {M : Type u} [instLocal2 : AddCommGroup.{u} M]  {H K : List E → M} {l : List E}
      (h : ∀ m, m.Sublist l → H m = K m) : OAI.Thomason.NormalizedChains.faces H l = OAI.Thomason.NormalizedChains.faces K l := by
    induction l generalizing H K with
    | nil => rfl
    | cons a l ih =>
      rw [proof_faces_cons_35, proof_faces_cons_35, h l (List.sublist_cons_self a l)]
      congr 1
      exact ih (fun m hm => h (a :: m) (List.Sublist.cons_cons a hm))
  have proof_faces_sub_39 {E : Type u} {M : Type u} [instLocal2 : AddCommGroup.{u} M]  (H K : List E → M) (l : List E) :
      OAI.Thomason.NormalizedChains.faces (fun m => H m - K m) l = OAI.Thomason.NormalizedChains.faces H l - OAI.Thomason.NormalizedChains.faces K l := by
    induction l generalizing H K with
    | nil => simp [proof_faces_nil_34]
    | cons a l ih => simp only [proof_faces_cons_35, ih]; abel
  have proof_faces_faces_40 {E : Type u} {M : Type u} [instLocal2 : AddCommGroup.{u} M]  (H : List E → M) (l : List E) :
      OAI.Thomason.NormalizedChains.faces (OAI.Thomason.NormalizedChains.faces H) l = 0 := by
    induction l generalizing H with
    | nil => rfl
    | cons a l ih =>
      simp only [proof_faces_cons_35]
      rw [proof_faces_sub_39, ih]
      simp []
  have proof_boundary_wordBoundary_41 {E : Type u} [instLocal1 : PartialOrder.{u} E]  {l : List E} (h : l.Pairwise (· ≤ ·)) :
      OAI.Thomason.NormalizedChains.boundary (OAI.Thomason.NormalizedChains.wordBoundary l) = 0 := by
    rw [← proof_faces_bracket_37]
    change OAI.Thomason.NormalizedChains.boundary.toAddMonoidHom (OAI.Thomason.NormalizedChains.faces OAI.Thomason.NormalizedChains.bracket l) = 0
    rw [proof_faces_hom_36]
    have hc : OAI.Thomason.NormalizedChains.faces (fun m => OAI.Thomason.NormalizedChains.boundary (OAI.Thomason.NormalizedChains.bracket m)) l = OAI.Thomason.NormalizedChains.faces OAI.Thomason.NormalizedChains.wordBoundary l := by
      apply proof_faces_congr_38
      intro m hm
      exact proof_boundary_bracket_33 (h.sublist hm)
    change OAI.Thomason.NormalizedChains.faces (fun m => OAI.Thomason.NormalizedChains.boundary (OAI.Thomason.NormalizedChains.bracket m)) l = 0
    rw [hc]
    change OAI.Thomason.NormalizedChains.faces (fun m => OAI.Thomason.NormalizedChains.wordBoundary m) l = 0
    simp_rw [← proof_faces_bracket_37]
    exact proof_faces_faces_40 OAI.Thomason.NormalizedChains.bracket l
  have proof_boundary_boundary_19 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (c : OAI.Thomason.NormalizedChains.Chains E) : OAI.Thomason.NormalizedChains.boundary (OAI.Thomason.NormalizedChains.boundary c) = 0 := by
    classical
    induction c using Finsupp.induction with
    | zero => simp []
    | @single_add l z c _ _ ih =>
      simp only [map_add, ih, add_zero]
      have hz : Finsupp.single l z = z • OAI.Thomason.NormalizedChains.bracket l.val := by
        rw [proof_bracket_of_pairwise_22 l.property]
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hz]
      simp only [map_smul]
      rw [proof_boundary_bracket_33 (l.property.imp fun h => le_of_lt h),
        proof_boundary_wordBoundary_41 (l.property.imp fun h => le_of_lt h), smul_zero]
  exact {
    Chain p := OAI.Thomason.NormalizedChains.grade (E := E) (p+1)
    group _ := inferInstance
    d p :=
      { toFun := fun c => ⟨OAI.Thomason.NormalizedChains.boundary c.val, proof_boundary_mem_grade_18 c.property⟩
        map_zero' := Subtype.ext (map_zero _)
        map_add' := fun x y => Subtype.ext (map_add _ x.val y.val) }
    d_d p x := Subtype.ext (proof_boundary_boundary_19 x.val)
    augmentation :=
      { toFun := fun c => OAI.Thomason.NormalizedChains.emptyCoefficient (OAI.Thomason.NormalizedChains.boundary c.val)
        map_zero' := by simp []
        map_add' := by intros; simp [] }
    augmentation_d x := by
      change OAI.Thomason.NormalizedChains.emptyCoefficient (OAI.Thomason.NormalizedChains.boundary (OAI.Thomason.NormalizedChains.boundary x.val)) = 0
      rw [proof_boundary_boundary_19, map_zero]
    positive := OAI.Thomason.NormalizedChains.positiveGrade
  }


end OAI.Thomason.NormalizedChains
end

section
namespace OAI.Thomason.NormalizedChains
variable {E : Type u} [PartialOrder E]
variable {D : Type v} [PartialOrder D] {B : Type w} [PartialOrder B]

noncomputable def map (f : E →o D) : OAI.Thomason.NormalizedChains.Chains E →ₗ[ℤ] OAI.Thomason.NormalizedChains.Chains D :=
  Finsupp.linearCombination ℤ (fun l : OAI.Thomason.NormalizedChains.Word E => OAI.Thomason.NormalizedChains.bracket (l.val.map f))


end OAI.Thomason.NormalizedChains
end

section
namespace OAI.Thomason.NormalizedChains
variable {E : Type u} [PartialOrder E]

noncomputable def complexMap {D : Type v} [PartialOrder D] (f : E →o D) :
    OAI.Thomason.DirectedComplex.Hom (OAI.Thomason.NormalizedChains.complex E) (OAI.Thomason.NormalizedChains.complex D) := by
  classical
  have proof_mem_grade_iff_20 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (k : ℕ) (c : OAI.Thomason.NormalizedChains.Chains E) :
      c ∈ OAI.Thomason.NormalizedChains.grade k ↔ ∀ w, c w ≠ 0 → w.val.length = k := by
    simp only [OAI.Thomason.NormalizedChains.grade, Finsupp.mem_supported, Set.subset_def, Finsupp.mem_support_iff,
      Finset.mem_coe, Set.mem_ofPred_eq]
  have proof_linearCombination_mem_grade_46 {E : Type u} [instLocal1 : PartialOrder.{u} E]  {D : Type v} [PartialOrder D]
      (H : OAI.Thomason.NormalizedChains.Word E → OAI.Thomason.NormalizedChains.Chains D) (k j : ℕ)
      (hH : ∀ w, w.val.length = k → H w ∈ OAI.Thomason.NormalizedChains.grade j)
      {c : OAI.Thomason.NormalizedChains.Chains E} (hc : c ∈ OAI.Thomason.NormalizedChains.grade k) :
      Finsupp.linearCombination ℤ H c ∈ OAI.Thomason.NormalizedChains.grade j := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro w hw
    exact Submodule.smul_mem _ _ (hH w ((proof_mem_grade_iff_20 k c).mp hc w
      (Finsupp.mem_support_iff.mp hw)))
  have proof_bracket_of_pairwise_47 {E : Type v} [instLocal1 : PartialOrder.{v} E]  {l : List E} (h : l.Pairwise (· < ·)) :
      OAI.Thomason.NormalizedChains.bracket l = Finsupp.single ⟨l, h⟩ 1 := by
    classical
    simp [OAI.Thomason.NormalizedChains.bracket, h]
  have proof_bracket_of_not_pairwise_48 {E : Type v} [instLocal1 : PartialOrder.{v} E]  {l : List E} (h : ¬l.Pairwise (· < ·)) :
      OAI.Thomason.NormalizedChains.bracket l = 0 := by
    classical
    simp [OAI.Thomason.NormalizedChains.bracket, h]
  have proof_bracket_mem_grade_49 {E : Type v} [instLocal1 : PartialOrder.{v} E]  (l : List E) : OAI.Thomason.NormalizedChains.bracket l ∈ OAI.Thomason.NormalizedChains.grade l.length := by
    classical
    by_cases h : l.Pairwise (· < ·)
    · rw [proof_bracket_of_pairwise_47 h]
      exact Finsupp.single_mem_supported ℤ 1 rfl
    · rw [proof_bracket_of_not_pairwise_48 h]
      exact Submodule.zero_mem _
  have proof_map_mem_grade_42 {E : Type u} [instLocal1 : PartialOrder.{u} E]  {D : Type v} [PartialOrder D] (f : E →o D) {k : ℕ}
      {c : OAI.Thomason.NormalizedChains.Chains E} (hc : c ∈ OAI.Thomason.NormalizedChains.grade k) : OAI.Thomason.NormalizedChains.map f c ∈ OAI.Thomason.NormalizedChains.grade k := by
    apply proof_linearCombination_mem_grade_46 _ k k _ hc
    intro w hw
    simpa only [List.length_map, hw] using proof_bracket_mem_grade_49 (w.val.map f)
  have proof_bracket_of_pairwise_22 {E : Type u} [instLocal1 : PartialOrder.{u} E]  {l : List E} (h : l.Pairwise (· < ·)) :
      OAI.Thomason.NormalizedChains.bracket l = Finsupp.single ⟨l, h⟩ 1 := by
    classical
    simp [OAI.Thomason.NormalizedChains.bracket, h]
  have proof_bracket_of_not_pairwise_23 {E : Type u} [instLocal1 : PartialOrder.{u} E]  {l : List E} (h : ¬l.Pairwise (· < ·)) :
      OAI.Thomason.NormalizedChains.bracket l = 0 := by
    classical
    simp [OAI.Thomason.NormalizedChains.bracket, h]
  have proof_prepend_bracket_27 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (a : E) (l : List E) :
      OAI.Thomason.NormalizedChains.prepend a (OAI.Thomason.NormalizedChains.bracket l) = OAI.Thomason.NormalizedChains.bracket (a :: l) := by
    classical
    by_cases h : l.Pairwise (· < ·)
    · rw [proof_bracket_of_pairwise_22 h]
      change Finsupp.linearCombination ℤ (fun l : OAI.Thomason.NormalizedChains.Word E => OAI.Thomason.NormalizedChains.bracket (a :: l.val))
        (Finsupp.single (⟨l, h⟩ : OAI.Thomason.NormalizedChains.Word E) 1) = _
      rw [Finsupp.linearCombination_single]
      simp
    · have h' : ¬(a :: l).Pairwise (· < ·) := fun hw => h hw.tail
      simp [proof_bracket_of_not_pairwise_23 h, proof_bracket_of_not_pairwise_23 h']
  have proof_prepend_prepend_self_30 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (a : E) (c : OAI.Thomason.NormalizedChains.Chains E) : OAI.Thomason.NormalizedChains.prepend a (OAI.Thomason.NormalizedChains.prepend a c) = 0 := by
    classical
    induction c using Finsupp.induction with
    | zero => simp []
    | @single_add l z c _ _ ih =>
      simp only [map_add, ih, add_zero]
      have hz : Finsupp.single l z = z • OAI.Thomason.NormalizedChains.bracket l.val := by
        rw [proof_bracket_of_pairwise_22 l.property]
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hz]
      simp only [map_smul, proof_prepend_bracket_27]
      have h : ¬(a :: a :: l.val).Pairwise (· < ·) := by simp []
      simp [proof_bracket_of_not_pairwise_23 h]
  have proof_wordBoundary_nil_25 {E : Type u} [instLocal1 : PartialOrder.{u} E]  : OAI.Thomason.NormalizedChains.wordBoundary ([] : List E) = 0 := rfl
  have proof_wordBoundary_cons_26 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (a : E) (l : List E) :
      OAI.Thomason.NormalizedChains.wordBoundary (a :: l) = OAI.Thomason.NormalizedChains.bracket l - OAI.Thomason.NormalizedChains.prepend a (OAI.Thomason.NormalizedChains.wordBoundary l) := rfl
  have proof_wordBoundary_repeated_31 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (a : E) (l : List E) :
      OAI.Thomason.NormalizedChains.wordBoundary (a :: a :: l) = 0 := by
    simp [proof_prepend_bracket_27, OAI.Thomason.NormalizedChains.wordBoundary, map_sub, proof_prepend_prepend_self_30]
  have proof_wordBoundary_eq_zero_of_not_pairwise_32 {E : Type u} [instLocal1 : PartialOrder.{u} E]  {l : List E}
      (h : l.Pairwise (· ≤ ·)) (hn : ¬l.Pairwise (· < ·)) : OAI.Thomason.NormalizedChains.wordBoundary l = 0 := by
    induction l with
    | nil => exact (hn (by simp)).elim
    | cons a l ih =>
      by_cases hl : l.Pairwise (· < ·)
      · cases l with
        | nil => exact (hn (by simp)).elim
        | cons b l =>
          have hab : a ≤ b := (List.pairwise_cons.mp h).1 b (by simp)
          have hab' : ¬a < b := by
            intro hab'
            exact hn (List.Pairwise.cons_cons_of_trans hab' hl)
          have heq : a = b := (lt_or_eq_of_le hab).resolve_left hab'
          subst b
          exact proof_wordBoundary_repeated_31 a l
      · simp [OAI.Thomason.NormalizedChains.wordBoundary, proof_bracket_of_not_pairwise_23 hl, ih h.tail hl]
  have proof_boundary_bracket_33 {E : Type u} [instLocal1 : PartialOrder.{u} E]  {l : List E} (h : l.Pairwise (· ≤ ·)) :
      OAI.Thomason.NormalizedChains.boundary (OAI.Thomason.NormalizedChains.bracket l) = OAI.Thomason.NormalizedChains.wordBoundary l := by
    classical
    by_cases hs : l.Pairwise (· < ·)
    · rw [proof_bracket_of_pairwise_22 hs]
      change Finsupp.linearCombination ℤ (fun l : OAI.Thomason.NormalizedChains.Word E => OAI.Thomason.NormalizedChains.wordBoundary l.val)
        (Finsupp.single (⟨l, hs⟩ : OAI.Thomason.NormalizedChains.Word E) 1) = _
      rw [Finsupp.linearCombination_single]
      simp []
    · simp [proof_bracket_of_not_pairwise_23 hs, proof_wordBoundary_eq_zero_of_not_pairwise_32 h hs]
  have proof_faces_nil_34 {E : Type u} {M : Type u} [instLocal2 : AddCommGroup.{u} M]  (H : List E → M) : OAI.Thomason.NormalizedChains.faces H [] = 0 := rfl
  have proof_faces_cons_35 {E : Type u} {M : Type u} [instLocal2 : AddCommGroup.{u} M]  (H : List E → M) (a : E) (l : List E) :
      OAI.Thomason.NormalizedChains.faces H (a :: l) = H l - OAI.Thomason.NormalizedChains.faces (fun m => H (a :: m)) l := rfl
  have proof_faces_hom_36 {E : Type u} {M : Type u} [instLocal2 : AddCommGroup.{u} M]  {M' : Type u} [AddCommGroup M'] (q : M →+ M')
      (H : List E → M) (l : List E) :
      q (OAI.Thomason.NormalizedChains.faces H l) = OAI.Thomason.NormalizedChains.faces (fun m => q (H m)) l := by
    induction l generalizing H with
    | nil => simp only [OAI.Thomason.NormalizedChains.faces, map_zero]
    | cons a l ih => simp only [OAI.Thomason.NormalizedChains.faces, map_sub, ih]
  have proof_faces_bracket_37 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (l : List E) : OAI.Thomason.NormalizedChains.faces OAI.Thomason.NormalizedChains.bracket l = OAI.Thomason.NormalizedChains.wordBoundary l := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [proof_faces_cons_35, proof_wordBoundary_cons_26]
      have h := proof_faces_hom_36 (OAI.Thomason.NormalizedChains.prepend a).toAddMonoidHom OAI.Thomason.NormalizedChains.bracket l
      simp only [LinearMap.toAddMonoidHom_coe, proof_prepend_bracket_27] at h
      rw [← h, ih]
  have proof_faces_nil_50 {E : Type v} {M : Type v} [instLocal2 : AddCommGroup.{v} M]  (H : List E → M) : OAI.Thomason.NormalizedChains.faces H [] = 0 := rfl
  have proof_faces_cons_51 {E : Type v} {M : Type v} [instLocal2 : AddCommGroup.{v} M]  (H : List E → M) (a : E) (l : List E) :
      OAI.Thomason.NormalizedChains.faces H (a :: l) = H l - OAI.Thomason.NormalizedChains.faces (fun m => H (a :: m)) l := rfl
  have proof_wordBoundary_nil_52 {E : Type v} [instLocal1 : PartialOrder.{v} E]  : OAI.Thomason.NormalizedChains.wordBoundary ([] : List E) = 0 := rfl
  have proof_wordBoundary_cons_53 {E : Type v} [instLocal1 : PartialOrder.{v} E]  (a : E) (l : List E) :
      OAI.Thomason.NormalizedChains.wordBoundary (a :: l) = OAI.Thomason.NormalizedChains.bracket l - OAI.Thomason.NormalizedChains.prepend a (OAI.Thomason.NormalizedChains.wordBoundary l) := rfl
  have proof_faces_hom_54 {E : Type v} {M : Type v} [instLocal2 : AddCommGroup.{v} M]  {M' : Type v} [AddCommGroup M'] (q : M →+ M')
      (H : List E → M) (l : List E) :
      q (OAI.Thomason.NormalizedChains.faces H l) = OAI.Thomason.NormalizedChains.faces (fun m => q (H m)) l := by
    induction l generalizing H with
    | nil => simp [proof_faces_nil_50]
    | cons a l ih => simp only [proof_faces_cons_51, map_sub, ih]
  have proof_prepend_bracket_55 {E : Type v} [instLocal1 : PartialOrder.{v} E]  (a : E) (l : List E) :
      OAI.Thomason.NormalizedChains.prepend a (OAI.Thomason.NormalizedChains.bracket l) = OAI.Thomason.NormalizedChains.bracket (a :: l) := by
    classical
    by_cases h : l.Pairwise (· < ·)
    · rw [proof_bracket_of_pairwise_47 h]
      change Finsupp.linearCombination ℤ (fun l : OAI.Thomason.NormalizedChains.Word E => OAI.Thomason.NormalizedChains.bracket (a :: l.val))
        (Finsupp.single (⟨l, h⟩ : OAI.Thomason.NormalizedChains.Word E) 1) = _
      rw [Finsupp.linearCombination_single]
      simp
    · have h' : ¬(a :: l).Pairwise (· < ·) := fun hw => h hw.tail
      simp [proof_bracket_of_not_pairwise_48 h, proof_bracket_of_not_pairwise_48 h']
  have proof_faces_bracket_56 {E : Type v} [instLocal1 : PartialOrder.{v} E]  (l : List E) : OAI.Thomason.NormalizedChains.faces OAI.Thomason.NormalizedChains.bracket l = OAI.Thomason.NormalizedChains.wordBoundary l := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [proof_faces_cons_51, proof_wordBoundary_cons_53]
      have h := proof_faces_hom_54 (OAI.Thomason.NormalizedChains.prepend a).toAddMonoidHom OAI.Thomason.NormalizedChains.bracket l
      simp only [LinearMap.toAddMonoidHom_coe, proof_prepend_bracket_55] at h
      rw [← h, ih]
  have proof_faces_hom_57 {E : Type u} {M : Type u} [instLocal2 : AddCommGroup.{u} M]  {M' : Type v} [AddCommGroup M'] (q : M →+ M')
      (H : List E → M) (l : List E) :
      q (OAI.Thomason.NormalizedChains.faces H l) = OAI.Thomason.NormalizedChains.faces (fun m => q (H m)) l := by
    induction l generalizing H with
    | nil => simp only [OAI.Thomason.NormalizedChains.faces, map_zero]
    | cons a l ih => simp only [OAI.Thomason.NormalizedChains.faces, map_sub, ih]
  have proof_faces_map_58 {E : Type v} {M : Type v} [instLocal2 : AddCommGroup.{v} M]  {D : Type u} (f : D → E) (H : List E → M) (l : List D) :
      OAI.Thomason.NormalizedChains.faces H (l.map f) = OAI.Thomason.NormalizedChains.faces (fun m => H (m.map f)) l := by
    induction l generalizing H with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons, OAI.Thomason.NormalizedChains.faces, ih]
  have proof_faces_nil_59 {E : Type u} {M : Type v} [instLocal2 : AddCommGroup.{v} M]  (H : List E → M) : OAI.Thomason.NormalizedChains.faces H [] = 0 := rfl
  have proof_faces_cons_60 {E : Type u} {M : Type v} [instLocal2 : AddCommGroup.{v} M]  (H : List E → M) (a : E) (l : List E) :
      OAI.Thomason.NormalizedChains.faces H (a :: l) = H l - OAI.Thomason.NormalizedChains.faces (fun m => H (a :: m)) l := rfl
  have proof_faces_congr_61 {E : Type u} {M : Type v} [instLocal2 : AddCommGroup.{v} M]  {H K : List E → M} {l : List E}
      (h : ∀ m, m.Sublist l → H m = K m) : OAI.Thomason.NormalizedChains.faces H l = OAI.Thomason.NormalizedChains.faces K l := by
    induction l generalizing H K with
    | nil => rfl
    | cons a l ih =>
      rw [proof_faces_cons_60, proof_faces_cons_60, h l (List.sublist_cons_self a l)]
      congr 1
      exact ih (fun m hm => h (a :: m) (List.Sublist.cons_cons a hm))
  have proof_pairwise_of_map_62 {E : Type u} [instLocal1 : PartialOrder.{u} E] {D : Type v} [instLocal3 : PartialOrder.{v} D]  {l : List E} (h : l.Pairwise (· ≤ ·)) (f : E → D)
      (hf : (l.map f).Pairwise (· < ·)) : l.Pairwise (· < ·) := by
    apply (h.and (List.pairwise_map.mp hf)).imp
    intro a b hab
    exact lt_of_le_of_ne hab.1 (fun he => (ne_of_lt hab.2) (congrArg f he))
  have proof_map_bracket_63 {E : Type u} [instLocal1 : PartialOrder.{u} E] {D : Type v} [instLocal3 : PartialOrder.{v} D]  (f : E →o D) {l : List E} (h : l.Pairwise (· ≤ ·)) :
      OAI.Thomason.NormalizedChains.map f (OAI.Thomason.NormalizedChains.bracket l) = OAI.Thomason.NormalizedChains.bracket (l.map f) := by
    classical
    by_cases hs : l.Pairwise (· < ·)
    · rw [proof_bracket_of_pairwise_22 hs]
      change Finsupp.linearCombination ℤ (fun l : OAI.Thomason.NormalizedChains.Word E => OAI.Thomason.NormalizedChains.bracket (l.val.map f))
        (Finsupp.single (⟨l, hs⟩ : OAI.Thomason.NormalizedChains.Word E) 1) = _
      rw [Finsupp.linearCombination_single]
      simp
    · have hf : ¬(l.map f).Pairwise (· < ·) := fun hm => hs (proof_pairwise_of_map_62 h f hm)
      simp [proof_bracket_of_not_pairwise_23 hs, proof_bracket_of_not_pairwise_48 hf]
  have proof_map_wordBoundary_64 {E : Type u} [instLocal1 : PartialOrder.{u} E] {D : Type v} [instLocal3 : PartialOrder.{v} D]  (f : E →o D) {l : List E} (h : l.Pairwise (· ≤ ·)) :
      OAI.Thomason.NormalizedChains.map f (OAI.Thomason.NormalizedChains.wordBoundary l) = OAI.Thomason.NormalizedChains.wordBoundary (l.map f) := by
    rw [← proof_faces_bracket_37, ← proof_faces_bracket_56]
    change (OAI.Thomason.NormalizedChains.map f).toAddMonoidHom (OAI.Thomason.NormalizedChains.faces OAI.Thomason.NormalizedChains.bracket l) = _
    rw [proof_faces_hom_57, proof_faces_map_58]
    apply proof_faces_congr_61
    intro m hm
    exact proof_map_bracket_63 f (h.sublist hm)
  have proof_prepend_prepend_self_65 {E : Type v} [instLocal1 : PartialOrder.{v} E]  (a : E) (c : OAI.Thomason.NormalizedChains.Chains E) : OAI.Thomason.NormalizedChains.prepend a (OAI.Thomason.NormalizedChains.prepend a c) = 0 := by
    classical
    induction c using Finsupp.induction with
    | zero => simp []
    | @single_add l z c _ _ ih =>
      simp only [map_add, ih, add_zero]
      have hz : Finsupp.single l z = z • OAI.Thomason.NormalizedChains.bracket l.val := by
        rw [proof_bracket_of_pairwise_47 l.property]
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hz]
      simp only [map_smul, proof_prepend_bracket_55]
      have h : ¬(a :: a :: l.val).Pairwise (· < ·) := by simp []
      simp [proof_bracket_of_not_pairwise_48 h]
  have proof_wordBoundary_repeated_66 {E : Type v} [instLocal1 : PartialOrder.{v} E]  (a : E) (l : List E) :
      OAI.Thomason.NormalizedChains.wordBoundary (a :: a :: l) = 0 := by
    simp [proof_prepend_bracket_55, OAI.Thomason.NormalizedChains.wordBoundary, map_sub, proof_prepend_prepend_self_65]
  have proof_wordBoundary_eq_zero_of_not_pairwise_67 {E : Type v} [instLocal1 : PartialOrder.{v} E]  {l : List E}
      (h : l.Pairwise (· ≤ ·)) (hn : ¬l.Pairwise (· < ·)) : OAI.Thomason.NormalizedChains.wordBoundary l = 0 := by
    induction l with
    | nil => exact (hn (by simp)).elim
    | cons a l ih =>
      by_cases hl : l.Pairwise (· < ·)
      · cases l with
        | nil => exact (hn (by simp)).elim
        | cons b l =>
          have hab : a ≤ b := (List.pairwise_cons.mp h).1 b (by simp)
          have hab' : ¬a < b := by
            intro hab'
            exact hn (List.Pairwise.cons_cons_of_trans hab' hl)
          have heq : a = b := (lt_or_eq_of_le hab).resolve_left hab'
          subst b
          exact proof_wordBoundary_repeated_66 a l
      · simp [OAI.Thomason.NormalizedChains.wordBoundary, proof_bracket_of_not_pairwise_48 hl, ih h.tail hl]
  have proof_boundary_bracket_68 {E : Type v} [instLocal1 : PartialOrder.{v} E]  {l : List E} (h : l.Pairwise (· ≤ ·)) :
      OAI.Thomason.NormalizedChains.boundary (OAI.Thomason.NormalizedChains.bracket l) = OAI.Thomason.NormalizedChains.wordBoundary l := by
    classical
    by_cases hs : l.Pairwise (· < ·)
    · rw [proof_bracket_of_pairwise_47 hs]
      change Finsupp.linearCombination ℤ (fun l : OAI.Thomason.NormalizedChains.Word E => OAI.Thomason.NormalizedChains.wordBoundary l.val)
        (Finsupp.single (⟨l, hs⟩ : OAI.Thomason.NormalizedChains.Word E) 1) = _
      rw [Finsupp.linearCombination_single]
      simp []
    · simp [proof_bracket_of_not_pairwise_48 hs, proof_wordBoundary_eq_zero_of_not_pairwise_67 h hs]
  have proof_map_boundary_43 {E : Type u} [instLocal1 : PartialOrder.{u} E] {D : Type v} [instLocal3 : PartialOrder.{v} D]  (f : E →o D) (c : OAI.Thomason.NormalizedChains.Chains E) :
      OAI.Thomason.NormalizedChains.map f (OAI.Thomason.NormalizedChains.boundary c) = OAI.Thomason.NormalizedChains.boundary (OAI.Thomason.NormalizedChains.map f c) := by
    classical
    induction c using Finsupp.induction with
    | zero => simp []
    | @single_add l z c _ _ ih =>
      simp only [map_add, ih]
      congr 1
      have hz : Finsupp.single l z = z • OAI.Thomason.NormalizedChains.bracket l.val := by
        rw [proof_bracket_of_pairwise_22 l.property]
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      have hl := l.property.imp fun h => le_of_lt h
      rw [hz]
      simp only [map_smul]
      rw [proof_boundary_bracket_33 hl, proof_map_wordBoundary_64 f hl, proof_map_bracket_63 f hl,
        proof_boundary_bracket_68 (List.pairwise_map.mpr (hl.imp fun hh => f.monotone hh))]
  have proof_emptyCoefficient_bracket_69 {E : Type v} [instLocal1 : PartialOrder.{v} E]  (l : List E) :
      OAI.Thomason.NormalizedChains.emptyCoefficient (OAI.Thomason.NormalizedChains.bracket l) = if l = [] then 1 else 0 := by
    classical
    by_cases hl : l = []
    · subst l
      simp [OAI.Thomason.NormalizedChains.emptyCoefficient, proof_bracket_of_pairwise_47 List.Pairwise.nil, OAI.Thomason.NormalizedChains.emptyWord]
    · by_cases hs : l.Pairwise (· < ·)
      · have hw : (⟨l, hs⟩ : OAI.Thomason.NormalizedChains.Word E) ≠ OAI.Thomason.NormalizedChains.emptyWord := by
          intro he
          exact hl (congrArg Subtype.val he)
        simp [OAI.Thomason.NormalizedChains.emptyCoefficient, proof_bracket_of_pairwise_47 hs, hw, hl]
      · simp [proof_bracket_of_not_pairwise_48 hs, hl]
  have proof_emptyCoefficient_bracket_70 {E : Type u} [instLocal1 : PartialOrder.{u} E]  (l : List E) :
      OAI.Thomason.NormalizedChains.emptyCoefficient (OAI.Thomason.NormalizedChains.bracket l) = if l = [] then 1 else 0 := by
    classical
    by_cases hl : l = []
    · subst l
      simp [OAI.Thomason.NormalizedChains.emptyCoefficient, proof_bracket_of_pairwise_22 List.Pairwise.nil, OAI.Thomason.NormalizedChains.emptyWord]
    · by_cases hs : l.Pairwise (· < ·)
      · have hw : (⟨l, hs⟩ : OAI.Thomason.NormalizedChains.Word E) ≠ OAI.Thomason.NormalizedChains.emptyWord := by
          intro he
          exact hl (congrArg Subtype.val he)
        simp [OAI.Thomason.NormalizedChains.emptyCoefficient, proof_bracket_of_pairwise_22 hs, hw, hl]
      · simp [proof_bracket_of_not_pairwise_23 hs, hl]
  have proof_emptyCoefficient_map_44 {E : Type u} [instLocal1 : PartialOrder.{u} E]  {D : Type v} [PartialOrder D] (f : E →o D) (c : OAI.Thomason.NormalizedChains.Chains E) :
      OAI.Thomason.NormalizedChains.emptyCoefficient (OAI.Thomason.NormalizedChains.map f c) = OAI.Thomason.NormalizedChains.emptyCoefficient c := by
    classical
    induction c using Finsupp.induction with
    | zero => simp []
    | @single_add l z c _ _ ih =>
      simp only [map_add, ih]
      congr 1
      have hz : Finsupp.single l z = z • OAI.Thomason.NormalizedChains.bracket l.val := by
        rw [proof_bracket_of_pairwise_22 l.property]
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hz]
      simp only [map_smul, proof_map_bracket_63 _ (l.property.imp fun h => le_of_lt h),
        proof_emptyCoefficient_bracket_69, proof_emptyCoefficient_bracket_70, List.map_eq_nil_iff]
  have proof_linearCombination_positive_71 {E : Type u} [instLocal1 : PartialOrder.{u} E]  {D : Type v} [PartialOrder D]
      (H : OAI.Thomason.NormalizedChains.Word E → OAI.Thomason.NormalizedChains.Chains D) (hH : ∀ w, OAI.Thomason.NormalizedChains.Positive (H w))
      {c : OAI.Thomason.NormalizedChains.Chains E} (hc : OAI.Thomason.NormalizedChains.Positive c) :
      OAI.Thomason.NormalizedChains.Positive (Finsupp.linearCombination ℤ H c) := by
    intro w
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    simp only [Finset.sum_apply, Finsupp.coe_finsetSum]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hc i) (hH i w)
  have proof_bracket_positive_72 {E : Type v} [instLocal1 : PartialOrder.{v} E]  (l : List E) : OAI.Thomason.NormalizedChains.Positive (OAI.Thomason.NormalizedChains.bracket l) := by
    classical
    intro w
    by_cases h : l.Pairwise (· < ·)
    · simp [proof_bracket_of_pairwise_47 h, Finsupp.single_apply]
      split <;> omega
    · simp [proof_bracket_of_not_pairwise_48 h]
  have proof_map_positive_45 {E : Type u} [instLocal1 : PartialOrder.{u} E]  {D : Type v} [PartialOrder D] (f : E →o D)
      {c : OAI.Thomason.NormalizedChains.Chains E} (hc : OAI.Thomason.NormalizedChains.Positive c) : OAI.Thomason.NormalizedChains.Positive (OAI.Thomason.NormalizedChains.map f c) :=
    proof_linearCombination_positive_71 _ (fun w => proof_bracket_positive_72 (w.val.map f)) hc
  exact {
    map p :=
      { toFun := fun c => ⟨OAI.Thomason.NormalizedChains.map f c.val, proof_map_mem_grade_42 f c.property⟩
        map_zero' := Subtype.ext (map_zero _)
        map_add' := fun x y => Subtype.ext (map_add _ x.val y.val) }
    map_d p x := Subtype.ext (proof_map_boundary_43 f x.val)
    map_augmentation x := by
      change OAI.Thomason.NormalizedChains.emptyCoefficient (OAI.Thomason.NormalizedChains.boundary (OAI.Thomason.NormalizedChains.map f x.val)) = OAI.Thomason.NormalizedChains.emptyCoefficient (OAI.Thomason.NormalizedChains.boundary x.val)
      rw [← proof_map_boundary_43, proof_emptyCoefficient_map_44]
    map_positive p x hx := proof_map_positive_45 f hx
  }


end OAI.Thomason.NormalizedChains
end

section
namespace OAI.Thomason.NormalizedChains
variable {E : Type u} [PartialOrder E]
open CategoryTheory

noncomputable def simplexComplexes : SimplexCategory ⥤ OAI.Thomason.DirectedComplex.{0} := by
  classical
  have proof_bracket_of_pairwise_75 {E : Type 0} [instLocal1 : PartialOrder.{0} E]  {l : List E} (h : l.Pairwise (· < ·)) :
      OAI.Thomason.NormalizedChains.bracket l = Finsupp.single ⟨l, h⟩ 1 := by
    classical
    simp [OAI.Thomason.NormalizedChains.bracket, h]
  have proof_pairwise_of_map_76 {E : Type 0} [instLocal1 : PartialOrder.{0} E] {D : Type 0} [instLocal3 : PartialOrder.{0} D]  {l : List E} (h : l.Pairwise (· ≤ ·)) (f : E → D)
      (hf : (l.map f).Pairwise (· < ·)) : l.Pairwise (· < ·) := by
    apply (h.and (List.pairwise_map.mp hf)).imp
    intro a b hab
    exact lt_of_le_of_ne hab.1 (fun he => (ne_of_lt hab.2) (congrArg f he))
  have proof_bracket_of_not_pairwise_77 {E : Type 0} [instLocal1 : PartialOrder.{0} E]  {l : List E} (h : ¬l.Pairwise (· < ·)) :
      OAI.Thomason.NormalizedChains.bracket l = 0 := by
    classical
    simp [OAI.Thomason.NormalizedChains.bracket, h]
  have proof_map_bracket_78 {E : Type 0} [instLocal1 : PartialOrder.{0} E] {D : Type 0} [instLocal3 : PartialOrder.{0} D]  (f : E →o D) {l : List E} (h : l.Pairwise (· ≤ ·)) :
      OAI.Thomason.NormalizedChains.map f (OAI.Thomason.NormalizedChains.bracket l) = OAI.Thomason.NormalizedChains.bracket (l.map f) := by
    classical
    by_cases hs : l.Pairwise (· < ·)
    · rw [proof_bracket_of_pairwise_75 hs]
      change Finsupp.linearCombination ℤ (fun l : OAI.Thomason.NormalizedChains.Word E => OAI.Thomason.NormalizedChains.bracket (l.val.map f))
        (Finsupp.single (⟨l, hs⟩ : OAI.Thomason.NormalizedChains.Word E) 1) = _
      rw [Finsupp.linearCombination_single]
      simp
    · have hf : ¬(l.map f).Pairwise (· < ·) := fun hm => hs (proof_pairwise_of_map_76 h f hm)
      simp [proof_bracket_of_not_pairwise_77 hs, proof_bracket_of_not_pairwise_77 hf]
  have proof_map_id_79 {E : Type 0} [instLocal1 : PartialOrder.{0} E]  (c : OAI.Thomason.NormalizedChains.Chains E) : OAI.Thomason.NormalizedChains.map (OrderHom.id) c = c := by
    classical
    induction c using Finsupp.induction with
    | zero => simp
    | @single_add l z c _ _ ih =>
      simp only [map_add, ih]
      congr 1
      have hz : Finsupp.single l z = z • OAI.Thomason.NormalizedChains.bracket l.val := by
        rw [proof_bracket_of_pairwise_75 l.property]
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hz, map_smul, proof_map_bracket_78 _ (l.property.imp fun h => le_of_lt h)]
      simp
  have proof_complexMap_id_73 {E : Type 0} [instLocal1 : PartialOrder.{0} E]  : OAI.Thomason.NormalizedChains.complexMap (OrderHom.id : E →o E) =
      OAI.Thomason.DirectedComplex.Hom.id (OAI.Thomason.NormalizedChains.complex E) := by
    ext p x
    apply Subtype.ext
    exact proof_map_id_79 x.val
  have proof_map_comp_80 {E : Type 0} [instLocal1 : PartialOrder.{0} E] {D : Type 0} [instLocal3 : PartialOrder.{0} D] {B : Type 0} [instLocal5 : PartialOrder.{0} B]  (f : E →o D) (g : D →o B) (c : OAI.Thomason.NormalizedChains.Chains E) :
      OAI.Thomason.NormalizedChains.map (g.comp f) c = OAI.Thomason.NormalizedChains.map g (OAI.Thomason.NormalizedChains.map f c) := by
    classical
    induction c using Finsupp.induction with
    | zero => simp
    | @single_add l z c _ _ ih =>
      simp only [map_add, ih]
      congr 1
      have hz : Finsupp.single l z = z • OAI.Thomason.NormalizedChains.bracket l.val := by
        rw [proof_bracket_of_pairwise_75 l.property]
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      have hl := l.property.imp fun h => le_of_lt h
      rw [hz]
      simp only [map_smul]
      rw [proof_map_bracket_78 _ hl, proof_map_bracket_78 _ hl,
        proof_map_bracket_78 _ (List.pairwise_map.mpr (hl.imp fun hh => f.monotone hh))]
      simp [List.map_map]
  have proof_complexMap_comp_74 {E : Type 0} [instLocal1 : PartialOrder.{0} E]  {D : Type 0} [PartialOrder D] {B : Type 0} [PartialOrder B]
      (f : E →o D) (g : D →o B) : OAI.Thomason.NormalizedChains.complexMap (g.comp f) =
        OAI.Thomason.DirectedComplex.Hom.comp (OAI.Thomason.NormalizedChains.complexMap f) (OAI.Thomason.NormalizedChains.complexMap g) := by
    ext p x
    apply Subtype.ext
    exact proof_map_comp_80 f g x.val
  exact {
    obj m := OAI.Thomason.NormalizedChains.complex (Fin (m.len+1))
    map f := OAI.Thomason.NormalizedChains.complexMap f.toOrderHom
    map_id _ := proof_complexMap_id_73
    map_comp f g := proof_complexMap_comp_74 f.toOrderHom g.toOrderHom
  }


end OAI.Thomason.NormalizedChains
end

section
namespace OAI.Thomason
open CategoryTheory Opposite

noncomputable def orientals : SimplexCategory ⥤ OAI.Thomason.OmegaCategory.{0} :=
  OAI.Thomason.NormalizedChains.simplexComplexes ⋙ OAI.Thomason.DirectedComplex.nuFunctor


end OAI.Thomason
end

section
namespace OAI.Thomason.OmegaCategory


noncomputable def ulift (C : OAI.Thomason.OmegaCategory.{u}) : OAI.Thomason.OmegaCategory.{max u v} where
  Cell := ULift.{v} C.Cell
  source k x := ⟨C.source k x.down⟩
  target k x := ⟨C.target k x.down⟩
  source_source i j x := congrArg ULift.up (C.source_source i j x.down)
  target_target i j x := congrArg ULift.up (C.target_target i j x.down)
  source_target i j x := by
    simpa only [apply_ite] using congrArg (ULift.up (α := C.Cell)) (C.source_target i j x.down)
  target_source i j x := by
    simpa only [apply_ite] using congrArg (ULift.up (α := C.Cell)) (C.target_source i j x.down)
  comp k x y h := ⟨C.comp k x.down y.down (congrArg ULift.down h)⟩
  source_comp_le i k hik x y h :=
    congrArg ULift.up (C.source_comp_le i k hik x.down y.down (congrArg ULift.down h))
  target_comp_le i k hik x y h :=
    congrArg ULift.up (C.target_comp_le i k hik x.down y.down (congrArg ULift.down h))
  source_comp_gt i k hki x y h hs :=
    congrArg ULift.up (C.source_comp_gt i k hki x.down y.down
      (congrArg ULift.down h) (congrArg ULift.down hs))
  target_comp_gt i k hki x y h ht :=
    congrArg ULift.up (C.target_comp_gt i k hki x.down y.down
      (congrArg ULift.down h) (congrArg ULift.down ht))
  unit_left k x h := congrArg ULift.up (C.unit_left k x.down (congrArg ULift.down h))
  unit_right k x h := congrArg ULift.up (C.unit_right k x.down (congrArg ULift.down h))
  assoc k x y z hxy hyz hxy_z hx_yz :=
    congrArg ULift.up (C.assoc k x.down y.down z.down
      (congrArg ULift.down hxy) (congrArg ULift.down hyz)
      (congrArg ULift.down hxy_z) (congrArg ULift.down hx_yz))
  interchange k l hkl a b c d hab hcd hac hbd h₁ h₂ :=
    congrArg ULift.up (C.interchange k l hkl a.down b.down c.down d.down
      (congrArg ULift.down hab) (congrArg ULift.down hcd)
      (congrArg ULift.down hac) (congrArg ULift.down hbd)
      (congrArg ULift.down h₁) (congrArg ULift.down h₂))
  finite_dimension x := by
    obtain ⟨k, hk⟩ := C.finite_dimension x.down
    exact ⟨k, congrArg ULift.up hk⟩

noncomputable def uliftUp (C : OAI.Thomason.OmegaCategory.{u}) : OAI.Thomason.OmegaCategory.Functor C (OAI.Thomason.OmegaCategory.ulift.{u,v} C) where
  map := ULift.up
  map_source _ _ := rfl
  map_target _ _ := rfl
  map_comp _ _ _ _ _ := rfl

noncomputable def uliftDown (C : OAI.Thomason.OmegaCategory.{u}) : OAI.Thomason.OmegaCategory.Functor (OAI.Thomason.OmegaCategory.ulift.{u,v} C) C where
  map := ULift.down
  map_source _ _ := rfl
  map_target _ _ := rfl
  map_comp _ _ _ _ _ := rfl


end OAI.Thomason.OmegaCategory
end

section
namespace OAI.Thomason.OmegaCategory
open CategoryTheory

noncomputable def uliftFunctor : OAI.Thomason.OmegaCategory.{u} ⥤ OAI.Thomason.OmegaCategory.{max u v} where
  obj := OAI.Thomason.OmegaCategory.ulift
  map {C D} F := OAI.Thomason.OmegaCategory.Functor.comp (OAI.Thomason.OmegaCategory.Functor.comp (OAI.Thomason.OmegaCategory.uliftDown C) F) (OAI.Thomason.OmegaCategory.uliftUp D)


end OAI.Thomason.OmegaCategory
end

section
namespace OAI.Thomason
open CategoryTheory Opposite

noncomputable def raisedOrientals : SimplexCategory ⥤ OAI.Thomason.OmegaCategory.{u} :=
  OAI.Thomason.orientals ⋙ OAI.Thomason.OmegaCategory.uliftFunctor.{0,u}


end OAI.Thomason
end

section
namespace OAI.Thomason.OmegaCategory


structure Presentation where
  Generator : Type u
  dimension : Generator → ℕ
  relations : (C : OAI.Thomason.OmegaCategory.{u}) → (Generator → C.Cell) → Prop


end OAI.Thomason.OmegaCategory
end

section
namespace OAI.Thomason.OmegaCategory.Presentation
variable (P : Presentation.{u})

structure Interpretation (C : OAI.Thomason.OmegaCategory.{u}) where
  map : P.Generator → C.Cell
  bounded : ∀ g, C.source (P.dimension g) (map g) = map g
  satisfies : P.relations C map


end OAI.Thomason.OmegaCategory.Presentation
end

section
namespace OAI.Thomason.OmegaCategory


inductive CellTerm (G : Type u) where
  | gen : G → CellTerm G
  | source : ℕ → CellTerm G → CellTerm G
  | target : ℕ → CellTerm G → CellTerm G
  | comp : ℕ → CellTerm G → CellTerm G → CellTerm G


end OAI.Thomason.OmegaCategory
end

section
namespace OAI.Thomason.OmegaCategory.CellTerm


noncomputable def composeOrLeft (C : OAI.Thomason.OmegaCategory.{v}) (k : ℕ) (x y : C.Cell) : C.Cell := by
  classical
  exact if h : C.target k x = C.source k y then C.comp k x y h else x

noncomputable def eval {G : Type u} (C : OAI.Thomason.OmegaCategory.{v}) (f : G → C.Cell) : OAI.Thomason.OmegaCategory.CellTerm G → C.Cell
  | gen g => f g
  | source k x => C.source k (eval C f x)
  | target k x => C.target k (eval C f x)
  | comp k x y => OAI.Thomason.OmegaCategory.CellTerm.composeOrLeft C k (eval C f x) (eval C f y)


end OAI.Thomason.OmegaCategory.CellTerm
end

section
namespace OAI.Thomason.OmegaCategory.Presentation
variable (P : Presentation.{u})

noncomputable def Equiv (x y : OAI.Thomason.OmegaCategory.CellTerm P.Generator) : Prop :=
  ∀ (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C), x.eval C I.map = y.eval C I.map

inductive Valid : OAI.Thomason.OmegaCategory.CellTerm P.Generator → Prop
  | gen (g) : Valid (.gen g)
  | source (k x) : Valid x → Valid (.source k x)
  | target (k x) : Valid x → Valid (.target k x)
  | comp (k x y) : Valid x → Valid y → P.Equiv (.target k x) (.source k y) → Valid (.comp k x y)

noncomputable abbrev ValidTerm := {x : OAI.Thomason.OmegaCategory.CellTerm P.Generator // P.Valid x}

noncomputable instance termSetoid : Setoid P.ValidTerm := by
  classical
  have proof_refl_81 {P : OAI.Thomason.OmegaCategory.Presentation.{u}}  (x : OAI.Thomason.OmegaCategory.CellTerm P.Generator) : P.Equiv x x := fun _ _ => rfl
  have proof_symm_82 {P : OAI.Thomason.OmegaCategory.Presentation.{u}} {x : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)} {y : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)}  (h : P.Equiv x y) : P.Equiv y x := fun C I => (h C I).symm
  have proof_trans_83 {P : OAI.Thomason.OmegaCategory.Presentation.{u}} {x : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)} {y : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)} {z : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)}  (h : P.Equiv x y) (h' : P.Equiv y z) : P.Equiv x z :=
    fun C I => (h C I).trans (h' C I)
  exact {
    r x y := P.Equiv x.val y.val
    iseqv := ⟨fun _ => proof_refl_81 _, fun h => (proof_symm_82 h), fun h h' => (proof_trans_83 h h')⟩
  }

noncomputable abbrev Cells := Quotient P.termSetoid

noncomputable def evaluate (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) : P.Cells → C.Cell :=
  Quotient.lift (fun x : P.ValidTerm => x.val.eval C I.map) (fun _ _ h => h C I)


end OAI.Thomason.OmegaCategory.Presentation
end

section
namespace OAI.Thomason.OmegaCategory.CellTerm


noncomputable def dimension {G : Type u} (d : G → ℕ) : OAI.Thomason.OmegaCategory.CellTerm G → ℕ
  | gen g => d g
  | source k _ => k
  | target k _ => k
  | comp k x y => max (k+1) (max (dimension d x) (dimension d y))


end OAI.Thomason.OmegaCategory.CellTerm
end

section
namespace OAI.Thomason.OmegaCategory.Presentation
variable (P : Presentation.{u})

noncomputable def sourceTerm (k : ℕ) (x : P.ValidTerm) : P.ValidTerm := ⟨.source k x.val, OAI.Thomason.OmegaCategory.Presentation.Valid.source (P := P) k x.val x.property⟩

noncomputable def source (k : ℕ) : P.Cells → P.Cells := by
  classical
  have proof_source_84 {P : OAI.Thomason.OmegaCategory.Presentation.{u}} {x : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)} {y : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)}  (k : ℕ) (h : P.Equiv x y) : P.Equiv (.source k x) (.source k y) :=
    fun C I => congrArg (C.source k) (h C I)
  exact
    Quotient.map (P.sourceTerm k) (fun _ _ h => (proof_source_84 k h))

noncomputable def targetTerm (k : ℕ) (x : P.ValidTerm) : P.ValidTerm := ⟨.target k x.val, OAI.Thomason.OmegaCategory.Presentation.Valid.target (P := P) k x.val x.property⟩

noncomputable def target (k : ℕ) : P.Cells → P.Cells := by
  classical
  have proof_target_85 {P : OAI.Thomason.OmegaCategory.Presentation.{u}} {x : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)} {y : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)}  (k : ℕ) (h : P.Equiv x y) : P.Equiv (.target k x) (.target k y) :=
    fun C I => congrArg (C.target k) (h C I)
  exact
    Quotient.map (P.targetTerm k) (fun _ _ h => (proof_target_85 k h))

noncomputable def compTerm (k : ℕ) (x y : P.ValidTerm) : P.ValidTerm := by
  classical
  exact if h : P.Equiv (.target k x.val) (.source k y.val) then
    ⟨.comp k x.val y.val, OAI.Thomason.OmegaCategory.Presentation.Valid.comp (P := P) k x.val y.val x.property y.property h⟩ else x

noncomputable def comp (k : ℕ) (x y : P.Cells) (_ : P.target k x = P.source k y) : P.Cells := by
  classical
  have proof_trans_83 {P : OAI.Thomason.OmegaCategory.Presentation.{u}} {x : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)} {y : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)} {z : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)}  (h : P.Equiv x y) (h' : P.Equiv y z) : P.Equiv x z :=
    fun C I => (h C I).trans (h' C I)
  have proof_symm_82 {P : OAI.Thomason.OmegaCategory.Presentation.{u}} {x : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)} {y : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)}  (h : P.Equiv x y) : P.Equiv y x := fun C I => (h C I).symm
  have proof_target_85 {P : OAI.Thomason.OmegaCategory.Presentation.{u}} {x : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)} {y : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)}  (k : ℕ) (h : P.Equiv x y) : P.Equiv (.target k x) (.target k y) :=
    fun C I => congrArg (C.target k) (h C I)
  have proof_source_84 {P : OAI.Thomason.OmegaCategory.Presentation.{u}} {x : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)} {y : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)}  (k : ℕ) (h : P.Equiv x y) : P.Equiv (.source k x) (.source k y) :=
    fun C I => congrArg (C.source k) (h C I)
  have proof_composable_congr_87 {P : OAI.Thomason.OmegaCategory.Presentation.{u}} {x : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)} {y : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)} {x' : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)} {y' : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)}  (k : ℕ) (hx : P.Equiv x x') (hy : P.Equiv y y') :
      P.Equiv (.target k x) (.source k y) ↔ P.Equiv (.target k x') (.source k y') :=
    ⟨fun h => (proof_trans_83
    (proof_symm_82 (proof_target_85 k hx))
    (proof_trans_83 h (proof_source_84 k hy))),
     fun h => (proof_trans_83 (proof_target_85 k hx)
    (proof_trans_83 h
      (proof_symm_82 (proof_source_84 k hy))))⟩
  have proof_comp_88 {P : OAI.Thomason.OmegaCategory.Presentation.{u}} {x : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)} {y : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)} {x' : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)} {y' : OAI.Thomason.OmegaCategory.CellTerm.{u} (OAI.Thomason.OmegaCategory.Presentation.Generator.{u} P)}  (k : ℕ) (hx : P.Equiv x x') (hy : P.Equiv y y') :
      P.Equiv (.comp k x y) (.comp k x' y') := by
    intro C I
    exact congrArg₂ (OAI.Thomason.OmegaCategory.CellTerm.composeOrLeft C k) (hx C I) (hy C I)
  have proof_compTerm_equiv_86 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (k : ℕ) {x y x' y' : P.ValidTerm}
      (hx : P.Equiv x.val x'.val) (hy : P.Equiv y.val y'.val) :
      P.Equiv (P.compTerm k x y).val (P.compTerm k x' y').val := by
    classical
    have he := proof_composable_congr_87 k hx hy
    by_cases h : P.Equiv (.target k x.val) (.source k y.val)
    · simp only [OAI.Thomason.OmegaCategory.Presentation.compTerm, dite_eq_left h, dite_eq_left (he.mp h)]
      exact proof_comp_88 k hx hy
    · simp only [OAI.Thomason.OmegaCategory.Presentation.compTerm, dite_eq_right h, dite_eq_right (mt he.mpr h)]
      exact hx
  exact
    Quotient.map₂ (P.compTerm k) (fun _ _ hx _ _ hy => (proof_compTerm_equiv_86 P k hx hy)) x y

noncomputable abbrev category : OAI.Thomason.OmegaCategory.{u} := by
  classical
  have proof_cells_ext_89 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  {x y : P.Cells}
      (h : ∀ (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C), P.evaluate C I x = P.evaluate C I y) : x = y := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact Quotient.sound h
  have proof_evaluate_source_90 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ) (x : P.Cells) :
      P.evaluate C I (P.source k x) = C.source k (P.evaluate C I x) := by
    induction x using Quotient.inductionOn
    rfl
  have proof_evaluate_target_91 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ) (x : P.Cells) :
      P.evaluate C I (P.target k x) = C.target k (P.evaluate C I x) := by
    induction x using Quotient.inductionOn
    rfl
  have proof_evaluate_composable_94 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ)
      (x y : P.Cells) (h : P.target k x = P.source k y) :
      C.target k (P.evaluate C I x) = C.source k (P.evaluate C I y) := by
    rw [← proof_evaluate_target_91, ← proof_evaluate_source_90, h]
  have proof_evaluate_comp_92 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ)
      (x y : P.Cells) (h : P.target k x = P.source k y) :
      P.evaluate C I (P.comp k x y h) =
        C.comp k (P.evaluate C I x) (P.evaluate C I y) (proof_evaluate_composable_94 P C I k x y h) := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        have hm : P.Equiv (.target k x.val) (.source k y.val) := Quotient.exact h
        change (P.compTerm k x y).val.eval C I.map = _
        have hm' : C.target k (x.val.eval C I.map) = C.source k (y.val.eval C I.map) := hm C I
        simp only [OAI.Thomason.OmegaCategory.Presentation.compTerm, dite_eq_left hm, OAI.Thomason.OmegaCategory.CellTerm.eval, OAI.Thomason.OmegaCategory.CellTerm.composeOrLeft, dite_eq_left hm']
        rfl
  have proof_source_source_self_95 (C : OAI.Thomason.OmegaCategory.{u})  (k : ℕ) (x : C.Cell) :
      C.source k (C.source k x) = C.source k x := by
    simp [C.source_source]
  have proof_source_target_self_96 (C : OAI.Thomason.OmegaCategory.{u})  (k : ℕ) (x : C.Cell) :
      C.source k (C.target k x) = C.target k x := by
    simp [C.source_target]
  have proof_source_composable_97 (C : OAI.Thomason.OmegaCategory.{u})  {k i : ℕ} (hki : k < i) {x y : C.Cell}
      (h : C.target k x = C.source k y) :
      C.target k (C.source i x) = C.source k (C.source i y) := by
    rw [C.target_source, ite_eq_left hki, C.source_source, min_eq_left (le_of_lt hki)]
    exact h
  have proof_source_fixed_upwards_98 (C : OAI.Thomason.OmegaCategory.{u})  {i j : ℕ} (hij : i ≤ j) {x : C.Cell}
      (h : C.source i x = x) : C.source j x = x := by
    rw [← h, C.source_source, min_eq_right hij]
  have proof_eval_dimension_93 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  {x : OAI.Thomason.OmegaCategory.CellTerm P.Generator} (hx : P.Valid x)
      (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) :
      C.source (x.dimension P.dimension) (x.eval C I.map) = x.eval C I.map := by
    induction hx with
    | gen g => exact I.bounded g
    | source k x hx ih => exact (proof_source_source_self_95 C k
    (OAI.Thomason.OmegaCategory.CellTerm.eval C (OAI.Thomason.OmegaCategory.Presentation.Interpretation.map I) x))
    | target k x hx ih => exact (proof_source_target_self_96 C k
    (OAI.Thomason.OmegaCategory.CellTerm.eval C (OAI.Thomason.OmegaCategory.Presentation.Interpretation.map I) x))
    | comp k x y hx hy h ihx ihy =>
      have hm := h C I
      change C.target k (x.eval C I.map) = C.source k (y.eval C I.map) at hm
      simp only [OAI.Thomason.OmegaCategory.CellTerm.dimension, OAI.Thomason.OmegaCategory.CellTerm.eval, OAI.Thomason.OmegaCategory.CellTerm.composeOrLeft, dite_eq_left hm]
      have hkn : k < max (k+1) (max (x.dimension P.dimension) (y.dimension P.dimension)) := by omega
      rw [C.source_comp_gt _ k hkn _ _ hm (proof_source_composable_97 C hkn hm)]
      congr 1
      · exact (proof_source_fixed_upwards_98 C (by omega) ihx)
      · exact (proof_source_fixed_upwards_98 C (by omega) ihy)
  exact {
    Cell := P.Cells
    source := P.source
    target := P.target
    comp := P.comp
    source_source i j x := by
      apply (proof_cells_ext_89 P)
      intro C I
      simp only [proof_evaluate_source_90, C.source_source]
    target_target i j x := by
      apply (proof_cells_ext_89 P)
      intro C I
      simp only [proof_evaluate_target_91, C.target_target]
    source_target i j x := by
      apply (proof_cells_ext_89 P)
      intro C I
      by_cases hij : i < j <;> simp [proof_evaluate_source_90, proof_evaluate_target_91, hij, C.source_target]
    target_source i j x := by
      apply (proof_cells_ext_89 P)
      intro C I
      by_cases hij : i < j <;> simp [proof_evaluate_source_90, proof_evaluate_target_91, hij, C.target_source]
    source_comp_le i k hik x y h := by
      apply (proof_cells_ext_89 P)
      intro C I
      simp only [proof_evaluate_source_90, proof_evaluate_comp_92]
      exact C.source_comp_le i k hik _ _ _
    target_comp_le i k hik x y h := by
      apply (proof_cells_ext_89 P)
      intro C I
      simp only [proof_evaluate_target_91, proof_evaluate_comp_92]
      exact C.target_comp_le i k hik _ _ _
    source_comp_gt i k hki x y h hs := by
      apply (proof_cells_ext_89 P)
      intro C I
      simp only [proof_evaluate_source_90, proof_evaluate_comp_92]
      exact C.source_comp_gt i k hki _ _ _ _
    target_comp_gt i k hki x y h hs := by
      apply (proof_cells_ext_89 P)
      intro C I
      simp only [proof_evaluate_target_91, proof_evaluate_comp_92]
      exact C.target_comp_gt i k hki _ _ _ _
    unit_left k x h := by
      apply (proof_cells_ext_89 P)
      intro C I
      simp only [proof_evaluate_source_90, proof_evaluate_comp_92]
      exact C.unit_left k _ _
    unit_right k x h := by
      apply (proof_cells_ext_89 P)
      intro C I
      simp only [proof_evaluate_target_91, proof_evaluate_comp_92]
      exact C.unit_right k _ _
    assoc k x y z hxy hyz hxy_z hx_yz := by
      apply (proof_cells_ext_89 P)
      intro C I
      simp only [proof_evaluate_comp_92]
      exact C.assoc k _ _ _ _ _ _ _
    interchange k l hkl a b c d hab hcd hac hbd hab_cd hac_bd := by
      apply (proof_cells_ext_89 P)
      intro C I
      simp only [proof_evaluate_comp_92]
      exact C.interchange k l hkl _ _ _ _ _ _ _ _ _ _
    finite_dimension x := by
      induction x using Quotient.inductionOn with | h x =>
        refine ⟨x.val.dimension P.dimension, ?_⟩
        apply (proof_cells_ext_89 P)
        intro C I
        exact (proof_eval_dimension_93 P (Subtype.property x) C I)
  }


end OAI.Thomason.OmegaCategory.Presentation
end

section
namespace OAI.Thomason.OmegaCategory
open CategoryTheory Limits
variable {J : Type u} [Category.{u} J]

noncomputable abbrev colimitPresentation (F : J ⥤ OAI.Thomason.OmegaCategory.{u}) : OAI.Thomason.OmegaCategory.Presentation.{u} where
  Generator := (j : J) × (F.obj j).Cell
  dimension g := Classical.choose ((F.obj g.1).finite_dimension g.2)
  relations C f := ∃ ι : ∀ j, OAI.Thomason.OmegaCategory.Functor (F.obj j) C,
    (∀ j x, f ⟨j, x⟩ = (ι j).map x) ∧
    (∀ ⦃j j'⦄ (a : j ⟶ j'), OAI.Thomason.OmegaCategory.Functor.comp (F.map a) (ι j') = ι j)


end OAI.Thomason.OmegaCategory
end

section
namespace OAI.Thomason.OmegaCategory.Presentation
variable (P : Presentation.{u})

noncomputable def generator (g : P.Generator) : P.Cells := Quotient.mk _ ⟨.gen g, .gen g⟩


end OAI.Thomason.OmegaCategory.Presentation
end

section
namespace OAI.Thomason.OmegaCategory
open CategoryTheory Limits
variable {J : Type u} [Category.{u} J]

noncomputable def colimitInclusion (F : J ⥤ OAI.Thomason.OmegaCategory.{u}) (j : J) :
    OAI.Thomason.OmegaCategory.Functor (F.obj j) (OAI.Thomason.OmegaCategory.colimitPresentation F).category := by
  classical
  have proof_cells_ext_89 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  {x y : P.Cells}
      (h : ∀ (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C), P.evaluate C I x = P.evaluate C I y) : x = y := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact Quotient.sound h
  have proof_evaluate_source_90 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ) (x : P.Cells) :
      P.evaluate C I (P.source k x) = C.source k (P.evaluate C I x) := by
    induction x using Quotient.inductionOn
    rfl
  have proof_evaluate_target_91 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ) (x : P.Cells) :
      P.evaluate C I (P.target k x) = C.target k (P.evaluate C I x) := by
    induction x using Quotient.inductionOn
    rfl
  have proof_evaluate_composable_94 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ)
      (x y : P.Cells) (h : P.target k x = P.source k y) :
      C.target k (P.evaluate C I x) = C.source k (P.evaluate C I y) := by
    rw [← proof_evaluate_target_91, ← proof_evaluate_source_90, h]
  have proof_evaluate_comp_92 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ)
      (x y : P.Cells) (h : P.target k x = P.source k y) :
      P.evaluate C I (P.comp k x y h) =
        C.comp k (P.evaluate C I x) (P.evaluate C I y) (proof_evaluate_composable_94 P C I k x y h) := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        have hm : P.Equiv (.target k x.val) (.source k y.val) := Quotient.exact h
        change (P.compTerm k x y).val.eval C I.map = _
        have hm' : C.target k (x.val.eval C I.map) = C.source k (y.val.eval C I.map) := hm C I
        simp only [OAI.Thomason.OmegaCategory.Presentation.compTerm, dite_eq_left hm, OAI.Thomason.OmegaCategory.CellTerm.eval, OAI.Thomason.OmegaCategory.CellTerm.composeOrLeft, dite_eq_left hm']
        rfl
  have proof_evaluate_generator_99  (P : OAI.Thomason.OmegaCategory.Presentation.{u}) (C : OAI.Thomason.OmegaCategory.{u})
      (I : P.Interpretation C) (g : P.Generator) : P.evaluate C I (P.generator g) = I.map g := rfl
  exact {
    map x := (OAI.Thomason.OmegaCategory.colimitPresentation F).generator ⟨j, x⟩
    map_source k x := by
      apply (proof_cells_ext_89 (OAI.Thomason.OmegaCategory.colimitPresentation F))
      intro C I
      rcases I.satisfies with ⟨ι, hi, _⟩
      simp only [proof_evaluate_source_90, proof_evaluate_generator_99, hi]
      exact (ι j).map_source k x
    map_target k x := by
      apply (proof_cells_ext_89 (OAI.Thomason.OmegaCategory.colimitPresentation F))
      intro C I
      rcases I.satisfies with ⟨ι, hi, _⟩
      simp only [proof_evaluate_target_91, proof_evaluate_generator_99, hi]
      exact (ι j).map_target k x
    map_comp k x y h h' := by
      apply (proof_cells_ext_89 (OAI.Thomason.OmegaCategory.colimitPresentation F))
      intro C I
      rcases I.satisfies with ⟨ι, hi, _⟩
      simp only [proof_evaluate_comp_92, proof_evaluate_generator_99, hi]
      exact (ι j).map_comp k x y h _
  }

noncomputable def presentedCocone (F : J ⥤ OAI.Thomason.OmegaCategory.{u}) : Cocone F := by
  classical
  have proof_cells_ext_89 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  {x y : P.Cells}
      (h : ∀ (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C), P.evaluate C I x = P.evaluate C I y) : x = y := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact Quotient.sound h
  exact {
    pt := (OAI.Thomason.OmegaCategory.colimitPresentation F).category
    ι := {
      app := OAI.Thomason.OmegaCategory.colimitInclusion F
      naturality := by
        intro j j' a
        apply OAI.Thomason.OmegaCategory.Functor.ext
        funext x
        apply (proof_cells_ext_89 (OAI.Thomason.OmegaCategory.colimitPresentation F))
        intro C I
        rcases I.satisfies with ⟨ι, hi, hw⟩
        change I.map ⟨j', (F.map a).map x⟩ = I.map ⟨j, x⟩
        rw [hi, hi]
        exact congrArg (fun h : OAI.Thomason.OmegaCategory.Functor (F.obj j) C => h.map x) (hw a) }
  }


end OAI.Thomason.OmegaCategory
end

section
namespace OAI.Thomason.OmegaCategory.Presentation
variable (P : Presentation.{u})

noncomputable def lift (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) : OAI.Thomason.OmegaCategory.Functor P.category C := by
  classical
  have proof_evaluate_source_90 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ) (x : P.Cells) :
      P.evaluate C I (P.source k x) = C.source k (P.evaluate C I x) := by
    induction x using Quotient.inductionOn
    rfl
  have proof_evaluate_target_91 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ) (x : P.Cells) :
      P.evaluate C I (P.target k x) = C.target k (P.evaluate C I x) := by
    induction x using Quotient.inductionOn
    rfl
  have proof_evaluate_composable_94 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ)
      (x y : P.Cells) (h : P.target k x = P.source k y) :
      C.target k (P.evaluate C I x) = C.source k (P.evaluate C I y) := by
    rw [← proof_evaluate_target_91, ← proof_evaluate_source_90, h]
  have proof_evaluate_comp_92 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ)
      (x y : P.Cells) (h : P.target k x = P.source k y) :
      P.evaluate C I (P.comp k x y h) =
        C.comp k (P.evaluate C I x) (P.evaluate C I y) (proof_evaluate_composable_94 P C I k x y h) := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        have hm : P.Equiv (.target k x.val) (.source k y.val) := Quotient.exact h
        change (P.compTerm k x y).val.eval C I.map = _
        have hm' : C.target k (x.val.eval C I.map) = C.source k (y.val.eval C I.map) := hm C I
        simp only [OAI.Thomason.OmegaCategory.Presentation.compTerm, dite_eq_left hm, OAI.Thomason.OmegaCategory.CellTerm.eval, OAI.Thomason.OmegaCategory.CellTerm.composeOrLeft, dite_eq_left hm']
        rfl
  exact {
    map := P.evaluate C I
    map_source := (proof_evaluate_source_90 P C I)
    map_target := (proof_evaluate_target_91 P C I)
    map_comp k x y h _ := (proof_evaluate_comp_92 P C I k x y h)
  }


end OAI.Thomason.OmegaCategory.Presentation
end

section
namespace OAI.Thomason.OmegaCategory
open CategoryTheory Limits
variable {J : Type u} [Category.{u} J]

noncomputable def colimitInterpretation (F : J ⥤ OAI.Thomason.OmegaCategory.{u}) (s : Cocone F) :
    (OAI.Thomason.OmegaCategory.colimitPresentation F).Interpretation s.pt where
  map g := (s.ι.app g.1).map g.2
  bounded g := by
    exact ((s.ι.app g.1).map_source _ g.2).symm.trans
      (congrArg (s.ι.app g.1).map (Classical.choose_spec ((F.obj g.1).finite_dimension g.2)))
  satisfies := ⟨fun j => s.ι.app j, fun _ _ => rfl, fun {_ _} a => s.w a⟩

noncomputable def presentedCoconeIsColimit (F : J ⥤ OAI.Thomason.OmegaCategory.{u}) :
    IsColimit (OAI.Thomason.OmegaCategory.presentedCocone F) := by
  classical
  have proof_mk_comp_101 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (k : ℕ) (x y : P.ValidTerm)
      (h : P.Equiv (.target k x.val) (.source k y.val))
      (h' : P.target k (Quotient.mk _ x) = P.source k (Quotient.mk _ y)) :
      P.comp k (Quotient.mk _ x) (Quotient.mk _ y) h' =
        Quotient.mk _ ⟨.comp k x.val y.val, OAI.Thomason.OmegaCategory.Presentation.Valid.comp (P := P) k x.val y.val x.property y.property h⟩ := by
    change Quotient.mk _ (P.compTerm k x y) = _
    simp only [OAI.Thomason.OmegaCategory.Presentation.compTerm, dite_eq_left h]
  have proof_map_composable_102 {C : OAI.Thomason.OmegaCategory.{u}} {D : OAI.Thomason.OmegaCategory.{u}}  (F : OAI.Thomason.OmegaCategory.Functor C D) {k : ℕ} {x y : C.Cell}
      (h : C.target k x = C.source k y) :
      D.target k (F.map x) = D.source k (F.map y) := by
    rw [← F.map_target, ← F.map_source, h]
  have proof_functor_ext_100 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  {C : OAI.Thomason.OmegaCategory.{u}} {F G : OAI.Thomason.OmegaCategory.Functor P.category C}
      (h : ∀ g, F.map (P.generator g) = G.map (P.generator g)) : F = G := by
    apply OAI.Thomason.OmegaCategory.Functor.ext
    funext x
    induction x using Quotient.inductionOn with | h x =>
      rcases x with ⟨x, hx⟩
      induction hx with
      | gen g => exact h g
      | source k x hx ih =>
        change F.map (P.category.source k (Quotient.mk _ ⟨x, hx⟩)) =
          G.map (P.category.source k (Quotient.mk _ ⟨x, hx⟩))
        rw [F.map_source, G.map_source, ih]
      | target k x hx ih =>
        change F.map (P.category.target k (Quotient.mk _ ⟨x, hx⟩)) =
          G.map (P.category.target k (Quotient.mk _ ⟨x, hx⟩))
        rw [F.map_target, G.map_target, ih]
      | comp k x y hx hy hm ihx ihy =>
        have hc : P.category.target k (Quotient.mk _ ⟨x, hx⟩) =
            P.category.source k (Quotient.mk _ ⟨y, hy⟩) := Quotient.sound hm
        rw [← (proof_mk_comp_101 P k ⟨x, hx⟩ ⟨y, hy⟩ hm hc)]
        change F.map (P.category.comp k _ _ hc) = G.map (P.category.comp k _ _ hc)
        rw [F.map_comp k _ _ hc (proof_map_composable_102 F hc), G.map_comp k _ _ hc (proof_map_composable_102 G hc)]
        congr 1
  exact {
    desc s := (OAI.Thomason.OmegaCategory.colimitPresentation F).lift s.pt (OAI.Thomason.OmegaCategory.colimitInterpretation F s)
    fac s j := by
      apply OAI.Thomason.OmegaCategory.Functor.ext
      funext x
      rfl
    uniq s m hm := by
      apply (proof_functor_ext_100 (OAI.Thomason.OmegaCategory.colimitPresentation F))
      intro ⟨j, x⟩
      exact congrArg (fun f : OAI.Thomason.OmegaCategory.Functor (F.obj j) s.pt => f.map x) (hm j)
  }

noncomputable instance hasColimits : HasColimitsOfSize.{u,u} OAI.Thomason.OmegaCategory.{u} where
  has_colimits_of_shape := fun _ _ => { has_colimit := fun F => ⟨⟨OAI.Thomason.OmegaCategory.presentedCocone F, OAI.Thomason.OmegaCategory.presentedCoconeIsColimit F⟩⟩ }


end OAI.Thomason.OmegaCategory
end

section
namespace OAI.Thomason
open CategoryTheory Opposite

noncomputable instance omegaHasSimplicialColimits :
    Limits.HasColimitsOfSize.{0,u} OAI.Thomason.OmegaCategory.{u} :=
  Limits.hasColimitsOfSizeShrink.{0,u} OAI.Thomason.OmegaCategory.{u}

noncomputable def categorification : SSet.{u} ⥤ OAI.Thomason.OmegaCategory.{u} :=
  (uliftYoneda.{u} : SimplexCategory ⥤ (SimplexCategoryᵒᵖ ⥤ Type u)).leftKanExtension OAI.Thomason.raisedOrientals.{u}


end OAI.Thomason
end

section
namespace OAI.Thomason
open CategoryTheory

noncomputable def thomasonLeft : SSet.{u} ⥤ OAI.Thomason.OmegaCategory.{u} :=
  (SSet.sd ⋙ SSet.sd) ⋙ OAI.Thomason.categorification


end OAI.Thomason
end

section
namespace OAI.Thomason
open CategoryTheory Opposite

noncomputable def streetNerve (C : OAI.Thomason.OmegaCategory.{u}) : SSet.{u} where
  obj m := OAI.Thomason.OmegaCategory.Functor (OAI.Thomason.orientals.obj m.unop) C
  map f := ↾fun x => OAI.Thomason.OmegaCategory.Functor.comp (OAI.Thomason.orientals.map f.unop) x
  map_id m := by
    apply ConcreteCategory.hom_ext
    intro x
    change OAI.Thomason.OmegaCategory.Functor.comp (OAI.Thomason.orientals.map (𝟙 m.unop)) x = x
    rw [OAI.Thomason.orientals.map_id]
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    change OAI.Thomason.OmegaCategory.Functor.comp (OAI.Thomason.orientals.map (g.unop ≫ f.unop)) x =
      OAI.Thomason.OmegaCategory.Functor.comp (OAI.Thomason.orientals.map g.unop)
        (OAI.Thomason.OmegaCategory.Functor.comp (OAI.Thomason.orientals.map f.unop) x)
    rw [OAI.Thomason.orientals.map_comp]
    rfl

noncomputable def streetNerveMap {C D : OAI.Thomason.OmegaCategory.{u}} (F : OAI.Thomason.OmegaCategory.Functor C D) :
    OAI.Thomason.streetNerve C ⟶ OAI.Thomason.streetNerve D where
  app _ := ↾fun x => OAI.Thomason.OmegaCategory.Functor.comp x F
  naturality _ _ _ := rfl

noncomputable def streetNerveFunctor : OAI.Thomason.OmegaCategory.{u} ⥤ SSet.{u} where
  obj := OAI.Thomason.streetNerve
  map := OAI.Thomason.streetNerveMap


end OAI.Thomason
end

section
namespace OAI.Thomason
open CategoryTheory

noncomputable def thomasonRight : OAI.Thomason.OmegaCategory.{u} ⥤ SSet.{u} :=
  OAI.Thomason.streetNerveFunctor ⋙ (SSet.ex ⋙ SSet.ex)


end OAI.Thomason
end

section
namespace OAI.Thomason
open CategoryTheory Opposite

noncomputable def streetYonedaEquiv (C : OAI.Thomason.OmegaCategory.{u}) (m : SimplexCategoryᵒᵖ) :
    ((Presheaf.restrictedULiftYoneda.{0} OAI.Thomason.raisedOrientals).obj C).obj m ≃
      (OAI.Thomason.streetNerve C).obj m where
  toFun F := OAI.Thomason.OmegaCategory.Functor.comp (OAI.Thomason.OmegaCategory.uliftUp _) F.down
  invFun F := ULift.up (OAI.Thomason.OmegaCategory.Functor.comp (OAI.Thomason.OmegaCategory.uliftDown _) F)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def streetYonedaIso : Presheaf.restrictedULiftYoneda.{0} OAI.Thomason.raisedOrientals.{u} ≅
    OAI.Thomason.streetNerveFunctor.{u} :=
  NatIso.ofComponents (fun C =>
    NatIso.ofComponents (fun m => (OAI.Thomason.streetYonedaEquiv C m).toIso) (by intros; rfl))
      (by intros; rfl)

noncomputable def categorificationAdjunction : OAI.Thomason.categorification.{u} ⊣ OAI.Thomason.streetNerveFunctor.{u} :=
  (Presheaf.uliftYonedaAdjunction.{0}
    ((uliftYoneda.{u} : SimplexCategory ⥤ (SimplexCategoryᵒᵖ ⥤ Type u)).leftKanExtension OAI.Thomason.raisedOrientals.{u})
    ((uliftYoneda.{u} : SimplexCategory ⥤ (SimplexCategoryᵒᵖ ⥤ Type u)).leftKanExtensionUnit OAI.Thomason.raisedOrientals.{u})).ofNatIsoRight OAI.Thomason.streetYonedaIso


end OAI.Thomason
end

section
namespace OAI.Thomason
open CategoryTheory

noncomputable def thomasonAdjunction : OAI.Thomason.thomasonLeft.{u} ⊣ OAI.Thomason.thomasonRight.{u} :=
  (SSet.sdExAdjunction.comp SSet.sdExAdjunction).comp OAI.Thomason.categorificationAdjunction


end OAI.Thomason
end

section
namespace OAI.Thomason.OmegaCategory


noncomputable abbrev truncationPresentation (n : ℕ) (C : OAI.Thomason.OmegaCategory.{u}) : OAI.Thomason.OmegaCategory.Presentation.{u} where
  Generator := C.Cell
  dimension _ := n
  relations D f := D.IsTruncated n ∧ ∃ F : OAI.Thomason.OmegaCategory.Functor C D, f = F.map

noncomputable def truncationUnit (n : ℕ) (C : OAI.Thomason.OmegaCategory.{u}) :
    OAI.Thomason.OmegaCategory.Functor C (OAI.Thomason.OmegaCategory.truncationPresentation n C).category := by
  classical
  have proof_cells_ext_89 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  {x y : P.Cells}
      (h : ∀ (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C), P.evaluate C I x = P.evaluate C I y) : x = y := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact Quotient.sound h
  have proof_evaluate_source_90 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ) (x : P.Cells) :
      P.evaluate C I (P.source k x) = C.source k (P.evaluate C I x) := by
    induction x using Quotient.inductionOn
    rfl
  have proof_evaluate_target_91 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ) (x : P.Cells) :
      P.evaluate C I (P.target k x) = C.target k (P.evaluate C I x) := by
    induction x using Quotient.inductionOn
    rfl
  have proof_evaluate_composable_94 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ)
      (x y : P.Cells) (h : P.target k x = P.source k y) :
      C.target k (P.evaluate C I x) = C.source k (P.evaluate C I y) := by
    rw [← proof_evaluate_target_91, ← proof_evaluate_source_90, h]
  have proof_evaluate_comp_92 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ)
      (x y : P.Cells) (h : P.target k x = P.source k y) :
      P.evaluate C I (P.comp k x y h) =
        C.comp k (P.evaluate C I x) (P.evaluate C I y) (proof_evaluate_composable_94 P C I k x y h) := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        have hm : P.Equiv (.target k x.val) (.source k y.val) := Quotient.exact h
        change (P.compTerm k x y).val.eval C I.map = _
        have hm' : C.target k (x.val.eval C I.map) = C.source k (y.val.eval C I.map) := hm C I
        simp only [OAI.Thomason.OmegaCategory.Presentation.compTerm, dite_eq_left hm, OAI.Thomason.OmegaCategory.CellTerm.eval, OAI.Thomason.OmegaCategory.CellTerm.composeOrLeft, dite_eq_left hm']
        rfl
  have proof_evaluate_generator_99  (P : OAI.Thomason.OmegaCategory.Presentation.{u}) (C : OAI.Thomason.OmegaCategory.{u})
      (I : P.Interpretation C) (g : P.Generator) : P.evaluate C I (P.generator g) = I.map g := rfl
  exact {
    map := (OAI.Thomason.OmegaCategory.truncationPresentation n C).generator
    map_source k x := by
      apply (proof_cells_ext_89 (OAI.Thomason.OmegaCategory.truncationPresentation n C))
      intro D I
      rcases I.satisfies with ⟨_, F, hF⟩
      simp only [proof_evaluate_source_90, proof_evaluate_generator_99, hF]
      exact F.map_source k x
    map_target k x := by
      apply (proof_cells_ext_89 (OAI.Thomason.OmegaCategory.truncationPresentation n C))
      intro D I
      rcases I.satisfies with ⟨_, F, hF⟩
      simp only [proof_evaluate_target_91, proof_evaluate_generator_99, hF]
      exact F.map_target k x
    map_comp k x y h h' := by
      apply (proof_cells_ext_89 (OAI.Thomason.OmegaCategory.truncationPresentation n C))
      intro D I
      rcases I.satisfies with ⟨_, F, hF⟩
      simp only [proof_evaluate_comp_92, proof_evaluate_generator_99, hF]
      exact F.map_comp k x y h _
  }

noncomputable def truncation (n : ℕ) (C : OAI.Thomason.OmegaCategory.{u}) : OAI.Thomason.OmegaCategory.NCategory.{u} n := by
  classical
  have proof_cells_ext_89 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  {x y : P.Cells}
      (h : ∀ (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C), P.evaluate C I x = P.evaluate C I y) : x = y := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact Quotient.sound h
  have proof_evaluate_source_90 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (C : OAI.Thomason.OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ) (x : P.Cells) :
      P.evaluate C I (P.source k x) = C.source k (P.evaluate C I x) := by
    induction x using Quotient.inductionOn
    rfl
  have proof_truncation_isTruncated_103  (n : ℕ) (C : OAI.Thomason.OmegaCategory.{u}) :
      (OAI.Thomason.OmegaCategory.truncationPresentation n C).category.IsTruncated n := by
    intro x
    apply (proof_cells_ext_89 (OAI.Thomason.OmegaCategory.truncationPresentation n C))
    intro D I
    rw [proof_evaluate_source_90]
    exact I.satisfies.1 _
  exact
    ⟨(OAI.Thomason.OmegaCategory.truncationPresentation n C).category, proof_truncation_isTruncated_103 n C⟩

noncomputable def truncationLift {n : ℕ} {C : OAI.Thomason.OmegaCategory.{u}} (D : OAI.Thomason.OmegaCategory.NCategory.{u} n)
    (F : OAI.Thomason.OmegaCategory.Functor C D.val) : OAI.Thomason.OmegaCategory.Functor (OAI.Thomason.OmegaCategory.truncation n C).val D.val :=
  (OAI.Thomason.OmegaCategory.truncationPresentation n C).lift D.val {
    map := F.map
    bounded := fun x => D.property (F.map x)
    satisfies := ⟨D.property, F, rfl⟩ }


end OAI.Thomason.OmegaCategory
end

section
namespace OAI.Thomason.OmegaCategory
open CategoryTheory

noncomputable def truncationFunctor (n : ℕ) : OAI.Thomason.OmegaCategory.{u} ⥤ OAI.Thomason.OmegaCategory.NCategory.{u} n := by
  classical
  have proof_mk_comp_101 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (k : ℕ) (x y : P.ValidTerm)
      (h : P.Equiv (.target k x.val) (.source k y.val))
      (h' : P.target k (Quotient.mk _ x) = P.source k (Quotient.mk _ y)) :
      P.comp k (Quotient.mk _ x) (Quotient.mk _ y) h' =
        Quotient.mk _ ⟨.comp k x.val y.val, OAI.Thomason.OmegaCategory.Presentation.Valid.comp (P := P) k x.val y.val x.property y.property h⟩ := by
    change Quotient.mk _ (P.compTerm k x y) = _
    simp only [OAI.Thomason.OmegaCategory.Presentation.compTerm, dite_eq_left h]
  have proof_map_composable_102 {C : OAI.Thomason.OmegaCategory.{u}} {D : OAI.Thomason.OmegaCategory.{u}}  (F : OAI.Thomason.OmegaCategory.Functor C D) {k : ℕ} {x y : C.Cell}
      (h : C.target k x = C.source k y) :
      D.target k (F.map x) = D.source k (F.map y) := by
    rw [← F.map_target, ← F.map_source, h]
  have proof_functor_ext_100 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  {C : OAI.Thomason.OmegaCategory.{u}} {F G : OAI.Thomason.OmegaCategory.Functor P.category C}
      (h : ∀ g, F.map (P.generator g) = G.map (P.generator g)) : F = G := by
    apply OAI.Thomason.OmegaCategory.Functor.ext
    funext x
    induction x using Quotient.inductionOn with | h x =>
      rcases x with ⟨x, hx⟩
      induction hx with
      | gen g => exact h g
      | source k x hx ih =>
        change F.map (P.category.source k (Quotient.mk _ ⟨x, hx⟩)) =
          G.map (P.category.source k (Quotient.mk _ ⟨x, hx⟩))
        rw [F.map_source, G.map_source, ih]
      | target k x hx ih =>
        change F.map (P.category.target k (Quotient.mk _ ⟨x, hx⟩)) =
          G.map (P.category.target k (Quotient.mk _ ⟨x, hx⟩))
        rw [F.map_target, G.map_target, ih]
      | comp k x y hx hy hm ihx ihy =>
        have hc : P.category.target k (Quotient.mk _ ⟨x, hx⟩) =
            P.category.source k (Quotient.mk _ ⟨y, hy⟩) := Quotient.sound hm
        rw [← (proof_mk_comp_101 P k ⟨x, hx⟩ ⟨y, hy⟩ hm hc)]
        change F.map (P.category.comp k _ _ hc) = G.map (P.category.comp k _ _ hc)
        rw [F.map_comp k _ _ hc (proof_map_composable_102 F hc), G.map_comp k _ _ hc (proof_map_composable_102 G hc)]
        congr 1
  have proof_truncation_functor_ext_104  {n : ℕ} {C D : OAI.Thomason.OmegaCategory.{u}}
      {F G : OAI.Thomason.OmegaCategory.Functor (OAI.Thomason.OmegaCategory.truncation n C).val D}
      (h : OAI.Thomason.OmegaCategory.Functor.comp (OAI.Thomason.OmegaCategory.truncationUnit n C) F = OAI.Thomason.OmegaCategory.Functor.comp (OAI.Thomason.OmegaCategory.truncationUnit n C) G) : F = G := by
    apply (proof_functor_ext_100 (OAI.Thomason.OmegaCategory.truncationPresentation n C))
    intro x
    exact congrArg (fun H : OAI.Thomason.OmegaCategory.Functor C D => H.map x) h
  exact {
    obj := OAI.Thomason.OmegaCategory.truncation n
    map {C D} F := OAI.Thomason.OmegaCategory.truncationLift (OAI.Thomason.OmegaCategory.truncation n D) (OAI.Thomason.OmegaCategory.Functor.comp F (OAI.Thomason.OmegaCategory.truncationUnit n D))
    map_id C := by
      apply proof_truncation_functor_ext_104
      rfl
    map_comp F G := by
      apply proof_truncation_functor_ext_104
      rfl
  }


end OAI.Thomason.OmegaCategory
end

section
namespace OAI.Thomason
open CategoryTheory Opposite

noncomputable def categorificationFinite (n : ℕ) : SSet.{u} ⥤ OAI.Thomason.OmegaCategory.NCategory.{u} n :=
  OAI.Thomason.categorification ⋙ OAI.Thomason.OmegaCategory.truncationFunctor n


end OAI.Thomason
end

section
namespace OAI.Thomason
open CategoryTheory

noncomputable def thomasonLeftFinite (n : ℕ) : SSet.{u} ⥤ OAI.Thomason.OmegaCategory.NCategory.{u} n :=
  (SSet.sd ⋙ SSet.sd) ⋙ OAI.Thomason.categorificationFinite n


end OAI.Thomason
end

section
namespace OAI.Thomason
open CategoryTheory Opposite

noncomputable def streetNerveFinite (n : ℕ) : OAI.Thomason.OmegaCategory.NCategory.{u} n ⥤ SSet.{u} where
  obj C := OAI.Thomason.streetNerve C.val
  map := OAI.Thomason.streetNerveMap


end OAI.Thomason
end

section
namespace OAI.Thomason
open CategoryTheory

noncomputable def thomasonRightFinite (n : ℕ) : OAI.Thomason.OmegaCategory.NCategory.{u} n ⥤ SSet.{u} :=
  OAI.Thomason.streetNerveFinite n ⋙ (SSet.ex ⋙ SSet.ex)


end OAI.Thomason
end

section
namespace OAI.Thomason.OmegaCategory
open CategoryTheory

noncomputable def nCategoryInclusion (n : ℕ) : OAI.Thomason.OmegaCategory.NCategory.{u} n ⥤ OAI.Thomason.OmegaCategory.{u} where
  obj C := C.val
  map F := F

noncomputable def truncationHomEquiv (n : ℕ) (C : OAI.Thomason.OmegaCategory.{u}) (D : OAI.Thomason.OmegaCategory.NCategory.{u} n) :
    ((OAI.Thomason.OmegaCategory.truncationFunctor n).obj C ⟶ D) ≃ (C ⟶ (OAI.Thomason.OmegaCategory.nCategoryInclusion n).obj D) := by
  classical
  have proof_mk_comp_101 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (k : ℕ) (x y : P.ValidTerm)
      (h : P.Equiv (.target k x.val) (.source k y.val))
      (h' : P.target k (Quotient.mk _ x) = P.source k (Quotient.mk _ y)) :
      P.comp k (Quotient.mk _ x) (Quotient.mk _ y) h' =
        Quotient.mk _ ⟨.comp k x.val y.val, OAI.Thomason.OmegaCategory.Presentation.Valid.comp (P := P) k x.val y.val x.property y.property h⟩ := by
    change Quotient.mk _ (P.compTerm k x y) = _
    simp only [OAI.Thomason.OmegaCategory.Presentation.compTerm, dite_eq_left h]
  have proof_map_composable_102 {C : OAI.Thomason.OmegaCategory.{u}} {D : OAI.Thomason.OmegaCategory.{u}}  (F : OAI.Thomason.OmegaCategory.Functor C D) {k : ℕ} {x y : C.Cell}
      (h : C.target k x = C.source k y) :
      D.target k (F.map x) = D.source k (F.map y) := by
    rw [← F.map_target, ← F.map_source, h]
  have proof_functor_ext_100 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  {C : OAI.Thomason.OmegaCategory.{u}} {F G : OAI.Thomason.OmegaCategory.Functor P.category C}
      (h : ∀ g, F.map (P.generator g) = G.map (P.generator g)) : F = G := by
    apply OAI.Thomason.OmegaCategory.Functor.ext
    funext x
    induction x using Quotient.inductionOn with | h x =>
      rcases x with ⟨x, hx⟩
      induction hx with
      | gen g => exact h g
      | source k x hx ih =>
        change F.map (P.category.source k (Quotient.mk _ ⟨x, hx⟩)) =
          G.map (P.category.source k (Quotient.mk _ ⟨x, hx⟩))
        rw [F.map_source, G.map_source, ih]
      | target k x hx ih =>
        change F.map (P.category.target k (Quotient.mk _ ⟨x, hx⟩)) =
          G.map (P.category.target k (Quotient.mk _ ⟨x, hx⟩))
        rw [F.map_target, G.map_target, ih]
      | comp k x y hx hy hm ihx ihy =>
        have hc : P.category.target k (Quotient.mk _ ⟨x, hx⟩) =
            P.category.source k (Quotient.mk _ ⟨y, hy⟩) := Quotient.sound hm
        rw [← (proof_mk_comp_101 P k ⟨x, hx⟩ ⟨y, hy⟩ hm hc)]
        change F.map (P.category.comp k _ _ hc) = G.map (P.category.comp k _ _ hc)
        rw [F.map_comp k _ _ hc (proof_map_composable_102 F hc), G.map_comp k _ _ hc (proof_map_composable_102 G hc)]
        congr 1
  have proof_truncation_functor_ext_104  {n : ℕ} {C D : OAI.Thomason.OmegaCategory.{u}}
      {F G : OAI.Thomason.OmegaCategory.Functor (OAI.Thomason.OmegaCategory.truncation n C).val D}
      (h : OAI.Thomason.OmegaCategory.Functor.comp (OAI.Thomason.OmegaCategory.truncationUnit n C) F = OAI.Thomason.OmegaCategory.Functor.comp (OAI.Thomason.OmegaCategory.truncationUnit n C) G) : F = G := by
    apply (proof_functor_ext_100 (OAI.Thomason.OmegaCategory.truncationPresentation n C))
    intro x
    exact congrArg (fun H : OAI.Thomason.OmegaCategory.Functor C D => H.map x) h
  exact {
    toFun F := OAI.Thomason.OmegaCategory.Functor.comp (OAI.Thomason.OmegaCategory.truncationUnit n C) F
    invFun := OAI.Thomason.OmegaCategory.truncationLift D
    left_inv F := by
      apply proof_truncation_functor_ext_104
      rfl
    right_inv _ := rfl
  }

noncomputable def truncationAdjunction (n : ℕ) : OAI.Thomason.OmegaCategory.truncationFunctor.{u} n ⊣ OAI.Thomason.OmegaCategory.nCategoryInclusion n := by
  classical
  have proof_mk_comp_101 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  (k : ℕ) (x y : P.ValidTerm)
      (h : P.Equiv (.target k x.val) (.source k y.val))
      (h' : P.target k (Quotient.mk _ x) = P.source k (Quotient.mk _ y)) :
      P.comp k (Quotient.mk _ x) (Quotient.mk _ y) h' =
        Quotient.mk _ ⟨.comp k x.val y.val, OAI.Thomason.OmegaCategory.Presentation.Valid.comp (P := P) k x.val y.val x.property y.property h⟩ := by
    change Quotient.mk _ (P.compTerm k x y) = _
    simp only [OAI.Thomason.OmegaCategory.Presentation.compTerm, dite_eq_left h]
  have proof_map_composable_102 {C : OAI.Thomason.OmegaCategory.{u}} {D : OAI.Thomason.OmegaCategory.{u}}  (F : OAI.Thomason.OmegaCategory.Functor C D) {k : ℕ} {x y : C.Cell}
      (h : C.target k x = C.source k y) :
      D.target k (F.map x) = D.source k (F.map y) := by
    rw [← F.map_target, ← F.map_source, h]
  have proof_functor_ext_100 (P : OAI.Thomason.OmegaCategory.Presentation.{u})  {C : OAI.Thomason.OmegaCategory.{u}} {F G : OAI.Thomason.OmegaCategory.Functor P.category C}
      (h : ∀ g, F.map (P.generator g) = G.map (P.generator g)) : F = G := by
    apply OAI.Thomason.OmegaCategory.Functor.ext
    funext x
    induction x using Quotient.inductionOn with | h x =>
      rcases x with ⟨x, hx⟩
      induction hx with
      | gen g => exact h g
      | source k x hx ih =>
        change F.map (P.category.source k (Quotient.mk _ ⟨x, hx⟩)) =
          G.map (P.category.source k (Quotient.mk _ ⟨x, hx⟩))
        rw [F.map_source, G.map_source, ih]
      | target k x hx ih =>
        change F.map (P.category.target k (Quotient.mk _ ⟨x, hx⟩)) =
          G.map (P.category.target k (Quotient.mk _ ⟨x, hx⟩))
        rw [F.map_target, G.map_target, ih]
      | comp k x y hx hy hm ihx ihy =>
        have hc : P.category.target k (Quotient.mk _ ⟨x, hx⟩) =
            P.category.source k (Quotient.mk _ ⟨y, hy⟩) := Quotient.sound hm
        rw [← (proof_mk_comp_101 P k ⟨x, hx⟩ ⟨y, hy⟩ hm hc)]
        change F.map (P.category.comp k _ _ hc) = G.map (P.category.comp k _ _ hc)
        rw [F.map_comp k _ _ hc (proof_map_composable_102 F hc), G.map_comp k _ _ hc (proof_map_composable_102 G hc)]
        congr 1
  have proof_truncation_functor_ext_104  {n : ℕ} {C D : OAI.Thomason.OmegaCategory.{u}}
      {F G : OAI.Thomason.OmegaCategory.Functor (OAI.Thomason.OmegaCategory.truncation n C).val D}
      (h : OAI.Thomason.OmegaCategory.Functor.comp (OAI.Thomason.OmegaCategory.truncationUnit n C) F = OAI.Thomason.OmegaCategory.Functor.comp (OAI.Thomason.OmegaCategory.truncationUnit n C) G) : F = G := by
    apply (proof_functor_ext_100 (OAI.Thomason.OmegaCategory.truncationPresentation n C))
    intro x
    exact congrArg (fun H : OAI.Thomason.OmegaCategory.Functor C D => H.map x) h
  exact
    Adjunction.mkOfHomEquiv {
        homEquiv := OAI.Thomason.OmegaCategory.truncationHomEquiv n
        homEquiv_naturality_left_symm := by
          intro C' C D F G
          apply proof_truncation_functor_ext_104
          rfl
        homEquiv_naturality_right := by
          intro C D D' F G
          rfl }


end OAI.Thomason.OmegaCategory
end

section
namespace OAI.Thomason
open CategoryTheory Opposite

noncomputable def categorificationFiniteAdjunction (n : ℕ) :
    OAI.Thomason.categorificationFinite.{u} n ⊣ OAI.Thomason.streetNerveFinite.{u} n :=
  OAI.Thomason.categorificationAdjunction.comp (OAI.Thomason.OmegaCategory.truncationAdjunction n)


end OAI.Thomason
end

section
namespace OAI.Thomason
open CategoryTheory

noncomputable def thomasonFiniteAdjunction (n : ℕ) :
    OAI.Thomason.thomasonLeftFinite.{u} n ⊣ OAI.Thomason.thomasonRightFinite.{u} n :=
  (SSet.sdExAdjunction.comp SSet.sdExAdjunction).comp (OAI.Thomason.categorificationFiniteAdjunction n)


end OAI.Thomason
end

section
namespace OAI.Thomason.WeakHomotopy
open scoped Topology Topology.Homotopy
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def loopMap (N : Type w) (f : C(X, Y)) (x : X) : GenLoop N X x → GenLoop N Y (f x) :=
  fun p => ⟨f.comp p.val, fun y hy => congrArg f (p.property y hy)⟩

noncomputable def groupMap (N : Type w) (f : C(X, Y)) (x : X) :
    HomotopyGroup N X x → HomotopyGroup N Y (f x) := by
  classical
  have proof_loopMap_homotopic_105 {X : Type u} {Y : Type v} [instLocal2 : TopologicalSpace.{u} X] [instLocal3 : TopologicalSpace.{v} Y]  (N : Type w) (f : C(X, Y)) (x : X)
      {p q : GenLoop N X x} (h : GenLoop.Homotopic p q) :
      GenLoop.Homotopic (OAI.Thomason.WeakHomotopy.loopMap N f x p) (OAI.Thomason.WeakHomotopy.loopMap N f x q) :=
    h.comp_continuousMap f
  exact
    Quotient.map (OAI.Thomason.WeakHomotopy.loopMap N f x) (fun _ _ h => proof_loopMap_homotopic_105 N f x h)

noncomputable def componentsMap (f : C(X, Y)) : ZerothHomotopy X → ZerothHomotopy Y :=
  ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (f x))
    (fun _ _ p => ZerothHomotopy.sound (p.map f.continuous))

noncomputable def Equivalence (f : C(X, Y)) : Prop :=
  Function.Bijective (OAI.Thomason.WeakHomotopy.componentsMap f) ∧
    ∀ (n : ℕ) (x : X), Function.Bijective (OAI.Thomason.WeakHomotopy.groupMap (Fin (n+1)) f x)


end OAI.Thomason.WeakHomotopy
end

section
namespace OAI.Thomason
open CategoryTheory

noncomputable def simplicialWeakEquivalences : MorphismProperty SSet.{u} :=
  fun _ _ f => OAI.Thomason.WeakHomotopy.Equivalence (SSet.toTop.map f).hom

noncomputable def simplicialFibrations : MorphismProperty SSet.{u} := (SSet.modelCategoryQuillen.J).rlp


end OAI.Thomason
end

section
namespace OAI.Thomason
open CategoryTheory Limits HomotopicalAlgebra

structure KanQuillenModel where
  model : ModelCategory SSet.{u}
  weak_eq : model.categoryWithWeakEquivalences.weakEquivalences = OAI.Thomason.simplicialWeakEquivalences
  fib_eq : model.categoryWithFibrations.fibrations = OAI.Thomason.simplicialFibrations
  cof_eq : model.categoryWithCofibrations.cofibrations = MorphismProperty.monomorphisms SSet

noncomputable def LeftProperFor {C : Type v} [Category.{u} C]
    (W Cof : MorphismProperty C) : Prop :=
  ∀ {A B X Y : C} (i : A ⟶ B) (f : A ⟶ X) (g : B ⟶ Y) (j : X ⟶ Y),
    IsPushout i f g j → Cof i → W f → W g

noncomputable def RightProperFor {C : Type v} [Category.{u} C]
    (W Fib : MorphismProperty C) : Prop :=
  ∀ {A B X Y : C} (f : A ⟶ B) (g : A ⟶ X) (p : B ⟶ Y) (q : X ⟶ Y),
    IsPullback f g p q → Fib q → W p → W g

noncomputable def FibrantFor {C : Type v} [Category.{u} C] (Fib : MorphismProperty C) (Y : C) : Prop :=
  ∃ (T : C) (_ : IsTerminal T) (p : Y ⟶ T), Fib p

noncomputable def boundaryImages {C : Type v} [Category.{u} C] (L : SSet.{u} ⥤ C) : MorphismProperty C :=
  .ofHoms (fun n : ℕ => L.map (SSet.boundary n).ι)

noncomputable def hornImages {C : Type v} [Category.{u} C] (L : SSet.{u} ⥤ C) : MorphismProperty C :=
  ⨆ n : ℕ, .ofHoms (fun i : Fin (n+2) => L.map (SSet.horn (n+1) i).ι)

structure ExactModelEndpoint {C : Type v} [Category.{u} C]
    (L : SSet.{u} ⥤ C) (R : C ⥤ SSet.{u}) (adj : L ⊣ R) where
  model : ModelCategory C
  weak_eq : model.categoryWithWeakEquivalences.weakEquivalences =
    OAI.Thomason.simplicialWeakEquivalences.inverseImage R
  fib_eq : model.categoryWithFibrations.fibrations = OAI.Thomason.simplicialFibrations.inverseImage R
  cof_eq : model.categoryWithCofibrations.cofibrations =
    ((OAI.Thomason.simplicialFibrations.inverseImage R) ⊓ (OAI.Thomason.simplicialWeakEquivalences.inverseImage R)).llp
  generating_cofibrations : (OAI.Thomason.boundaryImages L).rlp =
    model.categoryWithFibrations.fibrations ⊓ model.categoryWithWeakEquivalences.weakEquivalences
  generating_trivial_cofibrations : (OAI.Thomason.hornImages L).rlp = model.categoryWithFibrations.fibrations
  weak_factorization_one : MorphismProperty.IsWeakFactorizationSystem
    (model.categoryWithCofibrations.cofibrations ⊓ model.categoryWithWeakEquivalences.weakEquivalences)
    model.categoryWithFibrations.fibrations
  weak_factorization_two : MorphismProperty.IsWeakFactorizationSystem
    model.categoryWithCofibrations.cofibrations
    (model.categoryWithFibrations.fibrations ⊓ model.categoryWithWeakEquivalences.weakEquivalences)
  complete : HasLimitsOfSize.{u,u} C
  cocomplete : HasColimitsOfSize.{u,u} C
  locallyPresentable : IsLocallyPresentable.{u} C
  leftProper : OAI.Thomason.LeftProperFor model.categoryWithWeakEquivalences.weakEquivalences
    model.categoryWithCofibrations.cofibrations
  rightProper : OAI.Thomason.RightProperFor model.categoryWithWeakEquivalences.weakEquivalences
    model.categoryWithFibrations.fibrations
  leftQuillen : ∀ {K K' : SSet.{u}} (f : K ⟶ K'), Mono f →
    model.categoryWithCofibrations.cofibrations (L.map f) ∧
      (OAI.Thomason.simplicialWeakEquivalences f → model.categoryWithWeakEquivalences.weakEquivalences (L.map f))
  quillenEquivalence : ∀ (K : SSet.{u}) (Y : C),
    OAI.Thomason.FibrantFor model.categoryWithFibrations.fibrations Y →
    ∀ f : L.obj K ⟶ Y,
      model.categoryWithWeakEquivalences.weakEquivalences f ↔
        OAI.Thomason.simplicialWeakEquivalences (adj.homEquiv K Y f)

noncomputable def FullMain : Prop :=
  Nonempty OAI.Thomason.KanQuillenModel.{u} ∧
  Nonempty (OAI.Thomason.ExactModelEndpoint OAI.Thomason.thomasonLeft.{u} OAI.Thomason.thomasonRight OAI.Thomason.thomasonAdjunction) ∧
  ∀ n : ℕ, 1 ≤ n →
    Nonempty (OAI.Thomason.ExactModelEndpoint (OAI.Thomason.thomasonLeftFinite.{u} n) (OAI.Thomason.thomasonRightFinite n)
      (OAI.Thomason.thomasonFiniteAdjunction n))


end OAI.Thomason
end

section
namespace OAI.Thomason
open CategoryTheory

noncomputable def thomasonWeakEquivalences : MorphismProperty OAI.Thomason.OmegaCategory.{u} :=
  OAI.Thomason.simplicialWeakEquivalences.inverseImage OAI.Thomason.thomasonRight

noncomputable def thomasonWeakEquivalencesFinite (n : ℕ) :
    MorphismProperty (OAI.Thomason.OmegaCategory.NCategory.{u} n) :=
  OAI.Thomason.simplicialWeakEquivalences.inverseImage (OAI.Thomason.thomasonRightFinite n)


end OAI.Thomason
end

section
namespace OAI




end OAI
end
end


