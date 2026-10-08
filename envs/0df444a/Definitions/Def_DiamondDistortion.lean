-- Prove2me | Definitions.Def_DiamondDistortion
-- name    : DiamondDistortion
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:07.570385+00:00
-- url     : https://prove2.me/theorems/819877b6-639b-4cd4-b924-0685066b039d
-- statement:
--   A segment system on an index set ι specifies allowed finite subsets and requires every singleton to be allowed. For finitely supported real arrays u, each finite pairwise disjoint family of segments S₁, …, Sₘ gives the seminorm (∑ᵢ(∑ᵥ∈Sᵢ u(v))²)¹ᐟ²; their supremum is a norm, bounded above by ∑ᵥ|u(v)| and below by each |u(v)|. The associated James space is the completion of this normed space, and its dual is the full continuous real dual. Coordinate evaluations extend continuously to the completion, and unit coordinate vectors embed canonically in it. For a finite set H, the dual head operator sends a functional f to ∑ᵥ∈H f(eᵥ)δᵥ, where eᵥ is the unit vector and δᵥ is coordinate evaluation. The coordinate predual is defined as the norm closure of the linear span of these coordinate functionals inside the full dual. Given a reflexive antisymmetric relation r, its allowed segments are finite sets exactly equal to intervals {v : r(a,v) and r(v,b)} with r(a,b). An ancestral order is a partial order in which the predecessors of each vertex form a chain; its segments are these finite intervals. Two particular systems use prefix ancestry: the forest of pairs (h,w), where h≥1 and w is a finite word over the natural numbers of length at most h, with ancestry restricted to equal h; and the infinite tree of all finite words, including the empty root. The forest full dual and infinite-tree coordinate predual are distinguished. Finally, the countably branching diamond graphs start with a single edge between two vertices and repeatedly replace each edge by countably many two-edge paths through distinct new vertices, retaining existing vertices. Edges record their parent, new-vertex index, and side. At stage k, the specified distance is the undirected graph distance divided by 2ᵏ, so each final edge has length 2⁻ᵏ.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DiamondDistortion.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DiamondDistortion.lean; bytes 16..11996
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

universe u v


open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

structure SegmentSystem (ι : Type*) where
  IsSegment : Finset ι → Prop
  singleton : ∀ v, IsSegment {v}

namespace SegmentSystem

variable {ι : Type*} (T : SegmentSystem ι)

/-- The represented disjoint families in the definition of the primal segment norm. -/
structure Family where
  n : ℕ
  seg : Fin n → Finset ι
  allowed : ∀ i, T.IsSegment (seg i)
  disjoint : Pairwise (fun i j => Disjoint (seg i) (seg j))

instance : Nonempty T.Family := ⟨{
  n := 0
  seg := Fin.elim0
  allowed := fun i => Fin.elim0 i
  disjoint := fun {i} => Fin.elim0 i }⟩

variable {T}

/-- Segment testing as a Euclidean-valued linear map. -/
def Family.test (F : T.Family) : (ι →₀ ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin F.n) where
  toFun u := WithLp.toLp 2 (fun i => ∑ v ∈ F.seg i, u v)
  map_add' u v := by
    ext i
    simp [Finset.sum_add_distrib]
  map_smul' c u := by
    ext i
    simp [Finset.mul_sum]

def Family.seminorm (F : T.Family) : Seminorm ℝ (ι →₀ ℝ) :=
  (normSeminorm ℝ (EuclideanSpace ℝ (Fin F.n))).comp F.test

variable (T)

def primalSeminorm : Seminorm ℝ (ι →₀ ℝ) := ⨆ F : T.Family, F.seminorm

/-- Singleton families ensure that the segment seminorm separates points. -/
def singletonFamily (v : ι) : T.Family where
  n := 1
  seg _ := {v}
  allowed _ := T.singleton v
  disjoint := by intro i j h; exact False.elim (h (Subsingleton.elim _ _))

def Primal (_T : SegmentSystem ι) := ι →₀ ℝ

instance : AddCommGroup T.Primal := inferInstanceAs (AddCommGroup (ι →₀ ℝ))
instance : Module ℝ T.Primal := inferInstanceAs (Module ℝ (ι →₀ ℝ))

instance : NormedAddCommGroup T.Primal := by
  have Family.test_apply (F : T.Family) (u : ι →₀ ℝ) (i : Fin F.n) :
      F.test u i = ∑ v ∈ F.seg i, u v := rfl
  have Family.seminorm_apply (F : T.Family) (u : ι →₀ ℝ) :
      F.seminorm u = ‖F.test u‖ := rfl
  have Family.test_single_le (F : T.Family) (v : ι) (r : ℝ) :
      ‖F.test (Finsupp.single v r)‖ ≤ |r| := by
    classical
    rw [EuclideanSpace.norm_eq]
    apply (Real.sqrt_le_left (abs_nonneg r)).2
    by_cases h : ∃ i, v ∈ F.seg i
    · obtain ⟨i, hi⟩ := h
      have hne : ∀ j, j ≠ i → v ∉ F.seg j := by
        intro j hji hj
        exact Finset.disjoint_left.mp (F.disjoint hji) hj hi
      rw [Finset.sum_eq_single i]
      · simp [Family.test, Finsupp.single_apply, hi]
      · intro j _ hji
        simp [Family.test, Finsupp.single_apply, hne j hji]
      · simp
    · have hn : ∀ i, v ∉ F.seg i := by simpa using h
      simp [Family.test, Finsupp.single_apply, hn, sq_nonneg]
  have Family.test_le_l1 (F : T.Family) (u : ι →₀ ℝ) :
      ‖F.test u‖ ≤ u.sum (fun _ r => |r|) := by
    classical
    calc
      ‖F.test u‖ = ‖∑ v ∈ u.support, F.test (Finsupp.single v (u v))‖ := by
        rw [← map_sum]
        congr 2
        exact (Finsupp.sum_single u).symm
      _ ≤ ∑ v ∈ u.support, ‖F.test (Finsupp.single v (u v))‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ u.support, |u v| := Finset.sum_le_sum fun v _ => Family.test_single_le F v (u v)
      _ = u.sum (fun _ r => |r|) := rfl
  have families_bddAbove : BddAbove (Set.range (Family.seminorm (T := T))) := by
    rw [Seminorm.bddAbove_range_iff]
    intro u
    exact ⟨u.sum (fun _ r => |r|), by rintro _ ⟨F, rfl⟩; exact Family.test_le_l1 F u⟩
  have test_le_primal (F : T.Family) (u : ι →₀ ℝ) :
      ‖F.test u‖ ≤ T.primalSeminorm u := by
    rw [primalSeminorm, Seminorm.iSup_apply families_bddAbove]
    exact le_ciSup (⟨u.sum (fun _ r => |r|), by
      rintro _ ⟨G, rfl⟩; exact Family.test_le_l1 G u⟩ :
      BddAbove (Set.range (fun G : T.Family => G.seminorm u))) F
  have coordinate_le_primal (u : ι →₀ ℝ) (v : ι) : |u v| ≤ T.primalSeminorm u := by
    have h := test_le_primal (T.singletonFamily v) u
    rw [EuclideanSpace.norm_eq] at h
    change Real.sqrt (∑ _ : Fin 1, ‖∑ w ∈ ({v} : Finset ι), u w‖ ^ 2) ≤ _ at h
    simpa [Real.sqrt_sq_eq_abs] using h
  have primal_eq_zero_iff (u : ι →₀ ℝ) : T.primalSeminorm u = 0 ↔ u = 0 := by
    constructor
    · intro h
      ext v
      have := coordinate_le_primal u v
      simpa [h] using this
    · rintro rfl
      exact map_zero _
  exact AddGroupNorm.toNormedAddCommGroup
    { T.primalSeminorm.toAddGroupSeminorm with
      eq_zero_of_map_eq_zero' := fun u h => (primal_eq_zero_iff u).mp h }

instance : NormedSpace ℝ T.Primal where
  norm_smul_le c u := le_of_eq (T.primalSeminorm.smul' c u)

abbrev JamesSpace := UniformSpace.Completion T.Primal

/-- Its full real continuous dual. -/
abbrev Dual := StrongDual ℝ T.JamesSpace

/-- Coordinate evaluation on finite arrays, bounded by the singleton test. -/
def coordinateFinite (v : ι) : T.Primal →L[ℝ] ℝ := by
  have Family.test_apply (F : T.Family) (u : ι →₀ ℝ) (i : Fin F.n) :
      F.test u i = ∑ v ∈ F.seg i, u v := rfl
  have Family.seminorm_apply (F : T.Family) (u : ι →₀ ℝ) :
      F.seminorm u = ‖F.test u‖ := rfl
  have Family.test_single_le (F : T.Family) (v : ι) (r : ℝ) :
      ‖F.test (Finsupp.single v r)‖ ≤ |r| := by
    classical
    rw [EuclideanSpace.norm_eq]
    apply (Real.sqrt_le_left (abs_nonneg r)).2
    by_cases h : ∃ i, v ∈ F.seg i
    · obtain ⟨i, hi⟩ := h
      have hne : ∀ j, j ≠ i → v ∉ F.seg j := by
        intro j hji hj
        exact Finset.disjoint_left.mp (F.disjoint hji) hj hi
      rw [Finset.sum_eq_single i]
      · simp [Family.test, Finsupp.single_apply, hi]
      · intro j _ hji
        simp [Family.test, Finsupp.single_apply, hne j hji]
      · simp
    · have hn : ∀ i, v ∉ F.seg i := by simpa using h
      simp [Family.test, Finsupp.single_apply, hn, sq_nonneg]
  have Family.test_le_l1 (F : T.Family) (u : ι →₀ ℝ) :
      ‖F.test u‖ ≤ u.sum (fun _ r => |r|) := by
    classical
    calc
      ‖F.test u‖ = ‖∑ v ∈ u.support, F.test (Finsupp.single v (u v))‖ := by
        rw [← map_sum]
        congr 2
        exact (Finsupp.sum_single u).symm
      _ ≤ ∑ v ∈ u.support, ‖F.test (Finsupp.single v (u v))‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ u.support, |u v| := Finset.sum_le_sum fun v _ => Family.test_single_le F v (u v)
      _ = u.sum (fun _ r => |r|) := rfl
  have families_bddAbove : BddAbove (Set.range (Family.seminorm (T := T))) := by
    rw [Seminorm.bddAbove_range_iff]
    intro u
    exact ⟨u.sum (fun _ r => |r|), by rintro _ ⟨F, rfl⟩; exact Family.test_le_l1 F u⟩
  have test_le_primal (F : T.Family) (u : ι →₀ ℝ) :
      ‖F.test u‖ ≤ T.primalSeminorm u := by
    rw [primalSeminorm, Seminorm.iSup_apply families_bddAbove]
    exact le_ciSup (⟨u.sum (fun _ r => |r|), by
      rintro _ ⟨G, rfl⟩; exact Family.test_le_l1 G u⟩ :
      BddAbove (Set.range (fun G : T.Family => G.seminorm u))) F
  have coordinate_le_primal (u : ι →₀ ℝ) (v : ι) : |u v| ≤ T.primalSeminorm u := by
    have h := test_le_primal (T.singletonFamily v) u
    rw [EuclideanSpace.norm_eq] at h
    change Real.sqrt (∑ _ : Fin 1, ‖∑ w ∈ ({v} : Finset ι), u w‖ ^ 2) ≤ _ at h
    simpa [Real.sqrt_sq_eq_abs] using h
  exact (show T.Primal →ₗ[ℝ] ℝ from Finsupp.lapply v).mkContinuous 1 (by
      intro u
      change ‖(show ι →₀ ℝ from u) v‖ ≤ 1 * T.primalSeminorm u
      simpa only [one_mul, Real.norm_eq_abs] using coordinate_le_primal u v)

def coordinate (v : ι) : T.Dual :=
  (T.coordinateFinite v).extend UniformSpace.Completion.toComplL

/-- Primal unit coordinate and its canonical image in the completion. -/
def unitFinite (v : ι) : T.Primal := Finsupp.single v 1

def unitVector (v : ι) : T.JamesSpace := (T.unitFinite v : T.JamesSpace)

def headDual (H : Finset ι) : T.Dual →L[ℝ] T.Dual :=
  ∑ v ∈ H, (ContinuousLinearMap.apply ℝ ℝ (T.unitVector v)).smulRight (T.coordinate v)

/-- The norm-closed coordinate span, not the full infinite-tree dual. -/
def CoordinatePredual : Submodule ℝ T.Dual :=
  (Submodule.span ℝ (Set.range T.coordinate)).topologicalClosure

end SegmentSystem

/-- A finite interval in an ancestral order.  This keeps the root in every tree. -/
def intervalSystem {ι : Type*} (r : ι → ι → Prop)
    (hrefl : ∀ a, r a a) (hanti : ∀ a b, r a b → r b a → a = b) : SegmentSystem ι where
  IsSegment s := ∃ a b, r a b ∧ ∀ v, v ∈ s ↔ r a v ∧ r v b
  singleton v := by
    refine ⟨v, v, hrefl v, ?_⟩
    intro w
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨hrefl _, hrefl _⟩
    · intro h
      exact hanti w v h.2 h.1

/-- An ancestral partial order: the predecessors of any vertex form a chain. -/
class Ancestry (ι : Type*) extends PartialOrder ι where
  predecessors_total : ∀ {a b c : ι}, le a c → le b c → le a b ∨ le b a

namespace Ancestry

open scoped Classical
variable {ι : Type*} [A : Ancestry ι]
local instance : PartialOrder ι := A.toPartialOrder

/-- Nonempty finite intervals for an ancestral order. -/
def segments : SegmentSystem ι :=
  intervalSystem (· ≤ ·) (fun _ => le_rfl) (fun _ _ => le_antisymm)

end Ancestry

def ForestNode := {hw : ℕ × List ℕ // 1 ≤ hw.1 ∧ hw.2.length ≤ hw.1}

def ForestAncestor (a b : ForestNode) : Prop :=
  a.val.1 = b.val.1 ∧ a.val.2.IsPrefix b.val.2

@[instance_reducible] def forestAncestry : Ancestry ForestNode where
  le := ForestAncestor
  lt a b := ForestAncestor a b ∧ ¬ ForestAncestor b a
  le_refl a := ⟨rfl, List.prefix_refl _⟩
  le_trans _ _ _ hab hbc := ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩
  le_antisymm a b hab hba := by
    apply Subtype.ext
    exact Prod.ext hab.1 (hab.2.sublist.antisymm hba.2.sublist)
  predecessors_total hab hac := by
    rcases List.prefix_or_prefix_of_prefix hab.2 hac.2 with h | h
    · exact Or.inl ⟨hab.1.trans hac.1.symm, h⟩
    · exact Or.inr ⟨hac.1.trans hab.1.symm, h⟩

def forestSegments : SegmentSystem ForestNode :=
  Ancestry.segments (A := forestAncestry)

/-- Prefix order on all finite words, explicitly distinct from their lexicographic order. -/
@[instance_reducible] def infiniteAncestry : Ancestry (List ℕ) where
  le := List.IsPrefix
  lt a b := a.IsPrefix b ∧ ¬ b.IsPrefix a
  le_refl := List.prefix_refl
  le_trans _ _ _ := List.IsPrefix.trans
  le_antisymm _ _ hab hba := hab.sublist.antisymm hba.sublist
  predecessors_total := List.prefix_or_prefix_of_prefix

/-- The infinite-height tree of all finite words; this includes the empty root. -/
def infiniteSegments : SegmentSystem (List ℕ) :=
  Ancestry.segments (A := infiniteAncestry)

abbrev ForestDual := forestSegments.Dual
abbrev InfinitePredual := infiniteSegments.CoordinatePredual

namespace Diamond

/-- Stage edges, retaining their parent, child number, and side. -/
@[reducible] def Edge : ℕ → Type
  | 0 => Unit
  | n + 1 => Edge n × ℕ × Bool

/-- At every replacement every parent edge receives countably many distinct new vertices. -/
@[reducible] def Vertex : ℕ → Type
  | 0 => Bool
  | n + 1 => Vertex n ⊕ (Edge n × ℕ)

def endpoint : (n : ℕ) → Edge n → Bool → Vertex n
  | 0, _, b => b
  | n + 1, (e, _, false), false => Sum.inl (endpoint n e false)
  | _ + 1, (e, i, false), true => Sum.inr (e, i)
  | _ + 1, (e, i, true), false => Sum.inr (e, i)
  | n + 1, (e, _, true), true => Sum.inl (endpoint n e true)

/-- The undirected replacement graph. -/
def graph (n : ℕ) : SimpleGraph (Vertex n) :=
  SimpleGraph.fromRel (fun u v => ∃ e : Edge n, u = endpoint n e false ∧ v = endpoint n e true)

/-- Final edges have length 2⁻ᵏ: this is the shortest-path metric of the normalized graph. -/
def distance (k : ℕ) (u v : Vertex k) : ℝ :=
  ((graph k).dist u v : ℝ) / (Nat.cast 2 : ℝ) ^ k

end Diamond



end DiamondDistortion
end
end OAI


