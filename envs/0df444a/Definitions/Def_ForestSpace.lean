-- Prove2me | Definitions.Def_ForestSpace
-- name    : ForestSpace
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:11.787507+00:00
-- url     : https://prove2.me/theorems/9b77bbf2-df2a-44b0-85d7-0d100fd9d698
-- statement:
--   Over a real normed space E, this block sets up the machinery for asymptotic uniform convexity (AUC) and a forest/diamond example. Cofinite(E) is the type of closed subspaces F of finite codimension. For a function N:E→ℝ, t∈ℝ, x∈E, the inner one-sided excess aucInner is the infimum, over y∈F with N(y)=1, of N(x+ty)−1; aucCenter takes the supremum of this over all F; and aucModulus(N,t) is the infimum of aucCenter over all x with N(x)=1 (order inf, sup, inf). The averaged analogue replaces the excess by (N(x+ty)+N(x−ty))/2−1, giving averageInner, averageCenter and averageModulus in the same way, with no maximum taken. IsAUC(N) means aucModulus(N,t)>0 for every t>0. EquivalentNorm(E,α,β) packages a seminorm N with 0<α≤β and α‖x‖≤N(x)≤β‖x‖; Reflexive(E) means the canonical map into the double dual is surjective. On a partially ordered set V, a segment is a finite chain that is order-convex; segSum(u,S) sums u over S; and ρ(u) is the square root of the supremum of Σᵢ segSum(u,Sᵢ)² over finite families of pairwise disjoint segments. This gives a seminorm on finitely supported vectors, shown to be a norm on a type synonym TestVector(V) (using the ℓ¹ size as a bound), and J(V) is its completion, with FullDual(V) its continuous dual. Vertex is a disjoint forest: for each height h≥1, a copy of the finite words over ℕ of length at most h, ordered by prefix. Finally, a Network is a set of vertices with oriented edges having distinct endpoints, with its simple graph and shortest-path distance. Refine replaces each edge by countably many internally disjoint two-edge paths, and the diamond graph D_k is k iterated refinements of a single edge. EmbeddingBound(k,f,C) says that a map f from D_k into E satisfies s·d(u,v)≤‖f(u)−f(v)‖≤C·s·d(u,v) for some scale s>0 and all u,v.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ForestSpace.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ForestSpace.lean; bytes 16..18901
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

namespace ForestSpace

attribute [local instance] Classical.propDecidable

section ModulusDefinitions

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed finite-codimensional subspaces. -/
def Cofinite : Type :=
  {F : Submodule ℝ E // IsClosed (F : Set E) ∧ FiniteDimensional ℝ (E ⧸ F)}

/-- The inner one-sided excess values and their infimum. -/
def aucValues (N : E → ℝ) (t : ℝ) (x : E) (F : Cofinite E) : Set ℝ :=
  {a | ∃ y : E, y ∈ F.val ∧ N y = 1 ∧ a = N (x + t • y) - 1}

noncomputable def aucInner (N : E → ℝ) (t : ℝ) (x : E) (F : Cofinite E) : ℝ :=
  sInf (aucValues E N t x F)

noncomputable def aucCenter (N : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  sSup (Set.range (aucInner E N t x))

/-- The one-sided asymptotic uniform convexity modulus, with the order
of infimum, supremum and infimum. -/
noncomputable def aucModulus (N : E → ℝ) (t : ℝ) : ℝ :=
  sInf {a | ∃ x : E, N x = 1 ∧ a = aucCenter E N t x}

/-- The inner averaged signed excess; it is not replaced by a maximum. -/
def averageValues (N : E → ℝ) (t : ℝ) (x : E) (F : Cofinite E) : Set ℝ :=
  {a | ∃ y : E, y ∈ F.val ∧ N y = 1 ∧
    a = (N (x+t•y) + N (x-t•y))/((2 : ℕ) : ℝ) - 1}

noncomputable def averageInner (N : E → ℝ) (t : ℝ) (x : E) (F : Cofinite E) : ℝ :=
  sInf (averageValues E N t x F)

noncomputable def averageCenter (N : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  sSup (Set.range (averageInner E N t x))

/-- The averaged asymptotic midpoint modulus. -/
noncomputable def averageModulus (N : E → ℝ) (t : ℝ) : ℝ :=
  sInf {a | ∃ x : E, N x = 1 ∧ a = averageCenter E N t x}

end ModulusDefinitions

/-- An equivalent norm is kept as its exact real seminorm, with explicit positive
comparison constants. The lower inequality makes it a norm. -/
structure EquivalentNorm (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α β : ℝ) where
  N : Seminorm ℝ E
  alpha_pos : 0 < α
  alpha_le_beta : α ≤ β
  lower : ∀ x : E, α*‖x‖ ≤ N x
  upper : ∀ x : E, N x ≤ β*‖x‖

/-- Canonical (not merely abstract) reflexivity. -/
def Reflexive (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E)

/-- AUC requires positivity at every strictly positive parameter. -/
def IsAUC {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : E → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → 0 < aucModulus E N t

/-- A finite, order-convex chain. The empty chain is a harmless zero test. -/
def IsSegment {V : Type} [PartialOrder V] (S : Finset V) : Prop :=
  (∀ a ∈ S, ∀ b ∈ S, a ≤ b ∨ b ≤ a) ∧
  (∀ a ∈ S, ∀ b ∈ S, ∀ c, a ≤ c → c ≤ b → c ∈ S)

/-- The sum of coordinates over a segment. -/
def segSum {V : Type} (u : V → ℝ) (S : Finset V) : ℝ := ∑ v ∈ S, u v

/-- Squared bound on every disjoint family of segment tests. -/
def TestBound {V : Type} [PartialOrder V] (u : V → ℝ) (C : ℝ) : Prop :=
  ∀ (ι : Type) (_ : Fintype ι) (S : ι → Finset V),
    (∀ i, IsSegment (S i)) → Pairwise (fun i j => Disjoint (S i) (S j)) →
    ∑ i, segSum u (S i) ^ 2 ≤ C

section SegmentNorm

variable {V : Type} [PartialOrder V]

/-- All squared disjoint-segment tests. Quantifying over finite index types
is equivalent to families S₁,...,Sₘ; a zero-sized family
adds only zero to the set of test values. -/
def testValues (u : V → ℝ) : Set ℝ :=
  {r | ∃ (ι : Type) (_ : Fintype ι) (S : ι → Finset V),
    (∀ i, IsSegment (S i)) ∧ Pairwise (fun i j => Disjoint (S i) (S j)) ∧
    r = ∑ i, segSum u (S i) ^ 2}

noncomputable def squareSup (u : V → ℝ) : ℝ := sSup (testValues u)

/-- Exactly the disjoint-segment norm, written as the square root of its
squared testing supremum. -/
noncomputable def rho (u : V → ℝ) : ℝ := Real.sqrt (squareSup u)

noncomputable def l1size (u : V →₀ ℝ) : ℝ := ∑ v ∈ u.support, |u v|

end SegmentNorm

/-- The disjoint-segment seminorm on finite coordinate vectors. -/
def segmentSeminorm (V : Type) [PartialOrder V] : Seminorm ℝ (V →₀ ℝ) := by
  have segSum_zero [PartialOrder V] (S : Finset V) : segSum (0 : V → ℝ) S = 0 := by
    simp [segSum]
  have segSum_add [PartialOrder V] (u v : V → ℝ) (S : Finset V) :
      segSum (u + v) S = segSum u S + segSum v S := by
    simp [segSum, Finset.sum_add_distrib]
  have segSum_smul [PartialOrder V] (a : ℝ) (u : V → ℝ) (S : Finset V) :
      segSum (a • u) S = a * segSum u S := by
    simp [segSum, Finset.mul_sum]
  have TestBound.nonneg {u : V → ℝ} {C : ℝ} (h : TestBound u C) : 0 ≤ C := by
    simpa using h PEmpty inferInstance PEmpty.elim (by simp) (by simp [Pairwise])
  have TestBound.zero : TestBound (0 : V → ℝ) 0 := by
    intro ι inst S hS hd
    simp [segSum]
  have TestBound.smul {u : V → ℝ} {C : ℝ} (h : TestBound u C) (a : ℝ) :
      TestBound (a • u) (a ^ 2 * C) := by
    intro ι inst S hS hd
    have hh := mul_le_mul_of_nonneg_left (h ι inst S hS hd) (sq_nonneg a)
    simpa only [segSum_smul, mul_pow, Finset.mul_sum] using hh
  have TestBound.add {u v : V → ℝ} {A B : ℝ}
      (hu : TestBound u (A ^ 2)) (hv : TestBound v (B ^ 2))
      (hA : 0 ≤ A) (hB : 0 ≤ B) : TestBound (u + v) ((A + B) ^ 2) := by
    intro ι inst S hS hd
    have h₁ := hu ι inst S hS hd
    have h₂ := hv ι inst S hS hd
    have hc := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset ι)
      (fun i => segSum u (S i)) (fun i => segSum v (S i))
    have hs₁ : Real.sqrt (∑ i, segSum u (S i) ^ 2) ≤ A :=
      (Real.sqrt_le_iff).2 ⟨hA, h₁⟩
    have hs₂ : Real.sqrt (∑ i, segSum v (S i) ^ 2) ≤ B :=
      (Real.sqrt_le_iff).2 ⟨hB, h₂⟩
    have hc' : ∑ i, segSum u (S i) * segSum v (S i) ≤ A * B :=
      hc.trans (mul_le_mul hs₁ hs₂ (Real.sqrt_nonneg _) hA)
    have he : (∑ i, segSum (u + v) (S i) ^ 2) =
        (∑ i, segSum u (S i) ^ 2) + 2 * (∑ i, segSum u (S i) * segSum v (S i)) +
        (∑ i, segSum v (S i) ^ 2) := by
      simp only [segSum_add, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [he]
    nlinarith
  have zero_mem_testValues (u : V → ℝ) : 0 ∈ testValues u := by
    refine ⟨PEmpty, inferInstance, PEmpty.elim, by simp, by simp [Pairwise], ?_⟩
    simp [segSum]
  have TestBound.bddAbove {u : V → ℝ} {C : ℝ} (h : TestBound u C) :
      BddAbove (testValues u) := by
    refine ⟨C, ?_⟩
    rintro r ⟨ι, inst, S, hs, hd, rfl⟩
    exact h ι inst S hs hd
  have TestBound.squareSup_le {u : V → ℝ} {C : ℝ} (h : TestBound u C) :
      squareSup u ≤ C := by
    apply csSup_le ⟨0, zero_mem_testValues u⟩
    rintro r ⟨ι, inst, S, hs, hd, rfl⟩
    exact h ι inst S hs hd
  have testBound_squareSup {u : V → ℝ} (hu : ∃ C, TestBound u C) :
      TestBound u (squareSup u) := by
    intro ι inst S hs hd
    exact le_csSup (TestBound.bddAbove hu.choose_spec) ⟨ι, inst, S, hs, hd, rfl⟩
  have squareSup_nonneg {u : V → ℝ} (hu : ∃ C, TestBound u C) : 0 ≤ squareSup u :=
    TestBound.nonneg (testBound_squareSup hu)
  have rho_nonneg (u : V → ℝ) : 0 ≤ rho u := Real.sqrt_nonneg _
  have rho_sq {u : V → ℝ} (hu : ∃ C, TestBound u C) : rho u ^ 2 = squareSup u :=
    Real.sq_sqrt (squareSup_nonneg hu)
  have testBound_rho_sq {u : V → ℝ} (hu : ∃ C, TestBound u C) : TestBound u (rho u ^ 2) := by
    rw [rho_sq hu]
    exact testBound_squareSup hu
  have rho_le_of_testBound {u : V → ℝ} {C : ℝ} (hC : 0 ≤ C)
      (hu : TestBound u (C ^ 2)) : rho u ≤ C :=
    Real.sqrt_le_iff.mpr ⟨hC, TestBound.squareSup_le hu⟩
  have rho_add_le {u v : V → ℝ} (hu : ∃ C, TestBound u C) (hv : ∃ C, TestBound v C) :
      rho (u + v) ≤ rho u + rho v :=
    rho_le_of_testBound (add_nonneg (rho_nonneg u) (rho_nonneg v))
      (TestBound.add (testBound_rho_sq hu) (testBound_rho_sq hv) (rho_nonneg u) (rho_nonneg v))
  have rho_smul_le {u : V → ℝ} (hu : ∃ C, TestBound u C) (a : ℝ) :
      rho (a • u) ≤ |a| * rho u := by
    apply rho_le_of_testBound (mul_nonneg (abs_nonneg a) (rho_nonneg u))
    have hh := TestBound.smul (testBound_rho_sq hu) a
    simpa only [mul_pow, sq_abs] using hh
  have rho_zero : rho (0 : V → ℝ) = 0 := by
    apply le_antisymm _ (rho_nonneg _)
    apply rho_le_of_testBound (C := 0) (by norm_num)
    simpa using (TestBound.zero : TestBound (0 : V → ℝ) 0)
  have l1size_nonneg [PartialOrder V] (u : V →₀ ℝ) : 0 ≤ l1size u :=
    sum_nonneg (fun vertex _ => abs_nonneg (u vertex))
  have finset_abs_sum_le_l1size [PartialOrder V] (u : V →₀ ℝ) (S : Finset V) :
      ∑ v ∈ S, |u v| ≤ l1size u := by
    have he : (∑ v ∈ S ∪ u.support, |u v|) = l1size u := by
      symm
      apply sum_subset subset_union_right
      intro v hv hn
      rw [Finsupp.notMem_support_iff.mp hn, abs_zero]
    rw [← he]
    exact sum_le_sum_of_subset_of_nonneg subset_union_left (fun v hv hn => abs_nonneg _)
  have testBound_l1size (u : V →₀ ℝ) : TestBound u (l1size u ^ 2) := by
    intro ι inst S hS hd
    have habs : (∑ i, |segSum u (S i)|) ≤ l1size u := by
      calc
        (∑ i, |segSum u (S i)|) ≤ ∑ i, ∑ v ∈ S i, |u v| :=
          sum_le_sum fun i hi => abs_sum_le_sum_abs _ _
        _ = ∑ v ∈ univ.biUnion S, |u v| :=
          (sum_biUnion (by intro i hi j hj hij; exact hd hij)).symm
        _ ≤ l1size u := finset_abs_sum_le_l1size u _
    have hsq := sum_sq_le_sq_sum_of_nonneg
      (s := (univ : Finset ι)) (f := fun i => |segSum u (S i)|) (fun i hi => abs_nonneg _)
    simp only [sq_abs] at hsq
    have hnonneg : 0 ≤ ∑ i, |segSum u (S i)| := sum_nonneg (fun i hi => abs_nonneg _)
    nlinarith [l1size_nonneg u]
  have finsupp_has_testBound (u : V →₀ ℝ) : ∃ C, TestBound u C := ⟨_, testBound_l1size u⟩
  exact Seminorm.ofSMulLE (fun u : V →₀ ℝ => rho u) rho_zero
    (fun u v => rho_add_le (finsupp_has_testBound u) (finsupp_has_testBound v))
    (fun a u => by simpa only [Real.norm_eq_abs, Finsupp.coe_smul] using rho_smul_le (finsupp_has_testBound u) a)

/-- Finite coordinate vectors with the segment norm (a type synonym prevents
clashes with any other norm on finitely supported functions). -/
def TestVector (V : Type) := V →₀ ℝ

namespace TestVector

variable {V : Type}

instance : AddCommGroup (TestVector V) := inferInstanceAs (AddCommGroup (V →₀ ℝ))

instance : Module ℝ (TestVector V) := inferInstanceAs (Module ℝ (V →₀ ℝ))

def toFinsupp (u : TestVector V) : V →₀ ℝ := u

instance : CoeFun (TestVector V) (fun _ => V → ℝ) := ⟨fun u => u.toFinsupp⟩

variable [PartialOrder V]

instance : Norm (TestVector V) := ⟨fun u => rho u⟩

instance : NormedAddCommGroup (TestVector V) := by
  have isSegment_singleton (v : V) : IsSegment ({v} : Finset V) := by
    constructor
    · intro a ha b hb
      simp only [mem_singleton] at ha hb
      subst a
      subst b
      exact Or.inl le_rfl
    · intro a ha b hb c hac hcb
      simp only [mem_singleton] at ha hb ⊢
      subst a
      subst b
      exact le_antisymm hcb hac
  have TestBound.nonneg {u : V → ℝ} {C : ℝ} (h : TestBound u C) : 0 ≤ C := by
    simpa using h PEmpty inferInstance PEmpty.elim (by simp) (by simp [Pairwise])
  have TestBound.single {u : V → ℝ} {C : ℝ} (h : TestBound u C)
      {S : Finset V} (hS : IsSegment S) : segSum u S ^ 2 ≤ C := by
    simpa using h Unit inferInstance (fun _ => S) (fun _ => hS)
      (by simp [Pairwise])
  have TestBound.bddAbove {u : V → ℝ} {C : ℝ} (h : TestBound u C) :
      BddAbove (testValues u) := by
    refine ⟨C, ?_⟩
    rintro r ⟨ι, inst, S, hs, hd, rfl⟩
    exact h ι inst S hs hd
  have testBound_squareSup {u : V → ℝ} (hu : ∃ C, TestBound u C) :
      TestBound u (squareSup u) := by
    intro ι inst S hs hd
    exact le_csSup (TestBound.bddAbove hu.choose_spec) ⟨ι, inst, S, hs, hd, rfl⟩
  have squareSup_nonneg {u : V → ℝ} (hu : ∃ C, TestBound u C) : 0 ≤ squareSup u :=
    TestBound.nonneg (testBound_squareSup hu)
  have rho_nonneg (u : V → ℝ) : 0 ≤ rho u := Real.sqrt_nonneg _
  have rho_sq {u : V → ℝ} (hu : ∃ C, TestBound u C) : rho u ^ 2 = squareSup u :=
    Real.sq_sqrt (squareSup_nonneg hu)
  have testBound_rho_sq {u : V → ℝ} (hu : ∃ C, TestBound u C) : TestBound u (rho u ^ 2) := by
    rw [rho_sq hu]
    exact testBound_squareSup hu
  have coordinate_le_rho {u : V → ℝ} (hu : ∃ C, TestBound u C) (v : V) :
      |u v| ≤ rho u := by
    have hh := TestBound.single (testBound_rho_sq hu) (isSegment_singleton v)
    simp only [segSum, sum_singleton] at hh
    exact (sq_le_sq₀ (abs_nonneg _) (rho_nonneg _)).mp (by simpa only [sq_abs] using hh)
  have l1size_nonneg [PartialOrder V] (u : V →₀ ℝ) : 0 ≤ l1size u :=
    sum_nonneg (fun vertex _ => abs_nonneg (u vertex))
  have finset_abs_sum_le_l1size [PartialOrder V] (u : V →₀ ℝ) (S : Finset V) :
      ∑ v ∈ S, |u v| ≤ l1size u := by
    have he : (∑ v ∈ S ∪ u.support, |u v|) = l1size u := by
      symm
      apply sum_subset subset_union_right
      intro v hv hn
      rw [Finsupp.notMem_support_iff.mp hn, abs_zero]
    rw [← he]
    exact sum_le_sum_of_subset_of_nonneg subset_union_left (fun v hv hn => abs_nonneg _)
  have testBound_l1size (u : V →₀ ℝ) : TestBound u (l1size u ^ 2) := by
    intro ι inst S hS hd
    have habs : (∑ i, |segSum u (S i)|) ≤ l1size u := by
      calc
        (∑ i, |segSum u (S i)|) ≤ ∑ i, ∑ v ∈ S i, |u v| :=
          sum_le_sum fun i hi => abs_sum_le_sum_abs _ _
        _ = ∑ v ∈ univ.biUnion S, |u v| :=
          (sum_biUnion (by intro i hi j hj hij; exact hd hij)).symm
        _ ≤ l1size u := finset_abs_sum_le_l1size u _
    have hsq := sum_sq_le_sq_sum_of_nonneg
      (s := (univ : Finset ι)) (f := fun i => |segSum u (S i)|) (fun i hi => abs_nonneg _)
    simp only [sq_abs] at hsq
    have hnonneg : 0 ≤ ∑ i, |segSum u (S i)| := sum_nonneg (fun i hi => abs_nonneg _)
    nlinarith [l1size_nonneg u]
  have finsupp_has_testBound (u : V →₀ ℝ) : ∃ C, TestBound u C := ⟨_, testBound_l1size u⟩
  exact NormedAddCommGroup.ofCore (𝕜 := ℝ) {
    norm_nonneg u := apply_nonneg (segmentSeminorm V) u.toFinsupp
    norm_triangle u v := map_add_le_add (segmentSeminorm V) u.toFinsupp v.toFinsupp
    norm_smul a u := map_smul_eq_mul (segmentSeminorm V) a u.toFinsupp
    norm_eq_zero_iff u := ⟨by
      intro h
      apply Finsupp.ext
      intro v
      have hh := coordinate_le_rho (finsupp_has_testBound u.toFinsupp) v
      change rho u.toFinsupp = 0 at h
      rw [h] at hh
      exact abs_nonpos_iff.mp hh, by
      rintro rfl
      exact map_zero (segmentSeminorm V)⟩ }

instance : NormedSpace ℝ (TestVector V) where
  norm_smul_le a u := le_of_eq (map_smul_eq_mul (segmentSeminorm V) a u.toFinsupp)

end TestVector

/-- J(T), completion of the finite-support disjoint-segment norm. -/
abbrev J (V : Type) [PartialOrder V] := UniformSpace.Completion (TestVector V)

/-- The full continuous dual, used for the finite-height forest example. -/
abbrev FullDual (V : Type) [PartialOrder V] := StrongDual ℝ (J V)

section CoordinateCompletion

variable {W : no_index Type} [PartialOrder W]

instance fullDualAddCommGroup : AddCommGroup (FullDual W) :=
  inferInstanceAs (AddCommGroup (StrongDual ℝ (J W)))

end CoordinateCompletion

/-- Finite words, ordered by extension, including the empty root. -/
structure Word where
  letters : List ℕ
  deriving DecidableEq

namespace Word

instance : PartialOrder Word where
  le a b := a.letters <+: b.letters
  le_refl _ := List.prefix_rfl
  le_trans _ _ _ := List.IsPrefix.trans
  le_antisymm a b hab hba := by
    have h := hab.eq_of_length (Nat.le_antisymm hab.length_le hba.length_le)
    cases a; cases b; cases h; rfl

end Word

/-- A disjoint forest: one copy of `Nat^{≤h}` for every `h≥1`. -/
structure Vertex where
  height : ℕ
  positive : 1 ≤ height
  word : Word
  bounded : word.letters.length ≤ height
  deriving DecidableEq

namespace Vertex

instance : PartialOrder Vertex where
  le a b := a.height = b.height ∧ a.word ≤ b.word
  le_refl _ := ⟨rfl,le_rfl⟩
  le_trans a b c hab hbc := ⟨hab.1.trans hbc.1,hab.2.trans hbc.2⟩
  le_antisymm a b hab hba := by
    obtain ⟨hh, hw⟩ := hab
    have he := le_antisymm hw hba.2
    cases a; cases b; cases hh; cases he; rfl

end Vertex

namespace Diamond

/-- An oriented edge enumeration; only the associated undirected unit-edge
simple graph is used for distances. -/
structure Network where
  V : Type
  E : Type
  left : E → V
  right : E → V
  distinct : ∀ e, left e ≠ right e

namespace Network

variable (A : Network)

def graph : SimpleGraph A.V where
  Adj u v := ∃ e : A.E, (A.left e = u ∧ A.right e = v) ∨
    (A.right e = u ∧ A.left e = v)
  symm := ⟨by
    rintro u v ⟨e,h | h⟩
    · exact ⟨e,Or.inr ⟨h.2,h.1⟩⟩
    · exact ⟨e,Or.inl ⟨h.2,h.1⟩⟩⟩
  loopless := ⟨by
    rintro u ⟨e,h | h⟩
    · exact A.distinct e (h.1.trans h.2.symm)
    · exact A.distinct e (h.2.trans h.1.symm)⟩

/-- Every edge is replaced by countably many internally disjoint two-edge
paths. All old vertices remain, and each pair (edge,index) is a new midpoint. -/
@[reducible] def refine : Network where
  V := Sum A.V (A.E × ℕ)
  E := A.E × ℕ × Bool
  left e := if e.2.2 then Sum.inr (e.1,e.2.1) else Sum.inl (A.left e.1)
  right e := if e.2.2 then Sum.inl (A.right e.1) else Sum.inr (e.1,e.2.1)
  distinct := by rintro ⟨e,j,b⟩; cases b <;> simp

/-- Iterating the very same edge replacement, starting from an arbitrary
network. This recursion groups the first replacement before the remaining ones. -/
@[reducible] def iterate : Network → ℕ → Network
  | A,0 => A
  | A,n+1 => iterate A.refine n

end Network

/-- D₀ is precisely one edge. -/
@[reducible] def base : Network where
  V := Bool
  E := Unit
  left _ := false
  right _ := true
  distinct _ := by decide

/-- Countably branching diamonds, all current edges of length one. -/
@[reducible] def diamond (k : ℕ) := base.iterate k

/-- The shortest-path distance, via Mathlib's actual graph distance. -/
def distance (k : ℕ) (u v : (diamond k).V) : ℝ := ((diamond k).graph.dist u v : ℝ)
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The distortion convention, including its arbitrary positive scale. -/
def EmbeddingBound (k : ℕ) (f : (diamond k).V → E) (C : ℝ) : Prop :=
  ∃ s : ℝ, 0 < s ∧ ∀ u v,
    s*distance k u v ≤ ‖f u-f v‖ ∧ ‖f u-f v‖ ≤ C*s*distance k u v

end Diamond



end ForestSpace
end
end OAI


