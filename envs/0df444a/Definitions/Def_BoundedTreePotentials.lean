-- Prove2me | Definitions.Def_BoundedTreePotentials
-- name    : BoundedTreePotentials
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:02.512997+00:00
-- url     : https://prove2.me/theorems/3219a21b-dce7-4674-8487-37f3abc817f0
-- statement:
--   A test family on an index set I is a set K of real coefficient functions containing zero and every coordinate indicator, closed under negation, and satisfying |f(i)|≤1 for all f∈K and i∈I. On finitely supported real vectors, the pairing is ⟨f,x⟩=∑ᵢx(i)f(i), and the test norm is sup_{f∈K}|⟨f,x⟩|. The construction proves this is a norm, with |x(i)|≤‖x‖≤∑ᵢ|x(i)|, equips these vectors with a real normed-space structure, and takes their completion. For the tree of finite lists of natural numbers, rooted at the empty list, a coefficient function has potential P_f(s)=∑_{u prefix of s}f(u), including both the root and s. Tree tests require |P_f(s)|≤1 at every node and a quadratic budget ∑_{s∈B}f(s)²≤1 on each permitted finite set B. Three variants permit, respectively, sets of children of a common parent, antichains of pairwise incomparable nodes, or arbitrary finite node sets; their respective additional support requirements are none, finite support, and membership in ℓ². A Boolean parameter either includes the root coordinate or excludes it and requires its coefficient to be zero. Extending excluded coordinates by zero yields test families of the preceding kind; the construction establishes coefficient bounds and admissibility of zero, negatives, and coordinate indicators. For any real normed space E, closed finite-codimensional subspaces F are packaged with closedness and finite-dimensional quotient assumptions. Two real-valued asymptotic moduli take the infimum over unit vectors x, then the supremum over these F: the averaged modulus at t takes the infimum over y∈F with ‖y‖≥1 of (‖x+ty‖+‖x−ty‖)/2−1, while the one-sided modulus takes the infimum over unit y∈F of ‖x+ty‖−1. The defined proposition IsAUCReal requires the one-sided modulus to be strictly positive for every real t>0.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BoundedTreePotentials.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BoundedTreePotentials.lean; bytes 16..14216
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

universe u
open Set
open scoped ENNReal Classical

namespace BoundedTreePotentials

section TestNorms

variable {I : Type*}

structure TestFamily (I : Type*) where
  carrier : Set (I → ℝ)
  zero_mem : (0 : I → ℝ) ∈ carrier
  neg_mem : ∀ f ∈ carrier, -f ∈ carrier
  coeff_bound : ∀ f ∈ carrier, ∀ i, |f i| ≤ 1
  singleton_mem : ∀ i, (fun j => if j = i then (1 : ℝ) else 0) ∈ carrier

instance : CoeSort (TestFamily I) (Type _) := ⟨fun K => K.carrier⟩
instance (K : TestFamily I) : Nonempty K.carrier := ⟨⟨0, K.zero_mem⟩⟩

def finitePairing (f : I → ℝ) : (I →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ f

def testNorm (K : TestFamily I) (x : I →₀ ℝ) : ℝ :=
  ⨆ f : K, |finitePairing f.val x|

def testSeminorm (K : TestFamily I) : Seminorm ℝ (I →₀ ℝ) := by
  have finitePairing_apply (f : I → ℝ) (x : I →₀ ℝ) :
      finitePairing f x = ∑ i ∈ x.support, x i * f i := rfl
  have finitePairing_abs_bound (K : TestFamily I) (f : K) (x : I →₀ ℝ) :
      |finitePairing f.val x| ≤ ∑ i ∈ x.support, |x i| := by
    rw [finitePairing_apply]
    calc
      |∑ i ∈ x.support, x i * f.val i| ≤ ∑ i ∈ x.support, |x i * f.val i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ x.support, |x i| := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (K.coeff_bound _ f.property i)
  have testNorm_bddAbove (K : TestFamily I) (x : I →₀ ℝ) :
      BddAbove (range fun f : K => |finitePairing f.val x|) :=
    ⟨∑ i ∈ x.support, |x i|, by rintro _ ⟨f, rfl⟩; exact finitePairing_abs_bound K f x⟩
  have finitePairing_le_testNorm (K : TestFamily I) (f : K) (x : I →₀ ℝ) :
      |finitePairing f.val x| ≤ testNorm K x := le_ciSup (testNorm_bddAbove K x) f
  have testNorm_nonneg (K : TestFamily I) (x : I →₀ ℝ) : 0 ≤ testNorm K x :=
    (abs_nonneg _).trans (finitePairing_le_testNorm K ⟨0, K.zero_mem⟩ x)
  have testNorm_le_l1 (K : TestFamily I) (x : I →₀ ℝ) :
      testNorm K x ≤ ∑ i ∈ x.support, |x i| := by
    apply ciSup_le
    exact fun f => finitePairing_abs_bound K f x
  have testNorm_zero (K : TestFamily I) : testNorm K 0 = 0 := by
    apply le_antisymm
    · simpa using testNorm_le_l1 K 0
    · exact testNorm_nonneg K 0
  have testNorm_add_le (K : TestFamily I) (x y : I →₀ ℝ) :
      testNorm K (x + y) ≤ testNorm K x + testNorm K y := by
    apply ciSup_le
    intro f
    rw [map_add]
    exact (abs_add_le _ _).trans (add_le_add
      (finitePairing_le_testNorm K f x) (finitePairing_le_testNorm K f y))
  have testNorm_smul_le (K : TestFamily I) (a : ℝ) (x : I →₀ ℝ) :
      testNorm K (a • x) ≤ ‖a‖ * testNorm K x := by
    apply ciSup_le
    intro f
    rw [map_smul, smul_eq_mul, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (finitePairing_le_testNorm K f x) (abs_nonneg a)
  exact Seminorm.ofSMulLE (testNorm K) (testNorm_zero K) (testNorm_add_le K) (testNorm_smul_le K)

def TestVector (_ : TestFamily I) := I →₀ ℝ

instance (K : TestFamily I) : AddCommGroup (TestVector K) := inferInstanceAs (AddCommGroup (I →₀ ℝ))
instance (K : TestFamily I) : Module ℝ (TestVector K) := inferInstanceAs (Module ℝ (I →₀ ℝ))
instance (K : TestFamily I) : Norm (TestVector K) := ⟨testNorm K⟩

instance (K : TestFamily I) : NormedAddCommGroup (TestVector K) := by
  have finitePairing_apply (f : I → ℝ) (x : I →₀ ℝ) :
      finitePairing f x = ∑ i ∈ x.support, x i * f i := rfl
  have finitePairing_abs_bound (K : TestFamily I) (f : K) (x : I →₀ ℝ) :
      |finitePairing f.val x| ≤ ∑ i ∈ x.support, |x i| := by
    rw [finitePairing_apply]
    calc
      |∑ i ∈ x.support, x i * f.val i| ≤ ∑ i ∈ x.support, |x i * f.val i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ x.support, |x i| := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (K.coeff_bound _ f.property i)
  have testNorm_bddAbove (K : TestFamily I) (x : I →₀ ℝ) :
      BddAbove (range fun f : K => |finitePairing f.val x|) :=
    ⟨∑ i ∈ x.support, |x i|, by rintro _ ⟨f, rfl⟩; exact finitePairing_abs_bound K f x⟩
  have finitePairing_le_testNorm (K : TestFamily I) (f : K) (x : I →₀ ℝ) :
      |finitePairing f.val x| ≤ testNorm K x := le_ciSup (testNorm_bddAbove K x) f
  have finitePairing_single_test (x : I →₀ ℝ) (i : I) :
      finitePairing (fun j => if j = i then (1 : ℝ) else 0) x = x i := by
    classical
    rw [finitePairing_apply]
    simp only [mul_ite, mul_one, mul_zero]
    by_cases hi : i ∈ x.support
    · simp [hi]
    · simp [hi, Finsupp.notMem_support_iff.mp hi]
  have coordinate_le_testNorm (K : TestFamily I) (x : I →₀ ℝ) (i : I) :
      |x i| ≤ testNorm K x := by
    convert finitePairing_le_testNorm K ⟨_, K.singleton_mem i⟩ x using 1
    rw [finitePairing_single_test]
  exact NormedAddCommGroup.ofCore (𝕜 := ℝ) {
    norm_nonneg := apply_nonneg (testSeminorm K)
    norm_smul := map_smul_eq_mul (testSeminorm K)
    norm_triangle := map_add_le_add (testSeminorm K)
    norm_eq_zero_iff := fun x => ⟨by
      intro h
      apply Finsupp.ext
      intro i
      exact abs_nonpos_iff.mp (h ▸ coordinate_le_testNorm K x i), by
      rintro rfl
      exact map_zero (testSeminorm K)⟩ }

instance (K : TestFamily I) : NormedSpace ℝ (TestVector K) where
  norm_smul_le a x := le_of_eq (map_smul_eq_mul (testSeminorm K) a x)

abbrev TestCompletion (K : TestFamily I) := UniformSpace.Completion (TestVector K)

end TestNorms

namespace TreeCalculus

abbrev Node := List ℕ

def potential (f : Node → ℝ) (s : Node) : ℝ := (s.inits.map f).sum

inductive QuadraticKind where
  | sibling | antichain | global
  deriving DecidableEq

def QuadraticGroup : QuadraticKind → Finset Node → Prop
  | .sibling, B => ∃ r, ∀ s ∈ B, ∃ j, s = r ++ [j]
  | .antichain, B => (B : Set Node).Pairwise (fun s t => ¬s <+: t ∧ ¬t <+: s)
  | .global, _ => True

def QuadraticBudget (k : QuadraticKind) (f : Node → ℝ) : Prop :=
  ∀ B : Finset Node, QuadraticGroup k B → ∑ s ∈ B, f s ^ 2 ≤ 1

def CoefficientSupport : QuadraticKind → (Node → ℝ) → Prop
  | .sibling, _ => True
  | .antichain, f => (Function.support f).Finite
  | .global, f => Memℓp f 2

structure IsTreeTest (includeRoot : Bool) (k : QuadraticKind) (f : Node → ℝ) : Prop where
  root_zero : includeRoot = false → f [] = 0
  potential_bound : ∀ s, |potential f s| ≤ 1
  quadratic_budget : QuadraticBudget k f
  coefficient_support : CoefficientSupport k f

abbrev TreeCoordinate (includeRoot : Bool) := {s : Node // includeRoot = true ∨ s ≠ []}

def liftCoefficients (r : Bool) (f : TreeCoordinate r → ℝ) (s : Node) : ℝ :=
  if h : r = true ∨ s ≠ [] then f ⟨s, h⟩ else 0

def treeTestFamily (r : Bool) (k : QuadraticKind) : TestFamily (TreeCoordinate r) := by
  have potential_root (f : Node → ℝ) : potential f [] = f [] := by simp [potential]
  have potential_child (f : Node → ℝ) (s : Node) (j : ℕ) :
      potential f (s ++ [j]) = potential f s + f (s ++ [j]) := by
    simp [potential, List.inits_append]
  have potential_smul (a : ℝ) (f : Node → ℝ) (s : Node) :
      potential (a • f) s = a * potential f s := by
    induction s using List.reverseRecOn with
    | nil => simp [potential_root]
    | append_singleton s j ih => simp only [potential_child, ih, Pi.smul_apply, smul_eq_mul]; ring
  have quadratic_singleton (k : QuadraticKind) {s : Node} (hs : s ≠ []) :
      QuadraticGroup k {s} := by
    cases k with
    | sibling =>
      cases s using List.reverseRecOn with
      | nil => exact (hs rfl).elim
      | append_singleton s j =>
        refine ⟨s, ?_⟩
        intro t ht
        have ht' : t = s ++ [j] := by simpa using ht
        exact ⟨j, ht'⟩
    | antichain => simp [QuadraticGroup]
    | global => trivial
  have test_coefficient_bound {r : Bool} {k : QuadraticKind} {f : Node → ℝ}
      (hf : IsTreeTest r k f) (s : Node) : |f s| ≤ 1 := by
    by_cases hs : s = []
    · subst s; simpa only [potential_root] using hf.potential_bound []
    · have h := hf.quadratic_budget {s} (quadratic_singleton k hs)
      rw [Finset.sum_singleton] at h
      exact (sq_le_one_iff_abs_le_one (f s)).mp h
  have quadraticBudget_dominate {k : QuadraticKind} {f g : Node → ℝ}
      (hf : QuadraticBudget k f) (h : ∀ s, |g s| ≤ |f s|) : QuadraticBudget k g := by
    intro B hB
    apply le_trans _ (hf B hB)
    apply Finset.sum_le_sum
    intro s hs
    exact (sq_le_sq).mpr (h s)
  have coefficientSupport_dominate {k : QuadraticKind} {f g : Node → ℝ}
      (hf : CoefficientSupport k f) (h : ∀ s, |g s| ≤ |f s|) : CoefficientSupport k g := by
    cases k with
    | sibling => trivial
    | antichain =>
      apply hf.subset
      intro s hs
      change g s ≠ 0 at hs
      change f s ≠ 0
      intro hzero
      have hh := h s
      rw [hzero, abs_zero] at hh
      exact hs (abs_nonpos_iff.mp hh)
    | global =>
      exact (hf.norm).mono (by intro s; simpa only [Real.norm_eq_abs] using h s)
  have zero_isTreeTest (r : Bool) (k : QuadraticKind) : IsTreeTest r k 0 := by
    constructor
    · simp
    · intro s
      change |(s.inits.map fun _ => (0 : ℝ)).sum| ≤ 1
      simp
    · intro B hB; simp
    · cases k with
      | sibling => trivial
      | antichain => simp [CoefficientSupport]
      | global => exact zero_memℓp
  have neg_isTreeTest {r : Bool} {k : QuadraticKind} {f : Node → ℝ}
      (hf : IsTreeTest r k f) : IsTreeTest r k (-f) := by
    constructor
    · intro hr; simpa using congrArg Neg.neg (hf.root_zero hr)
    · intro s
      have he : -f = (-1 : ℝ) • f := by ext s; simp
      rw [he, potential_smul, neg_one_mul, abs_neg]
      exact hf.potential_bound s
    · exact quadraticBudget_dominate hf.quadratic_budget (by intro s; simp)
    · exact coefficientSupport_dominate hf.coefficient_support (by intro s; simp)
  have inits_nodup (s : Node) : s.inits.Nodup := by
    induction s using List.reverseRecOn with
    | nil => simp
    | append_singleton s j ih =>
      have he : (s ++ [j]).inits = s.inits ++ [s ++ [j]] := by simp [List.inits_append]
      rw [he, List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb hab
      have hb' : b = s ++ [j] := by simpa using hb
      have hp := ((List.mem_inits a s).mp ha).length_le
      rw [hab, hb', List.length_append, List.length_singleton] at hp
      exact Nat.not_succ_le_self _ hp
  have potential_single (i s : Node) :
      potential (Pi.single i (1 : ℝ)) s = if i <+: s then 1 else 0 := by
    rw [potential, ← List.sum_toFinset _ (inits_nodup s)]
    simp only [Pi.single_apply]
    by_cases h : i <+: s
    · have hm : i ∈ s.inits.toFinset := List.mem_toFinset.mpr ((List.mem_inits i s).mpr h)
      simp [hm, h]
    · have hm : i ∉ s.inits.toFinset := fun hm => h ((List.mem_inits i s).mp (List.mem_toFinset.mp hm))
      simp [hm, h]
  have single_isTreeTest (r : Bool) (k : QuadraticKind) {i : Node}
      (hi : r = true ∨ i ≠ []) : IsTreeTest r k (Pi.single i (1 : ℝ)) := by
    constructor
    · intro hr
      have hn : [] ≠ i := by
        rcases hi with hi | hi
        · simp_all
        · exact Ne.symm hi
      exact Pi.single_eq_of_ne hn _
    · intro s
      rw [potential_single]
      split_ifs <;> norm_num
    · intro B hB
      simp only [Pi.single_apply, ite_pow, one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      by_cases h : i ∈ B <;> simp [h]
    · cases k with
      | sibling => trivial
      | antichain =>
        change (Function.support (Pi.single i (1 : ℝ))).Finite
        exact (Set.finite_singleton i).subset (by intro s hs; simpa [Function.mem_support, Pi.single_apply] using hs)
      | global => exact (lp.single (E := fun _ : Node => ℝ) 2 i (1 : ℝ)).property
  have liftCoefficients_coord {r : Bool} (f : TreeCoordinate r → ℝ) (s : TreeCoordinate r) :
      liftCoefficients r f s.val = f s := by simp [liftCoefficients, s.property]
  have liftCoefficients_zero (r : Bool) : liftCoefficients r 0 = 0 := by
    ext s; simp [liftCoefficients]
  have liftCoefficients_neg (r : Bool) (f : TreeCoordinate r → ℝ) :
      liftCoefficients r (-f) = -liftCoefficients r f := by
    ext s
    by_cases h : r = true ∨ s ≠ [] <;> simp [liftCoefficients, h]
  exact {
    carrier := {f | IsTreeTest r k (liftCoefficients r f)}
    zero_mem := by
      change IsTreeTest r k (liftCoefficients r 0)
      rw [liftCoefficients_zero]
      exact zero_isTreeTest r k
    neg_mem := by
      intro f hf
      change IsTreeTest r k (liftCoefficients r (-f))
      rw [liftCoefficients_neg]
      exact neg_isTreeTest hf
    coeff_bound := by
      intro f hf i
      simpa only [liftCoefficients_coord] using test_coefficient_bound hf i.val
    singleton_mem := by
      rintro ⟨i, hi⟩
      change IsTreeTest r k (liftCoefficients r _)
      convert single_isTreeTest r k hi using 1
      ext s
      by_cases h : r = true ∨ s ≠ []
      · simp [liftCoefficients, h, Pi.single_apply, Subtype.mk.injEq]
      · have hn : s ≠ i := by rintro rfl; exact h hi
        simp [liftCoefficients, h, hn] }

end TreeCalculus

section AsymptoticModuli

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

structure ClosedFiniteCodim where
  space : Submodule ℝ E
  closed : IsClosed (space : Set E)
  finiteCodim : Module.Finite ℝ (E ⧸ space)

def averagedModulusReal (t : ℝ) : ℝ :=
  ⨅ x : {x : E // ‖x‖=1},⨆ F : ClosedFiniteCodim E,
    ⨅ y : {y : E // y ∈ F.space ∧ 1≤‖y‖},
      (‖x.val+t • y.val‖+‖x.val-t • y.val‖)/((2 : ℕ) : ℝ)-1

def oneSidedModulusReal (t : ℝ) : ℝ :=
  ⨅ x : {x : E // ‖x‖=1},⨆ F : ClosedFiniteCodim E,
    ⨅ y : {y : E // y ∈ F.space ∧ ‖y‖=1},‖x.val+t • y.val‖-1

def IsAUCReal : Prop := ∀ t : ℝ, 0 < t → 0 < oneSidedModulusReal E t

end AsymptoticModuli



end BoundedTreePotentials
end
end OAI


