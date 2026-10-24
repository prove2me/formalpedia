-- Prove2me | Definitions.Def_OAIQWBTP000
-- name    : OAIQWBTP000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T18:24:16.30166+00:00
-- url     : https://prove2.me/theorems/f84c87f8-5b5b-4085-b163-74cd28d1347e
-- title:
--   OpenAI bounded tree potentials split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof that the four completed tree-potential spaces have a positive averaged midpoint modulus but no asymptotically uniformly convex renorming (`OAI.BoundedTreePotentials.TreeCalculus.main_counterexample`, the paper's Theorem 2.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/TreePotential` (OpenAI, *Midpoint convexity from bounded tree potentials and path costs*, OpenAI Math Release, September 27, 2026, result family 331, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a: finite-tree heads, the extended-real asymptotic moduli and AUC predicate, and the auxiliary norms and maps the proofs use. The bundle also contains the lemmas those definitions use in their bodies.
--
--   The definitions of the published statement (`TestFamily`, `testNorm`, `TestCompletion`, `Node`, `potential`, `QuadraticKind`, `IsTreeTest`, `treeTestFamily`, `averagedModulusReal`, `oneSidedModulusReal`, `IsAUCReal` and the rest) are not repeated: the bundle imports them from the published bundle `Def_BoundedTreePotentials`. It imports no other bundle.
--
--   Modules: `FiniteTree.lean`, `TestNorm.lean`, `Inward.lean`, `Completion.lean`, `TreeTests.lean`, `FiniteHeads.lean`, `Moduli.lean`, `WeakNull.lean`, `TreeObstruction.lean`, `RealModuli.lean`.
--
--   The theorems of the development that the definitions do not need are proved in the four solutions of this split. Three of them prove the published intermediate statements `OAI.BoundedTreePotentials.TreeCalculus.four_completed_space`, `OAI.BoundedTreePotentials.TreeCalculus.four_averaged_modulus_real` and `OAI.BoundedTreePotentials.TreeCalculus.four_no_equivalent_AUC_real`, the three parts of Theorem 2.1, and the fourth proves `OAI.BoundedTreePotentials.TreeCalculus.main_counterexample` from them. The split publishes the three parts as statements of their own; the single-file proof also timed out in the platform's verifier.
-- source:
--   OpenAI, Midpoint convexity from bounded tree potentials and path costs, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 331; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Midpoint-convexity-from-bounded-tree-potentials-and-path-costs-September-27-2026/manuscript.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/TreePotential at commit adc7f12

import Mathlib
import Definitions.Def_BoundedTreePotentials

section
-- module Solutions.OAIQW_BoundedTreePotentials.FiniteTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section FiniteHeightTrees

/-- The countably branching, finite-height, root-inclusive tree. -/
abbrev Tree (n : ℕ) := {s : List ℕ // s.length ≤ n}

def root (n : ℕ) : Tree n := ⟨[], Nat.zero_le n⟩
instance instInhabitedTree (n : ℕ) : Inhabited (Tree n) := ⟨root n⟩

end FiniteHeightTrees


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.TestNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section TestNorms
open scoped Classical
variable {I : Type*}

lemma finitePairing_apply (f : I → ℝ) (x : I →₀ ℝ) :
    finitePairing f x = ∑ i ∈ x.support, x i * f i := rfl

lemma finitePairing_abs_bound (K : TestFamily I) (f : K) (x : I →₀ ℝ) :
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

lemma testNorm_bddAbove (K : TestFamily I) (x : I →₀ ℝ) :
    BddAbove (range fun f : K => |finitePairing f.val x|) :=
  ⟨∑ i ∈ x.support, |x i|, by rintro _ ⟨f, rfl⟩; exact finitePairing_abs_bound K f x⟩

lemma finitePairing_le_testNorm (K : TestFamily I) (f : K) (x : I →₀ ℝ) :
    |finitePairing f.val x| ≤ testNorm K x := le_ciSup (testNorm_bddAbove K x) f

lemma testNorm_nonneg (K : TestFamily I) (x : I →₀ ℝ) : 0 ≤ testNorm K x :=
  (abs_nonneg _).trans (finitePairing_le_testNorm K ⟨0, K.zero_mem⟩ x)

lemma testNorm_le_l1 (K : TestFamily I) (x : I →₀ ℝ) :
    testNorm K x ≤ ∑ i ∈ x.support, |x i| := by
  apply ciSup_le
  exact fun f => finitePairing_abs_bound K f x

@[simp] lemma testNorm_zero (K : TestFamily I) : testNorm K 0 = 0 := by
  apply le_antisymm
  · simpa using testNorm_le_l1 K 0
  · exact testNorm_nonneg K 0

lemma testNorm_add_le (K : TestFamily I) (x y : I →₀ ℝ) :
    testNorm K (x + y) ≤ testNorm K x + testNorm K y := by
  apply ciSup_le
  intro f
  rw [map_add]
  exact (abs_add_le _ _).trans (add_le_add
    (finitePairing_le_testNorm K f x) (finitePairing_le_testNorm K f y))

lemma testNorm_smul_le (K : TestFamily I) (a : ℝ) (x : I →₀ ℝ) :
    testNorm K (a • x) ≤ ‖a‖ * testNorm K x := by
  apply ciSup_le
  intro f
  rw [map_smul, smul_eq_mul, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (finitePairing_le_testNorm K f x) (abs_nonneg a)

lemma finitePairing_single_test (x : I →₀ ℝ) (i : I) :
    finitePairing (fun j => if j = i then (1 : ℝ) else 0) x = x i := by
  classical
  rw [finitePairing_apply]
  simp only [mul_ite, mul_one, mul_zero]
  by_cases hi : i ∈ x.support
  · simp [hi]
  · simp [hi, Finsupp.notMem_support_iff.mp hi]

lemma coordinate_le_testNorm (K : TestFamily I) (x : I →₀ ℝ) (i : I) :
    |x i| ≤ testNorm K x := by
  convert finitePairing_le_testNorm K ⟨_, K.singleton_mem i⟩ x using 1
  rw [finitePairing_single_test]

@[simp] lemma norm_TestVector (K : TestFamily I) (x : TestVector K) : ‖x‖ = testNorm K x := rfl

end TestNorms


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.Inward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section InwardScalarCalculus

/-- The two different inward pieces; their difference is the original relative
    potential. The value at the inherited head `c` determines their direction. -/
def inwardOne (c v : ℝ) : ℝ := if 0 ≤ c then min v 0 else max v 0
def inwardTwo (c v : ℝ) : ℝ := if 0 ≤ c then -max v 0 else -min v 0

@[simp] lemma inwardOne_zero (c : ℝ) : inwardOne c 0 = 0 := by simp [inwardOne]
@[simp] lemma inwardTwo_zero (c : ℝ) : inwardTwo c 0 = 0 := by simp [inwardTwo]

end InwardScalarCalculus

namespace TreeCalculus

@[simp] lemma potential_root (f : Node → ℝ) : potential f [] = f [] := by simp [potential]

@[simp] lemma potential_child (f : Node → ℝ) (s : Node) (j : ℕ) :
    potential f (s ++ [j]) = potential f s + f (s ++ [j]) := by
  simp [potential, List.inits_append]

lemma potential_smul (a : ℝ) (f : Node → ℝ) (s : Node) :
    potential (a • f) s = a * potential f s := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s j ih => simp only [potential_child, ih, Pi.smul_apply, smul_eq_mul]; ring

/-- Discrete derivative with dummy parent value zero above the root. -/
def increments (P : Node → ℝ) (s : Node) : ℝ :=
  if s = [] then P [] else P s - P s.dropLast

@[simp] lemma increments_root (P : Node → ℝ) : increments P [] = P [] := by simp [increments]
@[simp] lemma increments_child (P : Node → ℝ) (s : Node) (j : ℕ) :
    increments P (s ++ [j]) = P (s ++ [j]) - P s := by simp [increments]

@[simp] theorem potential_increments (P : Node → ℝ) (s : Node) :
    potential (increments P) s = P s := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s j ih => rw [potential_child, ih, increments_child]; ring

@[simp] theorem increments_potential (f : Node → ℝ) (s : Node) :
    increments (potential f) s = f s := by
  cases s using List.reverseRecOn with
  | nil => simp
  | append_singleton s j => simp

/-- Head sets are predecessor-closed. The empty set is allowed for block heads. -/
def Initial (D : Set Node) : Prop := ∀ ⦃s r⦄, s ∈ D → r <+: s → r ∈ D

def headPart (D : Set Node) (f : Node → ℝ) : Node → ℝ := D.indicator f

def tailPart (D : Set Node) (f : Node → ℝ) : Node → ℝ := Dᶜ.indicator f

def inwardPotentialOne (D : Set Node) (h g : Node → ℝ) (s : Node) : ℝ :=
  inwardOne (potential h s) (potential (tailPart D g) s)
def inwardPotentialTwo (D : Set Node) (h g : Node → ℝ) (s : Node) : ℝ :=
  inwardTwo (potential h s) (potential (tailPart D g) s)
def inwardCoeffsOne (D : Set Node) (h g : Node → ℝ) := increments (inwardPotentialOne D h g)
def inwardCoeffsTwo (D : Set Node) (h g : Node → ℝ) := increments (inwardPotentialTwo D h g)

end TreeCalculus


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section TestCompletions
open scoped Classical
variable {I : Type*}

def testVectorEquiv (K : TestFamily I) : TestVector K ≃ₗ[ℝ] (I →₀ ℝ) :=
  { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

def finiteTestFunctional (K : TestFamily I) (f : K) : TestVector K →L[ℝ] ℝ :=
  ((finitePairing f.val).comp (testVectorEquiv K).toLinearMap).mkContinuous 1 fun x => by
    change |finitePairing f.val ((testVectorEquiv K) x)| ≤ 1 * testNorm K ((testVectorEquiv K) x)
    simpa only [one_mul] using finitePairing_le_testNorm K f ((testVectorEquiv K) x)

@[simp] lemma finiteTestFunctional_apply (K : TestFamily I) (f : K) (x : TestVector K) :
    finiteTestFunctional K f x = finitePairing f.val x := rfl

def completedTestFunctional (K : TestFamily I) (f : K) : TestCompletion K →L[ℝ] ℝ :=
  (finiteTestFunctional K f).extend UniformSpace.Completion.toComplL

@[simp] lemma completedTestFunctional_coe (K : TestFamily I) (f : K) (x : TestVector K) :
    completedTestFunctional K f (x : TestCompletion K) = finitePairing f.val x := by
  exact (finiteTestFunctional K f).extend_eq UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformEmbedding_coe _).isUniformInducing x

end TestCompletions


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.TreeTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

namespace TreeCalculus
open scoped Classical

lemma quadratic_singleton (k : QuadraticKind) {s : Node} (hs : s ≠ []) :
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

lemma test_coefficient_bound {r : Bool} {k : QuadraticKind} {f : Node → ℝ}
    (hf : IsTreeTest r k f) (s : Node) : |f s| ≤ 1 := by
  by_cases hs : s = []
  · subst s; simpa using hf.potential_bound []
  · have h := hf.quadratic_budget {s} (quadratic_singleton k hs)
    simpa only [Finset.sum_singleton, sq_le_one_iff_abs_le_one] using h

lemma quadraticBudget_dominate {k : QuadraticKind} {f g : Node → ℝ}
    (hf : QuadraticBudget k f) (h : ∀ s, |g s| ≤ |f s|) : QuadraticBudget k g := by
  intro B hB
  apply le_trans _ (hf B hB)
  apply Finset.sum_le_sum
  intro s hs
  exact (sq_le_sq).mpr (h s)

lemma coefficientSupport_dominate {k : QuadraticKind} {f g : Node → ℝ}
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

lemma zero_isTreeTest (r : Bool) (k : QuadraticKind) : IsTreeTest r k 0 := by
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

lemma neg_isTreeTest {r : Bool} {k : QuadraticKind} {f : Node → ℝ}
    (hf : IsTreeTest r k f) : IsTreeTest r k (-f) := by
  constructor
  · intro hr; simpa using congrArg Neg.neg (hf.root_zero hr)
  · intro s
    have he : -f = (-1 : ℝ) • f := by ext s; simp
    rw [he, potential_smul, neg_one_mul, abs_neg]
    exact hf.potential_bound s
  · exact quadraticBudget_dominate hf.quadratic_budget (by intro s; simp)
  · exact coefficientSupport_dominate hf.coefficient_support (by intro s; simp)

lemma inits_nodup (s : Node) : s.inits.Nodup := by
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
    omega

lemma potential_single (i s : Node) :
    potential (Pi.single i (1 : ℝ)) s = if i <+: s then 1 else 0 := by
  rw [potential, ← List.sum_toFinset _ (inits_nodup s)]
  simp only [Pi.single_apply]
  by_cases h : i <+: s
  · have hm : i ∈ s.inits.toFinset := List.mem_toFinset.mpr ((List.mem_inits i s).mpr h)
    simp [hm, h]
  · have hm : i ∉ s.inits.toFinset := fun hm => h ((List.mem_inits i s).mp (List.mem_toFinset.mp hm))
    simp [hm, h]

lemma single_isTreeTest (r : Bool) (k : QuadraticKind) {i : Node}
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

@[simp] lemma liftCoefficients_coord {r : Bool} (f : TreeCoordinate r → ℝ) (s : TreeCoordinate r) :
    liftCoefficients r f s.val = f s := by simp [liftCoefficients, s.property]

@[simp] lemma liftCoefficients_zero (r : Bool) : liftCoefficients r 0 = 0 := by
  ext s; simp [liftCoefficients]

lemma liftCoefficients_neg (r : Bool) (f : TreeCoordinate r → ℝ) :
    liftCoefficients r (-f) = -liftCoefficients r f := by
  ext s
  by_cases h : r = true ∨ s ≠ [] <;> simp [liftCoefficients, h]

lemma lift_restrict {r : Bool} (f : Node → ℝ) (hroot : r = false → f [] = 0) :
    liftCoefficients r (fun s : TreeCoordinate r => f s.val) = f := by
  ext s
  by_cases h : r = true ∨ s ≠ []
  · simp [liftCoefficients, h]
  · have hs : s = [] := by tauto
    subst s
    have hr : r = false := by cases r <;> simp_all
    simp [liftCoefficients, hroot hr]

def asTreeTest {r : Bool} {k : QuadraticKind} (f : Node → ℝ) (hf : IsTreeTest r k f) :
    treeTestFamily r k :=
  ⟨(fun s => f s.val), by change IsTreeTest r k (liftCoefficients r _); rw [lift_restrict f hf.root_zero]; exact hf⟩



def treePairing {r : Bool} (f : Node → ℝ) : (TreeCoordinate r →₀ ℝ) →ₗ[ℝ] ℝ :=
  finitePairing (fun s => f s.val)

@[simp] lemma treePairing_lift {r : Bool} (f : TreeCoordinate r → ℝ) (x : TreeCoordinate r →₀ ℝ) :
    treePairing (liftCoefficients r f) x = finitePairing f x := by
  have he : (fun s : TreeCoordinate r => liftCoefficients r f s.val) = f :=
    funext (liftCoefficients_coord f)
  change finitePairing (fun s => liftCoefficients r f s.val) x = finitePairing f x
  rw [he]

@[simp] lemma treePairing_add_coeff {r : Bool} (f g : Node → ℝ) (x : TreeCoordinate r →₀ ℝ) :
    treePairing (f + g) x = treePairing f x + treePairing g x := by
  simp only [treePairing, finitePairing_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

@[simp] lemma treePairing_sub_coeff {r : Bool} (f g : Node → ℝ) (x : TreeCoordinate r →₀ ℝ) :
    treePairing (f - g) x = treePairing f x - treePairing g x := by
  simp only [treePairing, finitePairing_apply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

@[simp] lemma treePairing_smul_coeff {r : Bool} (a : ℝ) (f : Node → ℝ) (x : TreeCoordinate r →₀ ℝ) :
    treePairing (a • f) x = a * treePairing f x := by
  simp only [treePairing, finitePairing_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end TreeCalculus


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.FiniteHeads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section CompletedHeads
open scoped Classical
variable {I : Type*}

def coordinateFunctional (K : TestFamily I) (i : I) : TestCompletion K →L[ℝ] ℝ :=
  completedTestFunctional K ⟨_, K.singleton_mem i⟩

@[simp] lemma coordinateFunctional_coe (K : TestFamily I) (i : I) (x : TestVector K) :
    coordinateFunctional K i (x : TestCompletion K) = (testVectorEquiv K x) i := by
  rw [coordinateFunctional, completedTestFunctional_coe]
  change finitePairing _ ((testVectorEquiv K) x) = _
  convert finitePairing_single_test ((testVectorEquiv K) x) i using 1

def coordinateVector (K : TestFamily I) (i : I) : TestCompletion K :=
  ((testVectorEquiv K).symm (Finsupp.single i 1) : TestVector K)

@[simp] lemma coordinateFunctional_vector (K : TestFamily I) (i j : I) :
    coordinateFunctional K i (coordinateVector K j) = if i = j then 1 else 0 := by
  simp only [coordinateVector, coordinateFunctional_coe, LinearEquiv.apply_symm_apply]
  simp [Finsupp.single_apply, eq_comm]

def completedHead (K : TestFamily I) (B : Finset I) : TestCompletion K →L[ℝ] TestCompletion K :=
  ∑ i ∈ B, (coordinateFunctional K i).smulRight (coordinateVector K i)

@[simp] lemma completedHead_apply (K : TestFamily I) (B : Finset I) (x : TestCompletion K) :
    completedHead K B x = ∑ i ∈ B, coordinateFunctional K i x • coordinateVector K i := by
  simp [completedHead]

def headCoordinates (K : TestFamily I) (B : Finset I) : TestCompletion K →L[ℝ] (B → ℝ) :=
  ContinuousLinearMap.pi (fun i => coordinateFunctional K i.val)

/-- Closed finite-codimensional coordinate tail, with no topological assumption
    on an arbitrary algebraic complement. -/
def coordinateTail (K : TestFamily I) (B : Finset I) : Submodule ℝ (TestCompletion K) :=
  (headCoordinates K B).ker

instance coordinateTail_finiteCodim (K : TestFamily I) (B : Finset I) :
    Module.Finite ℝ (TestCompletion K ⧸ coordinateTail K B) :=
  Module.Finite.equiv (headCoordinates K B).toLinearMap.quotKerEquivRange.symm

def completedTail (K : TestFamily I) (B : Finset I) : TestCompletion K →L[ℝ] TestCompletion K :=
  ContinuousLinearMap.id ℝ (TestCompletion K) - completedHead K B

@[simp] lemma completedTail_apply (K : TestFamily I) (B : Finset I) (x : TestCompletion K) :
    completedTail K B x = x - completedHead K B x := rfl

end CompletedHeads

namespace TreeCalculus
open scoped Classical

def coordinateHead (r : Bool) (D : Finset Node) : Finset (TreeCoordinate r) :=
  D.subtype (fun s => r = true ∨ s ≠ [])

@[simp] lemma mem_coordinateHead (r : Bool) (D : Finset Node) (s : TreeCoordinate r) :
    s ∈ coordinateHead r D ↔ s.val ∈ D := by simp [coordinateHead]

def initialHull {r : Bool} (x : TreeCoordinate r →₀ ℝ) : Finset Node :=
  insert [] (x.support.biUnion (fun s => s.val.inits.toFinset))

end TreeCalculus


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.Moduli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section AsymptoticModuli
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- We take these infima and suprema in the extended reals, so their definitions
    are meaningful without tacit boundedness side conditions. On infinite
    dimensional normed spaces their values at positive radii are finite. -/
def averagedModulus (t : ℝ) : EReal :=
  ⨅ x : {x : E // ‖x‖ = 1}, ⨆ F : ClosedFiniteCodim E,
    ⨅ y : {y : E // y ∈ F.space ∧ 1 ≤ ‖y‖},
      (((‖x.val + t • y.val‖ + ‖x.val - t • y.val‖) / 2 - 1 : ℝ) : EReal)

def oneSidedModulus (t : ℝ) : EReal :=
  ⨅ x : {x : E // ‖x‖ = 1}, ⨆ F : ClosedFiniteCodim E,
    ⨅ y : {y : E // y ∈ F.space ∧ ‖y‖ = 1},
      ((‖x.val + t • y.val‖ - 1 : ℝ) : EReal)

def IsAUC : Prop := ∀ t : ℝ, 0 < t → 0 < oneSidedModulus E t

end AsymptoticModuli

section TestSeparable
open scoped Classical
variable {I : Type*}

def testVectorBasis (K : TestFamily I) : Module.Basis I ℝ (TestVector K) :=
  Finsupp.basisSingleOne.map (testVectorEquiv K).symm

instance testVector_separable (K : TestFamily I) [Countable I] :
    TopologicalSpace.SeparableSpace (TestVector K) := by
  apply TopologicalSpace.isSeparable_univ_iff.mp
  have h := (Set.countable_range (testVectorBasis K)).isSeparable.span (R := ℝ)
  simpa only [(testVectorBasis K).span_eq, Submodule.top_coe] using h

end TestSeparable

namespace TreeCalculus
open scoped Classical

instance treeCoordinate_infinite (r : Bool) : Infinite (TreeCoordinate r) :=
  Infinite.of_injective (fun n : ℕ => (⟨[n], Or.inr (by simp)⟩ : TreeCoordinate r))
    (fun _ _ h => by simpa using congrArg Subtype.val h)

end TreeCalculus


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.WeakNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section WeakNullSequences
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Weak convergence to zero, expressed by all continuous real linear tests. -/
def WeaklyNull (d : ℕ → E) : Prop :=
  ∀ φ : E →L[ℝ] ℝ, Tendsto (fun n => φ (d n)) atTop (𝓝 0)

def functionalKernel (φ : E →L[ℝ] ℝ) : ClosedFiniteCodim E where
  space := φ.ker
  closed := φ.isClosed_ker
  finiteCodim := Module.Finite.equiv φ.toLinearMap.quotKerEquivRange.symm

end WeakNullSequences

section BoundedTrees
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def child {h : ℕ} (s : Tree h) (hs : s.val.length < h) (n : ℕ) : Tree h :=
  ⟨s.val ++ [n], by simp only [List.length_append, List.length_singleton]; omega⟩

@[simp] lemma child_length {h : ℕ} (s : Tree h) (hs : s.val.length < h) (n : ℕ) :
    (child s hs n).val.length = s.val.length + 1 := by simp [child]

end BoundedTrees

end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.TreeObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

namespace TreeCalculus
open scoped Classical

def nodeArray (r : Bool) (s : Node) : TreeCoordinate r →₀ ℝ :=
  if h : r = true ∨ s ≠ [] then Finsupp.single ⟨s,h⟩ 1 else 0

def pathArray (r : Bool) (s : Node) : TreeCoordinate r →₀ ℝ :=
  (s.inits.map (nodeArray r)).sum

def treePath (r : Bool) (k : QuadraticKind) (s : Node) : TestCompletion (treeTestFamily r k) :=
  ((testVectorEquiv (treeTestFamily r k)).symm (pathArray r s) : TestVector (treeTestFamily r k))

def childCoordinate (r : Bool) (s : Node) (n : ℕ) : TreeCoordinate r :=
  ⟨s ++ [n], Or.inr (by simp)⟩

/-- Shift by the fixed nonroot vertex [0], so the rootless row also starts at a
    nonzero path. No root coefficient is inserted in that row. -/
def fourBoundedTree (r : Bool) (k : QuadraticKind) (h : ℕ) (s : Tree h) :
    TestCompletion (treeTestFamily r k) := treePath r k ([0] ++ s.val)

end TreeCalculus

end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.RealModuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials

section RealModuli
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

instance instNonemptyClosedFiniteCodim : Nonempty (ClosedFiniteCodim E) :=
  ⟨⟨⊤,by simp,inferInstance⟩⟩

end RealModuli
end BoundedTreePotentials

end

end OAI
end


