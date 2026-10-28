-- Prove2me | Definitions.Def_OAIQ66So001
-- name    : OAIQ66So001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:10:05.640458+00:00
-- url     : https://prove2.me/theorems/786bf706-738c-4cf0-a1a9-4ff5df7930e8
-- title:
--   Definitions bundle OAIQ66So001 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 164 declarations of OpenAI's Lean: 68 definitions, 2 inductive types or structures, 1 instance and 93 theorems. The definitions and types are `OAI.BasedComplex.Contraction`, `OAI.BasedComplex.Data`, `OAI.BasedComplex.extend`, `OAI.BasedComplex.extendBasis`, `OAI.BasedComplex.homotopy`, `OAI.BasedComplex.homotopyBasis`, `OAI.BinaryAlgebraPresentation.Binary`, `OAI.BinaryAlgebraPresentation.Integral`, `OAI.BinaryAlgebraPresentation.reduction`, `OAI.BinaryPrefixOperators.Arithmetic.Lists.Poly`, `OAI.BinaryPrefixOperators.Arithmetic.Lists.coefficient`, `OAI.BinaryPrefixOperators.Arithmetic.Lists.depth`, `OAI.BinaryPrefixOperators.Arithmetic.Lists.expandTerm`, `OAI.BinaryPrefixOperators.Arithmetic.Lists.isZero`, `OAI.BinaryPrefixOperators.Arithmetic.Lists.mulTerm`, `OAI.BinaryPrefixOperators.Arithmetic.Lists.negate`, `OAI.BinaryPrefixOperators.Arithmetic.Lists.oneName`, `OAI.BinaryPrefixOperators.Arithmetic.Lists.product`, `OAI.BinaryPrefixOperators.Arithmetic.Lists.spread`, `OAI.BinaryPrefixOperators.Arithmetic.Lists.suffixes`, `OAI.BinaryPrefixOperators.Arithmetic.Lists.toArray`, `OAI.BinaryPrefixOperators.Arithmetic.Lists.value`, `OAI.BinaryPrefixOperators.Arithmetic.Lists.zeroTest`, `OAI.BinaryPrefixOperators.Arithmetic.Pair`, `OAI.BinaryPrefixOperators.Arithmetic.Word`, `OAI.BinaryPrefixOperators.Arithmetic.cancel`, `OAI.BinaryPrefixOperators.Arithmetic.deletion`, `OAI.BinaryPrefixOperators.Arithmetic.evaluate`, `OAI.BinaryPrefixOperators.Arithmetic.insertion`, `OAI.BinaryPrefixOperators.Arithmetic.marker`, `OAI.BinaryPrefixOperators.Arithmetic.multiplyPair`, `OAI.BinaryPrefixOperators.Arithmetic.replacement`, `OAI.BinaryPrefixOperators.Arithmetic.subdivide`, `OAI.BinaryPrefixOperators.Arithmetic.uniform`, `OAI.BinaryPrefixOperators.Space`, `OAI.BinaryPrefixOperators.algebra`, `OAI.BinaryPrefixOperators.copy`, `OAI.BinaryPrefixOperators.l`, `OAI.BinaryPrefixOperators.left`, `OAI.BinaryPrefixOperators.r` and 30 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteType_BasedComplex`, `FiniteType_BasedHorn`, `FiniteType_BinaryAlgebraPresentation`, `FiniteType_BinaryPrefixOperators`, `FiniteType_BoundaryValue`, `FiniteType_CubeDisk`, `FiniteType_DiskHEP`, `FiniteType_DuffySimplex`, `FiniteType_DuffyTriangle`, `FiniteType_FiniteIdempotentDiagrams`, `FiniteType_LoopPath`, `FiniteType_PresentationGeometry`, `FiniteType_PresentationGeometryCellCoverExtensionAnyAttachingLiftNullhomotopic`, `FiniteType_SingularSubdivisionIterateApplyComm`, `SimpleOvergroups_PrefixArithmetic`, `SimpleOvergroups_PrefixEffective`, `SimpleOvergroups_PrefixLists`, `SimpleOvergroups_PrefixNames`, `SimpleOvergroups_PrefixProduct`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So010`, `OAIQ66So011`, `OAIQ66So012`, `OAIQ66So013`, `OAIQ66So014` and `OAIQ66So015`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ066_SO.Compat
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BasedComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace BasedComplex

structure Data (B : Type*) where
  degree : B → ℕ
  d : (B →₀ ℤ) →ₗ[ℤ] (B →₀ ℤ)
  aug : (B →₀ ℤ) →ₗ[ℤ] ℤ
  d_squared : ∀ c, d (d c) = 0
  lowers : ∀ b t, t ∈ (d (Finsupp.single b 1)).support → degree t + 1 = degree b
  aug_single : ∀ b, aug (Finsupp.single b 1) = if degree b = 0 then 1 else 0
  aug_d : ∀ c, aug (d c) = 0

variable {B : Type*} (C : Data B)

structure Contraction {M : Type*} [AddCommGroup M]
    (d : M →ₗ[ℤ] M) (aug : M →ₗ[ℤ] ℤ) where
  point : M
  cone : M →ₗ[ℤ] M
  d_point : d point = 0
  aug_point : aug point = 1
  aug_cone : ∀ c, aug (cone c) = 0
  identity : ∀ c, d (cone c) + cone (d c) = c - aug c • point

variable {M : Type*} [AddCommGroup M]
  (d : M →ₗ[ℤ] M) (aug : M →ₗ[ℤ] ℤ) (T : B → Contraction d aug)

def extendBasis (b : B) : M :=
  if C.degree b = 0 then (T b).point else
    (T b).cone (∑ t ∈ (C.d (Finsupp.single b 1)).support.attach,
      C.d (Finsupp.single b 1) t.1 • extendBasis t.1)
termination_by C.degree b
decreasing_by
  have h := C.lowers b t.1 t.2
  omega

def extend : (B →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (extendBasis C d aug T)

@[simp] lemma extend_single (b : B) :
    extend C d aug T (Finsupp.single b 1) = extendBasis C d aug T b := by
  simp only [extend, Finsupp.linearCombination_single, one_smul]

lemma map_mem_of_support {N : Type*} [AddCommGroup N]
    (f : (B →₀ ℤ) →ₗ[ℤ] N) (K : Submodule ℤ N) (c : B →₀ ℤ)
    (h : ∀ b ∈ c.support, f (Finsupp.single b 1) ∈ K) : f c ∈ K := by
  classical
  rw [← Finsupp.sum_single c, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro b hb
  have he : Finsupp.single b (c b) = (c b) • Finsupp.single b 1 := by simp
  rw [he, LinearMap.map_smul]
  exact K.smul_mem _ (h b hb)

variable (F G : (B →₀ ℤ) →ₗ[ℤ] M)

def homotopyBasis (b : B) : M :=
  (T b).cone (F (Finsupp.single b 1) - G (Finsupp.single b 1) -
    ∑ t ∈ (C.d (Finsupp.single b 1)).support.attach,
      C.d (Finsupp.single b 1) t.1 • homotopyBasis t.1)
termination_by C.degree b
decreasing_by
  have h := C.lowers b t.1 t.2
  omega

def homotopy : (B →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (homotopyBasis C d aug T F G)

end BasedComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CubeDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
namespace CubeDisk
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1

def toDisk (n : ℕ) : C((Fin n → I),Disk n) :=
  ⟨fun w => ⟨fun i => 2*(w i:ℝ)-1,by
      rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
      intro i
      rw [Real.norm_eq_abs,abs_le]
      constructor <;> linarith [(w i).2.1,(w i).2.2]⟩,
    (continuous_pi (fun i => by fun_prop)).subtype_mk _⟩

def toCube (n : ℕ) : C(Disk n,(Fin n → I)) :=
  ⟨fun v i => ⟨(v.1 i+1)/2,by
      have h : |v.1 i| ≤ 1 := by
        apply le_trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v.1 i)
        simpa only [mem_closedBall,dist_zero_right] using v.2
      obtain ⟨hl,hu⟩ := abs_le.mp h
      constructor <;> linarith⟩,
    continuous_pi (fun i => Continuous.subtype_mk (by
      exact (((continuous_apply i).comp continuous_subtype_val).add continuous_const).div_const 2) _)⟩

@[simp] theorem toCube_toDisk (n : ℕ) (w : Fin n → I) : toCube n (toDisk n w) = w := by
  funext i
  apply Subtype.ext
  change (2*(w i:ℝ)-1+1)/2 = _
  ring

@[simp] theorem toDisk_toCube (n : ℕ) (v : Disk n) : toDisk n (toCube n v) = v := by
  apply Subtype.ext
  funext i
  change 2*((v.1 i+1)/2)-1 = _
  ring

def homeomorph (n : ℕ) : (Fin n → I) ≃ₜ Disk n where
  toFun := toDisk n
  invFun := toCube n
  left_inv := toCube_toDisk n
  right_inv := toDisk_toCube n
  continuous_toFun := (toDisk n).continuous
  continuous_invFun := (toCube n).continuous

theorem norm_eq_one_of_boundary {n : ℕ} (w : Fin n → I) (h : w ∈ Cube.boundary (Fin n)) :
    ‖(toDisk n w).1‖ = 1 := by
  apply le_antisymm
  · simpa only [mem_closedBall,dist_zero_right] using (toDisk n w).2
  · obtain ⟨i,hi⟩ := h
    have hl := norm_le_pi_norm (toDisk n w).1 i
    rcases hi with hi | hi
    · norm_num [toDisk,hi] at hl ⊢
      exact hl
    · norm_num [toDisk,hi] at hl ⊢
      exact hl

theorem boundary_of_norm_eq_one {n : ℕ} (v : Disk n) (hv : ‖v.1‖ = 1) :
    toCube n v ∈ Cube.boundary (Fin n) := by
  by_contra hh
  have hl : ‖v.1‖ < 1 := by
    rw [pi_norm_lt_iff (by norm_num : (0:ℝ) < 1)]
    intro i
    have hn0 : toCube n v i ≠ 0 := fun h => hh ⟨i,Or.inl h⟩
    have hn1 : toCube n v i ≠ 1 := fun h => hh ⟨i,Or.inr h⟩
    have hb := (toCube n v i).2
    have h0 : (toCube n v i:ℝ) ≠ 0 := fun h => hn0 (Subtype.ext h)
    have h1 : (toCube n v i:ℝ) ≠ 1 := fun h => hn1 (Subtype.ext h)
    have hc0 : 0 < (toCube n v i:ℝ) := lt_of_le_of_ne hb.1 (Ne.symm h0)
    have hc1 : (toCube n v i:ℝ) < 1 := lt_of_le_of_ne hb.2 h1
    change 0 < (v.1 i+1)/2 at hc0
    change (v.1 i+1)/2 < 1 at hc1
    rw [Real.norm_eq_abs,abs_lt]
    constructor <;> linarith
  linarith

end CubeDisk

open Set Topology Metric
open scoped unitInterval

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology

noncomputable section

namespace PresentationGeometry

namespace Rose

abbrev Point := PUnit

end Rose

end PresentationGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSubdivisionIterateApplyComm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial

namespace SingularSubspace
open Classical
open Set _root_.CategoryTheory AlgebraicTopology Limits
variable {X : Type} [TopologicalSpace X] (A : Set X)

def inclusionMap : C(A,X) := ⟨Subtype.val,continuous_subtype_val⟩

end SingularSubspace
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryCellCoverExtensionAnyAttachingLiftNullhomotopic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Topology Metric
namespace SimplexDisk

def Fat (n : ℕ) : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

lemma closed (n : ℕ) : IsClosed (Fat n) := by
  have h : Fat n = (⋂ i, {x : Fin n → ℝ | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ 1} := by
    ext x; simp [Fat]
  rw [h]
  exact (isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))).inter
    (isClosed_le (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const)

lemma convex (n : ℕ) : Convex ℝ (Fat n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change ∑ i, (a*x i + b*y i) ≤ 1
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]

lemma bounded (n : ℕ) : Bornology.IsBounded (Fat n) := by
  apply (isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset
  intro x hx
  rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
  intro i
  rw [Real.norm_eq_abs,abs_of_nonneg (hx.1 i)]
  exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2

lemma interior_nonempty (n : ℕ) : (interior (Fat n)).Nonempty := by
  let O : Set (Fin n → ℝ) := {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}
  have hO : IsOpen O := by
    have h : O = (⋂ i, {x : Fin n → ℝ | 0 < x i}) ∩ {x | ∑ i, x i < 1} := by
      ext x; simp [O]
    rw [h]
    exact (isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))).inter
      (isOpen_lt (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const)
  have hsub : O ⊆ Fat n := fun x hx => ⟨fun i => (hx.1 i).le,hx.2.le⟩
  refine ⟨fun _ => 1 / ((n:ℝ)+1), hO.subset_interior_iff.mpr hsub ?_⟩
  constructor
  · intro i
    positivity
  · dsimp
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [mul_one_div]
    exact (div_lt_one (by positivity)).mpr (by linarith)

lemma exists_ambient (n : ℕ) : ∃ h : (Fin n → ℝ) ≃ₜ (Fin n → ℝ),
    h '' interior (Fat n) = ball 0 1 ∧ h '' Fat n = closedBall 0 1 ∧
      h '' frontier (Fat n) = sphere 0 1 := by
  simpa only [(closed n).closure_eq] using
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (convex n) (interior_nonempty n) (bounded n)

lemma interior_pos {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ interior (Fat n)) (i : Fin n) :
    0 < x i := by
  have h : x ∈ interior ((fun x : Fin n → ℝ => x i) ⁻¹' Ici 0) :=
    interior_mono (fun _ hy => hy.1 i) hx
  have h' := (isOpenMap_eval i).interior_preimage_subset_preimage_interior h
  simpa only [interior_Ici,mem_preimage,mem_Ioi] using h'

def sumCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] ℝ := ∑ i, ContinuousLinearMap.proj i

@[simp] lemma sumCLM_apply (n : ℕ) (x : Fin n → ℝ) : sumCLM n x = ∑ i, x i := by
  simp [sumCLM]

lemma sumCLM_surj (n : ℕ) : Function.Surjective (sumCLM (n+1)) := by
  intro r
  refine ⟨Pi.single (0 : Fin (n+1)) r, ?_⟩
  simp [sumCLM_apply]

lemma interior_sum_lt {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ interior (Fat n)) :
    ∑ i, x i < 1 := by
  cases n with
  | zero => simp
  | succ n =>
    have h : x ∈ interior ((sumCLM (n+1)) ⁻¹' Iic 1) :=
      interior_mono (fun _ hy => by simpa using hy.2) hx
    have h' := ((sumCLM (n+1)).isOpenMap (sumCLM_surj n)).interior_preimage_subset_preimage_interior h
    simpa only [interior_Iic,mem_preimage,mem_Iio,sumCLM_apply] using h'

def ambient (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) := Classical.choose (exists_ambient n)

lemma ambient_image (n : ℕ) : ambient n '' Fat n = closedBall 0 1 :=
  (Classical.choose_spec (exists_ambient n)).2.1

lemma ambient_frontier (n : ℕ) : ambient n '' frontier (Fat n) = sphere 0 1 :=
  (Classical.choose_spec (exists_ambient n)).2.2

end SimplexDisk

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_DiskHEP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval

namespace SimplexBoundary
open Set Topology Metric
open scoped unitInterval
abbrev Simplex (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n+1))
abbrev Boundary (n : ℕ) := {s : Simplex n // ∃ i, s.weights i = 0}

universe u

end SimplexBoundary

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_DuffySimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval
namespace DuffySimplex
abbrev Std (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n+1))

end DuffySimplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_DuffyTriangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval
namespace DuffyTriangle
open Set Topology
open scoped unitInterval
open DuffySimplex SimplexBoundary

def lastFace : ∀ n, Fin 3 → Fin (n+3)
  | 0,i => i
  | n+1,i => (lastFace n i).succ

lemma lastFace_val : ∀ n (i : Fin 3), (lastFace n i).val = n+i.val
  | 0,i => by simp [lastFace]
  | n+1,i => by simp only [lastFace,Fin.val_succ,lastFace_val]; omega

universe u

end DuffyTriangle

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_LoopPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval
namespace LoopPath
open Set Topology
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

def fromPath (P : Path (GenLoop.const : GenLoop (Fin n) X x) GenLoop.const) :
    GenLoop (Fin (n+1)) X x :=
  ⟨⟨fun t => P (t (Fin.last n)) (Fin.init t), by
    exact ((continuous_subtype_val.comp P.continuous).comp (continuous_apply (Fin.last n))).eval
      (continuous_pi (fun i : Fin n => continuous_apply i.castSucc))⟩,by
    rintro t ⟨i,hi⟩
    change P (t (Fin.last n)) (Fin.init t) = x
    induction i using Fin.lastCases with
    | last =>
      rcases hi with hi | hi
      · rw [hi,P.source]; rfl
      · rw [hi,P.target]; rfl
    | cast i => exact (P (t (Fin.last n))).2 _ ⟨i,hi⟩⟩

@[simp] lemma fromPath_apply (P : Path (GenLoop.const : GenLoop (Fin n) X x) GenLoop.const)
    (t : Fin (n+1) → I) : fromPath P t = P (t (Fin.last n)) (Fin.init t) := rfl

lemma fromPath_trans (P Q : Path (GenLoop.const : GenLoop (Fin n) X x) GenLoop.const) :
    fromPath (P.trans Q) = GenLoop.transAt (Fin.last n) (fromPath P) (fromPath Q) := by
  ext t
  simp only [fromPath_apply,Path.trans_apply,GenLoop.transAt,GenLoop.coe_copy,
    Function.update_self]
  split_ifs with h
  · congr 1
    · rw [Set.projIcc_of_mem _ (show 2*(t (Fin.last n):ℝ) ∈ Set.Icc 0 1 from
        ⟨by linarith [(t (Fin.last n)).2.1],by linarith⟩)]
    · funext i
      simp [Fin.init]
  · congr 1
    · rw [Set.projIcc_of_mem _ (show 2*(t (Fin.last n):ℝ)-1 ∈ Set.Icc 0 1 from
        ⟨by linarith,by linarith [(t (Fin.last n)).2.2]⟩)]
    · funext i
      simp [Fin.init]

def fromHomotopy {P Q : Path (GenLoop.const : GenLoop (Fin n) X x) GenLoop.const}
    (H : P.Homotopy Q) : (fromPath P).1.HomotopyRel (fromPath Q).1 (Cube.boundary (Fin (n+1))) where
  toHomotopy :=
  { toFun z := H (z.1,z.2 (Fin.last n)) (Fin.init z.2)
    continuous_toFun := ((continuous_subtype_val.comp H.continuous).comp
      (continuous_fst.prodMk ((continuous_apply (Fin.last n)).comp continuous_snd))).eval
        (continuous_pi (fun i : Fin n => (continuous_apply i.castSucc).comp continuous_snd))
    map_zero_left := fun t => congrArg (fun p : GenLoop (Fin n) X x => p (Fin.init t))
      (H.apply_zero (t (Fin.last n)))
    map_one_left := fun t => congrArg (fun p : GenLoop (Fin n) X x => p (Fin.init t))
      (H.apply_one (t (Fin.last n))) }
  prop' := by
    rintro a t ⟨i,hi⟩
    rw [(fromPath P).2 t ⟨i,hi⟩]
    induction i using Fin.lastCases with
    | last =>
      rcases hi with hi | hi
      · change H (a,t (Fin.last n)) (Fin.init t) = x
        rw [hi,H.source]; rfl
      · change H (a,t (Fin.last n)) (Fin.init t) = x
        rw [hi,H.target]; rfl
    | cast i => exact (H (a,t (Fin.last n))).2 _ ⟨i,hi⟩

end LoopPath

namespace SimplexHorn
open Set Topology
open SimplexBoundary
abbrev Std (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n+1))
variable {n : ℕ}

abbrev Horn (i : Fin (n+2)) := {s : Std (n+1) // ∃ j, j ≠ i ∧ s.1 j = 0}

def minimum (i : Fin (n+2)) (s : Std (n+1)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j : Fin (n+1) => s.1 (i.succAbove j))

lemma minimum_nonneg (i : Fin (n+2)) (s : Std (n+1)) : 0 ≤ minimum i s := by
  exact Finset.le_inf' _ _ (fun coordinate _ => s.weights_nonneg (i.succAbove coordinate))

lemma minimum_le (i : Fin (n+2)) (s : Std (n+1)) (j : Fin (n+1)) :
    minimum i s ≤ s.1 (i.succAbove j) :=
  Finset.inf'_le _ (Finset.mem_univ j)

lemma minimum_attained (i : Fin (n+2)) (s : Std (n+1)) :
    ∃ j : Fin (n+1), minimum i s = s.1 (i.succAbove j) := by
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty
    (fun j : Fin (n+1) => s.1 (i.succAbove j))
  exact ⟨j,hj⟩

lemma minimum_eq_zero (i : Fin (n+2)) (s : Horn i) : minimum i s.1 = 0 := by
  obtain ⟨j,hji,hj⟩ := s.2
  obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hji
  exact le_antisymm (by simpa only [hj] using minimum_le i s.1 k) (minimum_nonneg i s.1)

abbrev Faces (i : Fin (n+2)) := {j : Fin (n+2) // j ≠ i}

universe u

end SimplexHorn

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BasedHorn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval
namespace BasedHorn
open Set Topology DuffySimplex SimplexBoundary DuffyTriangle
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

lemma lastFace_injective (n : ℕ) : Function.Injective (lastFace n) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [lastFace_val] at hv
  omega

end BasedHorn

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FiniteIdempotentDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteIdempotentDiagrams
section

variable {R T : Type*} [NonUnitalRing R] [AddCommGroup T]

variable {K m : Type*} [CommRing K] [Fintype m]

open Matrix
open scoped Matrix

abbrev rankOne (u l : m → K) : Matrix m m K := vecMulVec u l

variable [DecidableEq m]

abbrev basisVector (i : m) : m → K := Pi.single i 1
abbrev diagonalUnit (i : m) : Matrix m m K :=
  rankOne (basisVector i) (basisVector i)

@[simp] lemma basisVector_pair (i j : m) :
    (basisVector i : m → K) ⬝ᵥ basisVector j = if i = j then 1 else 0 := by
  simp only [basisVector, single_dotProduct, one_mul, Pi.single_apply]

end

section

open Matrix
open scoped Matrix

variable {K R T : Type*} [CommRing K] [Ring R] [AddCommGroup T]

abbrev Mat3 (K : Type*) := Matrix (Fin 3) (Fin 3) K

lemma three_diagonal_sum :
    (diagonalUnit 0 + diagonalUnit 1 + diagonalUnit 2 : Mat3 K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalUnit, rankOne, basisVector, vecMulVec_apply]

end

open Matrix
open scoped Matrix

variable {K R : Type*} [CommRing K] [Ring R]

def contraction {n : Type*} [Fintype n] [DecidableEq n]
    (S : Matrix Unit n R) (D : Matrix n Unit R) (h : D * S = 1) :
    Matrix n n R →ₙ+* Matrix Unit Unit R where
  toFun M := S * M * D
  map_zero' := by simp
  map_add' M N := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_mul' M N := by
    calc S * (M * N) * D = (S * M) * (N * D) := by
           simp only [Matrix.mul_assoc]
         _ = (S * M) * ((D * S) * (N * D)) := by rw [h, Matrix.one_mul]
         _ = (S * M * D) * (S * N * D) := by simp only [Matrix.mul_assoc]

def oneByOne : Matrix Unit Unit R →+* R where
  toFun M := M () ()
  map_zero' := rfl
  map_one' := by simp
  map_add' _ _ := rfl
  map_mul' M N := by simp [Matrix.mul_apply]

variable [Algebra K R]

noncomputable def matrixCopy {n : Type*} [Fintype n] [DecidableEq n]
    (s d : n → R) (h : ∀ i j, d i * s j = if i = j then 1 else 0) :
    Matrix n n K →ₙ+* R :=
  oneByOne.toNonUnitalRingHom.comp
    ((contraction (Matrix.of fun _ j => s j) (Matrix.of fun i _ => d i) (by
        ext i j
        change (∑ _k : Unit, d i * s j) = if i = j then 1 else 0
        simpa using h i j)).comp
      (algebraMap K R).mapMatrix.toNonUnitalRingHom)

lemma matrixCopy_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (s d : n → R) (h : ∀ i j, d i * s j = if i = j then 1 else 0) (i : n) :
    matrixCopy (K := K) s d h (diagonalUnit i) = s i * d i := by
  change ((Matrix.of fun (_ : Unit) j => s j) *
    (diagonalUnit i).map (algebraMap K R) * (Matrix.of fun i (_ : Unit) => d i)) () () = _
  simp [diagonalUnit, rankOne, basisVector, Matrix.mul_apply,
    Matrix.vecMulVec_apply, Pi.single_apply, Matrix.map_apply, apply_ite]

end FiniteIdempotentDiagrams

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BoundaryValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval
namespace BoundaryValue
section
open Set Topology SimplexBoundary
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

abbrev A (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X) :=
  Additive (HomotopyGroup.Pi (n+2) X x)

end

open Set Topology SimplexBoundary DuffyTriangle
universe u

end BoundaryValue

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BinaryPrefixOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace BinaryPrefixOperators
section

variable (K : Type*) [CommRing K]

abbrev Space := Stream' (Fin 2) →₀ K

noncomputable def left (i : Fin 2) : Module.End K (Space K) :=
  Finsupp.lmapDomain K K (Stream'.cons i)

noncomputable def right (i : Fin 2) : Module.End K (Space K) :=
  Finsupp.linearCombination K fun x : Stream' (Fin 2) =>
    if x.head = i then Finsupp.single x.tail 1 else 0

@[simp] lemma left_single (i : Fin 2) (x : Stream' (Fin 2)) (a : K) :
    left K i (Finsupp.single x a) = Finsupp.single (Stream'.cons i x) a := by
  simp [left]

@[simp] lemma right_single (i : Fin 2) (x : Stream' (Fin 2)) (a : K) :
    right K i (Finsupp.single x a) =
      if x.head = i then Finsupp.single x.tail a else 0 := by
  by_cases h : x.head = i <;> simp [right, h]

lemma right_left (i j : Fin 2) :
    right K i * left K j = if i = j then 1 else 0 := by
  apply Finsupp.lhom_ext
  intro x a
  by_cases h : i = j
  · subst j
    simp [Module.End.mul_apply]
  · simp [Module.End.mul_apply, h, Ne.symm h]

lemma partition : left K 0 * right K 0 + left K 1 * right K 1 = 1 := by
  apply Finsupp.lhom_ext
  intro x a
  have hx := Stream'.cons_head_tail x
  have hx0 : x.head = 0 ∨ x.head = 1 := by omega
  rcases hx0 with h | h
  · simpa [Module.End.mul_apply, h] using congrArg (fun y => Finsupp.single y a) hx
  · simpa [Module.End.mul_apply, h] using congrArg (fun y => Finsupp.single y a) hx

noncomputable def algebra : Subalgebra K (Module.End K (Space K)) :=
  Algebra.adjoin K (Set.range (left K) ∪ Set.range (right K))

noncomputable instance algebraRing : Ring (algebra K) :=
  Subalgebra.toRing (R := K) (A := Module.End K (Space K)) (algebra K)

noncomputable def l (i : Fin 2) : algebra K :=
  ⟨left K i, Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)⟩

noncomputable def r (i : Fin 2) : algebra K :=
  ⟨right K i, Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)⟩

lemma r_l (i j : Fin 2) : r K i * l K j = if i = j then 1 else 0 := by
  apply Subtype.ext
  by_cases h : i = j <;> simp [r, l, h, right_left]

lemma l_r_partition : l K 0 * r K 0 + l K 1 * r K 1 = 1 := by
  apply Subtype.ext
  exact partition K

end

open FiniteIdempotentDiagrams

variable (K : Type*) [CommRing K]

@[simp] lemma r_l_mul (i j : Fin 2) (x : algebra K) :
    r K i * (l K j * x) = if i = j then x else 0 := by
  rw [← mul_assoc, r_l]
  split <;> simp

noncomputable def sources (i j : Fin 3) : algebra K :=
  (![![(l K 0 * l K 0), (l K 0 * l K 1), l K 1],
      ![(l K 0 * l K 0 * l K 0), (l K 0 * l K 1), l K 1],
      ![(l K 0 * l K 0 * l K 1), (l K 0 * l K 1), l K 1]] :
    Fin 3 → Fin 3 → algebra K) i j

noncomputable def targets (i j : Fin 3) : algebra K :=
  (![![(r K 0 * r K 0), (r K 1 * r K 0), r K 1],
      ![(r K 0 * r K 0 * r K 0), (r K 1 * r K 0), r K 1],
      ![(r K 1 * r K 0 * r K 0), (r K 1 * r K 0), r K 1]] :
    Fin 3 → Fin 3 → algebra K) i j

lemma targets_sources (i j k : Fin 3) :
    targets K i j * sources K i k = if j = k then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [targets, sources, mul_assoc, r_l_mul, r_l]

noncomputable def copy (i : Fin 3) : Mat3 K →ₙ+* algebra K :=
  matrixCopy (sources K i) (targets K i) (targets_sources K i)

@[simp] lemma copy_diagonal (i j : Fin 3) :
    copy K i (diagonalUnit j) = sources K i j * targets K i j :=
  matrixCopy_diagonal _ _ _ _

end BinaryPrefixOperators

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BinaryAlgebraPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
namespace BinaryAlgebraPresentation
abbrev Integral (A : Type*) := FreeAbelianGroup (FreeMonoid A)
abbrev Binary (A : Type*) := FreeAlgebra (ZMod 2) A
variable (A : Type*)

def reduction : Integral A →+* Binary A :=
  FreeAbelianGroup.liftMonoid (FreeMonoid.lift (FreeAlgebra.ι (ZMod 2)))

@[simp] lemma reduction_gen (a : A) :
    reduction A (FreeAbelianGroup.of (FreeMonoid.of a)) = FreeAlgebra.ι (ZMod 2) a := by
  simp [reduction]

end BinaryAlgebraPresentation

open scoped Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_PrefixArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace BinaryPrefixOperators.Arithmetic

abbrev Word := List (Fin 2)
abbrev Pair := Word × Word

variable (K : Type*) [CommRing K]
noncomputable section

def insertion : Word → algebra K
  | [] => 1
  | i :: w => l K i * insertion w

def deletion : Word → algebra K
  | [] => 1
  | i :: w => deletion w * r K i

@[simp] theorem prefix_nil : insertion K [] = 1 := rfl
@[simp] theorem prefix_cons (i : Fin 2) (w : Word) :
    insertion K (i::w) = l K i * insertion K w := rfl
@[simp] theorem deletion_nil : deletion K [] = 1 := rfl
@[simp] theorem deletion_cons (i : Fin 2) (w : Word) :
    deletion K (i::w) = deletion K w * r K i := rfl

@[simp] theorem prefix_append (v w : Word) : insertion K (v++w) = insertion K v * insertion K w := by
  induction v <;> simp [*, mul_assoc]
@[simp] theorem deletion_append (v w : Word) :
    deletion K (v++w) = deletion K w * deletion K v := by
  induction v <;> simp [*, mul_assoc]

@[simp] theorem prefix_single (w : Word) (x : Stream' (Fin 2)) (a : K) :
    (insertion K w : Module.End K (Space K)) (Finsupp.single x a) =
      Finsupp.single (w ++ₛ x) a := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change left K i ((insertion K w : Module.End K (Space K)) (Finsupp.single x a)) = _
    rw [ih, left_single]
    rfl

@[simp] theorem deletion_single (w : Word) (x : Stream' (Fin 2)) (a : K) :
    (deletion K w : Module.End K (Space K)) (Finsupp.single x a) =
      if x.take w.length = w then Finsupp.single (x.drop w.length) a else 0 := by
  induction w generalizing x with
  | nil => simp [deletion]
  | cons i w ih =>
    change (deletion K w : Module.End K (Space K)) (right K i (Finsupp.single x a)) = _
    rw [right_single]
    by_cases hx : x.head = i
    · rw [ite_eq_left hx, ih]
      simp only [List.length_cons, Stream'.take_succ, List.cons.injEq, hx, true_and,
        Stream'.drop_succ]
    · rw [ite_eq_right hx, map_zero]
      simp [Stream'.take_succ, hx]

def replacement (p : Pair) : algebra K := insertion K p.1 * deletion K p.2

@[simp] theorem replacement_single (p : Pair) (x : Stream' (Fin 2)) (a : K) :
    (replacement K p : Module.End K (Space K)) (Finsupp.single x a) =
      if x.take p.2.length = p.2 then Finsupp.single (p.1 ++ₛ x.drop p.2.length) a else 0 := by
  change (insertion K p.1 : Module.End K (Space K))
    ((deletion K p.2 : Module.End K (Space K)) (Finsupp.single x a)) = _
  rw [deletion_single]
  split <;> simp [*]

theorem replacement_domain (v w t : Word) (x : Stream' (Fin 2)) (a : K)
    (hw : w.length = t.length) :
    (replacement K (v,w) : Module.End K (Space K)) (Finsupp.single (t ++ₛ x) a) =
      if w = t then Finsupp.single (v ++ₛ x) a else 0 := by
  rw [replacement_single]
  simp only [hw, Stream'.take_append_of_le_length _ _ _ (Nat.le_refl _), List.take_length,
    Stream'.drop_append_stream]
  by_cases h : w=t <;> simp [h, Ne.symm]

theorem split_replacement (v w : Word) :
    replacement K (v,w) = replacement K (v++[0],w++[0]) +
      replacement K (v++[1],w++[1]) := by
  simp only [replacement, prefix_append, deletion_append, prefix_cons, prefix_nil,
    deletion_cons, deletion_nil, mul_one, one_mul]
  calc insertion K v * deletion K w =
      insertion K v * (l K 0 * r K 0 + l K 1 * r K 1) * deletion K w := by
        rw [l_r_partition, mul_one]
    _ = _ := by noncomm_ring

def marker (L : ℕ) : Stream' (Fin 2) := fun n => if n=L then 1 else 0

theorem marker_separates (L : ℕ) {v w : Word} (hv : v.length ≤ L) (hw : w.length ≤ L)
    (h : v ++ₛ marker L = w ++ₛ marker L) : v=w := by
  have hlen : v.length = w.length := by
    have no_lt : ∀ (a b : Word), a.length ≤ L → b.length ≤ L →
        a ++ₛ marker L = b ++ₛ marker L → ¬ a.length < b.length := by
      intro a b ha hb he hab
      have ht := congrArg (fun s : Stream' (Fin 2) => s.get (b.length + L)) he
      have hi : b.length + L = a.length + (b.length + L - a.length) := by omega
      rw [Stream'.get_append_right, hi, Stream'.get_append_right] at ht
      have hh : L < b.length + L - a.length := by omega
      change marker L (b.length + L - a.length) = marker L L at ht
      simp [marker, Nat.ne_of_gt hh] at ht
    exact Nat.le_antisymm (Nat.le_of_not_gt (no_lt w v hw hv h.symm))
      (Nat.le_of_not_gt (no_lt v w hv hw h))
  exact Stream'.append_left_injective _ _ _ _ h hlen

def evaluate : (Pair →₀ K) →ₗ[K] algebra K :=
  Finsupp.linearCombination K (replacement K)

@[simp] theorem evaluate_single (p : Pair) (a : K) :
    evaluate K (Finsupp.single p a) = a • replacement K p := by
  simp [evaluate]

theorem coefficient_test (p : Pair →₀ K) (m L : ℕ)
    (hm : ∀ q ∈ p.support, q.2.length = m)
    (hL : ∀ q ∈ p.support, q.1.length ≤ L)
    (v w : Word) (hv : v.length ≤ L) (hw : w.length = m) :
    ((evaluate K p : Module.End K (Space K))
      (Finsupp.single (w ++ₛ marker L) 1)) (v ++ₛ marker L) = p (v,w) := by
  classical
  have hs : evaluate K p = p.sum (fun q a => a • replacement K q) := rfl
  rw [hs]
  change ((algebra K).val (∑ q ∈ p.support, p q • replacement K q))
    (Finsupp.single (w ++ₛ marker L) 1) (v ++ₛ marker L) = _
  simp only [map_sum, map_smul]
  simp only [LinearMap.sum_apply, Finsupp.finsetSum_apply, LinearMap.smul_apply,
    Finsupp.smul_apply, smul_eq_mul]
  apply (Finset.sum_congr rfl (fun q hq => ?_)).trans
    (show (∑ q ∈ p.support, (Finsupp.single q (p q)) (v,w)) = p (v,w) from by
      rw [← Finsupp.finsetSum_apply]
      exact congrArg (fun a : Pair →₀ K => a (v,w)) (Finsupp.sum_single p))
  change p q * (((replacement K q : Module.End K (Space K)))
    (Finsupp.single (w ++ₛ marker L) 1)) (v ++ₛ marker L) = _
  rw [replacement_domain K _ _ _ _ _ ((hm _ hq).trans hw.symm)]
  have hsep : q.1 ++ₛ marker L = v ++ₛ marker L ↔ q.1 = v :=
    ⟨marker_separates L (hL q hq) hv, by rintro rfl; rfl⟩
  by_cases hqw : q.2 = w
  · simp only [ite_eq_left hqw, Finsupp.single_apply, hsep]
    by_cases hqv : q.1 = v
    · simp [hqv, hqw, Prod.ext_iff]
    · simp [hqv, Prod.ext_iff]
  · simp [hqw, Prod.ext_iff]

theorem evaluate_eq_zero_of_depth (p : Pair →₀ K) (m : ℕ)
    (hm : ∀ q ∈ p.support, q.2.length = m) : evaluate K p = 0 ↔ p=0 := by
  classical
  constructor
  · intro hz
    let L := p.support.sup (fun q => q.1.length)
    have hL : ∀ q ∈ p.support, q.1.length ≤ L := fun q hq => Finset.le_sup (f := fun q : Pair => q.1.length) hq
    apply Finsupp.ext
    intro q
    by_cases hq : q ∈ p.support
    · have ht := coefficient_test K p m L hm hL q.1 q.2 (hL q hq) (hm q hq)
      rw [hz] at ht
      simpa only [Subalgebra.coe_zero, LinearMap.zero_apply, Finsupp.zero_apply] using ht.symm
    · exact Finsupp.notMem_support_iff.mp hq
  · rintro rfl
    exact map_zero _

def subdivide : ℕ → Pair → (Pair →₀ K)
  | 0, p => Finsupp.single p 1
  | n+1, (v,w) => subdivide n (v++[0],w++[0]) + subdivide n (v++[1],w++[1])

@[simp] theorem evaluate_subdivide (n : ℕ) (p : Pair) :
    evaluate K (subdivide K n p) = replacement K p := by
  induction n generalizing p with
  | zero => simp [subdivide]
  | succ n ih =>
    rcases p with ⟨v,w⟩
    rw [subdivide, map_add, ih, ih, ← split_replacement]

theorem subdivide_depth (n : ℕ) (p q : Pair) (h : q ∈ (subdivide K n p).support) :
    q.2.length = p.2.length + n := by
  induction n generalizing p with
  | zero =>
    have hq := ((Finsupp.mem_support_single _ _ _).mp h).1
    simp [hq]
  | succ n ih =>
    rcases p with ⟨v,w⟩
    rw [subdivide] at h
    rcases Finset.mem_union.mp (Finsupp.support_add h) with h | h
    · have hh := ih _ h
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    · have hh := ih _ h
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

def uniform (m : ℕ) : (Pair →₀ K) →ₗ[K] (Pair →₀ K) :=
  Finsupp.linearCombination K (fun p => subdivide K (m-p.2.length) p)

@[simp] theorem uniform_single (m : ℕ) (p : Pair) (a : K) :
    uniform K m (Finsupp.single p a) = a • subdivide K (m-p.2.length) p := by
  simp [uniform]

@[simp] theorem evaluate_uniform (m : ℕ) (p : Pair →₀ K) :
    evaluate K (uniform K m p) = evaluate K p := by
  have he : (evaluate K).comp (uniform K m) = evaluate K := by
    apply Finsupp.lhom_ext
    intro q a
    simp [LinearMap.comp_apply]
  exact LinearMap.congr_fun he p

theorem uniform_depth (m : ℕ) (p : Pair →₀ K)
    (hm : ∀ q ∈ p.support, q.2.length ≤ m) :
    ∀ q ∈ (uniform K m p).support, q.2.length = m := by
  let V : Submodule K (Pair →₀ K) := Finsupp.supported K K {q | q.2.length = m}
  change uniform K m p ∈ V
  change (∑ q ∈ p.support, p q • subdivide K (m - q.2.length) q) ∈ V
  apply Submodule.sum_mem
  intro q hq
  apply Submodule.smul_mem
  intro t ht
  exact (subdivide_depth K _ q t ht).trans (Nat.add_sub_of_le (hm q hq))

end
end BinaryPrefixOperators.Arithmetic

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_PrefixLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace BinaryPrefixOperators.Arithmetic
namespace Lists

abbrev Poly (K : Type*) := List (K × Pair)

variable {K : Type*} [CommRing K]

noncomputable def toArray : Poly K → (Pair →₀ K)
  | [] => 0
  | (a,p) :: ps => Finsupp.single p a + toArray ps

@[simp] theorem toArray_nil : toArray ([] : Poly K) = 0 := rfl
@[simp] theorem toArray_cons (a : K) (p : Pair) (ps : Poly K) :
    toArray ((a,p)::ps) = Finsupp.single p a + toArray ps := rfl
@[simp] theorem toArray_append (p q : Poly K) : toArray (p++q) = toArray p + toArray q := by
  induction p with
  | nil => simp
  | cons x p ih => rcases x with ⟨a,x⟩; simp [ih, add_assoc]

def coefficient (p : Poly K) (q : Pair) : K :=
  p.foldr (fun x a => (if x.2 = q then x.1 else 0) + a) 0

@[simp] theorem coefficient_nil (q : Pair) : coefficient ([] : Poly K) q = 0 := rfl
@[simp] theorem coefficient_cons (a : K) (p q : Pair) (ps : Poly K) :
    coefficient ((a,p)::ps) q = (if p=q then a else 0) + coefficient ps q := rfl

theorem coefficient_eq (p : Poly K) (q : Pair) : coefficient p q = toArray p q := by
  induction p with
  | nil => rfl
  | cons x p ih => rcases x with ⟨a,x⟩; simp [ih, Finsupp.single_apply]

theorem coefficient_eq_zero_of_not_mem (p : Poly K) (q : Pair)
    (h : ∀ a, (a,q) ∉ p) : coefficient p q = 0 := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    rcases x with ⟨a,x⟩
    have hne : x ≠ q := by intro he; exact h a (by simp [he])
    rw [coefficient_cons, ite_eq_right hne, zero_add]
    exact ih (by intro b hb; exact h b (by simp [hb]))

def isZero [DecidableEq K] (p : Poly K) : Bool :=
  p.all (fun q => decide (coefficient p q.2 = 0))

theorem isZero_iff [DecidableEq K] (p : Poly K) : isZero p = true ↔ toArray p = 0 := by
  rw [isZero, List.all_eq_true]
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    ext q
    rw [← coefficient_eq]
    by_cases hq : ∃ a, (a,q) ∈ p
    · obtain ⟨a,ha⟩ := hq; exact h (a,q) ha
    · exact coefficient_eq_zero_of_not_mem p q (by simpa using hq)
  · intro h q hq
    rw [coefficient_eq, h]
    rfl

def suffixes : ℕ → List Word
  | 0 => [[]]
  | n+1 => (suffixes n).map (0 :: ·) ++ (suffixes n).map (1 :: ·)

def expandTerm (n : ℕ) (a : K × Pair) : Poly K :=
  (suffixes n).map (fun t => (a.1, (a.2.1 ++ t, a.2.2 ++ t)))

@[simp] theorem expandTerm_zero {K : Type*} [CommRing K] (a : K × Pair) :
    expandTerm 0 a = [a] := by
  simp [expandTerm, suffixes]

theorem expandTerm_succ {K : Type*} [CommRing K] (n : ℕ) (a : K) (v w : Word) :
    expandTerm (n+1) (a,(v,w)) =
      expandTerm n (a,(v++[0],w++[0])) ++ expandTerm n (a,(v++[1],w++[1])) := by
  simp only [expandTerm, suffixes, List.map_append, List.map_map]
  simp [Function.comp_def, List.append_assoc]

theorem toArray_expandTerm (n : ℕ) (a : K) (p : Pair) :
    toArray (expandTerm n (a,p)) = a • subdivide K n p := by
  induction n generalizing p with
  | zero => simp [subdivide]
  | succ n ih =>
    rcases p with ⟨v,w⟩
    rw [expandTerm_succ, toArray_append, ih, ih, subdivide, smul_add]

def depth : Poly K → ℕ
  | [] => 0
  | (_,p)::ps => max p.2.length (depth ps)

def spread (m : ℕ) (p : Poly K) : Poly K :=
  p.flatMap (fun a => expandTerm (m-a.2.2.length) a)

theorem toArray_spread (m : ℕ) (p : Poly K) :
    toArray (spread m p) = uniform K m (toArray p) := by
  induction p with
  | nil => simp [spread]
  | cons a p ih =>
    rcases a with ⟨a,v,w⟩
    simp only [spread, List.flatMap_cons, toArray_append, toArray_cons, map_add,
      uniform_single, ← ih, toArray_expandTerm]

theorem depth_bound (p : Poly K) : ∀ q ∈ (toArray p).support, q.2.length ≤ depth p := by
  induction p with
  | nil => simp
  | cons a p ih =>
    rcases a with ⟨a,v,w⟩
    intro q hq
    rcases Finset.mem_union.mp (Finsupp.support_add hq) with h | h
    · have he := ((Finsupp.mem_support_single _ _ _).mp h).1
      simp only [he, depth]
      exact Nat.le_max_left _ _
    · exact (ih q h).trans (Nat.le_max_right _ _)

def zeroTest [DecidableEq K] (p : Poly K) : Bool := isZero (spread (depth p) p)

theorem zeroTest_iff [DecidableEq K] (p : Poly K) :
    zeroTest p = true ↔ evaluate K (toArray p) = 0 := by
  rw [zeroTest, isZero_iff, toArray_spread,
    ← evaluate_eq_zero_of_depth K _ (depth p) (uniform_depth K _ _ (depth_bound p)),
    evaluate_uniform]

end Lists
end BinaryPrefixOperators.Arithmetic

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_PrefixEffective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace BinaryPrefixOperators.Arithmetic.Lists
variable {K : Type*} [CommRing K] [Primcodable K] [Finite K] [DecidableEq K]

theorem prim_add {K : Type*} [CommRing K] [Primcodable K] [Finite K]
    [DecidableEq K] : Primrec₂ ((· + ·) : K → K → K) :=
  (Primrec.dom_finite (fun p : K × K => p.1+p.2)).to₂

 theorem primrec_coefficient : Primrec₂ (coefficient (K:=K)) := by
  change Primrec (fun p : Poly K × Pair =>
    p.1.foldr (fun x a => (if x.2 = p.2 then x.1 else 0) + a) 0)
  apply Primrec.list_foldr (h := fun (p : Poly K × Pair) (a : (K × Pair) × K) =>
    (if a.1.2 = p.2 then a.1.1 else 0) + a.2) Primrec.fst (Primrec.const 0)
  exact (prim_add.comp
    (Primrec.ite (Primrec.eq.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const 0))
    (Primrec.snd.comp Primrec.snd)).to₂

 theorem primrec_isZero : Primrec (isZero (K:=K)) := by
  have hr : PrimrecRel (fun (a : K × Pair) (p : Poly K) => coefficient p a.2 = 0) :=
    Primrec.eq.comp (primrec_coefficient.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
      (Primrec.const 0)
  have hp : PrimrecPred (fun p : Poly K => ∀ a ∈ p, coefficient p a.2 = 0) :=
    hr.forall_mem_list.comp Primrec.id Primrec.id
  exact hp.decide.of_eq fun p => by
    apply Bool.eq_iff_iff.mpr
    simp [isZero]

 theorem primrec_suffixes : Primrec suffixes := by
  have h0 : Primrec (fun _ : Unit => ([[]] : List Word)) := Primrec.const _
  have hs : Primrec₂ (fun (_ : Unit) (p : ℕ × List Word) =>
      p.2.map (0::·) ++ p.2.map (1::·)) := by
    exact (Primrec.list_append.comp
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.const 0) Primrec.snd).to₂)
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.const 1) Primrec.snd).to₂)).to₂
  refine ((Primrec.nat_rec h0 hs).comp (Primrec.const ()) Primrec.id).of_eq ?_
  intro n
  dsimp only [id, Prod.snd]
  induction n with
  | zero => rfl
  | succ n ih => simp [suffixes, ih]

 theorem primrec_expandTerm {K : Type*} [CommRing K] [Primcodable K] [Finite K]
    [DecidableEq K] : Primrec₂ (expandTerm (K:=K)) := by
  unfold expandTerm
  apply Primrec.list_map (primrec_suffixes.comp Primrec.fst)
  exact ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
    ((Primrec.list_append.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd).pair
    (Primrec.list_append.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd))).to₂

 theorem primrec_depth {K : Type*} [CommRing K] [Primcodable K] [Finite K]
    [DecidableEq K] : Primrec (depth (K:=K)) := by
  have h : Primrec (fun p : Poly K =>
      p.foldr (fun a b => max a.2.2.length b) 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_max.comp
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.fst.comp Primrec.snd)))) (Primrec.snd.comp Primrec.snd)).to₂
  refine h.of_eq ?_
  intro p
  induction p with
  | nil => rfl
  | cons a p ih => simp [depth, ih]

 theorem primrec_spread : Primrec₂ (spread (K:=K)) := by
  unfold spread
  apply Primrec.list_flatMap Primrec.snd
  exact (primrec_expandTerm.comp
    (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    Primrec.snd).to₂

 theorem primrec_zeroTest : Primrec (zeroTest (K:=K)) :=
  primrec_isZero.comp (primrec_spread.comp primrec_depth Primrec.id)

end BinaryPrefixOperators.Arithmetic.Lists

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_PrefixProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace BinaryPrefixOperators.Arithmetic
variable (K : Type*) [CommRing K]

def cancel (w u : Word) : Option Pair :=
  if u.take w.length = w then some (u.drop w.length, []) else
    if w.take u.length = u then some ([], w.drop u.length) else none

def multiplyPair (p q : Pair) : Option Pair :=
  (cancel p.2 q.1).map (fun r => (p.1++r.1,q.2++r.2))

namespace Lists
variable {K}

def mulTerm (a b : K × Pair) : Poly K :=
  ((multiplyPair a.2 b.2).map (fun p => (a.1*b.1,p))).toList

def product (p q : Poly K) : Poly K :=
  p.flatMap (fun a => q.flatMap (mulTerm a))

noncomputable def value (p : Poly K) : algebra K := evaluate K (toArray p)

@[simp] theorem value_nil : value ([] : Poly K) = 0 := rfl
@[simp] theorem value_cons (a : K) (p : Pair) (ps : Poly K) :
    value ((a,p)::ps) = a • replacement K p + value ps := by
  simp [value]
@[simp] theorem value_append (p q : Poly K) : value (p++q) = value p + value q := by
  simp [value]

@[simp] theorem value_singleton (a : K) (p : Pair) :
    value [(a,p)] = a • replacement K p := by simp

end Lists
end BinaryPrefixOperators.Arithmetic

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_PrefixNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace BinaryPrefixOperators.Arithmetic

 theorem primrec_cancel : Primrec₂ cancel := by
  unfold cancel
  exact Primrec.ite
    (Primrec.eq.comp (Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd)
      Primrec.fst)
    (Primrec.option_some.comp ((Primrec.list_drop.comp
      (Primrec.list_length.comp Primrec.fst) Primrec.snd).pair (Primrec.const [])))
    (Primrec.ite
      (Primrec.eq.comp (Primrec.list_take.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst)
        Primrec.snd)
      (Primrec.option_some.comp ((Primrec.const []).pair
        (Primrec.list_drop.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst)))
      (Primrec.const none))

 theorem primrec_multiplyPair : Primrec₂ multiplyPair := by
  unfold multiplyPair
  exact Primrec.option_map
    (primrec_cancel.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    ((Primrec.list_append.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.list_append.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))).to₂

namespace Lists
variable {K : Type*} [CommRing K]

def negate (p : Poly K) : Poly K := p.map (fun a => (-a.1,a.2))

@[simp] theorem value_negate (p : Poly K) : value (negate p) = -value p := by
  induction p with
  | nil => simp [negate]
  | cons a p ih =>
    rcases a with ⟨a,v⟩
    simp only [negate] at ih ⊢
    simp [ih, neg_smul, neg_add_rev, add_comm]

def oneName : Poly K := [(1,([],[]))]

@[simp] theorem value_oneName : value (oneName (K:=K)) = 1 := by
  simp [oneName, replacement]

variable [Primcodable K] [Finite K]

 theorem primrec_negate : Primrec (negate (K:=K)) :=
  Primrec.list_map Primrec.id (((Primrec.dom_finite (fun a : K => -a)).comp
    (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)).to₂

 theorem primrec_mulTerm : Primrec₂ (mulTerm (K:=K)) := by
  have h : Primrec₂ (fun a b : K × Pair =>
      (multiplyPair a.2 b.2).map (fun p => (a.1*b.1,p))) := by
    exact Primrec.option_map
      (primrec_multiplyPair.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
      ((((Primrec.dom_finite (fun a : K × K => a.1*a.2)).comp
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))).pair Primrec.snd)).to₂
  have ht : Primrec (fun x : Option (K × Pair) => x.toList) := by
    refine (Primrec.option_casesOn Primrec.id (Primrec.const [])
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])).to₂).of_eq ?_
    intro x; cases x <;> rfl
  exact ht.comp h

variable [DecidableEq K]

noncomputable section
open scoped Classical

theorem computable_value_eq : ComputablePred
    (fun p : Poly K × Poly K => value p.1 = value p.2) := by
  have hc : ComputablePred (fun p : Poly K × Poly K =>
      zeroTest (p.1 ++ negate p.2) = true) :=
    (Primrec.eq.comp (primrec_zeroTest.comp
      (Primrec.list_append.comp Primrec.fst (primrec_negate.comp Primrec.snd)))
      (Primrec.const true)).computablePred
  apply hc.of_eq
  intro p
  rw [zeroTest_iff]
  change value (p.1 ++ negate p.2) = 0 ↔ _
  rw [value_append, value_negate, ← sub_eq_add_neg, sub_eq_zero]

end
end Lists
end BinaryPrefixOperators.Arithmetic

end OAI
end


