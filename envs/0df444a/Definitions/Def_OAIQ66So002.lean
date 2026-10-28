-- Prove2me | Definitions.Def_OAIQ66So002
-- name    : OAIQ66So002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:10:55.372006+00:00
-- url     : https://prove2.me/theorems/15e64952-6b39-4714-8abe-e6b228e1f9fd
-- title:
--   Definitions bundle OAIQ66So002 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 391 declarations of OpenAI's Lean: 162 definitions, 2 inductive types or structures, 2 instances and 225 theorems. The definitions and types are `OAI.CWCellular.SkeletalMap`, `OAI.CWCellular.SkeletalMap.onSkel`, `OAI.CWCellular.lowerHomeo`, `OAI.CWCellular.skeletonHomeo`, `OAI.CWCollar.OpenCells`, `OAI.CWCollar.OpenDisk`, `OAI.CWCollar.collar`, `OAI.CWCollar.collarEquiv`, `OAI.CWCollar.collarHomotopy`, `OAI.CWCollar.collarInclusion`, `OAI.CWCollar.lower`, `OAI.CWCollar.openCellMap`, `OAI.CWCollar.openCellsEquiv`, `OAI.CWCollar.openDom`, `OAI.CWCollar.openPreimage`, `OAI.CWCollar.openPreimageEquiv`, `OAI.CWCollar.paths`, `OAI.CWCollar.radius`, `OAI.CWCollar.retract`, `OAI.CWCylinder.Boundary`, `OAI.CWCylinder.Disk`, `OAI.CWCylinder.Faces`, `OAI.CWCylinder.SphereFill`, `OAI.CWCylinder.boundaryDisk`, `OAI.CWCylinder.diskTail`, `OAI.CWCylinder.diskTime`, `OAI.CWCylinder.encode`, `OAI.CWExtension.Boundary`, `OAI.CWExtension.Disk`, `OAI.CWExtension.Skel`, `OAI.CWExtension.boundarySkel`, `OAI.CWExtension.charMap`, `OAI.CWExtension.charSkel`, `OAI.CWExtension.extendSkel`, `OAI.CWExtension.familyData`, `OAI.CWExtension.skelIncl`, `OAI.CWExtension.skelLE`, `OAI.CWExtension.skelToComplex`, `OAI.CWExtension.stageData`, `OAI.CWExtension.stageQuot` and 124 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteCompiler_Normalization`, `FiniteCompiler_Simulator`, `FiniteType_BoundaryValue`, `FiniteType_CWCellular`, `FiniteType_CWCellularSkelInclHomologyIsIso`, `FiniteType_CWCylinder`, `FiniteType_ChainShortExact`, `FiniteType_DiskHEP`, `FiniteType_DiskRadial`, `FiniteType_DiskSigmaCollar`, `FiniteType_HomotopyFunctor`, `FiniteType_NonunitalCompression`, `FiniteType_PresentationGeometry`, `FiniteType_PresentationGeometryDescend`, `FiniteType_QuotientComplex`, `FiniteType_RegularCoverGeometry`, `FiniteType_RelativeChains`, `FiniteType_RelativeChainsEmptyProjectionQuasiIso`, `FiniteType_RepresentationKilling`, `FiniteType_SimplexRotation`, `FiniteType_SimplexSign`, `FiniteType_SingularExcision`, `FiniteType_SingularSigma`, `FiniteType_SingularSphereCycle`, `FiniteType_SingularSubdivisionIterate`, `FiniteType_SphereCover`, `FiniteType_SphereQuotient`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So010`, `OAIQ66So011`, `OAIQ66So012`, `OAIQ66So013`, `OAIQ66So014` and `OAIQ66So022`.
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
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Simulator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Literal finite-quota machine simulation and readout correctness.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator

inductive Move
  | stay | left | right
  deriving DecidableEq

end FiniteAlgebraicEnvelopes.Compiler.Simulator

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Raw-run folds, full word compilation, partial budgets, and bounded normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C S : Type*}

abbrev Item (C S : Type*) := Sum C (List S)

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CWCylinder
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
namespace CWCylinder
universe u
variable {Y : Type u} [TopologicalSpace Y]
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Boundary (n : ℕ) := sphere (0 : Fin n → ℝ) 1

theorem norm_cons {n : ℕ} (a : ℝ) (v : Fin n → ℝ) :
    ‖(Fin.cons a v : Fin (n+1) → ℝ)‖ = max ‖a‖ ‖v‖ := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg a) (le_max_left _ _))]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact (by simpa using norm_le_pi_norm v j : ‖(Fin.cons a v : Fin (n+1) → ℝ) j.succ‖ ≤ ‖v‖).trans (le_max_right _ _)
  · apply max_le
    · simpa using norm_le_pi_norm (Fin.cons a v : Fin (n+1) → ℝ) 0
    · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro j
      simpa using norm_le_pi_norm (Fin.cons a v : Fin (n+1) → ℝ) j.succ

theorem norm_tail_le {n : ℕ} (v : Fin (n+1) → ℝ) : ‖Fin.tail v‖ ≤ ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro j
  exact norm_le_pi_norm v j.succ

theorem norm_eq_max {n : ℕ} (v : Fin (n+1) → ℝ) :
    ‖v‖ = max ‖v 0‖ ‖Fin.tail v‖ := by
  have he : Fin.cons (v 0) (Fin.tail v) = v := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  simpa only [he] using norm_cons (v 0) (Fin.tail v)

theorem time_bound (t : I) : ‖2*(t:ℝ)-1‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_le]
  constructor <;> linarith [t.2.1,t.2.2]

def encode (n : ℕ) : C(I × Disk n,Disk (n+1)) :=
  ⟨fun z => ⟨Fin.cons (2*(z.1:ℝ)-1) z.2,by
      rw [mem_closedBall,dist_zero_right,norm_cons]
      exact max_le (time_bound z.1) (by simpa only [mem_closedBall,dist_zero_right] using z.2.2)⟩,
    (continuous_pi (fun i => Fin.cases (by fun_prop) (fun j => by fun_prop) i)).subtype_mk _⟩

def diskTail (n : ℕ) : C(Disk (n+1),Disk n) :=
  ⟨fun v => ⟨Fin.tail v.1,by
      rw [mem_closedBall,dist_zero_right]
      exact (norm_tail_le v.1).trans (by simpa only [mem_closedBall,dist_zero_right] using v.2)⟩,
    (by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro j
      exact (continuous_apply j.succ).comp continuous_subtype_val)⟩

def diskTime (n : ℕ) : C(Disk (n+1),I) :=
  ⟨fun v => ⟨(v.1 0 + 1)/2,by
      have hv : ‖v.1 0‖ ≤ 1 := (norm_le_pi_norm v.1 0).trans
        (by simpa only [mem_closedBall,dist_zero_right] using v.2)
      rw [Real.norm_eq_abs,abs_le] at hv
      constructor <;> linarith [hv.1,hv.2]⟩,
    (by
      apply Continuous.subtype_mk
      exact (((continuous_apply (0 : Fin (n+1))).comp continuous_subtype_val).add continuous_const).div_const 2)⟩

@[simp] theorem encode_tail (n : ℕ) (z : I × Disk n) : diskTail n (encode n z) = z.2 := by
  apply Subtype.ext
  funext i
  rfl

@[simp] theorem encode_time (n : ℕ) (z : I × Disk n) : diskTime n (encode n z) = z.1 := by
  apply Subtype.ext
  change ((2*(z.1:ℝ)-1)+1)/2 = (z.1:ℝ)
  ring

abbrev Faces (n : ℕ) := Disk n ⊕ (Disk n ⊕ (I × Boundary n))

def boundaryDisk (n : ℕ) : C(Boundary n,Disk n) :=
  ⟨fun v => ⟨v,sphere_subset_closedBall v.2⟩,continuous_subtype_val.subtype_mk _⟩

def SphereFill (Y : Type u) [TopologicalSpace Y] : Prop :=
  ∀ n (f : C(Boundary n,Y)), ∃ g : C(Disk n,Y), ∀ v, g (boundaryDisk n v) = f v

end CWCylinder

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SphereQuotient
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
namespace SphereQuotient
open Set Topology Metric
open scoped unitInterval
universe u
abbrev Disk := CWCylinder.Disk
abbrev Boundary := CWCylinder.Boundary

def height (r : ℝ) : ℝ := min 1 (max (-1) (6*r-3))
def scale (r : ℝ) : ℝ := min 1 (3*(1-r)) / max r (1/3)

theorem height_low {r : ℝ} (h : r ≤ 1/3) : height r = -1 := by
  unfold height
  rw [max_eq_left (by linarith),min_eq_right (by norm_num)]
theorem scale_low {r : ℝ} (h : r ≤ 1/3) : scale r = 3 := by
  unfold scale
  rw [max_eq_right h,min_eq_left (by linarith)]
  norm_num

theorem height_mid {r : ℝ} (h : 1/3 ≤ r) (h' : r ≤ 2/3) : height r = 6*r-3 := by
  unfold height
  rw [max_eq_right (by linarith),min_eq_right (by linarith)]
theorem scale_mid {r : ℝ} (h : 1/3 ≤ r) (h' : r ≤ 2/3) : scale r = 1/r := by
  unfold scale
  rw [max_eq_left h,min_eq_left (by linarith)]

theorem height_high {r : ℝ} (h : 2/3 ≤ r) : height r = 1 := by
  unfold height
  rw [max_eq_right (by linarith),min_eq_left (by linarith)]
theorem scale_high {r : ℝ} (h : 2/3 ≤ r) : scale r = 3*(1-r)/r := by
  unfold scale
  rw [max_eq_left (by linarith),min_eq_right (by linarith)]

theorem scale_nonneg {r : ℝ} (h : 0 ≤ r) (h' : r ≤ 1) : 0 ≤ scale r := by
  unfold scale
  exact div_nonneg (le_min (by norm_num) (by linarith)) (le_max_of_le_left h)

def point (n : ℕ) (v : Disk n) : Fin (n+1) → ℝ :=
  Fin.cons (height ‖v.1‖) (scale ‖v.1‖ • v.1)

theorem point_norm (n : ℕ) (v : Disk n) : ‖point n v‖ = 1 := by
  have hr : 0 ≤ ‖v.1‖ := norm_nonneg _
  have hr' : ‖v.1‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using v.2
  rw [point,CWCylinder.norm_cons,norm_smul,Real.norm_of_nonneg (scale_nonneg hr hr')]
  by_cases hlo : ‖v.1‖ ≤ 1/3
  · rw [height_low hlo,scale_low hlo]
    norm_num
    linarith
  by_cases hhi : 2/3 ≤ ‖v.1‖
  · rw [height_high hhi,scale_high hhi]
    have hn : ‖v.1‖ ≠ 0 := by linarith
    rw [div_mul_cancel₀ _ hn]
    norm_num
    linarith
  · rw [height_mid (le_of_not_ge hlo) (le_of_not_ge hhi),scale_mid (le_of_not_ge hlo) (le_of_not_ge hhi)]
    have hn : ‖v.1‖ ≠ 0 := by linarith
    rw [one_div_mul_cancel hn,max_eq_right]
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> linarith

def quotient (n : ℕ) : C(Disk n,Boundary (n+1)) :=
  ⟨fun v => ⟨point n v,by simpa only [mem_sphere,dist_zero_right] using point_norm n v⟩,by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Continuous (fun v : Disk n => height ‖v.1‖)
      unfold height
      fun_prop
    · change Continuous (fun v : Disk n => scale ‖v.1‖ * v.1 j)
      apply Continuous.mul
      · unfold scale
        apply Continuous.div
        · fun_prop
        · fun_prop
        · intro v
          have : (0:ℝ) < max ‖v.1‖ (1/3) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
          exact ne_of_gt this
      · exact (continuous_apply j).comp continuous_subtype_val⟩

def pole (n : ℕ) : Boundary (n+1) :=
  ⟨Fin.cons 1 0,by rw [mem_sphere,dist_zero_right,CWCylinder.norm_cons]; simp⟩

theorem quotient_boundary {n : ℕ} (v : Disk n) (hv : ‖v.1‖ = 1) : quotient n v = pole n := by
  apply Subtype.ext
  change (Fin.cons (height ‖v.1‖) (scale ‖v.1‖ • v.1) : Fin (n+1) → ℝ) = Fin.cons 1 0
  rw [hv,height_high (by norm_num),scale_high (by norm_num)]
  norm_num

theorem height_eq_low_iff (r : ℝ) : height r = -1 ↔ r ≤ 1/3 := by
  constructor
  · intro he
    by_contra hr
    have hh : -1 < height r := by
      apply lt_min (by norm_num)
      exact lt_max_of_lt_right (by linarith)
    linarith
  · exact height_low

theorem height_eq_high_iff (r : ℝ) : height r = 1 ↔ 2/3 ≤ r := by
  constructor
  · intro he
    by_contra hr
    have hh : height r < 1 := by
      apply lt_of_le_of_lt (min_le_right _ _)
      exact max_lt (by norm_num) (by linarith)
    linarith
  · exact height_high

theorem profile_injective {r s : ℝ} (hh : height r = height s)
    (ht : scale r * r = scale s * s) : r = s := by
  by_cases hr : r ≤ 1/3
  · have hs : s ≤ 1/3 := (height_eq_low_iff s).mp (hh.symm.trans (height_low hr))
    rw [scale_low hr,scale_low hs] at ht
    linarith
  by_cases hr' : 2/3 ≤ r
  · have hs' : 2/3 ≤ s := (height_eq_high_iff s).mp (hh.symm.trans (height_high hr'))
    rw [scale_high hr',scale_high hs',div_mul_cancel₀ _ (by linarith : r ≠ 0),
      div_mul_cancel₀ _ (by linarith : s ≠ 0)] at ht
    linarith
  · have hs : ¬s ≤ 1/3 := fun hs => hr ((height_eq_low_iff r).mp (hh.trans (height_low hs)))
    have hs' : ¬2/3 ≤ s := fun hs' => hr' ((height_eq_high_iff r).mp (hh.trans (height_high hs')))
    rw [height_mid (le_of_not_ge hr) (le_of_not_ge hr'),
      height_mid (le_of_not_ge hs) (le_of_not_ge hs')] at hh
    linarith

theorem quotient_eq {n : ℕ} {v w : Disk n} (h : quotient n v = quotient n w) :
    v = w ∨ (‖v.1‖ = 1 ∧ ‖w.1‖ = 1) := by
  have hv : ‖v.1‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using v.2
  have hw : ‖w.1‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using w.2
  have h₀ : height ‖v.1‖ = height ‖w.1‖ := congrArg (fun z : Boundary (n+1) => z.1 0) h
  have hs : scale ‖v.1‖ • v.1 = scale ‖w.1‖ • w.1 :=
    congrArg (fun z : Boundary (n+1) => Fin.tail z.1) h
  have hn : scale ‖v.1‖ * ‖v.1‖ = scale ‖w.1‖ * ‖w.1‖ := by
    simpa only [norm_smul,Real.norm_of_nonneg (scale_nonneg (norm_nonneg _) hv),
      Real.norm_of_nonneg (scale_nonneg (norm_nonneg _) hw)] using congrArg norm hs
  have hr := profile_injective h₀ hn
  by_cases hr1 : ‖v.1‖ = 1
  · exact Or.inr ⟨hr1,hr.symm.trans hr1⟩
  · apply Or.inl
    have hp : 0 < scale ‖v.1‖ := by
      apply div_pos
      · exact lt_min (by norm_num) (by have := lt_of_le_of_ne hv hr1; linarith)
      · exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    apply Subtype.ext
    rw [← hr] at hs
    exact smul_right_injective _ (ne_of_gt hp) hs

theorem quotient_eq_pole {n : ℕ} {v : Disk n} (h : quotient n v = pole n) : ‖v.1‖ = 1 := by
  have h₀ : height ‖v.1‖ = 1 := congrArg (fun z : Boundary (n+1) => z.1 0) h
  have hs : scale ‖v.1‖ • v.1 = (0 : Fin n → ℝ) :=
    congrArg (fun z : Boundary (n+1) => Fin.tail z.1) h
  have hv := (height_eq_high_iff _).mp h₀
  have hn : scale ‖v.1‖ * ‖v.1‖ = 0 := by
    have hv' : ‖v.1‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using v.2
    simpa only [norm_smul,Real.norm_of_nonneg (scale_nonneg (norm_nonneg _) hv'),norm_zero] using congrArg norm hs
  rw [scale_high hv,div_mul_cancel₀ _ (by linarith : ‖v.1‖ ≠ 0)] at hn
  linarith

theorem boundary_ext {n : ℕ} {v w : Boundary (n+1)}
    (h₀ : v.1 0 = w.1 0) (ht : Fin.tail v.1 = Fin.tail w.1) : v = w := by
  apply Subtype.ext
  funext i
  exact Fin.cases h₀ (fun j => congrFun ht j) i

theorem quotient_surjective_or_pole (n : ℕ) (z : Boundary (n+1)) :
    z = pole n ∨ ∃ v,quotient n v = z := by
  have hz : ‖z.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using z.2
  have hs : ‖Fin.tail z.1‖ ≤ 1 := (CWCylinder.norm_tail_le z.1).trans_eq hz
  have ha : |z.1 0| ≤ 1 := by
    simpa only [Real.norm_eq_abs,hz] using norm_le_pi_norm z.1 0
  have hal := (abs_le.mp ha).1
  have hau := (abs_le.mp ha).2
  by_cases hlo : z.1 0 = -1
  · apply Or.inr
    let x : Fin n → ℝ := (1/3 : ℝ) • Fin.tail z.1
    have hx : ‖x‖ = (1/3 : ℝ) * ‖Fin.tail z.1‖ := by
      rw [norm_smul,Real.norm_of_nonneg (by norm_num)]
    have hx' : ‖x‖ ≤ 1/3 := by rw [hx]; linarith
    let v : Disk n := ⟨x,by rw [mem_closedBall,dist_zero_right]; linarith⟩
    refine ⟨v,boundary_ext ?_ ?_⟩
    · exact (height_low hx').trans hlo.symm
    · change scale ‖x‖ • x = _
      rw [scale_low hx']
      dsimp [x]
      rw [smul_smul]
      norm_num
  by_cases hhi : z.1 0 = 1
  · by_cases hs0 : Fin.tail z.1 = 0
    · exact Or.inl (boundary_ext hhi hs0)
    apply Or.inr
    have hspos : 0 < ‖Fin.tail z.1‖ := norm_pos_iff.mpr hs0
    let r : ℝ := 1 - ‖Fin.tail z.1‖/3
    have hrlo : 2/3 ≤ r := by dsimp [r]; linarith
    have hrhi : r ≤ 1 := by dsimp [r]; linarith
    have hrpos : 0 < r := by linarith
    let x : Fin n → ℝ := (r/‖Fin.tail z.1‖) • Fin.tail z.1
    have hx : ‖x‖ = r := by
      rw [norm_smul,Real.norm_of_nonneg (div_nonneg hrpos.le hspos.le),div_mul_cancel₀ _ (ne_of_gt hspos)]
    let v : Disk n := ⟨x,by rw [mem_closedBall,dist_zero_right,hx]; exact hrhi⟩
    refine ⟨v,boundary_ext ?_ ?_⟩
    · change height ‖x‖ = z.1 0
      rw [hx,height_high hrlo,hhi]
    · change scale ‖x‖ • x = _
      rw [hx,scale_high hrlo]
      dsimp only [x]
      rw [smul_smul]
      have he : 3*(1-r)/r * (r/‖Fin.tail z.1‖) = 1 := by
        field_simp [ne_of_gt hrpos,ne_of_gt hspos]
        dsimp [r]
        ring
      rw [he,one_smul]
  · apply Or.inr
    have ht : ‖Fin.tail z.1‖ = 1 := by
      have hmax : max ‖z.1 0‖ ‖Fin.tail z.1‖ = 1 := by rw [← CWCylinder.norm_eq_max,hz]
      have hne : ‖z.1 0‖ ≠ 1 := by
        intro he
        rw [Real.norm_eq_abs] at he
        rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp he with he | he
        · exact hhi he
        · exact hlo he
      exact (max_eq_iff.mp hmax).resolve_left (fun h => hne h.1) |>.1
    let r : ℝ := (z.1 0 + 3)/6
    have hrlo : 1/3 ≤ r := by dsimp [r]; linarith
    have hrhi : r ≤ 2/3 := by dsimp [r]; linarith
    have hrpos : 0 < r := by linarith
    let x : Fin n → ℝ := r • Fin.tail z.1
    have hx : ‖x‖ = r := by rw [norm_smul,Real.norm_of_nonneg hrpos.le,ht,mul_one]
    let v : Disk n := ⟨x,by rw [mem_closedBall,dist_zero_right,hx]; linarith⟩
    refine ⟨v,boundary_ext ?_ ?_⟩
    · change height ‖x‖ = z.1 0
      rw [hx,height_mid hrlo hrhi]
      dsimp [r]
      ring
    · change scale ‖x‖ • x = _
      rw [hx,scale_mid hrlo hrhi]
      dsimp only [x]
      rw [smul_smul,one_div_mul_cancel (ne_of_gt hrpos),one_smul]

def sphereQuot (n : ℕ) : C(Disk n ⊕ Unit,Boundary (n+1)) :=
  ⟨Sum.elim (quotient n) (fun _ => pole n),
    continuous_sum_dom.mpr ⟨(quotient n).continuous,continuous_const⟩⟩

theorem sphereQuot_surjective (n : ℕ) : Function.Surjective (sphereQuot n) := by
  intro z
  rcases quotient_surjective_or_pole n z with hz | ⟨v,hv⟩
  · exact ⟨Sum.inr (),hz.symm⟩
  · exact ⟨Sum.inl v,hv⟩

theorem sphereQuot_isQuotientMap (n : ℕ) : IsQuotientMap (sphereQuot n) :=
  IsQuotientMap.of_surjective_continuous (sphereQuot_surjective n) (sphereQuot n).continuous

end SphereQuotient

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_HomotopyFunctor
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

namespace HurewiczConstruction
open Set Topology Metric _root_.CategoryTheory AlgebraicTopology
open scoped unitInterval
open SphereQuotient
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

abbrev integralHomology (n : ℕ) (X : Type) [TopologicalSpace X] : ModuleCat ℤ :=
  ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)

def pushforward (n : ℕ) (f : C(X,Y)) : integralHomology n X →ₗ[ℤ] integralHomology n Y :=
  (((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).hom

theorem pushforward_homotopic (n : ℕ) {f g : C(X,Y)} (H : f.Homotopy g) :
    pushforward n f = pushforward n g := by
  have h := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (f := TopCat.ofHom f) (g := TopCat.ofHom g) H (ModuleCat.of ℤ ℤ) n
  exact congrArg ModuleCat.Hom.hom h

end HurewiczConstruction

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

theorem quotientMk_isClosedMap {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (r : Setoid X) (hr : IsClosed {p : X × X | r p.1 p.2}) :
    IsClosedMap (Quotient.mk r) := by
  intro A hA
  apply isQuotientMap_quotient_mk'.isClosed_preimage.mp
  have hs := isClosedMap_snd_of_compactSpace
    ({p : X × X | r p.1 p.2} ∩ Prod.fst ⁻¹' A) (hr.inter (hA.preimage continuous_fst))
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_preimage, mem_image, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, hx⟩
    exact ⟨(a, x), ⟨Quotient.exact hx, ha⟩, rfl⟩
  · rintro ⟨⟨a, b⟩, ⟨hab, ha⟩, rfl⟩
    exact ⟨a, ha, Quotient.sound hab⟩

theorem quotient_t2Space {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (r : Setoid X) (hr : IsClosed {p : X × X | r p.1 p.2}) :
    T2Space (Quotient r) := by
  have hp : IsProperMap (Quotient.mk r) := by
    apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    refine ⟨continuous_quotient_mk', quotientMk_isClosedMap r hr, ?_⟩
    intro y
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective y
    have hc : IsClosed {a | r a x} := hr.preimage (continuous_id.prodMk continuous_const)
    convert hc.isCompact using 1
    all_goals try with_reducible_and_instances rfl
    ext a
    exact Quotient.eq
  apply t2_iff_isClosed_diagonal.mpr
  have h := (hp.prodMap hp).isClosedMap _ hr
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [mem_diagonal_iff, mem_image, mem_ofPred_eq]
  constructor
  · intro he
    obtain ⟨x, hx⟩ := Quotient.mk_surjective p.1
    exact ⟨(x, x), r.refl x, Prod.ext hx (hx.trans he)⟩
  · rintro ⟨⟨a, b⟩, hab, he⟩
    cases he
    exact Quotient.sound hab

namespace Adjunction

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {A : Set Y}

noncomputable def normalize (f : C(A, X)) : X ⊕ Y → X ⊕ Y := by
  classical
  exact Sum.elim Sum.inl (fun y => if h : y ∈ A then Sum.inl (f ⟨y, h⟩) else Sum.inr y)

noncomputable def relation (f : C(A, X)) : Setoid (X ⊕ Y) :=
  Setoid.ker (normalize f)

@[simp] theorem relation_iff (f : C(A, X)) (a b : X ⊕ Y) :
    relation f a b ↔ normalize f a = normalize f b := Iff.rfl

abbrev Space (f : C(A, X)) := Quotient (relation f)

def old (f : C(A, X)) (x : X) : Space f := Quotient.mk _ (Sum.inl x)
def disk (f : C(A, X)) (y : Y) : Space f := Quotient.mk _ (Sum.inr y)

@[simp] theorem normalize_inl (f : C(A, X)) (x : X) :
    normalize f (Sum.inl x) = Sum.inl x := rfl

@[simp] theorem normalize_inr_mem (f : C(A, X)) (y : A) :
    normalize f (Sum.inr y.1) = Sum.inl (f y) := by
  simp [normalize, y.property]

@[simp] theorem normalize_inr_notMem (f : C(A, X)) (y : Y) (hy : y ∉ A) :
    normalize f (Sum.inr y) = Sum.inr y := by
  simp [normalize, hy]

theorem relation_eq (f : C(A, X)) :
    {p : (X ⊕ Y) × (X ⊕ Y) | relation f p.1 p.2} =
    diagonal (X ⊕ Y) ∪
      range (fun a : A => (Sum.inl (f a), Sum.inr a.1)) ∪
      range (fun a : A => (Sum.inr a.1, Sum.inl (f a))) ∪
      (fun p : A × A => (Sum.inr p.1.1, Sum.inr p.2.1)) ''
        {p : A × A | f p.1 = f p.2} := by
  classical
  ext p
  rcases p with ⟨x | y, x' | y'⟩
  · simp [relation_iff, normalize]
  · by_cases hy : y' ∈ A
    · simp [relation_iff, normalize, hy, Subtype.exists, eq_comm]
    · simp [relation_iff, normalize, hy, Subtype.exists]
  · by_cases hy : y ∈ A
    · simp [relation_iff, normalize, hy, Subtype.exists]
    · simp [relation_iff, normalize, hy, Subtype.exists]
  · by_cases hy : y ∈ A <;> by_cases hy' : y' ∈ A
    · simp [relation_iff, normalize, hy, hy', Subtype.exists]
      rintro rfl
      rfl
    · simp [relation_iff, normalize, hy, hy', Subtype.exists]
      exact fun he => hy' (he ▸ hy)
    · simp [relation_iff, normalize, hy, hy', Subtype.exists]
      exact fun he => hy (he.symm ▸ hy')
    · simp [relation_iff, normalize, hy, hy', Subtype.exists]

theorem relation_isClosed [T2Space X] [T2Space Y] [CompactSpace Y]
    (hA : IsClosed A) (f : C(A, X)) :
    IsClosed {p : (X ⊕ Y) × (X ⊕ Y) | relation f p.1 p.2} := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  rw [relation_eq]
  refine ((isClosed_diagonal.union ?_).union ?_).union ?_
  · exact (isCompact_range (continuous_inl.comp f.continuous |>.prodMk
      (continuous_inr.comp continuous_subtype_val))).isClosed
  · exact (isCompact_range (continuous_inr.comp continuous_subtype_val |>.prodMk
      (continuous_inl.comp f.continuous))).isClosed
  · apply IsCompact.isClosed
    apply IsCompact.image
      (isClosed_eq (f.continuous.comp continuous_fst) (f.continuous.comp continuous_snd)).isCompact
    fun_prop

theorem t2Space [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]
    (hA : IsClosed A) (f : C(A, X)) : T2Space (Space f) :=
  quotient_t2Space (relation f) (relation_isClosed hA f)

theorem continuous_old (f : C(A, X)) : Continuous (old f) :=
  continuous_quotient_mk'.comp continuous_inl

theorem continuous_disk (f : C(A, X)) : Continuous (disk f) :=
  continuous_quotient_mk'.comp continuous_inr

@[simp] theorem old_inj (f : C(A, X)) {x x' : X} : old f x = old f x' ↔ x = x' := by
  change Quotient.mk (relation f) (Sum.inl x) = Quotient.mk (relation f) (Sum.inl x') ↔ _
  rw [Quotient.eq]
  simp only [relation_iff, normalize_inl, Sum.inl.injEq]

@[simp] theorem disk_boundary (f : C(A, X)) (y : A) : disk f y.1 = old f (f y) := by
  apply Quotient.sound
  exact normalize_inr_mem f y

theorem old_isClosedEmbedding [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]
    (hA : IsClosed A) (f : C(A, X)) : IsClosedEmbedding (old f) := by
  let := t2Space hA f
  exact (continuous_old f).isClosedEmbedding (fun _ _ => (old_inj f).mp)

def interiorMap (f : C(A, X)) (y : (Aᶜ : Set Y)) : Space f := disk f y.1

@[simp] theorem disk_eq_disk_of_notMem (f : C(A, X)) {y y' : Y} (hy : y ∉ A) :
    disk f y = disk f y' ↔ y = y' := by
  classical
  change Quotient.mk (relation f) _ = Quotient.mk (relation f) _ ↔ _
  rw [Quotient.eq, relation_iff, normalize_inr_notMem _ _ hy]
  by_cases hy' : y' ∈ A
  · simp only [normalize_inr_mem f ⟨y', hy'⟩, Sum.inr_ne_inl, false_iff]
    rintro rfl
    exact hy hy'
  · simp [normalize_inr_notMem _ _ hy']

@[simp] theorem old_ne_disk_of_notMem (f : C(A, X)) (x : X) {y : Y} (hy : y ∉ A) :
    old f x ≠ disk f y := by
  intro he
  have h : normalize f (Sum.inl x) = normalize f (Sum.inr y) := Quotient.exact he
  simp only [normalize_inl, normalize_inr_notMem _ _ hy, Sum.inl_ne_inr] at h

theorem interiorMap_preimage_image (f : C(A, X)) (U : Set (Aᶜ : Set Y)) :
    Quotient.mk (relation f) ⁻¹' (interiorMap f '' U) =
      (fun y : (Aᶜ : Set Y) => (Sum.inr y.1 : X ⊕ Y)) '' U := by
  ext z
  constructor
  · rintro ⟨y, hy, he⟩
    rcases z with x | z
    · exact False.elim (old_ne_disk_of_notMem f x y.property he.symm)
    · exact ⟨y, hy, congrArg Sum.inr ((disk_eq_disk_of_notMem f y.property).mp he)⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem interiorMap_isOpenEmbedding (hA : IsClosed A) (f : C(A, X)) :
    IsOpenEmbedding (interiorMap f) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (continuous_disk f).comp continuous_subtype_val
  · intro a b he
    exact Subtype.ext ((disk_eq_disk_of_notMem f a.property).mp he)
  · intro U hU
    apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
    change IsOpen (Quotient.mk (relation f) ⁻¹' (interiorMap f '' U))
    rw [interiorMap_preimage_image]
    exact (isOpenMap_inr.comp hA.isOpen_compl.isOpenMap_subtype_val) U hU

end Adjunction

namespace Cells
section

open Metric

abbrev Disk (d : ℕ) := (closedBall (0 : Fin d → ℝ) 1 : Set (Fin d → ℝ))
abbrev OpenDisk (d : ℕ) := (ball (0 : Fin d → ℝ) 1 : Set (Fin d → ℝ))

def boundary (k d : ℕ) : Set (Fin k × Disk d) :=
  {p | p.2.1 ∈ sphere (0 : Fin d → ℝ) 1}

theorem boundary_closed (k d : ℕ) : IsClosed (boundary k d) :=
  isClosed_sphere.preimage (continuous_subtype_val.comp continuous_snd)

variable {X : Type*} [TopologicalSpace X] {k d : ℕ}
variable (f : C(boundary k d, X))

abbrev Space := Adjunction.Space f

instance instT2SpaceSpaceOfCompactSpace [T2Space X] [CompactSpace X] : T2Space (Space f) :=
  Adjunction.t2Space (boundary_closed k d) f

def characteristic (i : Fin k) (v : Fin d → ℝ) : Space f := by
  classical
  exact if h : v ∈ closedBall (0 : Fin d → ℝ) 1
    then Adjunction.disk f (i, ⟨v, h⟩)
    else Adjunction.disk f (i, ⟨0, by simp⟩)

@[simp] theorem characteristic_on_disk (i : Fin k) (v : Disk d) :
    characteristic f i v.1 = Adjunction.disk f (i, v) := by
  simp [characteristic, v.property]

theorem characteristic_continuousOn (i : Fin k) :
    ContinuousOn (characteristic f i) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : ((closedBall 0 1).domRestrict (characteristic f i)) =
      fun v : Disk d => Adjunction.disk f (i, v) := by
    funext v
    exact characteristic_on_disk f i v
  rw [he]
  exact (Adjunction.continuous_disk f).comp (continuous_const.prodMk continuous_id)

def interiorInDisk (v : OpenDisk d) : Disk d := ⟨v.1, ball_subset_closedBall v.2⟩

theorem interiorInDisk_isOpenEmbedding : IsOpenEmbedding (interiorInDisk (d := d)) :=
  IsOpenEmbedding.id.restrict (fun _ h => ball_subset_closedBall h) isOpen_ball

def interiorInFamily (i : Fin k) (v : OpenDisk d) : ↑((boundary k d)ᶜ) :=
  ⟨(i, interiorInDisk v), by
    change v.1 ∉ sphere (0 : Fin d → ℝ) 1
    exact ne_of_lt v.2⟩

theorem prodMk_isOpenEmbedding (i : Fin k) :
    IsOpenEmbedding (Prod.mk i : Disk d → Fin k × Disk d) := by
  refine ⟨isEmbedding_prodMkRight i, ?_⟩
  have he : range (Prod.mk i : Disk d → Fin k × Disk d) = {i} ×ˢ univ := by
    ext p
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨rfl, mem_univ _⟩
    · rintro ⟨hp, _⟩
      exact ⟨p.2, Prod.ext hp.symm rfl⟩
  rw [he]
  exact (isOpen_discrete _).prod isOpen_univ

theorem interiorInFamily_isOpenEmbedding (i : Fin k) :
    IsOpenEmbedding (interiorInFamily (d := d) i) := by
  have hh : IsOpenEmbedding (fun v : OpenDisk d => (i, interiorInDisk v)) :=
    (prodMk_isOpenEmbedding i).comp interiorInDisk_isOpenEmbedding
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact hh.continuous.subtype_mk _
  · intro a b h
    exact hh.injective (congrArg Subtype.val h)
  · exact hh.isOpenMap.subtype_mk _

theorem characteristic_interior (i : Fin k) :
    (OpenDisk d).domRestrict (characteristic f i) =
      Adjunction.interiorMap f ∘ interiorInFamily i := by
  funext v
  exact characteristic_on_disk f i (interiorInDisk v)

theorem characteristic_isOpenEmbedding (i : Fin k) :
    IsOpenEmbedding ((OpenDisk d).domRestrict (characteristic f i)) := by
  rw [characteristic_interior]
  exact (Adjunction.interiorMap_isOpenEmbedding (boundary_closed k d) f).comp
    (interiorInFamily_isOpenEmbedding i)

theorem characteristic_injOn (i : Fin k) :
    InjOn (characteristic f i) (ball 0 1) := by
  intro a ha b hb he
  exact congrArg Subtype.val ((characteristic_isOpenEmbedding f i).injective
    (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) he)

def chart (i : Fin k) : PartialEquiv (Fin d → ℝ) (Space f) :=
  (characteristic_injOn f i).toPartialEquiv (characteristic f i) (ball 0 1)

@[simp] theorem chart_coe (i : Fin k) : (chart f i : (Fin d → ℝ) → Space f) =
    characteristic f i := rfl

@[simp] theorem chart_source (i : Fin k) : (chart f i).source = ball 0 1 := rfl

@[simp] theorem chart_target (i : Fin k) : (chart f i).target =
    characteristic f i '' ball 0 1 := rfl

theorem chart_continuousOn (i : Fin k) :
    ContinuousOn (chart f i) (closedBall 0 1) := characteristic_continuousOn f i

theorem chart_continuousOn_symm (i : Fin k) :
    ContinuousOn (chart f i).symm (chart f i).target := by
  rw [← (chart f i).image_source_eq_target]
  exact (characteristic_isOpenEmbedding f i).isOpenMap.continuousOn_image_of_leftInvOn
    (chart f i).leftInvOn

variable [T2Space X] [CompactSpace X] [Nonempty X]
variable [CWComplex (univ : Set X)]

def oldChart (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n) :
    PartialEquiv (Fin n → ℝ) (Space f) :=
  (RelCWComplex.map n i).trans
    ((Adjunction.old_isClosedEmbedding (boundary_closed k d) f).isEmbedding.toPartialHomeomorph
      (Adjunction.old f)).toPartialEquiv

@[simp] theorem oldChart_apply (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n)
    (v : Fin n → ℝ) : oldChart f n i v = Adjunction.old f (RelCWComplex.map n i v) := rfl

@[simp] theorem oldChart_source (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n) :
    (oldChart f n i).source = ball 0 1 := by
  simp [oldChart, PartialEquiv.trans_source, RelCWComplex.source_eq]

theorem oldChart_continuousOn (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n) :
    ContinuousOn (oldChart f n i) (closedBall 0 1) :=
  (Adjunction.continuous_old f).comp_continuousOn (RelCWComplex.continuousOn n i)

theorem oldChart_continuousOn_symm (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n) :
    ContinuousOn (oldChart f n i).symm (oldChart f n i).target := by
  let e := (Adjunction.old_isClosedEmbedding (boundary_closed k d) f).isEmbedding.toPartialHomeomorph
    (Adjunction.old f)
  change ContinuousOn ((RelCWComplex.map n i).symm ∘ e.symm)
    (e.target ∩ e.symm ⁻¹' (RelCWComplex.map n i).target)
  exact (RelCWComplex.continuousOn_symm n i).comp
    (e.continuousOn_symm.mono inter_subset_left) (fun _ h => h.2)

def NewCell (n : ℕ) := RelCWComplex.cell (univ : Set X) n ⊕ (Fin k × PLift (n = d))

def newChart (n : ℕ) : NewCell (X := X) (k := k) (d := d) n →
    PartialEquiv (Fin n → ℝ) (Space f)
  | Sum.inl i => oldChart f n i
  | Sum.inr ⟨i, ⟨h⟩⟩ => h.symm ▸ chart f i

@[simp] theorem newChart_old (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n) :
    newChart f n (Sum.inl i) = oldChart f n i := rfl

@[simp] theorem newChart_new (i : Fin k) :
    newChart f d (Sum.inr ⟨i, ⟨rfl⟩⟩) = chart f i := rfl

theorem newChart_source (n : ℕ) (i : NewCell (X := X) (k := k) (d := d) n) :
    (newChart f n i).source = ball 0 1 := by
  rcases i with i | ⟨i, ⟨h⟩⟩
  · exact oldChart_source f n i
  · subst n
    exact chart_source f i

theorem newChart_continuousOn (n : ℕ)
    (i : NewCell (X := X) (k := k) (d := d) n) :
    ContinuousOn (newChart f n i) (closedBall 0 1) := by
  rcases i with i | ⟨i, ⟨h⟩⟩
  · exact oldChart_continuousOn f n i
  · subst n
    exact chart_continuousOn f i

theorem newChart_continuousOn_symm (n : ℕ)
    (i : NewCell (X := X) (k := k) (d := d) n) :
    ContinuousOn (newChart f n i).symm (newChart f n i).target := by
  rcases i with i | ⟨i, ⟨h⟩⟩
  · exact oldChart_continuousOn_symm f n i
  · subst n
    exact chart_continuousOn_symm f i

omit [T2Space X] [CompactSpace X] [Nonempty X] [CWComplex (univ : Set X)] in
@[simp] theorem chart_apply_ball (i : Fin k) (v : Fin d → ℝ) (hv : v ∈ ball 0 1) :
    chart f i v = Adjunction.disk f (i, interiorInDisk ⟨v, hv⟩) :=
  characteristic_on_disk f i (interiorInDisk ⟨v, hv⟩)

omit [T2Space X] [CompactSpace X] [Nonempty X] [CWComplex (univ : Set X)] in
theorem chart_apply_sphere (i : Fin k) (v : Fin d → ℝ) (hv : v ∈ sphere 0 1) :
    chart f i v = Adjunction.old f
      (f ⟨(i, ⟨v, sphere_subset_closedBall hv⟩), hv⟩) := by
  rw [chart_coe, characteristic_on_disk f i ⟨v, sphere_subset_closedBall hv⟩]
  exact Adjunction.disk_boundary f ⟨(i, ⟨v, sphere_subset_closedBall hv⟩), hv⟩

theorem newChart_cell_eq {n m : ℕ}
    (i : NewCell (X := X) (k := k) (d := d) n)
    (j : NewCell (X := X) (k := k) (d := d) m)
    {v : Fin n → ℝ} {w : Fin m → ℝ} (hv : v ∈ ball 0 1) (hw : w ∈ ball 0 1)
    (he : newChart f n i v = newChart f m j w) :
    (⟨n, i⟩ : Σ n, NewCell (X := X) (k := k) (d := d) n) = ⟨m, j⟩ := by
  classical
  rcases i with i | ⟨i, ⟨hi⟩⟩ <;> rcases j with j | ⟨j, ⟨hj⟩⟩
  · have hx : RelCWComplex.map n i v = RelCWComplex.map m j w :=
      (Adjunction.old_inj f).mp he
    by_cases hij : (⟨n, i⟩ : Σ n, RelCWComplex.cell (univ : Set X) n) = ⟨m, j⟩
    · cases hij
      rfl
    · exact False.elim (Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne hij)
        ⟨v, hv, rfl⟩ ⟨w, hw, hx.symm⟩)
  · subst m
    have he' : Adjunction.old f (RelCWComplex.map n i v) =
        Adjunction.disk f (j, interiorInDisk ⟨w, hw⟩) := by
      simpa only [newChart_old, oldChart_apply, newChart_new, chart_apply_ball f j w hw] using he
    exact False.elim (Adjunction.old_ne_disk_of_notMem f _
      (interiorInFamily j ⟨w, hw⟩).property he')
  · subst n
    have he' : Adjunction.old f (RelCWComplex.map m j w) =
        Adjunction.disk f (i, interiorInDisk ⟨v, hv⟩) := by
      simpa only [newChart_old, oldChart_apply, newChart_new, chart_apply_ball f i v hv] using he.symm
    exact False.elim (Adjunction.old_ne_disk_of_notMem f _
      (interiorInFamily i ⟨v, hv⟩).property he')
  · subst n
    subst m
    have he' : Adjunction.disk f (i, interiorInDisk ⟨v, hv⟩) =
        Adjunction.disk f (j, interiorInDisk ⟨w, hw⟩) := by
      simpa only [newChart_new, chart_apply_ball f i v hv, chart_apply_ball f j w hw] using he
    have he'' := (Adjunction.disk_eq_disk_of_notMem f
      (interiorInFamily i ⟨v, hv⟩).property).mp he'
    have hij : i = j := congrArg Prod.fst he''
    subst j
    rfl

theorem newChart_pairwiseDisjoint :
    (univ : Set (Σ n, NewCell (X := X) (k := k) (d := d) n)).PairwiseDisjoint
      (fun ni => newChart f ni.1 ni.2 '' ball 0 1) := by
  rintro ⟨n, i⟩ _ ⟨m, j⟩ _ hne
  apply Set.disjoint_left.mpr
  rintro x ⟨v, hv, rfl⟩ ⟨w, hw, he⟩
  exact hne (newChart_cell_eq f i j hv hw he.symm)

variable (hdim : ∀ n, RelCWComplex.cell (univ : Set X) n → n < d)

include hdim in
theorem newChart_mapsTo (n : ℕ) (i : NewCell (X := X) (k := k) (d := d) n) :
    MapsTo (newChart f n i) (sphere 0 1)
      (⋃ (m < n) (j : NewCell (X := X) (k := k) (d := d) m),
        newChart f m j '' closedBall 0 1) := by
  rcases i with i | ⟨i, ⟨hi⟩⟩
  · obtain ⟨I, hI⟩ := CWComplex.mapsTo n i
    intro v hv
    have hh := hI hv
    simp only [mem_iUnion, mem_image] at hh ⊢
    obtain ⟨m, hm, j, _, w, hw, he⟩ := hh
    refine ⟨m, hm, Sum.inl j, w, hw, ?_⟩
    exact congrArg (Adjunction.old f) he
  · subst n
    intro v hv
    let y : boundary k d := ⟨(i, ⟨v, sphere_subset_closedBall hv⟩), hv⟩
    have hy : f y ∈ ⋃ (m : ℕ) (j : RelCWComplex.cell (univ : Set X) m),
        RelCWComplex.closedCell m j := by
      rw [CWComplex.union]
      trivial
    simp only [mem_iUnion, RelCWComplex.closedCell, mem_image] at hy
    obtain ⟨m, j, w, hw, he⟩ := hy
    simp only [mem_iUnion, mem_image]
    refine ⟨m, hdim m j, Sum.inl j, w, hw, ?_⟩
    change Adjunction.old f (RelCWComplex.map m j w) = chart f i v
    rw [he, chart_apply_sphere f i v hv]

theorem newChart_union :
    (⋃ (n : ℕ) (i : NewCell (X := X) (k := k) (d := d) n),
      newChart f n i '' closedBall 0 1) = univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨x | ⟨i, v⟩, rfl⟩ := Quotient.mk_surjective z
  · have hx : x ∈ ⋃ (m : ℕ) (j : RelCWComplex.cell (univ : Set X) m),
        RelCWComplex.closedCell m j := by
      rw [CWComplex.union]
      trivial
    simp only [mem_iUnion, RelCWComplex.closedCell, mem_image] at hx
    obtain ⟨n, i, v, hv, he⟩ := hx
    simp only [mem_iUnion, mem_image]
    exact ⟨n, Sum.inl i, v, hv, congrArg (Adjunction.old f) he⟩
  · simp only [mem_iUnion, mem_image]
    exact ⟨d, Sum.inr ⟨i, ⟨rfl⟩⟩, v.1, v.2, characteristic_on_disk f i v⟩

include hdim in
omit [T2Space X] [CompactSpace X] [Nonempty X] in
theorem newCell_eventually_isEmpty :
    ∀ᶠ n in Filter.atTop, IsEmpty (NewCell (X := X) (k := k) (d := d) n) := by
  refine Filter.eventually_atTop.mpr ⟨d + 1, ?_⟩
  intro n hn
  refine ⟨?_⟩
  rintro (i | ⟨i, ⟨hi⟩⟩)
  · have := hdim n i
    omega
  · omega

variable [RelCWComplex.FiniteType (univ : Set X)]

omit [T2Space X] [CompactSpace X] [Nonempty X] in
theorem newCell_finite (n : ℕ) :
    Finite (NewCell (X := X) (k := k) (d := d) n) := by
  let : Finite (RelCWComplex.cell (univ : Set X) n) :=
    RelCWComplex.FiniteType.finite_cell n
  unfold NewCell
  infer_instance

@[instance_reducible] def cwComplex : CWComplex (univ : Set (Space f)) :=
  CWComplex.mkFinite univ (NewCell (X := X) (k := k) (d := d)) (newChart f)
    (newCell_eventually_isEmpty hdim) newCell_finite (newChart_source f)
    (newChart_continuousOn f) (newChart_continuousOn_symm f)
    (newChart_pairwiseDisjoint f) (newChart_mapsTo f hdim) (newChart_union f)

end

end Cells

namespace Rose

def leftEnd : Fin 1 → ℝ := fun _ => -1
def rightEnd : Fin 1 → ℝ := fun _ => 1

theorem leftEnd_sphere : leftEnd ∈ Metric.sphere (0 : Fin 1 → ℝ) 1 := by
  change ‖(fun _ : Fin 1 => (-1 : ℝ)) - 0‖ = 1
  simp

theorem rightEnd_sphere : rightEnd ∈ Metric.sphere (0 : Fin 1 → ℝ) 1 := by
  change ‖(fun _ : Fin 1 => (1 : ℝ)) - 0‖ = 1
  simp

theorem segmentInDisk :
    Set.range (Path.segment leftEnd rightEnd) ⊆ Metric.closedBall (0 : Fin 1 → ℝ) 1 := by
  rw [Path.range_segment]
  exact (convex_closedBall (0 : Fin 1 → ℝ) 1).segment_subset
    (Metric.sphere_subset_closedBall leftEnd_sphere)
    (Metric.sphere_subset_closedBall rightEnd_sphere)

end Rose

namespace AttachingLoops

open scoped unitInterval

def onCircle {X : Type*} [TopologicalSpace X] {x : X} (γ : Path x x) :
    C(AddCircle (1 : ℝ), X) where
  toFun := AddCircle.liftIco 1 0 γ.extend
  continuous_toFun := AddCircle.liftIco_zero_continuous
    (by rw [γ.extend_zero, γ.extend_one]) γ.continuous_extend.continuousOn

abbrev SquareBoundary := (Metric.sphere (0 : Fin 2 → ℝ) 1 : Set (Fin 2 → ℝ))

def vectorComplex (v : Fin 2 → ℝ) : ℂ := (v 0 : ℂ) + (v 1 : ℂ) * Complex.I

@[simp] theorem vectorComplex_re (v : Fin 2 → ℝ) : (vectorComplex v).re = v 0 := by
  simp [vectorComplex]

@[simp] theorem vectorComplex_im (v : Fin 2 → ℝ) : (vectorComplex v).im = v 1 := by
  simp [vectorComplex]

theorem vectorComplex_continuous : Continuous vectorComplex := by
  unfold vectorComplex
  fun_prop

theorem vectorComplex_ne_zero (v : SquareBoundary) : vectorComplex v.1 ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  simp only [vectorComplex_re, vectorComplex_im, Complex.zero_re, Complex.zero_im] at hr hi
  have hv : v.1 = 0 := by
    funext i
    fin_cases i <;> assumption
  have hh := v.property
  rw [hv] at hh
  norm_num at hh

def boundaryAngle : C(SquareBoundary, Real.Angle) where
  toFun v := (Complex.arg (vectorComplex v.1) : Real.Angle)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro v
    exact (Complex.continuousAt_arg_coe_angle (vectorComplex_ne_zero v)).comp
      (f := fun z : SquareBoundary => vectorComplex z.1)
      (vectorComplex_continuous.comp continuous_subtype_val).continuousAt

def boundaryParameter : C(SquareBoundary, AddCircle (1 : ℝ)) :=
  let e := AddCircle.homeomorphAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero
  (⟨e, e.continuous⟩ : C(Real.Angle, AddCircle (1 : ℝ))).comp boundaryAngle

@[simp] theorem onCircle_coe {X : Type*} [TopologicalSpace X] {x : X}
    (γ : Path x x) (t : unitInterval) :
    onCircle γ ((t : ℝ) : AddCircle (1 : ℝ)) = γ t := by
  by_cases h : (t : ℝ) = 1
  · have ht : t = 1 := Subtype.ext h
    subst t
    change AddCircle.liftIco 1 0 γ.extend ((1 : ℝ) : AddCircle (1 : ℝ)) = _
    rw [AddCircle.coe_period]
    rw [← AddCircle.coe_zero, AddCircle.liftIco_zero_coe_apply (by norm_num)]
    simp
  · change AddCircle.liftIco 1 0 γ.extend ((t : ℝ) : AddCircle (1 : ℝ)) = _
    rw [AddCircle.liftIco_zero_coe_apply ⟨t.property.1, lt_of_le_of_ne t.property.2 h⟩]
    exact γ.extend_apply t.property

end AttachingLoops

namespace PresentationComplex

variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))

def relatorSet : Set (FreeGroup (Fin k)) := Set.range (fun i => FreeGroup.mk (w i))

end PresentationComplex

end PresentationGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryDescend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval

namespace PresentationGeometry.Cells
section

open Metric

abbrev Shell (d : ℕ) := {v : Fin d → ℝ | (1 / 2 : ℝ) ≤ ‖v‖ ∧ ‖v‖ ≤ 1}

instance shell_compactSpace (d : ℕ) : CompactSpace (Shell d) := by
  apply isCompact_iff_compactSpace.mp
  exact (isCompact_closedBall (0 : Fin d → ℝ) 1).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
    (fun v hv => mem_closedBall_zero_iff.mpr hv.2)

end

open Metric
open scoped unitInterval

end PresentationGeometry.Cells

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SphereCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
namespace SphereCover
section
open Set Metric
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Sphere (E : Type) [NormedAddCommGroup E] := sphere (0 : E) 1
abbrev Cap (v : Sphere E) := ({v}ᶜ : Set (Sphere E))
abbrev Orth (v : Sphere E) := (ℝ ∙ (v : E))ᗮ

def capEquiv (v : Sphere E) : Cap v ≃ₜ Orth v :=
  (stereographic (norm_eq_of_mem_sphere v)).toHomeomorphSourceTarget.trans (Homeomorph.Set.univ _)

lemma cap_contractible (v : Sphere E) : ContractibleSpace (Cap v) := (capEquiv v).contractibleSpace

lemma ne_neg (v : Sphere E) : v ≠ -v := by
  intro h
  have he : (v : E) = -(v : E) := congrArg Subtype.val h
  have hv : (v : E) = 0 := by
    have hz : (2 : ℝ) • (v : E) = 0 := by
      rw [two_smul]
      exact (congrArg (fun z => (v : E) + z) he).trans (add_neg_cancel _)
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  have := norm_eq_of_mem_sphere v
  simp [hv] at this

lemma cap_cover (v : Sphere E) : interior (Cap v) ∪ interior (Cap (-v)) = univ := by
  rw [isOpen_compl_singleton.interior_eq,isOpen_compl_singleton.interior_eq]
  apply eq_univ_of_forall
  intro x
  by_cases hx : x = v
  · right
    simpa [hx] using ne_neg v
  · exact Or.inl hx

abbrev Overlap (v : Sphere E) := Subtype (fun x : Cap (-v) => x.1 ∈ Cap v)

def antipode (v : Sphere E) : Cap (-v) := ⟨v,ne_neg v⟩

@[simp] lemma capEquiv_antipode (v : Sphere E) : capEquiv (-v) (antipode v) = 0 :=
  stereographic_neg_apply v

def overlapEquiv (v : Sphere E) : Overlap v ≃ₜ ({0}ᶜ : Set (Orth (-v))) :=
  (capEquiv (-v)).subtype (fun x => by
    change x.1 ≠ v ↔ capEquiv (-v) x ≠ 0
    rw [← capEquiv_antipode v, (capEquiv (-v)).injective.ne_iff]
    exact not_congr ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)

def puncturedEquiv (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ContinuousMap.HomotopyEquiv ({0}ᶜ : Set V) (Sphere V) := by
  letI : ContractibleSpace (Ioi (0 : ℝ)) := (convex_Ioi (0 : ℝ)).contractibleSpace nonempty_Ioi
  let e := (ContractibleSpace.hequiv_unit (Ioi (0 : ℝ))).some
  exact (homeomorphUnitSphereProd V).toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl (Sphere V)).prodCongr e).trans
      (Homeomorph.prodUnique (Sphere V) Unit).toHomotopyEquiv)

def overlapHomotopyEquiv (v : Sphere E) :
    ContinuousMap.HomotopyEquiv (Overlap v) (Sphere (Orth (-v))) :=
  (overlapEquiv v).toHomotopyEquiv.trans (puncturedEquiv _)

end

open Set Metric Topology
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def puncturedHomeomorph (e : E ≃L[ℝ] F) : ({0}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set F) :=
  e.toHomeomorph.subtype (fun x => by
    change x ≠ 0 ↔ e x ≠ 0
    exact not_congr ⟨fun h => h ▸ e.map_zero,fun h => e.injective (h.trans e.map_zero.symm)⟩)

def sphereHomotopyEquiv (e : E ≃L[ℝ] F) :
    ContinuousMap.HomotopyEquiv (Sphere E) (Sphere F) :=
  ((puncturedEquiv E).symm.trans (puncturedHomeomorph e).toHomotopyEquiv).trans (puncturedEquiv F)

end SphereCover

open scoped unitInterval
open Set
namespace DiscreteCoverCharts
variable {ι X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
variable (Z : FiberBundleCore ι X Q)

def point (i : ι) (x : X) (q : Q) : Z.TotalSpace :=
  (Z.localTriv i).toOpenPartialHomeomorph.symm (x,q)

@[simp] theorem point_proj (i : ι) (x : X) (q : Q) : Z.proj (point Z i x q) = x := rfl

@[simp] theorem point_val (i : ι) (x : X) (q : Q) :
    (point Z i x q).2 = Z.coordChange i (Z.indexAt x) x q := rfl

theorem point_change (i j : ι) {x : X} (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j) (q : Q) :
    point Z i x q = point Z j x (Z.coordChange i j x q) := by
  change (⟨x,Z.coordChange i (Z.indexAt x) x q⟩ : Z.TotalSpace) =
    ⟨x,Z.coordChange j (Z.indexAt x) x (Z.coordChange i j x q)⟩
  rw [Z.coordChange_comp i j (Z.indexAt x) x ⟨⟨hi,hj⟩,Z.mem_baseSet_at x⟩ q]

def chartPath (i : ι) {a b : X} (p : Path a b) (hp : Set.range p ⊆ Z.baseSet i) (q : Q) :
    Path (point Z i a q) (point Z i b q) where
  toFun t := point Z i (p t) q
  continuous_toFun := (Z.localTriv i).toOpenPartialHomeomorph.symm.continuousOn.comp_continuous
    (p.continuous.prodMk continuous_const) (fun t => (Z.mem_localTriv_target i _).mpr (hp ⟨t,rfl⟩))
  source' := by rw [p.source]
  target' := by rw [p.target]

@[simp] theorem chartPath_map (i : ι) {a b : X} (p : Path a b)
    (hp : Set.range p ⊆ Z.baseSet i) (q : Q) :
    (chartPath Z i p hp q).map Z.continuous_proj = p := by ext t; rfl

end DiscreteCoverCharts

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RegularCoverGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
open scoped unitInterval
open Set

namespace FiberCoreMap
open Set Topology DiscreteCoverCharts
variable {ι κ X Y Q : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Q]
  (Z : FiberBundleCore ι X Q) (W : FiberBundleCore κ Y Q)
  (f : C(X,Y)) (idx : ι → κ)
  (hs : ∀ i x, x ∈ Z.baseSet i → f x ∈ W.baseSet (idx i))
  (ht : ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j → ∀ q,
    W.coordChange (idx i) (idx j) (f x) q = Z.coordChange i j x q)

def map (e : Z.TotalSpace) : W.TotalSpace :=
  point W (idx (Z.indexAt e.1)) (f e.1) e.2

@[simp] lemma map_proj (e : Z.TotalSpace) : W.proj (map Z W f idx e) = f (Z.proj e) := rfl

include hs ht in
lemma map_chart (i : ι) (e : Z.TotalSpace) (he : e.1 ∈ Z.baseSet i) :
    map Z W f idx e = point W (idx i) (f e.1) ((Z.localTriv i) e).2 := by
  unfold map
  erw [point_change W (idx (Z.indexAt e.1)) (idx i)
    (hs _ _ (Z.mem_baseSet_at _)) (hs _ _ he),ht _ _ _ ⟨Z.mem_baseSet_at _,he⟩]
  rfl

include hs ht in
lemma continuous_map : Continuous (map Z W f idx) := by
  apply continuous_iff_continuousAt.mpr
  intro e
  let i := Z.indexAt e.1
  have he : e ∈ (Z.localTriv i).source := Z.mem_baseSet_at e.1
  have hc : ContinuousOn (fun a : Z.TotalSpace =>
      point W (idx i) (f a.1) ((Z.localTriv i) a).2) (Z.localTriv i).source := by
    apply (W.localTriv (idx i)).toOpenPartialHomeomorph.symm.continuousOn.comp
    · exact (f.continuous.comp Z.continuous_proj).continuousOn.prodMk
        (continuous_snd.comp_continuousOn (Z.localTriv i).continuousOn)
    · intro a ha
      exact (W.mem_localTriv_target (idx i) _).mpr (hs i a.1 ha)
  have hc' : ContinuousOn (map Z W f idx) (Z.localTriv i).source :=
    hc.congr (fun a ha => map_chart Z W f idx hs ht i a ha)
  exact hc'.continuousAt ((Z.localTriv i).open_source.mem_nhds he)

def continuousMap : C(Z.TotalSpace,W.TotalSpace) := ⟨map Z W f idx,continuous_map Z W f idx hs ht⟩

end FiberCoreMap

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSubdivisionIterate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace ModuleHomology
open _root_.CategoryTheory Limits
variable {R : Type} [Ring R] (S : ShortComplex (ModuleCat R))

abbrev Cycles := LinearMap.ker S.g.hom

def classMap : S.moduleCatLeftHomologyData.K ⟶ S.homology :=
  S.moduleCatCyclesIso.inv ≫ S.homologyπ

lemma classMap_surjective : Function.Surjective (classMap S) := by
  apply (ModuleCat.epi_iff_surjective _).mp
  dsimp [classMap]
  infer_instance

lemma classMap_zero_iff (c : Cycles S) : classMap S c = 0 ↔ ∃ b : S.X₁, S.f b = c.1 := by
  have hi := (ModuleCat.mono_iff_injective S.moduleCatHomologyIso.hom).mp inferInstance
  rw [← hi.eq_iff]
  change (classMap S ≫ S.moduleCatHomologyIso.hom) c = S.moduleCatHomologyIso.hom 0 ↔ _
  rw [classMap,Category.assoc,ShortComplex.π_moduleCatCyclesIso_hom,
    ← Category.assoc,Iso.inv_hom_id,Category.id_comp,map_zero]
  change (LinearMap.range S.moduleCatToCycles).mkQ c = 0 ↔ _
  change c ∈ LinearMap.ker (LinearMap.range S.moduleCatToCycles).mkQ ↔ _
  rw [Submodule.ker_mkQ]
  constructor
  · rintro ⟨b,hb⟩; exact ⟨b,congrArg Subtype.val hb⟩
  · rintro ⟨b,hb⟩; exact ⟨b,Subtype.ext hb⟩

lemma classMap_eq_iff (c d : Cycles S) : classMap S c = classMap S d ↔
    ∃ b : S.X₁, S.f b = c.1 - d.1 := by
  erw [← sub_eq_zero,← map_sub,classMap_zero_iff]
  rfl

variable {S} {T : ShortComplex (ModuleCat R)}

def cyclesMap (φ : S ⟶ T) : S.moduleCatLeftHomologyData.K ⟶ T.moduleCatLeftHomologyData.K :=
  ModuleCat.ofHom ((φ.τ₂.hom.domRestrict (LinearMap.ker S.g.hom)).codRestrict (LinearMap.ker T.g.hom) (by
    intro x
    change T.g (φ.τ₂ x.1) = 0
    have h := congrArg (fun h : S.X₂ ⟶ T.X₃ => h x.1) φ.comm₂₃
    change T.g (φ.τ₂ x.1) = φ.τ₃ (S.g x.1) at h
    have hx : S.g x.1 = 0 := x.2
    simpa only [hx,map_zero] using h))

lemma cyclesMap_i (φ : S ⟶ T) :
    cyclesMap φ ≫ T.moduleCatLeftHomologyData.i = S.moduleCatLeftHomologyData.i ≫ φ.τ₂ := rfl

lemma cyclesMap_eq (φ : S ⟶ T) :
    cyclesMap φ = S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ ≫ T.moduleCatCyclesIso.hom := by
  rw [← cancel_mono T.moduleCatLeftHomologyData.i]
  simp only [Category.assoc,ShortComplex.moduleCatCyclesIso_hom_i,
    ShortComplex.cyclesMap_i,ShortComplex.moduleCatCyclesIso_inv_iCycles_assoc,cyclesMap_i]

lemma classMap_natural (φ : S ⟶ T) :
    classMap S ≫ ShortComplex.homologyMap φ = cyclesMap φ ≫ classMap T := by
  simp only [classMap,cyclesMap_eq,Category.assoc,
    ShortComplex.homologyπ_naturality,← Category.assoc T.moduleCatCyclesIso.hom,
    Iso.hom_inv_id,Category.id_comp]

lemma homologyMap_class (φ : S ⟶ T) (c : Cycles S) :
    ShortComplex.homologyMap φ (classMap S c) = classMap T (cyclesMap φ c) :=
  congrArg (fun h : S.moduleCatLeftHomologyData.K ⟶ T.homology => h c) (classMap_natural φ)

lemma homologyMap_surjective (φ : S ⟶ T)
    (hs : ∀ c : Cycles T, ∃ d : Cycles S, ∃ b : T.X₁, T.f b = c.1 - φ.τ₂ d.1) :
    Function.Surjective (ShortComplex.homologyMap φ) := by
  intro a
  obtain ⟨c,rfl⟩ := classMap_surjective T a
  obtain ⟨d,b,hb⟩ := hs c
  refine ⟨classMap S d,?_⟩
  rw [homologyMap_class]
  symm
  exact (classMap_eq_iff T _ _).mpr ⟨b,hb⟩

lemma homologyMap_injective (φ : S ⟶ T)
    (hi : ∀ c : Cycles S, (∃ b : T.X₁, T.f b = φ.τ₂ c.1) → ∃ b : S.X₁, S.f b = c.1) :
    Function.Injective (ShortComplex.homologyMap φ) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨c,rfl⟩ := classMap_surjective S x
  erw [homologyMap_class,classMap_zero_iff] at hx
  exact (classMap_zero_iff S c).mpr (hi c hx)

end ModuleHomology

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_QuotientComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace QuotientComplex
section
open _root_.CategoryTheory
variable {R : Type} [Ring R] {I : Type} {c : ComplexShape I}
  (C : HomologicalComplex (ModuleCat R) c) (S : ∀ i, Submodule R (C.X i))
  (hS : ∀ i j, S i ≤ (S j).comap (C.d i j).hom)

def obj (i : I) : ModuleCat R := ModuleCat.of R ((C.X i) ⧸ S i)

def differential (i j : I) : obj C S i ⟶ obj C S j :=
  ModuleCat.ofHom ((S i).mapQ (S j) (C.d i j).hom (hS i j))

@[simp] lemma differential_mk (i j : I) (x : C.X i) :
    differential C S hS i j ((S i).mkQ x) = (S j).mkQ (C.d i j x) := rfl

lemma differential_shape (i j : I) (h : ¬ c.Rel i j) : differential C S hS i j = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x,rfl⟩ := (S i).mkQ_surjective x
  rw [differential_mk,C.shape _ _ h]
  simp
  rfl

lemma differential_comp (i j k : I) :
    differential C S hS i j ≫ differential C S hS j k = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x,rfl⟩ := (S i).mkQ_surjective x
  change differential C S hS j k (differential C S hS i j ((S i).mkQ x)) = 0
  rw [differential_mk,differential_mk]
  have h := congrArg (fun f : C.X i ⟶ C.X k => f x) (C.d_comp_d i j k)
  change C.d j k (C.d i j x) = 0 at h
  rw [h,map_zero]
  rfl

def complex : HomologicalComplex (ModuleCat R) c where
  X := obj C S
  d := differential C S hS
  shape := differential_shape C S hS
  d_comp_d' i j k _ _ := differential_comp C S hS i j k

def projection : C ⟶ complex C S hS where
  f i := ModuleCat.ofHom (S i).mkQ
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext x : 1
    rfl

@[simp] lemma projection_apply (i : I) (x : C.X i) : (projection C S hS).f i x = (S i).mkQ x := rfl

lemma projection_surjective (i : I) : Function.Surjective ((projection C S hS).f i) :=
  (S i).mkQ_surjective

lemma projection_zero_iff (i : I) (x : C.X i) : (projection C S hS).f i x = 0 ↔ x ∈ S i := by
  change (S i).mkQ x = 0 ↔ _
  change x ∈ LinearMap.ker (S i).mkQ ↔ _
  rw [Submodule.ker_mkQ]

end

open _root_.CategoryTheory
variable {R : Type} [Ring R] {I : Type} {c : ComplexShape I}
  {C D : HomologicalComplex (ModuleCat R) c}
  {S : ∀ i, Submodule R (C.X i)} {T : ∀ i, Submodule R (D.X i)}
  (hS : ∀ i j, S i ≤ (S j).comap (C.d i j).hom)
  (hT : ∀ i j, T i ≤ (T j).comap (D.d i j).hom)
  (f : C ⟶ D) (hf : ∀ i, S i ≤ (T i).comap (f.f i).hom)

def map : complex C S hS ⟶ complex D T hT where
  f i := ModuleCat.ofHom ((S i).mapQ (T i) (f.f i).hom (hf i))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext x : 1
    obtain ⟨x,rfl⟩ := (S i).mkQ_surjective x
    change (T j).mkQ (D.d i j (f.f i x)) = (T j).mkQ (f.f j (C.d i j x))
    exact congrArg (T j).mkQ (congrArg (fun h : C.X i ⟶ D.X j => h x) (f.comm i j))

@[simp] lemma map_projection (i : I) (x : C.X i) :
    (map hS hT f hf).f i ((projection C S hS).f i x) =
      (projection D T hT).f i (f.f i x) := rfl

end QuotientComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularExcision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial

namespace RelativeChains
open Set _root_.CategoryTheory HomologicalComplex
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def restrictMap (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : MapsTo f A B) : C(A,B) :=
  ⟨fun a => ⟨f a,hf a.2⟩,(f.continuous.comp continuous_subtype_val).subtype_mk _⟩

end RelativeChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RelativeChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial

open Set Topology Metric

namespace CWExtension
section
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] {C : Set X} [CWComplex C]

abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Boundary (n : ℕ) := sphere (0 : Fin n → ℝ) 1

def charMap (n : ℕ) (i : RelCWComplex.cell C n) : C(Disk n,C) :=
  ⟨fun v => ⟨RelCWComplex.map n i v,
     RelCWComplex.closedCell_subset_complex n i ⟨v,v.2,rfl⟩⟩,
   (continuousOn_iff_continuous_domRestrict.mp (RelCWComplex.continuousOn n i)).subtype_mk _⟩

theorem isClosed_of_cells (S : Set C)
    (hS : ∀ n i, IsClosed (charMap n i ⁻¹' S)) : IsClosed S := by
  apply isClosed_induced_iff.mpr
  refine ⟨Subtype.val '' (S), ?_, ?_⟩
  · apply (CWComplex.closed C _ (by
      rintro _ ⟨x,hx,rfl⟩
      exact x.2)).mpr
    intro n i
    have hk : IsCompact (charMap n i ⁻¹' S) :=
      (hS n i).isCompact
    have he : (Subtype.val '' (S)) ∩ RelCWComplex.closedCell n i =
        (fun v : Disk n => RelCWComplex.map n i v) '' (charMap n i ⁻¹' S) := by
      ext x
      constructor
      · rintro ⟨⟨z,hz,hzx⟩,v,hv,hvx⟩
        refine ⟨⟨v,hv⟩,?_,hvx⟩
        have : charMap n i ⟨v,hv⟩ = z := Subtype.ext (hvx.trans hzx.symm)
        change charMap n i ⟨v,hv⟩ ∈ S
        rw [this]
        exact hz
      · rintro ⟨v,hv,rfl⟩
        exact ⟨⟨charMap n i v,hv,rfl⟩,v,v.2,rfl⟩
    rw [he]
    exact (hk.image (continuousOn_iff_continuous_domRestrict.mp (RelCWComplex.continuousOn n i))).isClosed
  · ext x
    simp

end

section
open Set Topology Metric
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] {C : Set X} [CWComplex C]

abbrev Skel (C : Set X) [CWComplex C] (n : ℕ) :=
  (RelCWComplex.skeletonLT C (n : ℕ∞) : Set X)

def skelIncl (n : ℕ) : C(Skel C n,Skel C (n+1)) :=
  ⟨fun x => ⟨x,RelCWComplex.skeletonLT_mono (by exact_mod_cast Nat.le_succ n) x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

def charSkel (n : ℕ) (i : RelCWComplex.cell C n) : C(Disk n,Skel C (n+1)) :=
  ⟨fun v => ⟨RelCWComplex.map n i v,
      RelCWComplex.closedCell_subset_skeletonLT n i ⟨v,v.2,rfl⟩⟩,
    (continuousOn_iff_continuous_domRestrict.mp (RelCWComplex.continuousOn n i)).subtype_mk _⟩

def boundarySkel (n : ℕ) (i : RelCWComplex.cell C n) : C(Boundary n,Skel C n) :=
  ⟨fun v => ⟨RelCWComplex.map n i v,
      RelCWComplex.cellFrontier_subset_skeletonLT n i ⟨v,v.2,rfl⟩⟩,
    (continuousOn_iff_continuous_domRestrict.mp
      ((RelCWComplex.continuousOn n i).mono sphere_subset_closedBall)).subtype_mk _⟩

def stageQuot (n : ℕ) : C(Skel C n ⊕ (Σ _i : RelCWComplex.cell C n, Disk n),Skel C (n+1)) :=
  ⟨Sum.elim (skelIncl n) (fun z => charSkel n z.1 z.2),
    continuous_sum_dom.mpr ⟨(skelIncl n).continuous,continuous_sigma (fun i => (charSkel n i).continuous)⟩⟩

theorem stageQuot_surjective (n : ℕ) : Function.Surjective (stageQuot (C := C) n) := by
  intro x
  have hx := x.2
  change (x : X) ∈ (RelCWComplex.skeletonLT C ((n:ℕ∞)+1) : Set X) at hx
  rw [← RelCWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ] at hx
  rcases hx with hx | hx
  · exact ⟨Sum.inl ⟨x,hx⟩,rfl⟩
  · rcases mem_iUnion.mp hx with ⟨i,v,hv,hvx⟩
    exact ⟨Sum.inr ⟨i,⟨v,hv⟩⟩,Subtype.ext hvx⟩

theorem stageQuot_isQuotientMap (n : ℕ) : IsQuotientMap (stageQuot (C := C) n) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨stageQuot_surjective n, fun S => ⟨fun h => h.preimage (stageQuot n).continuous,?_⟩⟩
  intro hS
  apply isClosed_of_cells
  intro m i
  have hi : m < n+1 := by
    have := i.2
    simpa only [RelCWComplex.skeletonLT_I,mem_ofPred_eq,ENat.natCast_lt_natCast] using this
  by_cases hmn : m < n
  · let j : RelCWComplex.cell (Skel C n) m := ⟨i.1,by
      simpa only [RelCWComplex.skeletonLT_I,mem_ofPred_eq,ENat.natCast_lt_natCast] using hmn⟩
    have hc := hS.preimage (continuous_inl.comp (charMap m j).continuous)
    exact hc
  · have hmn : m = n := by omega
    subst m
    have hc := hS.preimage (continuous_inr.comp (continuous_sigmaMk (i := i.1)))
    exact hc

end

open Set Topology Metric
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] {C : Set X} [CWComplex C]

theorem boundary_of_mem_skel (n : ℕ) (i : RelCWComplex.cell C n) (v : Disk n)
    (hv : RelCWComplex.map n i v ∈ Skel C n) : (v : Fin n → ℝ) ∈ sphere 0 1 := by
  have hn : (v : Fin n → ℝ) ∉ ball 0 1 := by
    intro hb
    exact (RelCWComplex.disjoint_skeletonLT_openCell (C := C) (j := i) le_rfl).notMem_of_mem_left hv
      ⟨v,hb,rfl⟩
  rw [mem_sphere]
  exact le_antisymm v.2 (le_of_not_gt hn)

def stageData (n : ℕ) (f : C(Skel C n,Y))
    (g : ∀ _ : RelCWComplex.cell C n, C(Disk n,Y)) :
    C(Skel C n ⊕ (Σ _i : RelCWComplex.cell C n,Disk n),Y) :=
  ⟨Sum.elim f (fun z => g z.1 z.2),continuous_sum_dom.mpr
    ⟨f.continuous,continuous_sigma (fun i => (g i).continuous)⟩⟩

theorem stageData_factors (n : ℕ) (f : C(Skel C n,Y))
    (g : ∀ _ : RelCWComplex.cell C n, C(Disk n,Y))
    (hg : ∀ i (v : Boundary n),g i ⟨v,sphere_subset_closedBall v.2⟩ = f (boundarySkel n i v)) :
    Function.FactorsThrough (stageData n f g) (stageQuot n) := by
  intro a b hab
  have eqval := congrArg Subtype.val hab
  simp only [stageQuot,skelIncl,charSkel,ContinuousMap.coe_mk] at eqval
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg f (Subtype.ext eqval)
    | inr b =>
      change (a : X) = RelCWComplex.map n b.1 b.2 at eqval
      have hv : (b.2 : Fin n → ℝ) ∈ sphere 0 1 :=
        boundary_of_mem_skel n b.1 b.2 (eqval ▸ a.2)
      exact (congrArg f (Subtype.ext eqval)).trans (hg b.1 ⟨b.2,hv⟩).symm
  | inr a =>
    cases b with
    | inl b =>
      change RelCWComplex.map n a.1 a.2 = (b : X) at eqval
      have hv : (a.2 : Fin n → ℝ) ∈ sphere 0 1 :=
        boundary_of_mem_skel n a.1 a.2 (eqval.symm ▸ b.2)
      exact (hg a.1 ⟨a.2,hv⟩).trans (congrArg f (Subtype.ext eqval))
    | inr b =>
      change RelCWComplex.map n a.1 a.2 = RelCWComplex.map n b.1 b.2 at eqval
      by_cases ha : (a.2 : Fin n → ℝ) ∈ sphere 0 1
      · have hb : (b.2 : Fin n → ℝ) ∈ sphere 0 1 :=
          boundary_of_mem_skel n b.1 b.2 (eqval ▸
            RelCWComplex.cellFrontier_subset_skeletonLT n a.1 ⟨a.2,ha,rfl⟩)
        exact (hg a.1 ⟨a.2,ha⟩).trans
          ((congrArg f (Subtype.ext eqval)).trans (hg b.1 ⟨b.2,hb⟩).symm)
      · have ha' : (a.2 : Fin n → ℝ) ∈ ball 0 1 := lt_of_le_of_ne a.2.2 ha
        have hb : (b.2 : Fin n → ℝ) ∉ sphere 0 1 := by
          intro hb
          exact ha (boundary_of_mem_skel n a.1 a.2 (eqval.symm ▸
            RelCWComplex.cellFrontier_subset_skeletonLT n b.1 ⟨b.2,hb,rfl⟩))
        have hb' : (b.2 : Fin n → ℝ) ∈ ball 0 1 := lt_of_le_of_ne b.2.2 hb
        have hi : a.1 = b.1 := by
          by_contra hi
          exact (RelCWComplex.disjoint_openCell_of_ne (C := C) (by simp [hi] :
            (⟨n,a.1⟩ : Σ n,RelCWComplex.cell C n) ≠ ⟨n,b.1⟩)).notMem_of_mem_left
              ⟨a.2,ha',rfl⟩ ⟨b.2,hb',eqval.symm⟩
        rcases a with ⟨i,v⟩
        rcases b with ⟨j,w⟩
        dsimp at hi
        subst j
        have he : v = w := Subtype.ext ((RelCWComplex.map n i).injOn
          (by simpa [RelCWComplex.source_eq] using ha')
          (by simpa [RelCWComplex.source_eq] using hb') eqval)
        exact congrArg (g i) he

def extendSkel (n : ℕ) (f : C(Skel C n,Y))
    (g : ∀ _ : RelCWComplex.cell C n, C(Disk n,Y))
    (hg : ∀ i (v : Boundary n),g i ⟨v,sphere_subset_closedBall v.2⟩ = f (boundarySkel n i v)) :
    C(Skel C (n+1),Y) :=
  (stageQuot_isQuotientMap n).lift (stageData n f g) (stageData_factors n f g hg)

@[simp] theorem extendSkel_prior (n : ℕ) (f : C(Skel C n,Y))
    (g : ∀ _ : RelCWComplex.cell C n, C(Disk n,Y))
    (hg : ∀ i (v : Boundary n),g i ⟨v,sphere_subset_closedBall v.2⟩ = f (boundarySkel n i v))
    (x : Skel C n) : extendSkel n f g hg (skelIncl n x) = f x :=
  DFunLike.congr_fun ((stageQuot_isQuotientMap n).lift_comp (stageData n f g) (stageData_factors n f g hg)) (Sum.inl x)

@[simp] theorem extendSkel_disk (n : ℕ) (f : C(Skel C n,Y))
    (g : ∀ _ : RelCWComplex.cell C n, C(Disk n,Y))
    (hg : ∀ i (v : Boundary n),g i ⟨v,sphere_subset_closedBall v.2⟩ = f (boundarySkel n i v))
    (i : RelCWComplex.cell C n) (v : Disk n) : extendSkel n f g hg (charSkel n i v) = g i v :=
  DFunLike.congr_fun ((stageQuot_isQuotientMap n).lift_comp (stageData n f g) (stageData_factors n f g hg)) (Sum.inr (⟨i,v⟩ : Σ _j : RelCWComplex.cell C n,Disk n))

end CWExtension

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_DiskRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace DiskRadial
open Set Metric
open scoped unitInterval
variable {E : Type*} [NormedAddCommGroup E]
abbrev Disk := closedBall (0 : E) 1

def denom (v : E) : ℝ := max ‖v‖ (1/2)
lemma denom_pos (v : E) : 0 < denom v := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
lemma le_denom (v : E) : ‖v‖ ≤ denom v := le_max_left _ _
lemma continuous_denom : Continuous (denom : E → ℝ) := continuous_norm.max continuous_const

variable [NormedSpace ℝ E]

def inflate (v : Disk (E := E)) : Disk (E := E) :=
  ⟨(denom (v : E))⁻¹ • (v : E),by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (denom_pos _))]
    exact (inv_mul_le_iff₀ (denom_pos (v : E))).mpr (by simpa only [mul_one] using le_denom (v : E))⟩

lemma continuous_inflate : Continuous (inflate (E := E)) := by
  apply Continuous.subtype_mk
  exact ((((continuous_denom (E := E)).comp (continuous_subtype_val : Continuous (Subtype.val : Disk (E := E) → E))).inv₀
    (fun v => (denom_pos (v : E)).ne')).smul continuous_subtype_val)

lemma norm_inflate (v : Disk (E := E)) : ‖(inflate v : E)‖ = (denom (v : E))⁻¹ * ‖(v : E)‖ := by
  simp only [inflate,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (denom_pos _))]

lemma norm_le_inflate (v : Disk (E := E)) : ‖(v : E)‖ ≤ ‖(inflate v : E)‖ := by
  rw [norm_inflate]
  have hd : denom (v : E) ≤ 1 := max_le (by simpa only [mem_closedBall,dist_zero_right] using v.2) (by norm_num)
  have hi : 1 ≤ (denom (v : E))⁻¹ := (one_le_inv₀ (denom_pos _)).mpr hd
  nlinarith [norm_nonneg (v : E)]

lemma inflate_boundary (v : Disk (E := E)) (hv : ‖(v : E)‖ = 1) : inflate v = v := by
  apply Subtype.ext
  norm_num [inflate,denom,hv]

lemma norm_inflate_of_half_lt (v : Disk (E := E)) (hv : 1/2 < ‖(v : E)‖) : ‖(inflate v : E)‖ = 1 := by
  rw [norm_inflate,denom,max_eq_left (le_of_lt hv),inv_mul_cancel₀ (ne_of_gt (lt_trans (by norm_num) hv))]

def radial (t : I) (v : Disk (E := E)) : Disk (E := E) :=
  ⟨(1 - (t : ℝ)) • (v : E) + (t : ℝ) • (inflate v : E),
    (convex_closedBall (0 : E) 1) v.2 (inflate v).2 (sub_nonneg.mpr t.2.2) t.2.1 (by ring)⟩

lemma continuous_radial : Continuous (fun z : I × Disk (E := E) => radial z.1 z.2) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp continuous_snd)).add
    ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp (continuous_inflate.comp continuous_snd)))

@[simp] lemma radial_zero (v : Disk (E := E)) : radial 0 v = v := by ext; simp [radial]
@[simp] lemma radial_one (v : Disk (E := E)) : radial 1 v = inflate v := by ext; simp [radial]
lemma radial_boundary (t : I) (v : Disk (E := E)) (hv : ‖(v : E)‖ = 1) : radial t v = v := by
  apply Subtype.ext
  change (1-(t:ℝ)) • (v : E) + (t:ℝ) • (inflate v : E) = v
  rw [inflate_boundary v hv,← add_smul]
  simp

lemma norm_radial (t : I) (v : Disk (E := E)) :
    ‖(radial t v : E)‖ = (1-(t:ℝ)) * ‖(v : E)‖ + (t:ℝ) * ‖(inflate v : E)‖ := by
  change ‖(1-(t:ℝ)) • (v:E) + (t:ℝ) • ((denom (v:E))⁻¹ • (v:E))‖ = _
  rw [smul_smul,← add_smul,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (sub_nonneg.mpr t.2.2) (mul_nonneg t.2.1 (inv_nonneg.mpr (le_of_lt (denom_pos _))))),norm_inflate]
  ring

lemma norm_le_radial (t : I) (v : Disk (E := E)) : ‖(v : E)‖ ≤ ‖(radial t v : E)‖ := by
  rw [norm_radial]
  nlinarith [norm_le_inflate v,t.2.1]

end DiskRadial

namespace CWCollar
section
open Set Topology Metric CWExtension
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

def radius (n : ℕ) : C(Skel C (n+1),ℝ) :=
  extendSkel n (ContinuousMap.const _ 1) (fun _ => ⟨fun v => ‖(v : Fin n → ℝ)‖,continuous_norm.comp continuous_subtype_val⟩)
    (by intro i v; change ‖(v : Fin n → ℝ)‖ = 1; simpa only [mem_sphere,dist_zero_right] using v.2)

@[simp] lemma radius_prior (n : ℕ) (x : Skel C n) : radius n (skelIncl n x) = 1 :=
  extendSkel_prior _ _ _ _ _
@[simp] lemma radius_disk (n : ℕ) (i : RelCWComplex.cell C n) (v : Disk n) :
    radius n (charSkel n i v) = ‖(v : Fin n → ℝ)‖ := extendSkel_disk _ _ _ _ _ _

def lower (n : ℕ) : Set (Skel C (n+1)) := Subtype.val ⁻¹' Skel C n

theorem radius_eq_one_iff (n : ℕ) (x : Skel C (n+1)) : radius n x = 1 ↔ x ∈ lower n := by
  obtain ⟨a,rfl⟩ := stageQuot_surjective n x
  rcases a with a | ⟨i,v⟩
  · change radius n (skelIncl n a) = 1 ↔ _
    exact ⟨fun _ => a.2,fun _ => radius_prior n a⟩
  · change radius n (charSkel n i v) = 1 ↔ RelCWComplex.map n i v ∈ Skel C n
    rw [radius_disk]
    constructor
    · intro hv
      exact RelCWComplex.cellFrontier_subset_skeletonLT n i ⟨v,by simpa only [mem_sphere,dist_zero_right] using hv,rfl⟩
    · intro hv
      simpa only [mem_sphere,dist_zero_right] using boundary_of_mem_skel n i v hv

def collar (n : ℕ) : Set (Skel C (n+1)) := radius n ⁻¹' Ioi (1/2)
lemma collar_open (n : ℕ) : IsOpen (collar (C := C) n) := isOpen_Ioi.preimage (radius n).continuous
lemma lower_subset_collar (n : ℕ) : lower (C := C) n ⊆ collar n := by
  intro x hx
  change (1/2 : ℝ) < radius n x
  rw [(radius_eq_one_iff n x).mpr hx]
  norm_num

def paths (n : ℕ) : C(Skel C (n+1),C(I,Skel C (n+1))) :=
  extendSkel n
    ⟨fun x => ContinuousMap.const I (skelIncl n x),ContinuousMap.continuous_const'.comp (skelIncl n).continuous⟩
    (fun i => (⟨fun z : Disk n × I => charSkel n i (DiskRadial.radial z.2 z.1),
      (charSkel n i).continuous.comp (DiskRadial.continuous_radial.comp continuous_swap)⟩ : C(_, _)).curry)
    (by
      intro i v
      apply ContinuousMap.ext
      intro t
      change charSkel n i (DiskRadial.radial t ⟨v,sphere_subset_closedBall v.2⟩) = skelIncl n (boundarySkel n i v)
      rw [DiskRadial.radial_boundary t _ (by simpa only [mem_sphere,dist_zero_right] using v.2)]
      rfl)

@[simp] lemma paths_prior (n : ℕ) (x : Skel C n) (t : I) : paths n (skelIncl n x) t = skelIncl n x := by
  change (extendSkel (Y := C(I,Skel C (n+1))) n _ _ _ (skelIncl n x)) t = _
  rw [extendSkel_prior]
  rfl
@[simp] lemma paths_disk (n : ℕ) (i : RelCWComplex.cell C n) (v : Disk n) (t : I) :
    paths n (charSkel n i v) t = charSkel n i (DiskRadial.radial t v) := by
  change (extendSkel (Y := C(I,Skel C (n+1))) n _ _ _ (charSkel n i v)) t = _
  rw [extendSkel_disk]
  rfl

@[simp] lemma paths_zero (n : ℕ) (x : Skel C (n+1)) : paths n x 0 = x := by
  obtain ⟨a,rfl⟩ := stageQuot_surjective n x
  rcases a with a | ⟨i,v⟩
  · exact paths_prior n a 0
  · change paths n (charSkel n i v) 0 = charSkel n i v
    rw [paths_disk,DiskRadial.radial_zero]

lemma paths_fixed (n : ℕ) (x : Skel C (n+1)) (hx : x ∈ lower n) (t : I) : paths n x t = x :=
  paths_prior (C := C) n ⟨x.1,hx⟩ t

lemma radius_le_paths (n : ℕ) (x : Skel C (n+1)) (t : I) : radius n x ≤ radius n (paths n x t) := by
  obtain ⟨a,rfl⟩ := stageQuot_surjective n x
  rcases a with a | ⟨i,v⟩
  · change radius n (skelIncl n a) ≤ radius n (paths n (skelIncl n a) t)
    rw [paths_prior]
  · change radius n (charSkel n i v) ≤ radius n (paths n (charSkel n i v) t)
    rw [paths_disk,radius_disk,radius_disk]
    exact DiskRadial.norm_le_radial t v

lemma paths_mem_collar (n : ℕ) (x : Skel C (n+1)) (hx : x ∈ collar n) (t : I) : paths n x t ∈ collar n :=
  lt_of_lt_of_le hx (radius_le_paths n x t)

lemma paths_one_lower (n : ℕ) (x : Skel C (n+1)) (hx : x ∈ collar n) : paths n x 1 ∈ lower n := by
  apply (radius_eq_one_iff n _).mp
  obtain ⟨a,rfl⟩ := stageQuot_surjective n x
  rcases a with a | ⟨i,v⟩
  · change radius n (paths n (skelIncl n a) 1) = 1
    rw [paths_prior,radius_prior]
  · change radius n (paths n (charSkel n i v) 1) = 1
    simp only [paths_disk,radius_disk,DiskRadial.radial_one]
    apply DiskRadial.norm_inflate_of_half_lt
    change (1/2:ℝ) < radius n (charSkel n i v) at hx
    rwa [radius_disk] at hx

end

open Set Topology Metric CWExtension
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

lemma lower_closed (n : ℕ) : IsClosed (lower (C := C) n) := by
  have he : lower (C := C) n = radius (C := C) n ⁻¹' ({1} : Set ℝ) := by
    ext x
    exact (radius_eq_one_iff (C := C) n x).symm
  rw [he]
  exact isClosed_singleton.preimage (radius (C := C) n).continuous

def collarInclusion (n : ℕ) : C(lower (C := C) n,collar (C := C) n) :=
  ⟨Set.inclusion (lower_subset_collar (C := C) n),continuous_subtype_val.subtype_mk _⟩

def retract (n : ℕ) : C(collar (C := C) n,lower (C := C) n) :=
  ⟨fun x => ⟨paths (C := C) n x 1,paths_one_lower (C := C) n x x.2⟩,
    (((paths (C := C) n).continuous.comp continuous_subtype_val).eval continuous_const).subtype_mk _⟩

def collarHomotopy (n : ℕ) : ContinuousMap.Homotopy (ContinuousMap.id (collar (C := C) n))
    ((collarInclusion (C := C) n).comp (retract (C := C) n)) where
  toFun z := ⟨paths (C := C) n z.2 z.1,paths_mem_collar (C := C) n z.2 z.2.2 z.1⟩
  continuous_toFun := (((paths (C := C) n).continuous.comp (continuous_subtype_val.comp continuous_snd)).eval continuous_fst).subtype_mk _
  map_zero_left x := Subtype.ext (paths_zero (C := C) n x)
  map_one_left _ := rfl

def collarEquiv (n : ℕ) : ContinuousMap.HomotopyEquiv (lower (C := C) n) (collar (C := C) n) where
  toFun := collarInclusion (C := C) n
  invFun := retract (C := C) n
  left_inv := by
    have he : (retract (C := C) n).comp (collarInclusion (C := C) n) = ContinuousMap.id (lower (C := C) n) := by
      apply ContinuousMap.ext
      intro x
      exact Subtype.ext (paths_fixed (C := C) n x x.2 1)
    rw [he]
  right_inv := ⟨(collarHomotopy (C := C) n).symm⟩

abbrev OpenDisk (n : ℕ) := ball (0 : Fin n → ℝ) 1
abbrev OpenCells (n : ℕ) := Σ _i : RelCWComplex.cell C n, OpenDisk n

def openDom (n : ℕ) (z : OpenCells (C := C) n) : Skel C n ⊕ (Σ _i : RelCWComplex.cell C n,Disk n) :=
  Sum.inr ⟨z.1,⟨z.2,ball_subset_closedBall z.2.2⟩⟩

lemma openDom_embedding (n : ℕ) : IsEmbedding (openDom (C := C) n) := by
  change IsEmbedding ((Sum.inr : (Σ _i : RelCWComplex.cell C n,Disk n) → Skel C n ⊕ (Σ _i : RelCWComplex.cell C n,Disk n)) ∘ Sigma.map (β₁ := fun _ : RelCWComplex.cell C n => OpenDisk n) (β₂ := fun _ : RelCWComplex.cell C n => Disk n) (id : RelCWComplex.cell C n → RelCWComplex.cell C n) (fun _ => Set.inclusion (ball_subset_closedBall : ball (0 : Fin n → ℝ) 1 ⊆ closedBall 0 1)))
  exact IsEmbedding.inr.comp ((isEmbedding_sigmaMap («σ» := fun _ : RelCWComplex.cell C n => OpenDisk n) («τ» := fun _ : RelCWComplex.cell C n => Disk n) (f₁ := (id : RelCWComplex.cell C n → RelCWComplex.cell C n)) (f₂ := fun _ => Set.inclusion (ball_subset_closedBall : ball (0 : Fin n → ℝ) 1 ⊆ closedBall 0 1)) Function.injective_id).mpr (fun _ => IsEmbedding.inclusion _))

lemma openDom_mem (n : ℕ) (z : OpenCells (C := C) n) : stageQuot (C := C) n (openDom (C := C) n z) ∈ (lower (C := C) n)ᶜ := by
  intro h
  have hb := boundary_of_mem_skel n z.1 ⟨z.2,ball_subset_closedBall z.2.2⟩ h
  have hlt : ‖(z.2 : Fin n → ℝ)‖ < 1 := by simpa only [mem_ball,dist_zero_right] using z.2.2
  have heq : ‖(z.2 : Fin n → ℝ)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hb
  exact (ne_of_lt hlt) heq

def openPreimage (n : ℕ) : OpenCells (C := C) n → ↑(stageQuot (C := C) n ⁻¹' (lower (C := C) n)ᶜ) :=
  fun z => ⟨openDom (C := C) n z,openDom_mem (C := C) n z⟩

lemma openPreimage_surjective (n : ℕ) : Function.Surjective (openPreimage (C := C) n) := by
  rintro ⟨a,ha⟩
  rcases a with x | ⟨i,v⟩
  · exact False.elim (ha x.2)
  · have hv : (v : Fin n → ℝ) ∉ sphere 0 1 := by
      intro hv
      exact ha (RelCWComplex.cellFrontier_subset_skeletonLT n i ⟨v,hv,rfl⟩)
    have hv' : (v : Fin n → ℝ) ∈ ball 0 1 := lt_of_le_of_ne v.2 hv
    exact ⟨⟨i,⟨v,hv'⟩⟩,rfl⟩

def openPreimageEquiv (n : ℕ) : OpenCells (C := C) n ≃ₜ ↑(stageQuot (C := C) n ⁻¹' (lower (C := C) n)ᶜ) :=
  ((openDom_embedding (C := C) n).codRestrict _ (openDom_mem (C := C) n)).toHomeomorphOfSurjective (openPreimage_surjective (C := C) n)

def openCellMap (n : ℕ) : OpenCells (C := C) n → ↑((lower (C := C) n)ᶜ) :=
  fun z => ⟨stageQuot (C := C) n (openDom (C := C) n z),openDom_mem (C := C) n z⟩

lemma openCellMap_quotient (n : ℕ) : IsQuotientMap (openCellMap (C := C) n) :=
  ((stageQuot_isQuotientMap (C := C) n).restrictPreimage_isOpen (lower_closed (C := C) n).isOpen_compl).comp (openPreimageEquiv (C := C) n).isQuotientMap

lemma openCellMap_injective (n : ℕ) : Function.Injective (openCellMap (C := C) n) := by
  rintro ⟨i,v⟩ ⟨j,w⟩ he
  have h : RelCWComplex.map n i v = RelCWComplex.map n j w := congrArg (fun x => (x.1 : X)) he
  have hi : i = j := by
    by_contra hi
    exact (RelCWComplex.disjoint_openCell_of_ne (C := C) (by simp [hi] :
      (⟨n,i⟩ : Σ n,RelCWComplex.cell C n) ≠ ⟨n,j⟩)).notMem_of_mem_left ⟨v,v.2,rfl⟩ ⟨w,w.2,h.symm⟩
  subst j
  have hvw : v = w := Subtype.ext ((RelCWComplex.map n i).injOn
    (by simpa only [RelCWComplex.source_eq] using v.2)
    (by simpa only [RelCWComplex.source_eq] using w.2) h)
  subst w
  rfl

def openCellsEquiv (n : ℕ) : OpenCells (C := C) n ≃ₜ ↑((lower (C := C) n)ᶜ) :=
  (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨openCellMap_quotient (C := C) n,openCellMap_injective (C := C) n⟩).homeomorph _

@[simp] lemma openCellsEquiv_apply (n : ℕ) (z : OpenCells (C := C) n) :
    (openCellsEquiv n z).1 = charSkel n z.1 ⟨z.2,ball_subset_closedBall z.2.2⟩ := rfl

end CWCollar

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_DiskSigmaCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace DiskSigmaCollar
open Set Topology Metric
open scoped unitInterval
variable (ι E : Type) [NormedAddCommGroup E]

abbrev Disks := Σ _i : ι, DiskRadial.Disk (E := E)
abbrev Opens := Σ _i : ι, ball (0 : E) 1

def radius : C(Disks ι E,ℝ) :=
  ⟨fun z => ‖(z.2 : E)‖,continuous_sigma (fun _ => continuous_norm.comp continuous_subtype_val)⟩
def boundary : Set (Disks ι E) := radius ι E ⁻¹' {1}
def collar : Set (Disks ι E) := radius ι E ⁻¹' Ioi (1/2)
lemma boundary_closed : IsClosed (boundary ι E) := isClosed_singleton.preimage (radius ι E).continuous
lemma collar_open : IsOpen (collar ι E) := isOpen_Ioi.preimage (radius ι E).continuous
lemma boundary_subset_collar : boundary ι E ⊆ collar ι E := by intro x hx; change (1/2:ℝ) < radius ι E x; rw [show radius ι E x = 1 from hx]; norm_num

variable [NormedSpace ℝ E]

def paths : C(Disks ι E,C(I,Disks ι E)) :=
  ⟨fun z => ⟨fun t => ⟨z.1,DiskRadial.radial t z.2⟩,
    continuous_sigmaMk.comp (DiskRadial.continuous_radial.comp (continuous_id.prodMk continuous_const))⟩,
    continuous_sigma (fun i => (⟨fun z : DiskRadial.Disk (E := E) × I => (⟨i,DiskRadial.radial z.2 z.1⟩ : Disks ι E),
      continuous_sigmaMk.comp (DiskRadial.continuous_radial.comp continuous_swap)⟩ : C(_, _)).curry.continuous)⟩

@[simp] lemma paths_zero (x : Disks ι E) : paths ι E x 0 = x := by rcases x with ⟨i,v⟩; change (⟨i,DiskRadial.radial 0 v⟩ : Disks ι E) = _; rw [DiskRadial.radial_zero]
lemma paths_mem (x : Disks ι E) (hx : x ∈ collar ι E) (t : I) : paths ι E x t ∈ collar ι E :=
  lt_of_lt_of_le hx (DiskRadial.norm_le_radial t x.2)
lemma paths_one (x : Disks ι E) (hx : x ∈ collar ι E) : paths ι E x 1 ∈ boundary ι E := by
  change ‖(DiskRadial.radial 1 x.2 : E)‖ = 1
  rw [DiskRadial.radial_one]
  exact DiskRadial.norm_inflate_of_half_lt x.2 hx
lemma paths_fixed (x : Disks ι E) (hx : x ∈ boundary ι E) (t : I) : paths ι E x t = x := by
  rcases x with ⟨i,v⟩
  change (⟨i,DiskRadial.radial t v⟩ : Disks ι E) = _
  rw [DiskRadial.radial_boundary t v hx]

def inclusion : C(boundary ι E,collar ι E) :=
  ⟨Set.inclusion (boundary_subset_collar ι E),continuous_subtype_val.subtype_mk _⟩
def retract : C(collar ι E,boundary ι E) :=
  ⟨fun x => ⟨paths ι E x 1,paths_one ι E x x.2⟩,
    (((paths ι E).continuous.comp continuous_subtype_val).eval continuous_const).subtype_mk _⟩
def homotopy : ContinuousMap.Homotopy (ContinuousMap.id (collar ι E)) ((inclusion ι E).comp (retract ι E)) where
  toFun z := ⟨paths ι E z.2 z.1,paths_mem ι E z.2 z.2.2 z.1⟩
  continuous_toFun := (((paths ι E).continuous.comp (continuous_subtype_val.comp continuous_snd)).eval continuous_fst).subtype_mk _
  map_zero_left x := Subtype.ext (paths_zero ι E x)
  map_one_left _ := rfl

def collarEquiv : ContinuousMap.HomotopyEquiv (boundary ι E) (collar ι E) where
  toFun := inclusion ι E
  invFun := retract ι E
  left_inv := by
    have he : (retract ι E).comp (inclusion ι E) = ContinuousMap.id (boundary ι E) := by
      apply ContinuousMap.ext
      intro x
      exact Subtype.ext (paths_fixed ι E x x.2 1)
    rw [he]
  right_inv := ⟨(homotopy ι E).symm⟩

omit [NormedSpace ℝ E]

def openMap (x : Opens ι E) : Disks ι E := ⟨x.1,⟨x.2,ball_subset_closedBall x.2.2⟩⟩
lemma openMap_embedding : IsEmbedding (openMap ι E) := by
  change IsEmbedding (Sigma.map (β₁ := fun _ : ι => ball (0 : E) 1) (β₂ := fun _ : ι => DiskRadial.Disk (E := E)) id (fun _ => Set.inclusion ball_subset_closedBall))
  exact (isEmbedding_sigmaMap Function.injective_id).mpr (fun _ => IsEmbedding.inclusion _)
lemma openMap_mem (x : Opens ι E) : openMap ι E x ∈ (boundary ι E)ᶜ := by
  change ‖(x.2 : E)‖ ≠ 1
  exact ne_of_lt (by simpa only [mem_ball,dist_zero_right] using x.2.2)
lemma openMap_surj : Function.Surjective (fun x : Opens ι E => (⟨openMap ι E x,openMap_mem ι E x⟩ : ↑((boundary ι E)ᶜ))) := by
  rintro ⟨⟨i,v⟩,hv⟩
  have hv' : (v : E) ∈ ball 0 1 := by
    rw [mem_ball,dist_zero_right]
    exact lt_of_le_of_ne (by simpa only [mem_closedBall,dist_zero_right] using v.2) hv
  exact ⟨⟨i,⟨v,hv'⟩⟩,rfl⟩

def openEquiv : Opens ι E ≃ₜ ↑((boundary ι E)ᶜ) :=
  ((openMap_embedding ι E).codRestrict _ (openMap_mem ι E)).toHomeomorphOfSurjective (openMap_surj ι E)

@[simp] lemma openEquiv_apply (x : Opens ι E) : (openEquiv ι E x).1 = openMap ι E x := rfl

end DiskSigmaCollar

namespace CWSingularPair
open Set Topology Metric CWExtension _root_.CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

abbrev Disks (n : ℕ) := DiskSigmaCollar.Disks (RelCWComplex.cell C n) (Fin n → ℝ)
abbrev Boundary (n : ℕ) := DiskSigmaCollar.boundary (RelCWComplex.cell C n) (Fin n → ℝ)
abbrev Collar (n : ℕ) := DiskSigmaCollar.collar (RelCWComplex.cell C n) (Fin n → ℝ)

def attach (n : ℕ) : C(Disks (C := C) n,Skel C (n+1)) :=
  ⟨fun z => charSkel n z.1 z.2,continuous_sigma (fun i => (charSkel n i).continuous)⟩

lemma radius_attach (n : ℕ) (z : Disks (C := C) n) :
    CWCollar.radius n (attach n z) = DiskSigmaCollar.radius (RelCWComplex.cell C n) (Fin n → ℝ) z :=
  CWCollar.radius_disk n z.1 z.2

lemma maps_boundary (n : ℕ) : MapsTo (attach (C := C) n) (Boundary n) (CWCollar.lower n) := by
  intro z hz
  apply (CWCollar.radius_eq_one_iff n _).mp
  rw [radius_attach]
  exact hz
lemma maps_collar (n : ℕ) : MapsTo (attach (C := C) n) (Collar n) (CWCollar.collar n) := by
  intro z hz
  change (1/2:ℝ) < CWCollar.radius n (attach n z)
  rw [radius_attach]
  exact hz

def complementEquiv (n : ℕ) : ↑((Boundary (C := C) n)ᶜ) ≃ₜ ↑((CWCollar.lower (C := C) n)ᶜ) :=
  (DiskSigmaCollar.openEquiv (RelCWComplex.cell C n) (Fin n → ℝ)).symm.trans (CWCollar.openCellsEquiv n)

lemma complementEquiv_apply (n : ℕ) (x : ↑((Boundary (C := C) n)ᶜ)) :
    (complementEquiv n x).1 = attach n x.1 := by
  obtain ⟨z,rfl⟩ := (DiskSigmaCollar.openEquiv (RelCWComplex.cell C n) (Fin n → ℝ)).surjective x
  change (CWCollar.openCellsEquiv n ((DiskSigmaCollar.openEquiv (RelCWComplex.cell C n) (Fin n → ℝ)).symm
    ((DiskSigmaCollar.openEquiv (RelCWComplex.cell C n) (Fin n → ℝ)) z))).1 = _
  rw [Homeomorph.symm_apply_apply]
  rfl

end CWSingularPair

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ChainShortExact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace ChainShortExact
open _root_.CategoryTheory HomologicalComplex Limits
variable {S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)}

lemma quasiIso_g (hS : S.ShortExact) (h : ∀ n, IsZero (S.X₁.homology n)) : QuasiIso S.g := by
  refine ⟨fun n => (quasiIsoAt_iff_isIso_homologyMap _ _).mpr ?_⟩
  let : Mono (homologyMap S.g n) := (hS.homology_exact₂ n).mono_g ((h n).eq_of_src _ _)
  let : Epi (homologyMap S.g n) := by
    cases n with
    | zero =>
      let := hS.epi_g
      exact epi_homologyMap_of_epi_of_not_rel S.g 0 (by intro j; simp)
    | succ n => exact (hS.homology_exact₃ (n+1) n rfl).epi_f ((h n).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

lemma zero_homology₃_zero (hS : S.ShortExact) (h : IsZero (S.X₂.homology 0)) :
    IsZero (S.X₃.homology 0) := by
  let := hS.epi_g
  let : Epi (homologyMap S.g 0) := epi_homologyMap_of_epi_of_not_rel S.g 0 (by intro j; simp)
  exact h.of_epi (homologyMap S.g 0)

end ChainShortExact

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RelativeChainsEmptyProjectionQuasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric

namespace DiskHomology
open Set Metric _root_.CategoryTheory HomologicalComplex
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Disk := closedBall (0 : E) 1

lemma contractible : ContractibleSpace (Disk E) :=
  (convex_closedBall (0 : E) 1).contractibleSpace ⟨0,by norm_num⟩

end DiskHomology

namespace FinsuppHomology
open _root_.CategoryTheory HomologicalComplex
variable {R : Type} [CommRing R] (ι : Type)

abbrev obj (M : ModuleCat.{0} R) := ModuleCat.of R (ι →₀ M)
def map {M N : ModuleCat.{0} R} (f : M ⟶ N) : obj ι M ⟶ obj ι N :=
  ModuleCat.ofHom (Finsupp.mapRange.linearMap f.hom)
@[simp] lemma map_apply {M N : ModuleCat.{0} R} (f : M ⟶ N) (x : obj ι M) (i : ι) :
    map ι f x i = f (x i) := rfl

def singleObj (M : ModuleCat.{0} R) (i : ι) : M ⟶ obj ι M :=
  ModuleCat.ofHom (Finsupp.lsingle i)
def sumMap {M N : ModuleCat.{0} R} (f : ι → (M ⟶ N)) : obj ι M ⟶ N :=
  ModuleCat.ofHom (Finsupp.lsum R (fun i => (f i).hom))
lemma sumMap_single {M N : ModuleCat.{0} R} (f : ι → (M ⟶ N)) (i : ι) (x : M) :
    sumMap ι f (Finsupp.single i x) = f i x := Finsupp.lsum_single _ _ _ _

def complex (C : ChainComplex (ModuleCat.{0} R) ℕ) : ChainComplex (ModuleCat.{0} R) ℕ where
  X n := obj ι (C.X n)
  d n m := map ι (C.d n m)
  shape n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro i
    change C.d n m (x i) = 0
    rw [C.shape n m h]
    rfl
  d_comp_d' n m k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro i
    change C.d m k (C.d n m (x i)) = 0
    exact congrArg (fun f : C.X n ⟶ C.X k => f (x i)) (C.d_comp_d n m k)

def single (C : ChainComplex (ModuleCat.{0} R) ℕ) (i : ι) : C ⟶ complex ι C where
  f n := ModuleCat.ofHom (Finsupp.lsingle i)
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Finsupp.mapRange (C.d n m) (map_zero _) (Finsupp.single i x) = Finsupp.single i (C.d n m x)
    simp

def eval (C : ChainComplex (ModuleCat.{0} R) ℕ) (i : ι) : complex ι C ⟶ C where
  f _ := ModuleCat.ofHom (Finsupp.lapply i)
  comm' _ _ _ := rfl

lemma single_eval (C : ChainComplex (ModuleCat.{0} R) ℕ) (i : ι) : single ι C i ≫ eval ι C i = 𝟙 C := by
  ext n x
  change (Finsupp.single i x) i = x
  exact Finsupp.single_eq_same
lemma single_eval_ne (C : ChainComplex (ModuleCat.{0} R) ℕ) {i j : ι} (h : i ≠ j) :
    single ι C i ≫ eval ι C j = 0 := by
  ext n x
  change (Finsupp.single i x) j = 0
  exact Finsupp.single_eq_of_ne (Ne.symm h)

def homologySum (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    obj ι (C.homology n) ⟶ (complex ι C).homology n :=
  ModuleCat.ofHom (Finsupp.lsum R (fun i => (homologyMap (single ι C i) n).hom))

@[simp] lemma homologySum_single (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (i : ι)
    (x : C.homology n) : homologySum ι C n (Finsupp.single i x) = homologyMap (single ι C i) n x := by
  change Finsupp.lsum R (fun j => (homologyMap (single ι C j) n).hom) (Finsupp.single i x) = _
  exact Finsupp.lsum_single _ _ _ _

lemma eval_homologySum (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (i : ι)
    (x : obj ι (C.homology n)) : homologyMap (eval ι C i) n (homologySum ι C n x) = x i := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx,hy]
  | single j x =>
    rw [homologySum_single]
    change (homologyMap (single ι C j) n ≫ homologyMap (eval ι C i) n) x = _
    rw [← homologyMap_comp]
    by_cases h : j = i
    · subst j; simp [single_eval]
    · simp [single_eval_ne ι C h,Finsupp.single_eq_of_ne (Ne.symm h)]

lemma homologySum_injective (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Function.Injective (homologySum ι C n) := by
  intro x y h
  ext i
  calc
    x i = homologyMap (eval ι C i) n (homologySum ι C n x) := (eval_homologySum ι C n i x).symm
    _ = homologyMap (eval ι C i) n (homologySum ι C n y) := congrArg _ h
    _ = y i := eval_homologySum ι C n i y

lemma homologySum_surjective (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Function.Surjective (homologySum ι C n) := by
  classical
  let S := C.sc n
  let T := (complex ι C).sc n
  intro x
  obtain ⟨c,rfl⟩ := ModuleHomology.classMap_surjective T x
  let cc : ι →₀ C.X n := c.1
  have hc (i : ι) : S.g (cc i) = 0 := by
    have h := congrArg (fun v : ι →₀ C.X ((ComplexShape.down ℕ).next n) => v i) c.2
    exact h
  let z (i : ι) : S.moduleCatLeftHomologyData.K := ⟨cc i,hc i⟩
  refine ⟨∑ i ∈ cc.support, Finsupp.single i (ModuleHomology.classMap S (z i)),?_⟩
  simp only [map_sum]
  dsimp only [HomologicalComplex.homology] at *
  have hsingle (i : ι) : homologyMap (single ι C i) n (ModuleHomology.classMap S (z i)) =
      ModuleHomology.classMap T (ModuleHomology.cyclesMap ((shortComplexFunctor _ _ n).map (single ι C i)) (z i)) :=
    ModuleHomology.homologyMap_class _ _
  refine Eq.trans (b := ∑ i ∈ cc.support,
    homologyMap (single ι C i) n (ModuleHomology.classMap S (z i))) ?_ ?_
  · apply Finset.sum_congr rfl
    intro i hi
    exact homologySum_single ι C n i _
  refine Eq.trans (b := ∑ i ∈ cc.support, ModuleHomology.classMap T
    (ModuleHomology.cyclesMap ((shortComplexFunctor _ _ n).map (single ι C i)) (z i))) ?_ ?_
  · apply Finset.sum_congr rfl
    intro i hi
    exact hsingle i

  rw [← map_sum]
  congr 1
  apply Subtype.ext
  exact Eq.trans (map_sum (LinearMap.ker T.g.hom).subtype _ _) (Finsupp.sum_single cc)

def homologyIso (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    obj ι (C.homology n) ≅ (complex ι C).homology n :=
  LinearEquiv.toModuleIso (LinearEquiv.ofBijective (homologySum ι C n).hom
    ⟨homologySum_injective ι C n,homologySum_surjective ι C n⟩)

end FinsuppHomology

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSigma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace SingularSigma
open Set _root_.CategoryTheory HomologicalComplex
attribute [-instance] AddCommGroup.toIntModule
variable {ι X : Type} [TopologicalSpace X]
abbrev Space (ι X : Type) := Σ _ : ι, X

def incl (i : ι) : C(X,Space ι X) := ⟨fun x => (⟨i,x⟩ : Space ι X),(continuous_sigmaMk (σ := fun _ : ι => X))⟩
def snd : C(Space ι X,X) := ⟨Sigma.snd,continuous_sigma fun _ => continuous_id⟩

variable (ι) (A : Set X)
def subset : Set (Space ι X) := snd ⁻¹' A

attribute [instance] AddCommGroup.toIntModule
end SingularSigma

namespace FinsuppHomology
open _root_.CategoryTheory
variable {R : Type} [CommRing R] (ι : Type)
def objIso {M N : ModuleCat.{0} R} (e : M ≅ N) : obj ι M ≅ obj ι N :=
  LinearEquiv.toModuleIso (Finsupp.mapRange.linearEquiv e.toLinearEquiv)
lemma obj_isZero {M : ModuleCat.{0} R} (h : Limits.IsZero M) : Limits.IsZero (obj ι M) := by
  let := ModuleCat.subsingleton_of_isZero h
  exact ModuleCat.isZero_of_subsingleton _
end FinsuppHomology

namespace CWSkeletalHomology
attribute [-instance] AddCommGroup.toIntModule
open Set Topology Metric CWExtension _root_.CategoryTheory HomologicalComplex

attribute [instance] AddCommGroup.toIntModule
end CWSkeletalHomology

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CWCellular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace CWCellular
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

def lowerHomeo (n : ℕ) : Skel C n ≃ₜ CWCollar.lower (C := C) n where
  toEquiv :=
    { toFun := fun x => ⟨skelIncl n x,x.2⟩
      invFun := fun x => ⟨x.1.1,x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  continuous_toFun := (skelIncl n).continuous.subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

end CWCellular

namespace CWExtension
section
open Set Topology Metric
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] {C : Set X} [CWComplex C]

def skelLE {m n : ℕ} (h : m ≤ n) : C(Skel C m,Skel C n) :=
  ⟨fun x => ⟨x,RelCWComplex.skeletonLT_mono (by exact_mod_cast h) x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

def skelToComplex (n : ℕ) : C(Skel C n,C) :=
  ⟨fun x => ⟨x,(RelCWComplex.skeletonLT C n).subset_complex x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

def wholeQuot : C((Σ n : ℕ,Skel C n),C) :=
  ⟨fun z => skelToComplex z.1 z.2,continuous_sigma (fun n => (skelToComplex n).continuous)⟩

theorem wholeQuot_surjective : Function.Surjective (wholeQuot (C := C)) := by
  intro x
  have hx : (x : X) ∈ ⋃ n : ℕ,(RelCWComplex.skeletonLT C n : Set X) := by
    rw [RelCWComplex.iUnion_skeletonLT_eq_complex]
    exact x.2
  obtain ⟨n,hn⟩ := mem_iUnion.mp hx
  exact ⟨⟨n,⟨x,hn⟩⟩,rfl⟩

theorem wholeQuot_isQuotientMap : IsQuotientMap (wholeQuot (C := C)) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨wholeQuot_surjective,fun S => ⟨fun h => h.preimage wholeQuot.continuous,?_⟩⟩
  intro hS
  apply isClosed_of_cells
  intro n i
  have hc : Continuous (fun v : Disk n => (⟨n+1,charSkel n i v⟩ : Σ m : ℕ,Skel C m)) :=
    continuous_sigmaMk.comp (charSkel n i).continuous
  exact hS.preimage hc

theorem family_compat (F : ∀ n, C(Skel C n,Y))
    (hF : ∀ n x, F (n+1) (skelIncl n x) = F n x) {m n : ℕ} (hmn : m ≤ n)
    (x : Skel C m) : F n (skelLE hmn x) = F m x := by
  induction n,hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    exact (hF n (skelLE hmn x)).trans ih

def familyData (F : ∀ n, C(Skel C n,Y)) : C((Σ n : ℕ,Skel C n),Y) :=
  ⟨fun z => F z.1 z.2,continuous_sigma (fun n => (F n).continuous)⟩

theorem familyData_factors (F : ∀ n, C(Skel C n,Y))
    (hF : ∀ n x, F (n+1) (skelIncl n x) = F n x) :
    Function.FactorsThrough (familyData F) wholeQuot := by
  rintro ⟨m,x⟩ ⟨n,y⟩ h
  have he : (x : X) = y := congrArg Subtype.val h
  change F m x = F n y
  rw [← family_compat F hF (le_max_left m n) x,
      ← family_compat F hF (le_max_right m n) y]
  exact congrArg (F (max m n)) (Subtype.ext he)

def unionMap (F : ∀ n, C(Skel C n,Y))
    (hF : ∀ n x, F (n+1) (skelIncl n x) = F n x) : C(C,Y) :=
  wholeQuot_isQuotientMap.lift (familyData F) (familyData_factors F hF)

@[simp] theorem unionMap_skel (F : ∀ n, C(Skel C n,Y))
    (hF : ∀ n x, F (n+1) (skelIncl n x) = F n x) (n : ℕ) (x : Skel C n) :
    unionMap F hF (skelToComplex n x) = F n x :=
  DFunLike.congr_fun (wholeQuot_isQuotientMap.lift_comp (familyData F) (familyData_factors F hF)) ⟨n,x⟩

end

open Set Topology Metric
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

lemma finite_subset_skel {K : Set X} (hk : K.Finite) (hKC : K ⊆ C) : ∃ n : ℕ, K ⊆ Skel C n := by
  have h : ∀ K : Set X, K.Finite → K ⊆ C → ∃ n : ℕ, K ⊆ Skel C n := by
    intro K hK
    induction K,hK using Set.Finite.induction_on with
    | empty => exact fun _ => ⟨0,empty_subset _⟩
    | @insert x S hx hS ih =>
      intro hC
      obtain ⟨n,hn⟩ := ih (fun _ h => hC (mem_insert_of_mem _ h))
      have hxC := hC (mem_insert x S)
      have hxU : x ∈ ⋃ m : ℕ,Skel C m := by
        rw [RelCWComplex.iUnion_skeletonLT_eq_complex]
        exact hxC
      obtain ⟨m,hm⟩ := mem_iUnion.mp hxU
      refine ⟨max m n,?_⟩
      intro y hy
      rcases mem_insert_iff.mp hy with rfl | hy
      · exact RelCWComplex.skeletonLT_mono (by exact_mod_cast le_max_left m n) hm
      · exact RelCWComplex.skeletonLT_mono (by exact_mod_cast le_max_right m n) (hn hy)
  exact h K hk hKC

end CWExtension

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CWCellularSkelInclHomologyIsIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace CWCellular
section
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

lemma chain_homologyMap_class {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L)
    (k : ℕ) (c : ModuleHomology.Cycles (K.sc k)) :
    homologyMap f k (ModuleHomology.classMap (K.sc k) c) =
      ModuleHomology.classMap (L.sc k)
        (ModuleHomology.cyclesMap ((shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).map f) c) :=
  ModuleHomology.homologyMap_class _ _

attribute [instance] AddCommGroup.toIntModule
end

section
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex

attribute [instance] AddCommGroup.toIntModule
end

attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex
variable {X A : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace A]
  [CWComplex (univ : Set X)] (f : C(A,X)) (he : IsEmbedding f)
  (m : ℕ) (hr : Set.range f = Skel (univ : Set X) m)

def skeletonHomeo : A ≃ₜ Skel (univ : Set X) m :=
  he.toHomeomorph.trans (Homeomorph.setCongr hr)

lemma skeleton_factor : (Homeomorph.Set.univ X : C((univ : Set X),X)).comp
      ((skelToComplex m).comp (skeletonHomeo f he m hr : C(A,Skel (univ : Set X) m))) = f := rfl

attribute [instance] AddCommGroup.toIntModule
end CWCellular

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
namespace DiskHEP
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Boundary (n : ℕ) := sphere (0 : Fin n → ℝ) 1
abbrev Corner (n : ℕ) := {z : I × Disk n // z.1 = 0 ∨ ‖z.2.1‖ = 1}

def den {n : ℕ} (z : I × Disk n) : ℝ := max (2-(z.1:ℝ)) (2*‖z.2.1‖)
def ratio {n : ℕ} (z : I × Disk n) : ℝ := 2 / den z

lemma norm_le {n : ℕ} (x : Disk n) : ‖x.1‖ ≤ 1 := by
  simpa only [mem_closedBall,dist_zero_right] using x.2

lemma den_pos {n : ℕ} (z : I × Disk n) : 0 < den z :=
  lt_of_lt_of_le (by linarith [z.1.2.2] : 0 < 2-(z.1:ℝ)) (le_max_left _ _)

lemma den_le {n : ℕ} (z : I × Disk n) : den z ≤ 2 := by
  apply max_le <;> linarith [z.1.2.1,norm_le z.2]

lemma ratio_pos {n : ℕ} (z : I × Disk n) : 0 < ratio z := div_pos (by norm_num) (den_pos z)
lemma ratio_ge {n : ℕ} (z : I × Disk n) : 1 ≤ ratio z :=
  (le_div_iff₀ (den_pos z)).mpr (by simpa using den_le z)

lemma ratio_mul_den {n : ℕ} (z : I × Disk n) : ratio z * den z = 2 :=
  div_mul_cancel₀ _ (ne_of_gt (den_pos z))

lemma time_bounds {n : ℕ} (z : I × Disk n) :
    2 - ratio z * (2-(z.1:ℝ)) ∈ Icc (0:ℝ) 1 := by
  have hden : 2-(z.1:ℝ) ≤ den z := le_max_left _ _
  have hmul := mul_le_mul_of_nonneg_left hden (ratio_pos z).le
  rw [ratio_mul_den] at hmul
  have ht : 1 ≤ 2-(z.1:ℝ) := by linarith [z.1.2.2]
  constructor
  · linarith
  · nlinarith [ratio_ge z]

lemma point_bound {n : ℕ} (z : I × Disk n) : ‖ratio z • z.2.1‖ ≤ 1 := by
  rw [norm_smul,Real.norm_of_nonneg (ratio_pos z).le]
  have hden : 2*‖z.2.1‖ ≤ den z := le_max_right _ _
  have hmul := mul_le_mul_of_nonneg_left hden (ratio_pos z).le
  rw [ratio_mul_den] at hmul
  nlinarith

lemma hits_corner {n : ℕ} (z : I × Disk n) :
    2 - ratio z * (2-(z.1:ℝ)) = 0 ∨ ‖ratio z • z.2.1‖ = 1 := by
  rcases le_total (2*‖z.2.1‖) (2-(z.1:ℝ)) with h | h
  · left
    have he : den z = 2-(z.1:ℝ) := max_eq_left h
    have hm := ratio_mul_den z
    rw [he] at hm
    linarith
  · right
    have he : den z = 2*‖z.2.1‖ := max_eq_right h
    have hm := ratio_mul_den z
    rw [he] at hm
    rw [norm_smul,Real.norm_of_nonneg (ratio_pos z).le]
    nlinarith

lemma continuous_ratio (n : ℕ) : Continuous (ratio (n := n)) := by
  apply Continuous.div continuous_const
  · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).max
      (continuous_const.mul (continuous_subtype_val.comp continuous_snd).norm)
  · intro z
    exact ne_of_gt (den_pos z)

def retract (n : ℕ) : C(I × Disk n, Corner n) :=
  ⟨fun z => ⟨(⟨2-ratio z*(2-(z.1:ℝ)),time_bounds z⟩,
    ⟨ratio z • z.2.1,by simpa only [mem_closedBall,dist_zero_right] using point_bound z⟩),
    (hits_corner z).imp (fun h => Subtype.ext h) id⟩,
    (((continuous_const.sub ((continuous_ratio n).mul
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)))).subtype_mk _).prodMk
    (((continuous_ratio n).smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _)).subtype_mk _⟩

lemma ratio_eq_one {n : ℕ} (z : Corner n) : ratio z.1 = 1 := by
  have hd : den z.1 = 2 := by
    rcases z.2 with h | h
    · change max (2 - (z.1.1:ℝ)) (2 * ‖z.1.2.1‖) = 2
      rw [h]
      change max (2 - (0:ℝ)) (2 * ‖z.1.2.1‖) = 2
      rw [sub_zero]
      exact max_eq_left (by linarith [norm_le z.1.2])
    · simp only [den,h,mul_one]
      exact max_eq_right (by linarith [z.1.1.2.1])
  simp [ratio,hd]

@[simp] lemma retract_corner {n : ℕ} (z : Corner n) : retract n z.1 = z := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change 2-ratio z.1*(2-(z.1.1:ℝ)) = _
    rw [ratio_eq_one]
    ring
  · apply Subtype.ext
    change ratio z.1 • z.1.2.1 = _
    rw [ratio_eq_one,one_smul]

def boundaryInclusion (n : ℕ) : C(Boundary n,Disk n) :=
  ⟨fun x => ⟨x.1, sphere_subset_closedBall x.2⟩,continuous_subtype_val.subtype_mk _⟩

def bottom (n : ℕ) : C(Disk n,Corner n) :=
  ⟨fun x => ⟨(0,x),Or.inl rfl⟩,(continuous_const.prodMk continuous_id).subtype_mk _⟩

def side (n : ℕ) : C(I × Boundary n,Corner n) :=
  ⟨fun z => ⟨(z.1,boundaryInclusion n z.2),Or.inr (by
      simpa only [mem_sphere,dist_zero_right,boundaryInclusion,ContinuousMap.coe_mk] using z.2.2)⟩,
    (continuous_fst.prodMk ((boundaryInclusion n).continuous.comp continuous_snd)).subtype_mk _⟩

def cornerQuot (n : ℕ) : C(Disk n ⊕ (I × Boundary n),Corner n) :=
  ⟨Sum.elim (bottom n) (side n),continuous_sum_dom.mpr ⟨(bottom n).continuous,(side n).continuous⟩⟩

theorem cornerQuot_surjective (n : ℕ) : Function.Surjective (cornerQuot n) := by
  intro z
  rcases z.2 with h | h
  · refine ⟨Sum.inl z.1.2,Subtype.ext ?_⟩
    exact Prod.ext h.symm rfl
  · let b : Boundary n := ⟨z.1.2.1,by simpa only [mem_sphere,dist_zero_right] using h⟩
    exact ⟨Sum.inr (z.1.1,b),Subtype.ext (Prod.ext rfl (Subtype.ext rfl))⟩

theorem cornerQuot_isQuotientMap (n : ℕ) : IsQuotientMap (cornerQuot n) :=
  IsQuotientMap.of_surjective_continuous (cornerQuot_surjective n) (cornerQuot n).continuous

universe u
variable {Y : Type u} [TopologicalSpace Y]

def cornerData {n : ℕ} (f : C(Disk n,Y)) (h : C(I × Boundary n,Y)) :
    C(Disk n ⊕ (I × Boundary n),Y) :=
  ⟨Sum.elim f h,continuous_sum_dom.mpr ⟨f.continuous,h.continuous⟩⟩

theorem cornerData_factors {n : ℕ} (f : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h0 : ∀ b, h (0,b) = f (boundaryInclusion n b)) :
    Function.FactorsThrough (cornerData f h) (cornerQuot n) := by
  intro a b hab
  have he := congrArg Subtype.val hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg f (congrArg Prod.snd he)
    | inr b =>
      have ht : b.1 = 0 := (congrArg Prod.fst he).symm
      have hx : a = boundaryInclusion n b.2 := congrArg Prod.snd he
      change f a = h b
      rw [hx,← h0]
      exact congrArg h (Prod.ext ht.symm rfl)
  | inr a =>
    cases b with
    | inl b =>
      have ht : a.1 = 0 := congrArg Prod.fst he
      have hx : boundaryInclusion n a.2 = b := congrArg Prod.snd he
      change h a = f b
      rw [← hx,← h0]
      exact congrArg h (Prod.ext ht rfl)
    | inr b =>
      apply congrArg h
      refine Prod.ext (show a.1 = b.1 from congrArg (fun z : I × Disk n => z.1) he) ?_
      apply Subtype.ext
      exact congrArg (fun z : I × Disk n => z.2.1) he

def extend {n : ℕ} (f : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h0 : ∀ b, h (0,b) = f (boundaryInclusion n b)) : C(I × Disk n,Y) :=
  ((cornerQuot_isQuotientMap n).lift (cornerData f h) (cornerData_factors f h h0)).comp (retract n)

lemma extend_corner {n : ℕ} (f : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h0 : ∀ b, h (0,b) = f (boundaryInclusion n b))
    (z : Disk n ⊕ (I × Boundary n)) :
    extend f h h0 (cornerQuot n z).1 = cornerData f h z := by
  change (cornerQuot_isQuotientMap n).lift (cornerData f h) (cornerData_factors f h h0) (retract n (cornerQuot n z).1) = _
  rw [retract_corner]
  exact DFunLike.congr_fun ((cornerQuot_isQuotientMap n).lift_comp (cornerData f h) (cornerData_factors f h h0)) z

@[simp] theorem extend_zero {n : ℕ} (f : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h0 : ∀ b, h (0,b) = f (boundaryInclusion n b)) (x : Disk n) :
    extend f h h0 (0,x) = f x :=
  extend_corner f h h0 (Sum.inl x)

@[simp] theorem extend_side {n : ℕ} (f : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h0 : ∀ b, h (0,b) = f (boundaryInclusion n b)) (t : I) (b : Boundary n) :
    extend f h h0 (t,boundaryInclusion n b) = h (t,b) :=
  extend_corner f h h0 (Sum.inr (t,b))

end DiskHEP

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSphereCycle
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
namespace SingularSphereCycle
open Set Topology _root_.CategoryTheory AlgebraicTopology
open scoped Simplicial
open SphereQuotient

lemma face_zero {n : ℕ} (i : Fin (n+2)) (s : Convexity.StdSimplex ℝ (Fin (n+1))) :
    (Convexity.StdSimplex.map i.succAbove s).weights i = 0 := by
  exact Finsupp.mapDomain_of_notMem_range s.weights i (by simp)

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

abbrev chains (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat ℤ) ℕ :=
  (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℤ ℤ)

end SingularSphereCycle

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SimplexRotation
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
namespace SimplexRotation
open Set Topology
open scoped unitInterval
abbrev Std (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n+1))
abbrev Boundary (n : ℕ) := {s : Std n // ∃ i, s.weights i = 0}
variable {n : ℕ}

def minimum (s : Std n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty s.weights

lemma minimum_nonneg (s : Std n) : 0 ≤ minimum s :=
  Finset.le_inf' _ _ (fun i _ => s.weights_nonneg i)
lemma minimum_le (s : Std n) (i : Fin (n+1)) : minimum s ≤ s.weights i :=
  Finset.inf'_le _ (Finset.mem_univ i)
lemma minimum_attained (s : Std n) : ∃ i, minimum s = s.weights i := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty s.weights
  exact ⟨i,hi⟩
lemma minimum_boundary (s : Boundary n) : minimum s.1 = 0 := by
  obtain ⟨i,hi⟩ := s.2
  exact le_antisymm (by simpa only [hi] using minimum_le s.1 i) (minimum_nonneg s.1)

def radius (s : Std n) : ℝ := 1 - (n+1:ℕ)*minimum s

end SimplexRotation

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SimplexSign
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
namespace SimplexSign
open Set Topology SimplexRotation
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

def lastSwap (n : ℕ) : Equiv.Perm (Fin (n+2)) :=
  Equiv.swap ⟨n,by omega⟩ (Fin.last (n+1))

lemma lastSwap_zero (n : ℕ) : lastSwap (n+1) 0 = 0 := by
  apply Equiv.swap_apply_of_ne_of_ne <;> intro h <;> have := congrArg Fin.val h <;> simp at this

lemma lastSwap_succ (n : ℕ) (i : Fin (n+2)) :
    lastSwap (n+1) i.succ = (lastSwap n i).succ := by
  exact (Function.Injective.map_swap (Fin.succ_injective _) ⟨n,by omega⟩ (Fin.last (n+1)) i).symm

def reverseLast (n : ℕ) (t : Fin (n+1) → I) : Fin (n+1) → I :=
  fun i => if i = Fin.last n then σ (t i) else t i

lemma reverseLast_succ_zero (n : ℕ) (t : Fin (n+2) → I) : reverseLast (n+1) t 0 = t 0 := by
  simp [reverseLast,show (0 : Fin (n+2)) ≠ Fin.last (n+1) by intro h; have := congrArg Fin.val h; simp at this]

lemma reverseLast_succ_succ (n : ℕ) (t : Fin (n+2) → I) (i : Fin (n+1)) :
    reverseLast (n+1) t i.succ = reverseLast n (fun j => t j.succ) i := by
  simp only [reverseLast]
  congr 1
  apply propext
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ,Fin.val_last] at hv ⊢
    omega
  · rintro rfl
    rfl

end SimplexSign

namespace FacePermutation
open Equiv
variable {n : ℕ}

def restrict (p : Perm (Fin (n+1))) (i : Fin (n+1)) : Perm (Fin n) :=
  (finSuccAboveEquiv i).trans
    ((p.subtypeEquiv (fun j => by simp only [ne_eq, p.injective.eq_iff])).trans (finSuccAboveEquiv (p i)).symm)

lemma succAbove_restrict (p : Perm (Fin (n+1))) (i : Fin (n+1)) (k : Fin n) :
    (p i).succAbove (restrict p i k) = p (i.succAbove k) := by
  exact congrArg Subtype.val ((finSuccAboveEquiv (p i)).apply_symm_apply
    ((p.subtypeEquiv (fun j => by simp only [ne_eq, p.injective.eq_iff])) (finSuccAboveEquiv i k)))

def liftZero (q : Perm (Fin n)) : Perm (Fin (n+1)) :=
  Perm.decomposeFin.symm (0,q)

@[simp] lemma liftZero_zero (q : Perm (Fin n)) : liftZero q 0 = 0 := by
  simp [liftZero]
@[simp] lemma liftZero_succ (q : Perm (Fin n)) (i : Fin n) : liftZero q i.succ = (q i).succ := by
  simp [liftZero,Perm.decomposeFin_symm_apply_succ]
@[simp] lemma sign_liftZero (q : Perm (Fin n)) : Perm.sign (liftZero q) = Perm.sign q := by
  simp [liftZero,Perm.decomposeFin.symm_sign]

lemma decomposition (p : Perm (Fin (n+1))) (i : Fin (n+1)) :
    p = (p i).cycleRange⁻¹ * liftZero (restrict p i) * i.cycleRange := by
  apply Equiv.ext
  intro j
  obtain rfl | ⟨k,rfl⟩ := Fin.eq_self_or_eq_succAbove i j
  · simp
  · simp [succAbove_restrict]

lemma sign_restrict (p : Perm (Fin (n+1))) (i : Fin (n+1)) :
    (-1 : ℤˣ)^i.val * Perm.sign (restrict p i) = Perm.sign p * (-1 : ℤˣ)^(p i).val := by
  have h := congrArg Perm.sign (decomposition p i)
  simp only [map_mul,map_inv,Fin.sign_cycleRange,sign_liftZero] at h
  rw [h]
  calc
    (-1 : ℤˣ)^i.val * Perm.sign (restrict p i) =
        (((-1 : ℤˣ)^(p i).val)⁻¹ * (-1 : ℤˣ)^(p i).val) *
          (Perm.sign (restrict p i) * (-1 : ℤˣ)^i.val) := by simp [mul_comm]
    _ = _ := by ac_rfl

end FacePermutation

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

namespace SimplexDegeneracy
open Set Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

def append (v : Fin (n+1)) : Fin (n+2) → Fin (n+1) := Fin.lastCases v id

@[simp] lemma append_castSucc (v j : Fin (n+1)) : append v j.castSucc = j := by
  simp [append]
@[simp] lemma append_last (v : Fin (n+1)) : append v (Fin.last (n+1)) = v := by
  simp [append]

lemma append_eq (v i : Fin (n+1)) (hiv : i ≠ v) (j : Fin (n+2))
    (h : append v j = i) : j = i.castSucc := by
  induction j using Fin.lastCases with
  | last => exact (hiv (by simpa using h.symm)).elim
  | cast j => simpa only [append_castSucc,Fin.castSucc_inj] using h

lemma append_face_last (v : Fin (n+1)) : append v ∘ (Fin.last (n+1)).succAbove = id := by
  funext i
  simp

lemma append_face_last_castSucc :
    append (Fin.last n) ∘ (Fin.last n).castSucc.succAbove = (id : Fin (n+1) → Fin (n+1)) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [Fin.succAbove]
  | cast i =>
    have hi : i.castSucc.castSucc < (Fin.last n).castSucc := by
      simpa only [Fin.lt_def,Fin.val_castSucc,Fin.val_last] using i.isLt
    rw [Function.comp_apply,Fin.succAbove_of_castSucc_lt _ _ hi,append_castSucc]
    rfl

lemma append_face_penult {n : ℕ} :
    append (Fin.last n).castSucc ∘ (Fin.last n).castSucc.castSucc.succAbove =
      (SimplexSign.lastSwap n : Fin (n+2) → Fin (n+2)) := by
  funext i
  induction i using Fin.lastCases with
  | last =>
    rw [Function.comp_apply,Fin.succAbove_of_le_castSucc _ _ (by
      simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_last]; omega),Fin.succ_last,append_last]
    exact (Equiv.swap_apply_right _ _).symm
  | cast i =>
    induction i using Fin.lastCases with
    | last =>
      rw [Function.comp_apply,Fin.succAbove_of_le_castSucc _ _ le_rfl]
      have he : (Fin.last n).castSucc.succ = (Fin.last (n+1)).castSucc := Fin.ext rfl
      rw [he,append_castSucc]
      exact (Equiv.swap_apply_left _ _).symm
    | cast i =>
      have hi : i.castSucc.castSucc.castSucc < (Fin.last n).castSucc.castSucc := by
        simpa only [Fin.lt_def,Fin.val_castSucc,Fin.val_last] using i.isLt
      rw [Function.comp_apply,Fin.succAbove_of_castSucc_lt _ _ hi,append_castSucc]
      simp only [SimplexSign.lastSwap]
      exact (Equiv.swap_apply_of_ne_of_ne (by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castSucc] at hv
        omega) (Fin.castSucc_ne_last _)).symm

end SimplexDegeneracy

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RepresentationKilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace RepresentationKilling
attribute [-instance] AddCommGroup.toIntModule
attribute [instance] AddCommGroup.toIntModule
end RepresentationKilling

namespace CWCellular
section
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex
attribute [-instance] AddCommGroup.toIntModule

attribute [instance] AddCommGroup.toIntModule
end

section
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex
attribute [-instance] AddCommGroup.toIntModule

attribute [instance] AddCommGroup.toIntModule
end

open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex
variable {X Y Z : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  [TopologicalSpace Z] [T2Space Z] {C : Set X} {D : Set Y} {E : Set Z}
  [CWComplex C] [CWComplex D] [CWComplex E]

structure SkeletalMap (C : Set X) (D : Set Y) [CWComplex C] [CWComplex D] where
  toMap : C(X,Y)
  maps : ∀ n : ℕ, MapsTo toMap (Skel C n) (Skel D n)

namespace SkeletalMap
variable (f : SkeletalMap C D)
def onSkel (n : ℕ) : C(Skel C n,Skel D n) :=
  ⟨fun x => ⟨f.toMap x,f.maps n x.2⟩,(f.toMap.continuous.comp continuous_subtype_val).subtype_mk _⟩

lemma lower_maps (n : ℕ) : MapsTo (f.onSkel (n+1)) (CWCollar.lower (C := C) n)
    (CWCollar.lower (C := D) n) := fun _ hx => f.maps n hx

end SkeletalMap
end CWCellular

attribute [-instance] AddCommGroup.toIntModule

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_NonunitalCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace NonunitalCompression
variable {R S : Type*} [Ring R] [Ring S]
variable (φ : R →ₙ+* S)

def unitValue (x : R) : S := 1+φ (x-1)

end NonunitalCompression

end

end OAI
end


