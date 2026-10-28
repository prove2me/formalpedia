-- Prove2me | Definitions.Def_OAIQ021F003
-- name    : OAIQ021F003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T18:07:29.047294+00:00
-- url     : https://prove2.me/theorems/5de867f2-6200-4d37-8fac-82317217eca9
-- title:
--   Definitions bundle OAIQ021F003 of the split of OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt`, carved from OpenAI's openai/math development (OpenAI, *Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)*, OpenAI Math Release, September 24, 2026, result family 211, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 177 declarations of OpenAI's Lean: 71 definitions, 6 instances and 100 theorems. The definitions and types are `OAI.FKCRT.Inventory.Parameters.ofQ`, `OAI.FKCRT.Inventory.StackMatching.deleteInterval`, `OAI.FKCRT.Inventory.StackMatching.empty_interval_wedge`, `OAI.FKCRT.Inventory.StackMatching.keepInterval`, `OAI.FKCRT.Inventory.coreIncrement`, `OAI.FKCRT.Inventory.labelProfileSum`, `OAI.FKCRT.Inventory.oneLinkCore`, `OAI.FKCRT.Inventory.oneLinkMatching`, `OAI.FKCRT.OrderedActive`, `OAI.FKCRT.PermutationWedge.dartGraphEmbeddingIso`, `OAI.FKCRT.PermutationWedge.dartVertexEquiv`, `OAI.FKCRT.PermutationWedge.data`, `OAI.FKCRT.PermutationWedge.flipInclusion`, `OAI.FKCRT.PermutationWedge.flipInclusionHom`, `OAI.FKCRT.PermutationWedge.flipRetract`, `OAI.FKCRT.PermutationWedge.fullInclusion`, `OAI.FKCRT.PermutationWedge.fullInclusionHom`, `OAI.FKCRT.PermutationWedge.fullRetract`, `OAI.FKCRT.PermutationWedge.inclusion`, `OAI.FKCRT.PermutationWedge.inclusionHom`, `OAI.FKCRT.PermutationWedge.retract`, `OAI.FKCRT.PermutationWedge.vertexEmbeddingEquiv`, `OAI.FKCRT.RootedSpanningTree`, `OAI.FKCRT.SimpleWalk.excursionLaw`, `OAI.FKCRT.SimpleWalk.firstHit`, `OAI.FKCRT.SimpleWalk.gridIndex`, `OAI.FKCRT.SimpleWalk.gridSample`, `OAI.FKCRT.SimpleWalk.histogramDensity`, `OAI.FKCRT.SimpleWalk.normalizedTrace`, `OAI.FKCRT.SimpleWalk.observed`, `OAI.FKCRT.SimpleWalk.simplePolygon`, `OAI.FKCRT.SimpleWalk.splitPathAt`, `OAI.FKCRT.SimpleWalk.traceExcursion`, `OAI.FKCRT.SimpleWalk.traceKilledWeight`, `OAI.FKCRT.SimpleWalk.tracePoints`, `OAI.FKCRT.SimpleWalk.uniformLaw`, `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.spineLaw`, `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.squareTail`, `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.streamBridgeLaw`, `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.streamLaw` and 31 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/FKMaps, in whole or in part: `FKMaps_BlockLaw`, `FKMaps_CanonicalBijection`, `FKMaps_CoreCompression`, `FKMaps_CoreMetric`, `FKMaps_CoreWords`, `FKMaps_CornerInverse`, `FKMaps_CornerMass`, `FKMaps_ExcursionKernel`, `FKMaps_ExcursionLaw`, `FKMaps_FiniteLaw`, `FKMaps_GraphWedge`, `FKMaps_HeightBounds`, `FKMaps_HeightCoding`, `FKMaps_HeightTightness`, `FKMaps_MapCycles`, `FKMaps_MapEncoding`, `FKMaps_MarkedSpines`, `FKMaps_NodeOrder`, `FKMaps_Offspring`, `FKMaps_PlanarActivity`, `FKMaps_PlaneTrees`, `FKMaps_RadialBridge`, `FKMaps_RootedLaw`, `FKMaps_SimpleWalk`, `FKMaps_SpineBounds`, `FKMaps_SpineMoments`, `FKMaps_TourActivity`, `FKMaps_TraceLimit`, `FKMaps_TreeCode`, `FKMaps_WordLaw`.
--
--   **Imports.** It imports the published bundle `Def_FKCRT`; the bundles `OAIQ021F000` and `OAIQ021F001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ021F004`.
-- source:
--   OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 211; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/FKMaps at commit adc7f12

import Mathlib
import Definitions.Def_FKCRT
import Definitions.Def_OAIQ021F000
import Definitions.Def_OAIQ021F001

section
-- module Solutions.OAIQ021_FK.FKMaps_Offspring
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


def CriticalEvenOffspring.streamLaw (p : CriticalEvenOffspring) : Measure (ℕ → ℕ) :=
  Measure.infinitePi (fun _ : ℕ => p.law.toMeasure)


instance instIsProbabilityMeasureForallNatStreamLaw (p : CriticalEvenOffspring) : IsProbabilityMeasure p.streamLaw := by
  unfold CriticalEvenOffspring.streamLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_TreeCode
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


def jointCode {N : ℕ} (σ : ℝ) (d : Code N) : C(unitInterval, ℝ × ℝ) :=
  (interpolation N (fun i => (walk d.val i.val : ℝ) / (σ * Real.sqrt N))).prodMk
    (interpolation N (fun i => σ * height d.val i.val / (2 * Real.sqrt N)))


def codeWeight {N : ℕ} (p : CriticalEvenOffspring) (d : Code N) : ℝ :=
  ∏ i : Fin N, p.mass (d.val i).val


lemma codeWeight_nonneg {N : ℕ} (p : CriticalEvenOffspring) (d : Code N) :
    0 ≤ codeWeight p d := Finset.prod_nonneg (fun _i _ => p.nonneg _)


lemma walk_step {N : ℕ} (d : Fin N → Fin N) {j : ℕ} (hj : j < N) :
    walk d (j+1) = walk d j + ((d ⟨j, hj⟩).val : ℤ) - 1 := by
  have hsplit : ∀ i : Fin N,
      (if i.val < j+1 then ((d i).val : ℤ) - 1 else 0) =
        (if i.val < j then ((d i).val : ℤ) - 1 else 0) +
        (if i = ⟨j, hj⟩ then ((d i).val : ℤ) - 1 else 0) := by
    intro i
    by_cases h : i = ⟨j, hj⟩
    · subst i
      simp
    · have hv : i.val ≠ j := fun hv => h (Fin.ext hv)
      by_cases hi : i.val < j <;> simp [hi, h, show (i.val < j+1) ↔ i.val < j by omega]
  simp only [walk, hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  omega


lemma walk_binaryComb (n : ℕ) {j : ℕ} (hj : j ≤ 2*n+1) :
    walk (binaryCombDegrees n) j = if j ≤ n then (j : ℤ) else 2*(n : ℤ) - j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [walk_step _ (by omega), ih (by omega)]
    simp only [binaryCombDegrees, Nat.cast_ite, Nat.cast_ofNat]
    split_ifs <;> omega


def binaryComb (n : ℕ) : Code (2*n+1) :=
  ⟨binaryCombDegrees n, by
    constructor
    · rw [walk_binaryComb _ (le_refl _), ite_eq_right (by omega)]
      push_cast
      omega
    · intro j hj
      rw [walk_binaryComb _ hj.le]
      split_ifs <;> omega⟩


lemma codeWeight_binaryComb_pos (p : CriticalEvenOffspring) (n : ℕ) :
    0 < codeWeight p (binaryComb n) := by
  apply Finset.prod_pos
  intro i _
  change 0 < p.mass (if i.val < n then 2 else 0)
  split_ifs
  · exact p.two_pos
  · exact p.zero_pos


lemma degreeList_prefixSum {N : ℕ} (d : Fin N → Fin N) (j : ℕ) :
    prefixSum (degreeList d) j = walk d j := by
  simp only [prefixSum, degreeList, List.sum_take_ofFn, walk, Finset.sum_filter]


lemma degreeList_sum {N : ℕ} (d : Fin N → Fin N) :
    (degreeList d).sum = walk d N := by
  simp [degreeList, List.sum_ofFn, walk]


lemma isTreeCode_iff {N : ℕ} (d : Fin N → Fin N) :
    IsTreeCode d ↔ IsExcursionList (degreeList d) := by
  simp [IsTreeCode, IsExcursionList, degreeList_sum, degreeList_prefixSum]


lemma walk_rotate_terminal {N : ℕ} [NeZero N] (m : Fin N) (d : Fin N → Fin N) :
    walk (rotateDegrees m d) N = walk d N := by
  rw [← degreeList_sum, degreeList_rotate, (List.rotate_perm _ _).sum_eq, degreeList_sum]


def walkPolygon {N : ℕ} (σ : ℝ) (d : Fin N → Fin N) : C(unitInterval,ℝ) :=
  interpolation N (fun i => (walk d i.val:ℝ)/(σ*Real.sqrt N))


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_HeightCoding
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


def CriticalEvenOffspring.squareTail (p : CriticalEvenOffspring) (R : ℝ) : ℝ :=
  ∑' k : ℕ, if R < (k : ℝ) then (k : ℝ)^2 * p.mass k else 0


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_HeightBounds
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

def CriticalEvenOffspring.streamBridgeLaw (p : CriticalEvenOffspring) (n : ℕ) :
    Measure (ℕ → ℕ) := cond p.streamLaw {x | integerSum x (2*n+1)=-1}

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

instance instMeasurableSpaceCode (N : ℕ) : MeasurableSpace (Code N) := ⊤
instance instMeasurableSingletonClassCode (N : ℕ) : MeasurableSingletonClass (Code N) := ⟨fun _ => trivial⟩

def badHeightFraction {N : ℕ} (ν a : ℝ) (d : Code N) : ℝ :=
  (∑ v : Fin N, if a < |(walk d.val v.val:ℝ)-ν*height d.val v.val| then (1:ℝ) else 0)/(N:ℝ)

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_HeightTightness
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

def codeHeightModulusFailure {N : ℕ} (m : ℕ) (c : ℝ) : Set (Code N) :=
  {d | ∃ a b, a ≤ b ∧ b ≤ N ∧
    (∀ u v, a ≤ u → u ≤ b → a ≤ v → v ≤ b → (walk d.val u:ℝ)-(walk d.val v:ℝ) < c) ∧
    ¬(height d.val b ≤ height d.val a+m ∧ height d.val a ≤ height d.val b+m)}

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SimpleWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

def SimpleExcursion {N : ℕ} (d : SimpleWalk.Path N) : Prop :=
  SimpleWalk.pathSum d N= -1 ∧ ∀ k<N,0≤SimpleWalk.pathSum d k

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

def splitPathAt (n m : ℕ) : Path (n+m) ≃ Path n × Path m where
  toFun d := (fun i => d (Fin.castAdd m i),fun i => d (Fin.natAdd n i))
  invFun d := Fin.append d.1 d.2
  left_inv _ := Fin.append_castAdd_natAdd
  right_inv _ := by ext <;> simp

lemma pathSum_append_left {n m k : ℕ} (d : Path n) (e : Path m) (hk : k≤n) :
    pathSum (Fin.append d e) k=pathSum d k := by
  unfold pathSum
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right,Fin.val_castAdd,Fin.val_natAdd]
  have hzero : ∑ i : Fin m, (if n+i.val<k then sign (e i) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (by omega)]
  rw [hzero,add_zero]

lemma pathSum_append_right {n m : ℕ} (d : Path n) (e : Path m) (k : ℕ) :
    pathSum (Fin.append d e) (n+k)=pathSum d n+pathSum e k := by
  unfold pathSum
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right,Fin.val_castAdd,Fin.val_natAdd,
    Nat.add_lt_add_iff_left]
  have he : ∀ i : Fin n, (if i.val<n+k then sign (d i) else 0)=if i.val<n then sign (d i) else 0 :=
    fun i => by rw [ite_eq_left (by omega),ite_eq_left i.isLt]
  simp_rw [he]

lemma pathMass_append (n m : ℕ) (P : Path n → Prop) (Q : Path m → Prop) :
    pathMass (n+m) (fun d => P ((splitPathAt n m d).1) ∧ Q ((splitPathAt n m d).2))=
      pathMass n P*pathMass m Q := by
  unfold pathMass
  rw [Fintype.sum_equiv (splitPathAt n m) _
    (fun d => if P d.1 ∧ Q d.2 then (1:ℝ) else 0) (by intro d; split_ifs <;> rfl)]
  rw [Fintype.sum_prod_type]
  have he : ∀ d : Path n,∀ e : Path m,(if P d ∧ Q e then (1:ℝ) else 0)=
      (if P d then 1 else 0)*(if Q e then 1 else 0) := by
    intro d e; split_ifs <;> simp_all
  simp_rw [he,← Finset.mul_sum]
  rw [← Finset.sum_mul,pow_add]
  ring

/-- Probability of a first visit to -1, starting at a nonnegative integer. -/
def firstHit {n : ℕ} (a : ℕ) (d : Path n) : Prop :=
  (a:ℤ)+pathSum d n= -1 ∧ ∀ k<n,0≤(a:ℤ)+pathSum d k

lemma firstHit_last {n : ℕ} (a : ℕ) (d : Path n) (s : Path 1) :
    firstHit a (Fin.append d s) ↔
      nonnegativePath a d ∧ (a:ℤ)+pathSum d n=0 ∧ s 0=false := by
  have hs : pathSum s 1=sign (s 0) := by simp [pathSum]
  simp only [firstHit,pathSum_append_right,hs]
  constructor
  · rintro ⟨hend,hpos⟩
    have hd : nonnegativePath a d := by
      intro k hk
      have hh := hpos k (by omega)
      rwa [pathSum_append_left d s hk] at hh
    have hn := hd n le_rfl
    have hb : s 0=false := by
      cases h : s 0 <;> simp_all [sign]
      omega
    refine ⟨hd,?_,hb⟩
    rw [hb] at hend
    norm_num [sign] at hend
    linarith
  · rintro ⟨hd,he,hb⟩
    constructor
    · rw [hb]; norm_num [sign]; linarith
    · intro k hk
      rw [pathSum_append_left d s (by omega)]
      exact hd k (by omega)

lemma pathMass_firstHit (n a : ℕ) :
    pathMass (n+1) (firstHit a)=killed n a 0/2 := by
  have he : ∀ d : Path (n+1), firstHit a d↔
      (nonnegativePath a (splitPathAt n 1 d).1 ∧ (a:ℤ)+pathSum (splitPathAt n 1 d).1 n=0) ∧
      (splitPathAt n 1 d).2 0=false := by
    intro d
    obtain ⟨⟨d,e⟩,rfl⟩ := (splitPathAt n 1).symm.surjective d
    simp only [Equiv.apply_symm_apply]
    change firstHit a (Fin.append d e)↔_
    simpa only [and_assoc] using firstHit_last a d e
  rw [pathMass_congr he,pathMass_append n 1
    (fun d => nonnegativePath a d ∧ (a:ℤ)+pathSum d n=0) (fun s => s 0=false)]
  have hlast : pathMass 1 (fun s => s 0=false)=1/2 := by
    rw [pathMass_succ]
    norm_num [pathMass]
  rw [hlast]
  have hk := pathMass_killed n a 0
  norm_num only [Nat.cast_zero] at hk
  rw [hk]
  ring

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

/-- Successive specified heights, with free terminal suffix. -/
def tracePoints (a R : ℕ) : (xs : List (ℕ×ℕ)) → Path (traceSize R xs) → Prop
  | [],_ => True
  | x::xs,d => (a:ℤ)+pathSum (splitPathAt x.1 (traceSize R xs) d).1 x.1=x.2 ∧
    tracePoints x.2 R xs (splitPathAt x.1 (traceSize R xs) d).2

/-- The same specified heights, together with nonnegative segments and final first hit. -/
def traceExcursion (a R : ℕ) : (xs : List (ℕ×ℕ)) → Path (traceSize R xs) → Prop
  | [],d => firstHit a d
  | x::xs,d =>
    (nonnegativePath a (splitPathAt x.1 (traceSize R xs) d).1 ∧
      (a:ℤ)+pathSum (splitPathAt x.1 (traceSize R xs) d).1 x.1=x.2) ∧
    traceExcursion x.2 R xs (splitPathAt x.1 (traceSize R xs) d).2

def traceKilledWeight (a R : ℕ) : List (ℕ×ℕ) → ℝ
  | [] => pathMass R (firstHit a)
  | x::xs => killed x.1 a x.2*traceKilledWeight x.2 R xs

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
open TreeCoding
attribute [local instance] Classical.propDecidable

-- The inherited product-law realization, not a fresh informal conditioning.
def uniformLaw (N : ℕ) : Measure (Path N) := Measure.pi (fun _ => coinLaw)

instance uniformLaw_probability (N : ℕ) : IsProbabilityMeasure (uniformLaw N) := inferInstanceAs
  (IsProbabilityMeasure (Measure.pi (fun _ : Fin N => coinLaw)))

lemma uniformLaw_singleton (N : ℕ) (d : Path N) :
    (uniformLaw N).real {d}=1/(2:ℝ)^N := by
  rw [measureReal_def,uniformLaw,Measure.pi_singleton]
  simp [coinLaw]

lemma uniformLaw_real (N : ℕ) (A : Set (Path N)) :
    (uniformLaw N).real A=pathMass N (fun d => d∈A) := by
  classical
  have he : ((Finset.univ.filter (fun d => d∈A) : Finset (Path N)) : Set (Path N))=A := by
    ext d; simp
  rw [← he,← sum_measureReal_singleton]
  simp only [Finset.sum_filter,uniformLaw_singleton,pathMass,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  simp only [Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs <;> simp

/-- Uniform binary walks conditioned on their first hit of -1 at the odd endpoint. -/
def excursionLaw (n : ℕ) : Measure (Path (2*n+1)) :=
  cond (uniformLaw (2*n+1)) {d | firstHit 0 d}

end FKCRT.SimpleWalk
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_ExcursionKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

def observed {N : ℕ} (a : ℕ) (xs : List (ℕ×ℕ)) (d : Path N) : Prop :=
  ∀ x∈located xs,(a:ℤ)+pathSum d x.1=x.2

end FKCRT.SimpleWalk
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_WordLaw
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def Parameters.ofQ (q : ℝ) (hq : 4<q) : Parameters where
  p := Real.sqrt q/(Real.sqrt q+2)
  lower := by
    have hs : 2<Real.sqrt q := (Real.lt_sqrt (by norm_num)).mpr (by nlinarith)
    exact (lt_div_iff₀ (by positivity)).mpr (by linarith)
  upper := by
    apply (div_lt_one (by positivity : 0<Real.sqrt q+2)).mpr
    linarith

end FKCRT.Inventory
end



end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MapCycles
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cut/join identities for tour permutations. Fixed points are retained as
one-element cycles, as required by the Euler-characteristic map definition. -/


noncomputable section
open Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Swapping the outputs at two distinct rotation cycles preserves every
old vertex incidence and merges the indicated two vertices. -/
lemma sameCycle_le_vertexJoin (p : Perm α) {a b : α} (h : ¬p.SameCycle a b)
    {x y : α} (hxy : p.SameCycle x y) : (swap a b*p).SameCycle x y := by
  let q := swap a b*p
  have hab : q.SameCycle a b := sameCycle_swap_of_not_sameCycle p h
  apply sameCycle_mono (p := p) (q := q) ?_ hxy
  intro d
  have hd : q.SameCycle d (q d) := sameCycle_apply_right.mpr (SameCycle.refl q d)
  by_cases ha : p d=a
  · have he : q d=b := by simp [q,mul_apply,ha]
    rw [ha]
    exact (he ▸ hd).trans hab.symm
  · by_cases hb : p d=b
    · have he : q d=a := by simp [q,mul_apply,hb]
      rw [hb]
      exact (he ▸ hd).trans hab
    · simpa [q,mul_apply,swap_apply_of_ne_of_ne ha hb] using hd

/-- Exact vertex equivalence after one-vertex gluing. In particular no
additional vertices are identified, including fixed points and loop blocks. -/
theorem sameCycle_vertexJoin_iff (p : Perm α) {a b : α} (h : ¬p.SameCycle a b) (x y : α) :
    (swap a b*p).SameCycle x y ↔ JoinRel p a b x y := by
  constructor
  · intro hxy
    obtain ⟨n,rfl⟩ := hxy.exists_nat_pow_eq
    clear hxy
    induction n with
    | zero => simpa using JoinRel.refl p a b x
    | succ n ih =>
      rw [pow_succ',mul_apply]
      exact ih.trans (JoinRel.step p a b _)
  · rintro (hxy|⟨hx,hy⟩)
    · exact sameCycle_le_vertexJoin p h hxy
    · have hab := sameCycle_swap_of_not_sameCycle p h
      rcases hx with hx|hx <;> rcases hy with hy|hy
      · exact (sameCycle_le_vertexJoin p h hx).trans (sameCycle_le_vertexJoin p h hy).symm
      · exact (sameCycle_le_vertexJoin p h hx).trans (hab.trans (sameCycle_le_vertexJoin p h hy).symm)
      · exact (sameCycle_le_vertexJoin p h hx).trans (hab.symm.trans (sameCycle_le_vertexJoin p h hy).symm)
      · exact (sameCycle_le_vertexJoin p h hx).trans (sameCycle_le_vertexJoin p h hy).symm

end FKCRT.MapCycles
end


noncomputable section
open Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The inclusion of either block's vertices remains injective under the
actual vertex-rotation cut/join. -/
theorem vertexJoin_inside_iff {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) {a b x y : α} (ha : a∈S) (hb : b∉S)
    (hx : x∈S) (hy : y∈S) : (swap a b*p).SameCycle x y ↔ p.SameCycle x y := by
  rw [sameCycle_vertexJoin_iff p (not_sameCycle_partition hp ha hb)]
  constructor
  · rintro (h|⟨hxa|hxb,hya|hyb⟩)
    · exact h
    · exact hxa.trans hya.symm
    · exact False.elim (hb ((sameCycle_partition hp hyb).mp hy))
    · exact False.elim (hb ((sameCycle_partition hp hxb).mp hx))
    · exact False.elim (hb ((sameCycle_partition hp hxb).mp hx))
  · exact Or.inl

theorem vertexJoin_outside_iff {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) {a b x y : α} (ha : a∈S) (hb : b∉S)
    (hx : x∉S) (hy : y∉S) : (swap a b*p).SameCycle x y ↔ p.SameCycle x y := by
  have hh := vertexJoin_inside_iff (S := Sᶜ) (p := p)
    (fun d => not_congr (hp d)) hb (by simpa using ha) hx hy
  simpa only [swap_comm b a] using hh

/-- A vertex in one block coincides with a vertex in the other block if
and only if both are their respective attachment poles. -/
theorem vertexJoin_cross_iff {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) {a b x y : α} (ha : a∈S) (hb : b∉S)
    (hx : x∈S) (hy : y∉S) : (swap a b*p).SameCycle x y ↔ p.SameCycle x a ∧ p.SameCycle y b := by
  rw [sameCycle_vertexJoin_iff p (not_sameCycle_partition hp ha hb)]
  constructor
  · rintro (h|⟨hxa|hxb,hya|hyb⟩)
    · exact False.elim (hy ((sameCycle_partition hp h).mp hx))
    · exact False.elim (hy ((sameCycle_partition hp hya).mpr ha))
    · exact ⟨hxa,hyb⟩
    · exact False.elim (hb ((sameCycle_partition hp hxb).mp hx))
    · exact False.elim (hb ((sameCycle_partition hp hxb).mp hx))
  · rintro ⟨hxa,hyb⟩
    exact Or.inr ⟨Or.inl hxa,Or.inr hyb⟩

end FKCRT.MapCycles
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_GraphWedge
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Equiv Equiv.Perm
namespace FKCRT.PermutationWedge
open MapCycles
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α] [Fintype α]

variable {p e : Perm α} {S : Set α} {a b : α}
variable (hp : ∀ d,p d∈S ↔ d∈S) (ha : a∈S) (hb : b∉S)

/- The maps below operate on the actual rotation-cycle quotients. -/
def inclusion : Side p S→Vertex (swap a b*p) := Quotient.lift
  (fun d => vertex (swap a b*p) d.val)
  (fun _ _ h => Quotient.sound (sameCycle_le_vertexJoin p (not_sameCycle_partition hp ha hb) h))

lemma inclusion_injective : Function.Injective (inclusion hp ha hb) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      intro h
      apply Quotient.sound
      exact (vertexJoin_inside_iff hp ha hb x.property y.property).mp (Quotient.exact h)

include hp hb in
lemma retractD_eq_of_join {x y : α} (hxy : (swap a b*p).SameCycle x y) :
    retractD (p := p) ha x=retractD (p := p) ha y := by
  by_cases hx : x∈S
  · by_cases hy : y∈S
    · simp only [retractD,dite_eq_left hx,dite_eq_left hy]
      exact Quotient.sound ((vertexJoin_inside_iff hp ha hb hx hy).mp hxy)
    · simp only [retractD,dite_eq_left hx,dite_eq_right hy]
      exact Quotient.sound ((vertexJoin_cross_iff hp ha hb hx hy).mp hxy).1
  · by_cases hy : y∈S
    · simp only [retractD,dite_eq_right hx,dite_eq_left hy]
      exact (Quotient.sound ((vertexJoin_cross_iff hp ha hb hy hx).mp hxy.symm).1).symm
    · simp only [retractD,dite_eq_right hx,dite_eq_right hy]

def retract : Vertex (swap a b*p)→Side p S :=
  Quotient.lift (retractD (p := p) ha) (fun _ _ h => retractD_eq_of_join hp ha hb h)

lemma retract_inclusion (x : Side p S) : retract hp ha hb (inclusion hp ha hb x)=x := by
  induction x using Quotient.inductionOn with
  | h d => exact dite_eq_left d.property

def flipInclusion : Side p Sᶜ →Vertex (swap a b*p) := Quotient.lift
  (fun d => vertex (swap a b*p) d.val)
  (fun _ _ h => Quotient.sound (sameCycle_le_vertexJoin p (not_sameCycle_partition hp ha hb) h))

lemma flipInclusion_injective : Function.Injective (flipInclusion hp ha hb) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      intro h
      apply Quotient.sound
      exact (vertexJoin_outside_iff hp ha hb x.property y.property).mp (Quotient.exact h)

include hp ha in
lemma flipRetractD_eq_of_join {x y : α} (hxy : (swap a b*p).SameCycle x y) :
    flipRetractD (p := p) hb x=flipRetractD (p := p) hb y := by
  have h := retractD_eq_of_join (S := Sᶜ) (p := p)
    (fun d => not_congr (hp d)) hb (by simpa using ha)
    (show (swap b a*p).SameCycle x y by simpa only [swap_comm b a] using hxy)
  by_cases hx : x∈Sᶜ <;> by_cases hy : y∈Sᶜ <;>
    simp_all only [retractD,flipRetractD,dite_eq_left]

def flipRetract : Vertex (swap a b*p)→Side p Sᶜ :=
  Quotient.lift (flipRetractD (p := p) hb) (fun _ _ h => flipRetractD_eq_of_join hp ha hb h)

lemma flipRetract_flipInclusion (x : Side p Sᶜ) : flipRetract hp ha hb (flipInclusion hp ha hb x)=x := by
  induction x using Quotient.inductionOn with
  | h d => exact dite_eq_left d.property

lemma flipRetract_inclusion (x : Side p S) :
    flipRetract hp ha hb (inclusion hp ha hb x)=sideMk p Sᶜ b hb := by
  induction x using Quotient.inductionOn with
  | h d => exact dite_eq_right (by simp [d.property])

lemma retract_flipInclusion (x : Side p Sᶜ) :
    retract hp ha hb (flipInclusion hp ha hb x)=sideMk p S a ha := by
  induction x using Quotient.inductionOn with
  | h d => exact dite_eq_right d.property

lemma inclusion_poles : inclusion hp ha hb (sideMk p S a ha)=flipInclusion hp ha hb (sideMk p Sᶜ b hb) :=
  Quotient.sound (sameCycle_swap_of_not_sameCycle p (not_sameCycle_partition hp ha hb))

variable (he : ∀ d,e d∈S ↔ d∈S)

def inclusionHom : sideGraph e p S he →g dartGraph e (swap a b*p) where
  toFun := inclusion hp ha hb
  map_rel' := by
    intro x y hxy
    refine ⟨fun h => hxy.1 (inclusion_injective hp ha hb h),?_⟩
    rcases hxy.2 with ⟨d,hd,hx,hy⟩|⟨d,hd,hy,hx⟩
    · exact Or.inl ⟨d,by rw [← hx];rfl,by rw [← hy];rfl⟩
    · exact Or.inr ⟨d,by rw [← hy];rfl,by rw [← hx];rfl⟩

def flipInclusionHom : sideGraph e p Sᶜ (fun d => not_congr (he d)) →g dartGraph e (swap a b*p) where
  toFun := flipInclusion hp ha hb
  map_rel' := by
    intro x y hxy
    refine ⟨fun h => hxy.1 (flipInclusion_injective hp ha hb h),?_⟩
    rcases hxy.2 with ⟨d,hd,hx,hy⟩|⟨d,hd,hy,hx⟩
    · exact Or.inl ⟨d,by rw [← hx];rfl,by rw [← hy];rfl⟩
    · exact Or.inr ⟨d,by rw [← hy];rfl,by rw [← hx];rfl⟩

lemma retraction_edge {x y : Vertex (swap a b*p)} (hxy : (dartGraph e (swap a b*p)).Adj x y) :
    ((sideGraph e p S he).Adj (retract hp ha hb x) (retract hp ha hb y) ∧
      flipRetract hp ha hb x=flipRetract hp ha hb y) ∨
    (retract hp ha hb x=retract hp ha hb y ∧
      (sideGraph e p Sᶜ (fun d => not_congr (he d))).Adj (flipRetract hp ha hb x) (flipRetract hp ha hb y)) := by
  have forward (d : α) (hdiff : vertex (swap a b*p) d≠vertex (swap a b*p) (e d)) :
      ((sideGraph e p S he).Adj (retractD (p := p) ha d) (retractD (p := p) ha (e d)) ∧
        flipRetractD (p := p) hb d=flipRetractD (p := p) hb (e d)) ∨
      (retractD (p := p) ha d=retractD (p := p) ha (e d) ∧
        (sideGraph e p Sᶜ (fun d => not_congr (he d))).Adj (flipRetractD (p := p) hb d) (flipRetractD (p := p) hb (e d))) := by
    by_cases hd : d∈S
    · have he' := (he d).mpr hd
      left
      simp only [retractD,dite_eq_left hd,dite_eq_left he']
      refine ⟨⟨?_,Or.inl ⟨d,hd,rfl,rfl⟩⟩,?_⟩
      · intro h
        exact hdiff (congrArg (inclusion hp ha hb) h)
      · simp [flipRetractD,hd,he']
    · have he' : e d∉S := fun h => hd ((he d).mp h)
      right
      simp only [retractD,dite_eq_right hd,dite_eq_right he',flipRetractD,Set.mem_compl_iff,dite_eq_left hd,dite_eq_left he']
      refine ⟨trivial,⟨?_,Or.inl ⟨d,hd,rfl,rfl⟩⟩⟩
      intro h
      exact hdiff (congrArg (flipInclusion hp ha hb) h)
  rcases hxy.2 with ⟨d,rfl,rfl⟩|⟨d,rfl,rfl⟩
  · exact forward d hxy.1
  · rcases forward d hxy.1.symm with ⟨h,h'⟩|⟨h',h⟩
    · exact Or.inl ⟨h.symm,h'.symm⟩
    · exact Or.inr ⟨h'.symm,h.symm⟩

/-- Actual permutation-map insertion satisfies graph-wedge adjacency data.
No metric or distance assertion is supplied as an assumption. -/
def data : GraphWedge.Data (sideGraph e p S he)
    (sideGraph e p Sᶜ (fun d => not_congr (he d))) (dartGraph e (swap a b*p)) where
  left := inclusionHom hp ha hb he
  right := flipInclusionHom hp ha hb he
  poleLeft := sideMk p S a ha
  poleRight := sideMk p Sᶜ b hb
  shared := inclusion_poles hp ha hb
  retractLeft := retract hp ha hb
  retractRight := flipRetract hp ha hb
  left_left := retract_inclusion hp ha hb
  right_right := flipRetract_flipInclusion hp ha hb
  right_left := flipRetract_inclusion hp ha hb
  left_right := retract_flipInclusion hp ha hb
  edge := retraction_edge hp ha hb he

end FKCRT.PermutationWedge
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MapEncoding
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT

/-- A rooted connected rotation system has no nontrivial automorphisms.
Consequently the source's distinguished corners carry no symmetry divisor. -/
lemma rooted_automorphism_eq_one {n : ℕ} (M : LabelledMap n) (r : Equiv.Perm (Dart n))
    (h₀ : r 0=0) (ha : ∀ d,M.val.1 (r d)=r (M.val.1 d))
    (hs : ∀ d,M.val.2 (r d)=r (M.val.2 d)) : r=1 := by
  apply Equiv.ext
  change ∀ d,r d=d
  apply connected_dart_induction M.property.1 M.property.2.2.1 (P := fun d => r d=d) h₀
  · intro d hd
    rw [← ha,hd]
  · intro d hd
    rw [← hs,hd]

lemma root_isomorphism_unique {n : ℕ} {M N : LabelledMap n}
    {r r' : Equiv.Perm (Dart n)}
    (hr : r 0=0) (ha : ∀ d,N.val.1 (r d)=r (M.val.1 d))
    (hs : ∀ d,N.val.2 (r d)=r (M.val.2 d))
    (hr' : r' 0=0) (ha' : ∀ d,N.val.1 (r' d)=r' (M.val.1 d))
    (hs' : ∀ d,N.val.2 (r' d)=r' (M.val.2 d)) : r=r' := by
  have hh : r.trans r'.symm=1 := by
    apply rooted_automorphism_eq_one M
    · change r'.symm (r 0)=0
      rw [hr]
      exact r'.symm_apply_eq.mpr hr'.symm
    · intro d
      apply r'.injective
      simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
      rw [← ha',Equiv.apply_symm_apply,ha]
    · intro d
      apply r'.injective
      simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
      rw [← hs',Equiv.apply_symm_apply,hs]
  apply Equiv.ext
  intro d
  have he := congrArg (fun e : Equiv.Perm (Dart n) => r' (e d)) hh
  simpa using he

end FKCRT
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT

lemma spanningGraph_connected_of_face_cycle {n : ℕ} (a s : Equiv.Perm (Dart n))
    (hc : ∀ d e,(s*a).SameCycle d e) : (spanningGraph a s univ).Connected := by
  refine {preconnected := ?_, nonempty := ⟨orbit s 0⟩}
  intro v w
  induction v using Quotient.inductionOn with | h d =>
    induction w using Quotient.inductionOn with | h e =>
      obtain ⟨k,hk⟩ := (hc d e).exists_nat_pow_eq
      rw [← hk]
      have hp (j : ℕ) : (spanningGraph a s univ).Reachable (orbit s d) (orbit s (((s*a)^j) d)) := by
        induction j with
        | zero => exact SimpleGraph.Reachable.refl _
        | succ j ih =>
          rw [pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,orbit_perm]
          exact ih.trans (spanningGraph_reachable_reversal a s _)
      exact hp k

lemma pathRotation_val (n : ℕ) (d : Dart n) :
    (pathRotation n d).val=if d.val=0 then 0 else 2*(n+1)-d.val := by
  simp only [pathRotation,Equiv.Perm.mul_apply,Fin.revPerm_apply,finRotate_apply,
    Fin.val_add,Fin.val_rev,Fin.val_one]
  by_cases h : d.val=0
  · rw [ite_eq_left h,h]
    have he : 2*(n+1)-(0+1)+1=2*(n+1) := by omega
    rw [he,Nat.mod_self]
  · rw [ite_eq_right h,Nat.mod_eq_of_lt (by have := d.isLt; omega)]
    omega

lemma pathRotation_involutive (n : ℕ) : Function.Involutive (pathRotation n) := by
  intro d
  apply Fin.ext
  rw [pathRotation_val,pathRotation_val]
  have := d.isLt
  split_ifs <;> omega

lemma pathRotation_fixed (n : ℕ) (d : Dart n) : pathRotation n d=d ↔ d.val=0 ∨ d.val=n+1 := by
  rw [Fin.ext_iff,pathRotation_val]
  have := d.isLt
  split_ifs <;> omega

lemma pathRotation_fixed_card (n : ℕ) : Nat.card {d : Dart n // pathRotation n d=d}=2 := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have he : Finset.univ.filter (fun d : Dart n => pathRotation n d=d)=
      {(0 : Dart n),⟨n+1,by omega⟩} := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    rw [pathRotation_fixed]
    simp only [Fin.ext_iff,Fin.val_zero]
  rw [he]
  have hd : (0 : Dart n)≠⟨n+1,by omega⟩ := by intro h; have := congrArg Fin.val h; simp only [Fin.val_zero] at this; omega
  simp [hd]

lemma pathRotation_orbits (n : ℕ) : Nat.card (Orbit (pathRotation n))=n+2 := by
  have hh := MapFinite.twice_card_orbits (pathRotation n) (pathRotation_involutive n)
  simp only [← Nat.card_eq_fintype_card,pathRotation_fixed_card] at hh
  have hd : Nat.card (Dart n)=2*(n+1) := by simp [Dart]
  rw [hd] at hh
  change 2*Nat.card (Orbit (pathRotation n))=2*(n+1)+2 at hh
  omega

/-- A concrete genus-zero path map with every positive edge size. -/
def pathLabelledMap (n : ℕ) : LabelledMap n := ⟨(Fin.revPerm,pathRotation n),by
  refine ⟨Fin.rev_involutive,?_,?_,?_⟩
  · intro d h
    have he := congrArg Fin.val h
    simp only [Fin.revPerm_apply,Fin.val_rev] at he
    have := d.isLt
    omega
  · apply spanningGraph_connected_of_face_cycle
    rw [pathRotation_face]
    exact rotate_sameCycle n
  · change Nat.card (Orbit (pathRotation n))+Nat.card (Orbit (pathRotation n*Fin.revPerm))=n+3
    rw [pathRotation_face,pathRotation_orbits,rotate_orbits]⟩

instance rootedMap_nonempty (n : ℕ) : Nonempty (RootedMap n) := ⟨Quotient.mk _ (pathLabelledMap n)⟩

end FKCRT
end



/-! The exact edge-reversal tour of the rotation-system maps. -/


noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma edgeEnds_orbit (a s : Perm (Dart n)) (ha : Function.Involutive a) (d : Dart n) :
    edgeEnds a s (orbit a d) = s(orbit s d, orbit s (a d)) := by
  have hh := (MapFinite.mk_eq_iff_involution a ha d (orbit a d)).mp rfl
  rcases hh with hh | hh
  · conv_rhs => rw [hh]
    rfl
  · conv_rhs => rw [hh, ha]
    exact Sym2.eq_swap

lemma spanningGraph_edgeSet_subset (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) :
    (spanningGraph a s (A : Set (Orbit a))).edgeSet ⊆ edgeEnds a s '' (A : Set (Orbit a)) := by
  rintro e he
  induction e using Sym2.ind with | _ v w =>
    rcases (SimpleGraph.mem_edgeSet _).mp he with ⟨_,h | h⟩
    · obtain ⟨d,hd,hv,hw⟩ := h
      refine ⟨orbit a d, hd, ?_⟩
      rw [edgeEnds_orbit a s ha d, hv, hw]
    · obtain ⟨d,hd,hw,hv⟩ := h
      refine ⟨orbit a d, hd, ?_⟩
      rw [edgeEnds_orbit a s ha d, hv, hw]
      exact Sym2.eq_swap

lemma spanningGraph_card_edgeSet_le (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) :
    Nat.card (spanningGraph a s (A : Set (Orbit a))).edgeSet ≤ A.card := by
  rw [Nat.card_coe_set_eq]
  exact (Set.ncard_le_ncard (spanningGraph_edgeSet_subset a s ha A)).trans
    ((Set.ncard_image_le (f := edgeEnds a s) (s := (A : Set (Orbit a)))).trans
      (Set.ncard_coe_finset A).le)

/-- The selected edges of a one-cycle planar tour form an actual spanning tree
of the all-edge graph. There are no suppressed loop/parallel edges in
its size: the cardinality equality forces every chosen edge to be distinct
and non-loop. -/
theorem tour_spanningTree (M : LabelledMap n) (A : Finset (Orbit M.val.1))
    (hc : ∀ d e, (M.val.2 * partialReversal M.val.1 M.property.1 A).SameCycle d e) :
    (spanningGraph M.val.1 M.val.2 (A : Set (Orbit M.val.1))).IsTree ∧
      Nat.card (spanningGraph M.val.1 M.val.2 (A : Set (Orbit M.val.1))).edgeSet = A.card := by
  have hconn := spanningGraph_connected_of_tour M.val.1 M.val.2 M.property.1 A hc
  have hle := hconn.card_vert_le_card_edgeSet_add_one
  have hle' := spanningGraph_card_edgeSet_le M.val.1 M.val.2 M.property.1 A
  have he := tour_edge_card M A hc
  have hh : Nat.card (spanningGraph M.val.1 M.val.2
      (A : Set (Orbit M.val.1))).edgeSet = A.card := by omega
  exact ⟨SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hconn, by omega⟩, hh⟩

end FKCRT
end



/-! A genuine multigraph spanning tree has one complete edge-reversal tour.
This is the converse direction of the source's finite encoding, proved
without invoking a topological thickening or assuming planarity. -/
noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma spanningGraph_reachable_of_sameCycle (a s : Perm (Dart n))
    (ha : Function.Involutive a) (A : Finset (Orbit a)) {d e : Dart n}
    (h : (s * partialReversal a ha A).SameCycle d e) :
    (spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s d) (orbit s e) := by
  obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
  rw [← hk]
  clear hk
  induction k with
  | zero => exact .refl _
  | succ k ih =>
    rw [pow_succ',mul_apply,mul_apply,orbit_perm]
    exact ih.trans (spanningGraph_reachable_partial a s ha A _)

lemma spanningGraph_edgeSet_of_card (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a))
    (hc : Nat.card (spanningGraph a s (A : Set (Orbit a))).edgeSet = A.card) :
    (spanningGraph a s (A : Set (Orbit a))).edgeSet = edgeEnds a s '' (A : Set (Orbit a)) ∧
      Set.InjOn (edgeEnds a s) (A : Set (Orbit a)) := by
  have hh := spanningGraph_edgeSet_subset a s ha A
  have hi := Set.ncard_image_le (f := edgeEnds a s) (s := (A : Set (Orbit a)))
  have hec : (spanningGraph a s (A : Set (Orbit a))).edgeSet.ncard = A.card := by
    simpa only [Nat.card_coe_set_eq] using hc
  have him : (edgeEnds a s '' (A : Set (Orbit a))).ncard = A.card := by
    have := Set.ncard_le_ncard hh
    rw [Set.ncard_coe_finset] at hi
    omega
  refine ⟨Set.eq_of_subset_of_ncard_le hh (by omega),?_⟩
  apply Set.injOn_of_ncard_image_eq _ A.finite_toSet
  simpa only [Set.ncard_coe_finset] using him

lemma spanningGraph_delete_edge_le (a s : Perm (Dart n)) (ha : Function.Involutive a)
    {A : Finset (Orbit a)} (e : Orbit a) (he : e ∉ A)
    (hi : Set.InjOn (edgeEnds a s) ((insert e A : Finset (Orbit a)) : Set (Orbit a))) :
    spanningGraph a s (A : Set (Orbit a)) ≤
      (spanningGraph a s ((insert e A : Finset (Orbit a)) : Set (Orbit a))).deleteEdges {edgeEnds a s e} := by
  intro v w hvw
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨spanningGraph_mono a s (by intro x hx; exact Finset.mem_insert_of_mem hx) hvw,?_⟩
  intro heq
  have hh := spanningGraph_edgeSet_subset a s ha A ((SimpleGraph.mem_edgeSet _).mpr hvw)
  obtain ⟨f,hf,hfvw⟩ := hh
  have hfe : f = e := hi (Finset.mem_insert_of_mem hf) (Finset.mem_insert_self _ _) (by
    exact hfvw.trans (Set.mem_singleton_iff.mp heq))
  exact he (hfe ▸ hf)

/-- Each chosen forest edge joins two tour cycles, hence the exact cycle count. -/
theorem forest_tour_cycle_card (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a))
    (ht : (spanningGraph a s (A : Set (Orbit a))).IsAcyclic)
    (hn : ∀ e ∈ A, orbit s e.out ≠ orbit s (a e.out))
    (hi : Set.InjOn (edgeEnds a s) (A : Set (Orbit a))) :
    Nat.card (Orbit (s * partialReversal a ha A)) + A.card = Nat.card (Orbit s) := by
  induction A using Finset.induction_on with
  | empty => simp [partialReversal_empty]
  | @insert e A he ih =>
    have hsub : (A : Set (Orbit a)) ⊆ ((insert e A : Finset (Orbit a)) : Set (Orbit a)) := by
      intro f hf; exact Finset.mem_insert_of_mem hf
    have htA := ht.anti (spanningGraph_mono a s hsub)
    have hni : ∀ f ∈ A, orbit s f.out ≠ orbit s (a f.out) := fun f hf => hn f (hsub hf)
    have hii : Set.InjOn (edgeEnds a s) (A : Set (Orbit a)) := hi.mono hsub
    have ih' := ih htA hni hii
    have hedge : (spanningGraph a s ((insert e A : Finset (Orbit a)) : Set (Orbit a))).Adj
        (orbit s e.out) (orbit s (a e.out)) := by
      refine ⟨hn e (Finset.mem_insert_self _ _), Or.inl ⟨e.out,?_,rfl,rfl⟩⟩
      change orbit a e.out ∈ insert e A
      rw [show orbit a e.out = e from Quotient.out_eq e]
      exact Finset.mem_insert_self e A
    have hbridge := SimpleGraph.isAcyclic_iff_forall_isBridge.mp ht
      ((SimpleGraph.mem_edgeSet _).mpr hedge)
    have hnr : ¬(spanningGraph a s (A : Set (Orbit a))).Reachable
        (orbit s e.out) (orbit s (a e.out)) := by
      intro hh
      apply (SimpleGraph.isBridge_iff.mp hbridge)
      exact hh.mono (spanningGraph_delete_edge_le a s ha e he hi)
    have hnc : ¬(s * partialReversal a ha A).SameCycle e.out (a e.out) :=
      fun h => hnr (spanningGraph_reachable_of_sameCycle a s ha A h)
    have hjoin := MapCycles.card_orbits_swap_of_not_sameCycle
      (s * partialReversal a ha A) (a := (s * partialReversal a ha A) e.out)
      (b := (s * partialReversal a ha A) (a e.out)) (by
        simpa only [sameCycle_apply_left, sameCycle_apply_right] using hnc)
    rw [← mul_swap_eq_swap_mul] at hjoin
    rw [partialReversal_insert a ha A e he, ← mul_assoc,
      Finset.card_insert_of_notMem he]
    change Nat.card (Orbit ((s * partialReversal a ha A) * swap e.out (a e.out))) + (A.card+1) = _
    change Nat.card (Orbit ((s * partialReversal a ha A) * swap e.out (a e.out))) + 1 = Nat.card (Orbit (s * partialReversal a ha A)) at hjoin
    omega

end FKCRT
end



/-! Exact reconstruction in the rotation-system convention. The
Euler equalities on the two coloured matchings are equivalent to their
noncrossing property; maximum orbit counts are proved for stack matchings
in `WorkNoncrossing`, rather than postulated for a map. -/

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CornerInverse
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*} [DecidableEq α]

lemma turns_sublist_preserves {E F : List (α×α)} (hn : (endpoints F).Nodup)
    (hEF : E<+F) {S : Set α} (hF : ∀ d∈S,turns F d∈S) :
    ∀ d,turns E d∈S ↔ d∈S := by
  have he : (endpoints E).Nodup := hn.sublist (hEF.flatMap _)
  have hf (d : α) (hd : d∈S) : turns E d∈S := by
    by_cases hx : d∈endpoints E
    · rw [turns_sublist_apply hn hEF hx]
      exact hF d hd
    · simpa only [turns_fixed_of_notMem hx] using hd
  intro d
  constructor
  · intro hd
    simpa only [turns_involutive he d] using hf (turns E d) hd
  · exact hf d

end FKCRT.MapCycles
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CoreCompression
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
lemma StackMatching.empty_interval_preserves {w : α→TypedLetter} {u v z : List α}
    (M : StackMatching w (u++(v++z))) (hn : (u++(v++z)).Nodup)
    (hv : stackTypedRun (v.map w) []=some []) :
    (∀ d,M.mate d∈v ↔ d∈v) ∧ (∀ d,turns M.first d∈v ↔ d∈v) := by
  have hm (d : α) (hd : d∈v) : turns (M.first++M.second) d∈v := by
    exact empty_interval_matching_closed w u v z hn M.first M.second
      M.first_arches M.second_arches M.covers M.first_types M.second_types hv d hd
  have hn' : (endpoints (M.first++M.second)).Nodup := M.covers.nodup_iff.mpr hn
  exact ⟨turns_sublist_preserves hn' (List.Sublist.refl _) hm,
    turns_sublist_preserves hn' (List.sublist_append_left _ _) hm⟩

/-- The two graph pieces retain every edge, including both matching colours.
This is the actual all-edge graph at an arbitrary insertion interval. -/
def StackMatching.empty_interval_wedge {w : α→TypedLetter}
    (u L z : List α) (a b : α) (R : List α)
    (M : StackMatching w (u++((a::L)++z))) (hn : (u++((a::L)++z)).Nodup)
    (hv : stackTypedRun ((a::L).map w) []=some []) (hcomp : z++u=b::R) :
    let p := (a::L).formPerm*(b::R).formPerm*turns M.first
    let S : Set α := {d | d∈a::L}
    GraphWedge.Data (sideGraph M.mate p S (M.empty_interval_preserves hn hv).1)
      (sideGraph M.mate p Sᶜ (fun d => not_congr ((M.empty_interval_preserves hn hv).1 d)))
      (dartGraph M.mate (swap a b*p)) := by
  let S : Set α := {d | d∈a::L}
  let p := (a::L).formPerm*(b::R).formPerm*turns M.first
  have hh : ((a::L)++(b::R)).Nodup := by
    rw [← hcomp,← List.append_assoc]
    exact List.perm_append_comm.nodup_iff.mp hn
  have hd : (a::L).Disjoint (b::R) := List.disjoint_iff_ne.mpr (List.nodup_append.mp hh).2.2
  have hpres := M.empty_interval_preserves hn hv
  have hp : ∀ d,p d∈S ↔ d∈S := by
    intro d
    simp only [p,S,Set.mem_ofPred_eq,mul_apply,List.formPerm_mem_iff_mem,
      formPerm_other_mem_iff hd,hpres.2]
  exact PermutationWedge.data hp (by simp [S])
    (fun hb => List.disjoint_left.mp hd hb (by simp)) hpres.1

end FKCRT.Inventory
end


noncomputable section
open Equiv Equiv.Perm
namespace FKCRT.PermutationWedge
variable {α : Type*} [Fintype α]
attribute [local instance] Classical.propDecidable

def fullInclusion (p : Perm α) (S : Set α) : Side p S→Vertex p :=
  Quotient.lift (fun d => vertex p d.val) (fun _ _ h => Quotient.sound h)

omit [Fintype α] in
lemma fullInclusion_injective (p : Perm α) (S : Set α) :
    Function.Injective (fullInclusion p S) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      intro h
      apply Quotient.sound
      change vertex p x.val=vertex p y.val at h
      have hh : p.SameCycle x.val y.val := Quotient.exact h
      exact hh

lemma fullRetract_wellDefined {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (a : α) (ha : a∈S) {x y : α}
    (hxy : p.SameCycle x y) :
    (if hx : x∈S then sideMk p S x hx else sideMk p S a ha)=
      (if hy : y∈S then sideMk p S y hy else sideMk p S a ha) := by
  classical
  have hh := MapCycles.sameCycle_partition hp hxy
  by_cases hx : x∈S
  · rw [dite_eq_left hx,dite_eq_left (hh.mp hx)]
    exact Quotient.sound hxy
  · rw [dite_eq_right hx,dite_eq_right (fun h => hx (hh.mpr h))]

def fullRetract {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (a : α) (ha : a∈S) : Vertex p→Side p S := by
  classical
  exact Quotient.lift (fun d => if hd : d∈S then sideMk p S d hd else sideMk p S a ha)
    (fun _ _ h => fullRetract_wellDefined hp a ha h)

def fullInclusionHom {p e : Perm α} {S : Set α}
    (he : ∀ d,e d∈S ↔ d∈S) : sideGraph e p S he →g dartGraph e p where
  toFun := fullInclusion p S
  map_rel' := by
    intro x y hxy
    refine ⟨fun h => hxy.1 (fullInclusion_injective p S h),?_⟩
    rcases hxy.2 with ⟨d,hd,hx,hy⟩|⟨d,hd,hy,hx⟩
    · exact Or.inl ⟨d,congrArg (fullInclusion p S) hx,congrArg (fullInclusion p S) hy⟩
    · exact Or.inr ⟨d,congrArg (fullInclusion p S) hy,congrArg (fullInclusion p S) hx⟩

end FKCRT.PermutationWedge
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The actual retained matching after a successful insertion is erased. -/
def StackMatching.deleteInterval {w : α→TypedLetter} {u v z : List α}
    (M : StackMatching w (u++(v++z))) (hn : (u++(v++z)).Nodup)
    (hv : stackTypedRun (v.map w) []=some []) : StackMatching w (u++z) := by
  have hpres := (M.empty_interval_preserves hn hv).1
  let keep : α→Bool := fun d => decide (d∉v)
  have hk : ∀ d∈u++(v++z),keep (M.mate d)=keep d := by
    intro d _
    simp only [keep,decide_eq_decide]
    exact not_congr (hpres d)
  exact filter_delete_interval u v z hn ▸ M.filter hn keep hk

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The literal restricted successful matching, retaining an inserted word. -/
def StackMatching.keepInterval {w : α→TypedLetter} {u v z : List α}
    (M : StackMatching w (u++(v++z))) (hn : (u++(v++z)).Nodup)
    (hv : stackTypedRun (v.map w) []=some []) : StackMatching w v := by
  have hpres := (M.empty_interval_preserves hn hv).1
  let keep : α→Bool := fun d => decide (d∈v)
  have hk : ∀ d∈u++(v++z),keep (M.mate d)=keep d := by
    intro d _
    simp only [keep,decide_eq_decide]
    exact hpres d
  exact filter_keep_interval u v z hn ▸ M.filter hn keep hk

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CoreWords
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α] [Fintype β]

def vertexEmbeddingEquiv (f : α → β) (hf : Function.Injective f)
    {p : Perm α} {q : Perm β} (h : ∀ x,q (f x)=f (p x)) :
    Vertex p ≃ Side q (Set.range f) :=
  Quotient.congr (Equiv.ofInjective f hf) (sameCycle_embedding f hf h)

lemma vertexEmbeddingEquiv_vertex (f : α → β) (hf : Function.Injective f)
    {p : Perm α} {q : Perm β} (h : ∀ x,q (f x)=f (p x)) (x : α) :
    vertexEmbeddingEquiv f hf h (vertex p x)=sideMk q (Set.range f) (f x) ⟨x,rfl⟩ := rfl

/-- Relabelling literal darts, without adding edges or collapsing nonzero
original distances. -/
def dartGraphEmbeddingIso (f : α → β) (hf : Function.Injective f)
    {p e : Perm α} {q a : Perm β}
    (hp : ∀ x,q (f x)=f (p x)) (he : ∀ x,a (f x)=f (e x)) :
    dartGraph e p ≃g sideGraph a q (Set.range f) (perm_preserves_range f he) where
  toEquiv := vertexEmbeddingEquiv f hf hp
  map_rel_iff' := by
    intro x y
    constructor
    · rintro ⟨hne,h⟩
      refine ⟨fun h => hne (congrArg (vertexEmbeddingEquiv f hf hp) h),?_⟩
      have go (x y : Vertex p) (d : β) (hd : d∈Set.range f)
          (hx : sideMk q (Set.range f) d hd=vertexEmbeddingEquiv f hf hp x)
          (hy : sideMk q (Set.range f) (a d) ((perm_preserves_range f he d).mpr hd)=
            vertexEmbeddingEquiv f hf hp y) :
          ∃ z,vertex p z=x ∧ vertex p (e z)=y := by
        obtain ⟨z,rfl⟩ := hd
        refine ⟨z,(vertexEmbeddingEquiv f hf hp).injective hx,?_⟩
        apply (vertexEmbeddingEquiv f hf hp).injective
        rw [vertexEmbeddingEquiv_vertex]
        simpa only [he] using hy
      rcases h with ⟨d,hd,hx,hy⟩|⟨d,hd,hy,hx⟩
      · exact Or.inl (go x y d hd hx hy)
      · exact Or.inr (go y x d hd hy hx)
    · rintro ⟨hne,h⟩
      refine ⟨fun h => hne ((vertexEmbeddingEquiv f hf hp).injective h),?_⟩
      have go (x y : Vertex p) (d : α) (hx : vertex p d=x) (hy : vertex p (e d)=y) :
          ∃ z,∃ hz : z∈Set.range f,sideMk q (Set.range f) z hz=vertexEmbeddingEquiv f hf hp x ∧
            sideMk q (Set.range f) (a z) ((perm_preserves_range f he z).mpr hz)=
              vertexEmbeddingEquiv f hf hp y := by
        refine ⟨f d,⟨d,rfl⟩,congrArg (vertexEmbeddingEquiv f hf hp) hx,?_⟩
        have hh := congrArg (vertexEmbeddingEquiv f hf hp) hy
        simpa only [vertexEmbeddingEquiv_vertex,he] using hh
      rcases h with ⟨d,hx,hy⟩|⟨d,hy,hx⟩
      · exact Or.inl (go x y d hx hy)
      · exact Or.inr (go y x d hy hx)

end FKCRT.PermutationWedge
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PlaneTrees
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory

lemma corner_child_short (l : List (TypedLetter×List TypedLetter))
    (x : TypedLetter×List TypedLetter) (hx : x∈l) : x.2.length<(cornerInsert l).length := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    change x.2.length<((y.1::y.2)++cornerInsert l).length
    simp only [List.length_append,List.length_cons]
    rcases List.mem_cons.mp hx with rfl|hx
    · omega
    · have hh := ih hx;omega

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_RadialBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

/-- Angular integration gives the reflection-kernel formula, including the entrance r=0. -/
theorem cylindrical_integral {t r s : ℝ} (ht : 0<t) (hr : 0 ≤ r) (hs : 0≤ s) :
    2*Real.pi*s*(∫ x : ℝ in Ioo (-s) s,cylindricalDensity t r s x)=radialHeat t r s := by
  have hS : (Real.sqrt (2*Real.pi*t))^2=2*Real.pi*t := Real.sq_sqrt (by positivity)
  have hSn : Real.sqrt (2*Real.pi*t)≠0 := by positivity
  have htn : t≠0 := ht.ne'
  have hπ : Real.pi≠0 := Real.pi_ne_zero
  by_cases hr0 : r=0
  · subst r
    have he : (fun x : ℝ => cylindricalDensity t 0 s x)=
        fun _ : ℝ => Real.exp (-s^2/(2*t))/(Real.sqrt (2*Real.pi*t))^3 := by
      funext x
      simp [cylindricalDensity]
    rw [he,setIntegral_const,Real.volume_real_Ioo,max_eq_left (by linarith)]
    simp only [radialHeat,ite_true,smul_eq_mul,heat]
    have heS : (Real.sqrt (2*Real.pi*t))^3=Real.sqrt (2*Real.pi*t)*(2*Real.pi*t) := by
      calc
        _ = Real.sqrt (2*Real.pi*t)*(Real.sqrt (2*Real.pi*t))^2 := by ring
        _ = _ := by rw [hS]
    rw [heS]
    field_simp [htn,hπ,hSn]
    all_goals ring
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hk : r/t≠0 := (div_pos hrp ht).ne'
    have hi : (∫ x : ℝ in Ioo (-s) s,cylindricalDensity t r s x)=
        (t/r)*(cylindricalDensity t r s s-cylindricalDensity t r s (-s)) := by
      unfold cylindricalDensity
      have he : (fun x : ℝ => Real.exp (r*x/t))=fun x : ℝ => Real.exp ((r/t)*x) := by
        funext x
        congr 1
        ring
      rw [integral_const_mul,he,integral_exp_linear hk hs]
      rw [show (r/t)*s=r*s/t by ring,show (r/t)*(-s)=r*(-s)/t by ring]
      field_simp [htn,hr0]
    rw [hi,cylindricalDensity_endpoint ht,cylindricalDensity_neg_endpoint ht]
    simp only [radialHeat,ite_eq_right hr0,killedHeat]
    field_simp [htn,hπ,hSn]

/-- Exact radial image of the genuinely shifted three independent Gaussian densities.
The formula is a proved change of variables, not a Bessel-process assumption. -/
theorem lintegral_radial_gaussian {t r : ℝ} (ht : 0<t) (hr : 0 ≤ r)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p : ℝ×(ℝ×ℝ), ENNReal.ofReal (heat t (p.1-r)*heat t p.2.1*heat t p.2.2)*
      F (Real.sqrt (p.1^2+p.2.1^2+p.2.2^2)))=
      ∫⁻ s : ℝ in Ioi 0,ENNReal.ofReal (radialHeat t r s)*F s := by
  have hc := cylindricalDensity_continuous t r
  have hh := Radial.lintegral_cylindrical
    (fun p : ℝ×ℝ => ENNReal.ofReal (cylindricalDensity t r p.2 p.1)*F p.2)
    (hc.measurable.ennreal_ofReal.mul (hF.comp measurable_snd))
  simp only [cylindricalDensity_of_norm ht] at hh
  rw [hh,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s hs
  have hs : 0 < s := hs
  dsimp only
  have hD : Continuous (fun x : ℝ => cylindricalDensity t r s x) := by
    unfold cylindricalDensity
    fun_prop
  rw [lintegral_mul_const _ (hD.measurable.ennreal_ofReal),
    ← ofReal_integral_eq_lintegral_ofReal (hD.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      (Filter.Eventually.of_forall (fun x => cylindricalDensity_nonneg ht r s x))]
  rw [← mul_assoc,← mul_assoc,← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),cylindrical_integral ht hr hs.le]

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory WithLp
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open SimpleWalk

/-- The norm of a Gaussian step has exactly the derived radial heat-kernel law. -/
theorem lintegral_step_norm {t : ℝ} (ht : 0<t) (v : Space)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z,F ‖z‖ ∂step t v)=
      ∫⁻ s : ℝ in Ioi 0,ENNReal.ofReal (radialHeat t ‖v‖ s)*F s := by
  have hn : Measurable (fun z : Space => ‖z‖) := by fun_prop
  rw [← lintegral_map hF hn,step_norm_axis,lintegral_map hF hn,step_coordinates ht.le]
  change (∫⁻ z : Space,(F ∘ fun z : Space => ‖z‖) z ∂
    (Measure.pi (fun i : Fin 3 => gaussianReal (axis ‖v‖ i) (⟨t,ht.le⟩ : ℝ≥0))).map (toLp 2)) = _
  rw [lintegral_map (hF.comp hn) (by fun_prop)]
  let variance : ℝ≥0 := ⟨t,ht.le⟩
  change (∫⁻ x : Fin 3 → ℝ,F ‖toLp 2 x‖ ∂Measure.pi
    (fun i : Fin 3 => gaussianReal (axis ‖v‖ i) variance))=_
  have hp := coordinates_preserving (fun i : Fin 3 => gaussianReal (axis ‖v‖ i) variance)
  rw [← hp.symm.map_eq,lintegral_map (by fun_prop) coordinates.symm.measurable]
  change (∫⁻ p : ℝ×(ℝ×ℝ),F ‖toLp 2 (coordinates.symm p)‖ ∂
    (gaussianReal ‖v‖ variance).prod ((gaussianReal 0 variance).prod (gaussianReal 0 variance))) = _
  simp_rw [norm_coordinates]
  have htn : variance≠0 := by
    intro h
    have he := congrArg (fun x : ℝ≥0 => (x:ℝ)) h
    exact ht.ne' he
  rw [gaussianReal_of_var_ne_zero _ htn,gaussianReal_of_var_ne_zero _ htn]
  rw [prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
    prod_withDensity (measurable_gaussianPDF _ _) (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply]
  simp_rw [show variance=(⟨t,ht.le⟩ : ℝ≥0) from rfl,heat_gaussianPDF,sub_zero]
  have he (p : ℝ×(ℝ×ℝ)) :
      ENNReal.ofReal (heat t (p.1-‖v‖))*(ENNReal.ofReal (heat t p.2.1)*ENNReal.ofReal (heat t p.2.2))=
      ENNReal.ofReal (heat t (p.1-‖v‖)*heat t p.2.1*heat t p.2.2) := by
    rw [ENNReal.ofReal_mul (mul_nonneg (heat_pos ht _).le (heat_pos ht _).le),
      ENNReal.ofReal_mul (heat_pos ht _).le,mul_assoc]
  simp_rw [he]
  exact lintegral_radial_gaussian ht (norm_nonneg v) F hF

end FKCRT.Radial
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory WithLp
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open SimpleWalk

lemma lintegral_step_transition {t : ℝ} (ht : 0<t) (v : Space)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z,F ‖z‖ ∂step t v)=∫⁻ s,transition t ‖v‖ s*F s := by
  rw [lintegral_step_norm ht v F hF]
  simp only [transition,← indicator_mul_left]
  rw [lintegral_indicator measurableSet_Ioi]

/-- Radial integration for every finite affine Gaussian chain, without invoking
an unformalized Bessel process or its transition theorem. -/
theorem lintegral_chain (m : ℕ) (v : Space) (a t : Fin m → ℝ)
    (ht : ∀ i,0<t i) (F : (Fin m → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z,F (fun i => ‖chain v a t z i‖) ∂Measure.pi (fun _ => stdGaussian Space))=
    ∫⁻ x,F x*chainDensity ‖v‖ a t x := by
  induction m generalizing v with
  | zero =>
    have he (x : Fin 0 → ℝ) : F x=F Fin.elim0 := congrArg F (Subsingleton.elim _ _)
    simp only [he,chainDensity,mul_one]
    rw [Measure.pi_of_empty (fun _ : Fin 0 => stdGaussian Space),
      Measure.volume_pi_eq_dirac (α := fun _ : Fin 0 => ℝ)]
    simp
  | succ m ih =>
    let w : Space → Space := fun z => a 0 • v+Real.sqrt (t 0) • z
    let G : ℝ → ℝ≥0∞ := fun r => ∫⁻ x : Fin m → ℝ,
      F (Fin.cons r x)*chainDensity r (Fin.tail a) (Fin.tail t) x
    have hG : Measurable G := by
      apply Measurable.lintegral_prod_right
      exact (hF.comp (by fun_prop)).mul (measurable_chainDensity m (Fin.tail a) (Fin.tail t))
    have hz (z : Space) :
        (∫⁻ zs : Fin m → Space,F (fun i => ‖chain v a t (Fin.cons z zs) i‖)
          ∂Measure.pi (fun _ => stdGaussian Space))=G ‖w z‖ := by
      have hh := ih (w z) (Fin.tail a) (Fin.tail t) (fun i => ht i.succ)
        (fun x => F (Fin.cons ‖w z‖ x)) (hF.comp (by fun_prop))
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      funext zs
      congr 1
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hchain : Measurable (fun z => chain v a t z) :=
      ((continuous_chain (m+1) a t).comp (continuous_const.prodMk continuous_id)).measurable
    have hFn : Measurable (fun z => F (fun i => ‖chain v a t z i‖)) :=
      hF.comp (by fun_prop)
    rw [← (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => stdGaussian Space) 0).symm.map_eq]
    rw [lintegral_map hFn (by fun_prop)]
    change (∫⁻ z : Space×(Fin m → Space),F (fun i => ‖chain v a t (Fin.cons z.1 z.2) i‖)
      ∂(stdGaussian Space).prod (Measure.pi (fun _ => stdGaussian Space)))=_
    have hFn' : Measurable (fun z : Space×(Fin m → Space) =>
      F (fun i => ‖chain v a t (Fin.cons z.1 z.2) i‖)) := hFn.comp (by fun_prop)
    rw [lintegral_prod _ hFn'.aemeasurable]
    simp_rw [hz]
    have hw : Measurable w := by fun_prop
    rw [show (∫⁻ z,G ‖w z‖ ∂stdGaussian Space)=(∫⁻ z,G ‖z‖ ∂step (t 0) (a 0 • v)) by
      exact (lintegral_map (hG.comp (by fun_prop)) hw).symm,
      lintegral_step_transition (ht 0) _ G hG,norm_smul,Real.norm_eq_abs]
    have hden : Measurable (fun x => chainDensity ‖v‖ a t x) :=
      (measurable_chainDensity (m+1) a t).comp
        (show Measurable (fun x : Fin (m+1) → ℝ => (‖v‖,x)) from by fun_prop)
    conv_rhs => rw [volume_pi]
    rw [← (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => (volume : Measure ℝ)) 0).symm.map_eq]
    have hfd : Measurable (fun x : Fin (m+1) → ℝ => F x*chainDensity ‖v‖ a t x) := hF.mul hden
    rw [lintegral_map hfd (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm.measurable]
    rw [← volume_pi]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero]
    change (∫⁻ r,transition (t 0) (|a 0| *‖v‖) r*G r)=
      ∫⁻ p : ℝ×(Fin m → ℝ),F (Fin.cons p.1 p.2)*
        (transition (t 0) (|a 0| *‖v‖) p.1*chainDensity p.1 (Fin.tail a) (Fin.tail t) p.2)
        ∂volume.prod volume
    have htden : Measurable (fun p : ℝ×(Fin m → ℝ) =>
      chainDensity p.1 (Fin.tail a) (Fin.tail t) p.2) := measurable_chainDensity m _ _
    have htrans : Measurable (fun r => transition (t 0) (|a 0| * ‖v‖) r) :=
      measurable_transition.comp (show Measurable (fun r : ℝ => (t 0,|a 0| * ‖v‖,r)) from by fun_prop)
    rw [lintegral_prod _ (by fun_prop)]
    apply lintegral_congr
    intro r
    dsimp only [G]
    rw [← lintegral_const_mul _ (by fun_prop)]
    apply lintegral_congr
    intro x
    ring

end FKCRT.Radial
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_TraceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

def normalizedTrace {m : ℕ} (a R : ℕ) (d b : Fin m → ℕ) : ℝ :=
  traceKilledWeight a (R+1) (segments d b) /
    pathMass ((∑ i,d i)+R+1) (firstHit a)

end FKCRT.SimpleWalk
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_ExcursionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

def gridIndex {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ)
    (d : Path (2*n+1)) (i : Fin m) : ℕ :=
  (pathSum d (evenGrid n (u i.succ))).toNat/2

def gridSample {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ)
    (d : Path (2*n+1)) (i : Fin m) : ℝ := mesh n*(gridIndex u n d i:ℝ)

def histogramDensity {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ) :=
  Histogram.density (excursionLaw n) (gridSample u n) (mesh n)

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open TreeCoding

lemma bridgeDensity_probability {m : ℕ} (u : Fin (m+1) → unitInterval)
    (hu : StrictMono u) (h1 : ∀ i,(u i:ℝ)<1) :
    IsProbabilityMeasure (volume.withDensity (bridgeDensity u)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  have ht (i : Fin m) : 0<bridgeVariance (u i.castSucc) (u i.succ) :=
    bridgeVariance_pos (hu i.castSucc_lt_succ) (h1 _)
  have hh := lintegral_chain m (0:Space)
    (fun i => bridgeRatio (u i.castSucc) (u i.succ))
    (fun i => bridgeVariance (u i.castSucc) (u i.succ)) ht
    (fun _ => 1) measurable_const
  simpa only [lintegral_const,measure_univ,mul_one,norm_zero,one_mul,bridgeDensity] using hh.symm

end FKCRT.Radial
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
open TreeCoding

def simplePolygon {N : ℕ} (d : Path N) : C(unitInterval,ℝ) :=
  interpolation N (fun i => (pathSum d i.val:ℝ)/Real.sqrt (N:ℝ))

end FKCRT.SimpleWalk
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_BlockLaw
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Filter
open scoped BigOperators Topology
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

lemma actualBlockMass_zero_pos (P : Parameters) : 0<actualBlockMass P 0 := by
  rw [actualBlockMass_zero]
  exact div_pos zero_lt_one (emptyTotal_pos P)

end FKCRT.Inventory
end


noncomputable section
open List Filter
open scoped BigOperators Topology
namespace FKCRT.Inventory
open MapCycles Chords
attribute [local instance] Classical.propDecidable

/-- The true one-link word is a connected core, including its root seam. -/
lemma oneLink_core : CoreWord [TypedLetter.burger true,TypedLetter.order true] := by
  let v : Fin 2 → TypedLetter := ![.burger true,.order true]
  have he : stackTypedRun ((List.finRange 2).map v) []=some [] := by decide
  let M := StackMatching.ofEmpty he
  let i : Fin 2 := 0
  have hnf := M.no_fixed (List.nodup_finRange _) i (List.mem_finRange i)
  have hlt : i<M.mate i := by
    have hh := Fin.val_ne_of_ne hnf
    change (M.mate i).val≠0 at hh
    change 0<(M.mate i).val
    omega
  let r : Opener M.mate := ⟨i,hlt⟩
  refine ⟨2,v,M,by decide,r,rfl,?_⟩
  intro x
  have hx : x=r := by
    apply Subtype.ext
    apply Fin.ext
    have hh := x.property
    have hm := (M.mate x.val).isLt
    change x.val.val< (M.mate x.val).val at hh
    change x.val.val=0
    omega
  subst x
  exact SimpleGraph.Reachable.refl r

lemma coreCoefficientReal_one_pos {t : ℝ} (ht : 0<t) : 0 < coreCoefficientReal t 1 := by
  let w := [TypedLetter.burger true,TypedLetter.order true]
  have hw : w∈(typedEmptyWords (2*1)).filter CoreWord :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_wordsOfLength.mpr rfl,
      coreWord_empty _ oneLink_core⟩,oneLink_core⟩
  have h := Finset.single_le_sum (s := (typedEmptyWords (2*1)).filter CoreWord)
    (f := fun w => t^flexibleCount w []) (fun _ _ => pow_nonneg ht.le _) hw
  exact (pow_pos ht _).trans_le h

lemma actualBlockMass_one_pos (P : Parameters) : 0<actualBlockMass P 1 := by
  apply div_pos _ (emptyTotal_pos P)
  apply mul_pos
  · change 0<(if (1:ℕ)=0 then 1 else 0)+coreCoefficientReal (flexParameter P) 1
    simpa using coreCoefficientReal_one_pos (flexParameter_pos P)
  · exact pow_pos (mul_pos (radiusParameter_pos P) (sq_pos_of_pos (emptyTotal_pos P))) _

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PlanarActivity
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma spanningGraph_insert (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (e : Orbit a) :
    spanningGraph a s ((insert e A : Finset (Orbit a)) : Set (Orbit a)) =
      spanningGraph a s (A : Set (Orbit a)) ⊔ SimpleGraph.edge (orbit s e.out) (orbit s (a e.out)) := by
  ext v w
  change (v≠w ∧ ((∃ d,orbit a d∈insert e A ∧ orbit s d=v ∧ orbit s (a d)=w) ∨
    (∃ d,orbit a d∈insert e A ∧ orbit s d=w ∧ orbit s (a d)=v))) ↔ _
  constructor
  · rintro ⟨hne,hh|hh⟩
    · obtain ⟨d,hd,hv,hw⟩ := hh
      rcases Finset.mem_insert.mp hd with hd | hd
      · right
        apply (SimpleGraph.edge_adj _ _ _ _).mpr
        refine ⟨?_,hne⟩
        rcases (MapFinite.mk_eq_iff_involution a ha d e).mp hd with rfl | rfl
        · exact Or.inl ⟨hv.symm,hw.symm⟩
        · rw [ha] at hw
          exact Or.inr ⟨hv.symm,hw.symm⟩
      · exact Or.inl ⟨hne,Or.inl ⟨d,hd,hv,hw⟩⟩
    · obtain ⟨d,hd,hw,hv⟩ := hh
      rcases Finset.mem_insert.mp hd with hd | hd
      · right
        apply (SimpleGraph.edge_adj _ _ _ _).mpr
        refine ⟨?_,hne⟩
        rcases (MapFinite.mk_eq_iff_involution a ha d e).mp hd with rfl | rfl
        · exact Or.inr ⟨hv.symm,hw.symm⟩
        · rw [ha] at hv
          exact Or.inl ⟨hv.symm,hw.symm⟩
      · exact Or.inl ⟨hne,Or.inr ⟨d,hd,hw,hv⟩⟩
  · rintro (⟨hne,hh|hh⟩|hh)
    · obtain ⟨d,hd,hv,hw⟩ := hh
      exact ⟨hne,Or.inl ⟨d,Finset.mem_insert_of_mem hd,hv,hw⟩⟩
    · obtain ⟨d,hd,hw,hv⟩ := hh
      exact ⟨hne,Or.inr ⟨d,Finset.mem_insert_of_mem hd,hw,hv⟩⟩
    · rcases (SimpleGraph.edge_adj _ _ _ _).mp hh with ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,hne⟩
      · refine ⟨hne,Or.inl ⟨e.out,?_,rfl,rfl⟩⟩
        rw [show orbit a e.out=e from Quotient.out_eq e]
        exact Finset.mem_insert_self _ _
      · refine ⟨hne,Or.inr ⟨e.out,?_,rfl,rfl⟩⟩
        rw [show orbit a e.out=e from Quotient.out_eq e]
        exact Finset.mem_insert_self _ _

lemma components_insert_of_not_reachable (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (e : Orbit a)
    (h : ¬(spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    submapComponents a s (insert e A)+1=submapComponents a s A := by
  simp only [submapComponents,spanningGraph_insert a s ha]
  exact GraphMerge.card_sup_edge_of_not_reachable _ h

/-- The orientable genus defect, on all spanning ribbon subgraphs. -/
def submapDefect (a s : Perm (Dart n)) (ha : Function.Involutive a) (A : Finset (Orbit a)) : ℤ :=
  (A.card:ℤ) - Nat.card (Orbit s) + 2*(submapComponents a s A:ℤ) -
    Nat.card (Orbit (s*partialReversal a ha A))

lemma submapComponents_empty (a s : Perm (Dart n)) :
    submapComponents a s ∅=Nat.card (Orbit s) := by
  have hg : spanningGraph a s (∅ : Finset (Orbit a))=⊥ := by
    ext v w
    simp [spanningGraph]
  rw [submapComponents,hg]
  apply Nat.card_congr
  exact GraphMerge.componentEquiv _ id (Function.surjective_id) (by simp)

end FKCRT
end


noncomputable section
open scoped BigOperators
namespace FKCRT
variable {n : ℕ}

/-- The source's map marginal, with its common factor sqrt(q) removed. -/
def loopPolynomial (t : ℝ) (M : RootedMap n) : ℝ :=
  ∑ A : Finset (Edge M), t ^ ((Nat.card (Orbit (rotation M *
    partialReversal (reversal M) M.out.property.1 A)) : ℤ)-1)

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma Multiforest.mono {a s : Perm (Dart n)} {A B : Finset (Orbit a)}
    (h : Multiforest a s B) (hab : A⊆B) : Multiforest a s A :=
  ⟨h.1.anti (spanningGraph_mono a s hab),fun e he => h.2.1 e (hab he),h.2.2.mono hab⟩

lemma multiforest_of_tour (M : LabelledMap n) (A : Finset (Orbit M.val.1))
    (h : ∀ d e,(M.val.2*partialReversal M.val.1 M.property.1 A).SameCycle d e) :
    Multiforest M.val.1 M.val.2 A := by
  have ⟨ht,hc⟩ := tour_spanningTree M A h
  obtain ⟨he,hi⟩ := spanningGraph_edgeSet_of_card M.val.1 M.val.2 M.property.1 A hc
  refine ⟨ht.isAcyclic,?_,hi⟩
  intro e heA
  have he' : edgeEnds M.val.1 M.val.2 e∈(spanningGraph M.val.1 M.val.2 (A : Set _)).edgeSet :=
    he.symm ▸ ⟨e,heA,rfl⟩
  exact ((SimpleGraph.mem_edgeSet _).mp he').ne

lemma Multiforest.insert_not_reachable {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {A : Finset (Orbit a)} {e : Orbit a} (he : e∉A) (h : Multiforest a s (insert e A)) :
    ¬ (spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)) := by
  have hedge : (spanningGraph a s ((insert e A : Finset (Orbit a)) : Set (Orbit a))).Adj
      (orbit s e.out) (orbit s (a e.out)) := by
    refine ⟨h.2.1 e (Finset.mem_insert_self _ _),Or.inl ⟨e.out,?_,rfl,rfl⟩⟩
    change orbit a e.out∈insert e A
    rw [show orbit a e.out=e from Quotient.out_eq e]
    exact Finset.mem_insert_self _ _
  have hb := SimpleGraph.isAcyclic_iff_forall_isBridge.mp h.1 ((SimpleGraph.mem_edgeSet _).mpr hedge)
  intro hh
  apply (SimpleGraph.isBridge_iff.mp hb)
  exact hh.mono (spanningGraph_delete_edge_le a s ha e he h.2.2)

/-- The usual forest rank identity includes isolated vertices and does not
silently identify parallel map edges. -/
theorem Multiforest.components_card {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {A : Finset (Orbit a)} (h : Multiforest a s A) :
    submapComponents a s A+A.card=Nat.card (Orbit s) := by
  induction A using Finset.induction_on with
  | empty => simp [submapComponents_empty]
  | @insert e A he ih =>
    have hA := h.mono (Finset.subset_insert e A)
    have hi := ih hA
    have hk := components_insert_of_not_reachable a s ha A e (h.insert_not_reachable ha he)
    rw [Finset.card_insert_of_notMem he]
    omega

/-- Every component of a forest has one boundary cycle. Converse to the
always-valid implication from a boundary cycle to graph reachability. -/
theorem Multiforest.sameCycle_iff_reachable {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {A : Finset (Orbit a)} (h : Multiforest a s A) (d e : Dart n) :
    (s*partialReversal a ha A).SameCycle d e ↔
      (spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s d) (orbit s e) := by
  let G := spanningGraph a s (A : Set (Orbit a))
  let p := s*partialReversal a ha A
  let f : Orbit p → G.ConnectedComponent := Quotient.lift
    (fun x => G.connectedComponentMk (orbit s x)) (by
      intro x y hxy
      exact SimpleGraph.ConnectedComponent.sound (spanningGraph_reachable_of_sameCycle a s ha A hxy))
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨v,rfl⟩ := Quot.mk_surjective c
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective v
    exact ⟨orbit p x,rfl⟩
  have hc : Nat.card (Orbit p)=Nat.card G.ConnectedComponent := by
    have h1 := forest_tour_cycle_card a s ha A h.1 h.2.1 h.2.2
    have h2 := h.components_card ha
    change Nat.card (Orbit p)+A.card=Nat.card (Orbit s) at h1
    change Nat.card G.ConnectedComponent+A.card=Nat.card (Orbit s) at h2
    omega
  have hi := ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hf,hc⟩).1
  refine ⟨spanningGraph_reachable_of_sameCycle a s ha A,fun hr => ?_⟩
  exact Quotient.exact (hi (show f (orbit p d)=f (orbit p e) from
    SimpleGraph.ConnectedComponent.sound hr))

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

/-- Number of forced bridge/loop decisions along the branch belonging to T.
The next edge may depend on the entire previous partial branch, but not T. -/
def explorationActivity (a s : Perm (Dart n)) (select : EdgeSelector a)
    (C R T : Finset (Orbit a)) : ℕ → ℕ
  | 0 => 0
  | k+1 => if hR : R.Nonempty then
      let e := (select C R hR).val
      let R' := R.erase e
      if (spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)) then
        1+explorationActivity a s select C R' T k
      else if ¬(spanningGraph a s ((C∪R' : Finset (Orbit a)) : Set (Orbit a))).Reachable
          (orbit s e.out) (orbit s (a e.out)) then
        1+explorationActivity a s select (insert e C) R' T k
      else explorationActivity a s select (if e∈T then insert e C else C) R' T k
    else 0

end FKCRT
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_TourActivity
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Equiv Equiv.Perm
namespace FKCRT
variable {n : ℕ}

lemma tourNumbering_successor (p : Perm (Dart n)) (h : ∀ d e,p.SameCycle d e)
    (i : Dart n) :
    tourNumbering p h (finRotate (2*(n+1)) i) = p (tourNumbering p h i) := by
  simp only [tourNumbering_apply]
  rw [← mul_apply p (p^i.val),← pow_succ']
  apply (oneCycle_isCycleOn p h).pow_apply_eq_pow_apply (Finset.mem_univ (0 : Dart n)) |>.mpr
  simp only [Finset.card_univ,Fintype.card_fin] at ⊢
  change (finRotate (2*(n+1)) i).val % (2*(n+1)) = (i.val+1) % (2*(n+1))
  have hi : (finRotate (2*(n+1)) i).val = (i.val+1) % (2*(n+1)) := by
    rw [finRotate_apply,Fin.val_add]
    congr 1
  rw [hi,Nat.mod_mod]

/-- The root-preserving numbering is uniquely determined by the tour. -/
lemma tourNumbering_unique (p : Perm (Dart n)) (h : ∀ d e,p.SameCycle d e)
    (r : Perm (Dart n)) (hr : r 0=0)
    (hp : ∀ i,r (finRotate (2*(n+1)) i)=p (r i)) : r=tourNumbering p h := by
  apply Equiv.ext
  intro i
  have hrot : ∀ (k : ℕ) (hk : k<2*(n+1)), ((finRotate (2*(n+1)))^k) 0 = (⟨k,hk⟩ : Dart n) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ',mul_apply,ih (by omega),finRotate_apply]
      apply Fin.ext
      simp only [Fin.val_add]
      simp [Nat.mod_eq_of_lt (by omega : k+1<2*(n+1)),Nat.mod_eq_of_lt (by omega : 1<2*(n+1))]
  have he (k : ℕ) : r (((finRotate (2*(n+1)))^k) 0) = (p^k) 0 := by
    induction k with
    | zero => exact hr
    | succ k ih => rw [pow_succ',mul_apply,hp,ih,pow_succ',mul_apply]
  simpa only [hrot i.val i.isLt,tourNumbering_apply] using he i.val

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

/-- Source exploration: start at the root and follow decided tree/non-tree
rules until the first as-yet undecided edge. The fallback is only for states
without a spanning-tree completion; it is never used on a valid branch. -/
def tourSelector (a s : Perm (Dart n)) (ha : Function.Involutive a) : EdgeSelector a := fun C R hR =>
  if h : ∃ k : ℕ,orbit a (((s*partialReversal a ha C)^k) 0)∈R then
    ⟨orbit a (((s*partialReversal a ha C)^(Nat.find h)) 0),Nat.find_spec h⟩
  else ⟨hR.choose,hR.choose_spec⟩

lemma treeExtension_tour (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R T : Finset (Orbit a)) (h : T∈treeExtensions a s C R) :
    ∀ d e,(s*partialReversal a ha T).SameCycle d e := by
  have hh := (mem_treeExtensions a s C R T).mp h
  intro d e
  exact (hh.2.2.1.sameCycle_iff_reachable ha d e).mpr (hh.2.2.2.preconnected _ _)

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

/-- First occurrence of an edge in a fixed rooted one-cycle tour. -/
def edgeFirst (a p : Perm (Dart n)) (hp : ∀ d e,p.SameCycle d e) (e : Orbit a) : ℕ :=
  min ((tourNumbering p hp).symm e.out).val ((tourNumbering p hp).symm (a e.out)).val

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

def OrderedActive (a s : Perm (Dart n)) (T : Finset (Orbit a))
    (rank : Orbit a→ℕ) (e : Orbit a) : Prop :=
  ∀ f,rank e < rank f → ¬FundamentalCross a s T e f

end FKCRT
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CanonicalBijection
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
open MapCycles Chords
variable {n : ℕ}

lemma orbit_opener_injective (a : Perm (Dart n)) (ha : Function.Involutive a) :
    Function.Injective (fun x : Opener a => orbit a x.val) := by
  intro x y hh
  rcases (MapFinite.sameCycle_involution a ha x.val y.val).mp (Quotient.exact hh) with hh|hh
  · exact Subtype.ext hh.symm
  · have hx := x.property
    have hy := y.property
    rw [hh,ha] at hy
    exact False.elim ((not_lt_of_ge hx.le) hy)

end FKCRT
end


noncomputable section
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma relabelPerm_apply (r p : Perm (Dart n)) (d : Dart n) :
    relabelPerm r p d=r.symm (p (r d)) := rfl

lemma relabelPerm_mul (r p q : Perm (Dart n)) :
    relabelPerm r (p*q)=relabelPerm r p*relabelPerm r q := by unfold relabelPerm; group

lemma relabelPerm_involutive (r a : Perm (Dart n)) (ha : Function.Involutive a) :
    Function.Involutive (relabelPerm r a) := by
  intro d
  simp only [relabelPerm_apply,Equiv.apply_symm_apply]
  rw [ha,Equiv.symm_apply_apply]

lemma relabelPerm_no_fixed (r a : Perm (Dart n)) (hf : ∀ d,a d≠d) :
    ∀ d,relabelPerm r a d≠d := by
  intro d h
  have hh := congrArg r h
  exact hf (r d) (by simpa only [relabelPerm_apply,Equiv.apply_symm_apply] using hh)

lemma card_orbit_relabel (r p : Perm (Dart n)) :
    Nat.card (Orbit (relabelPerm r p))=Nat.card (Orbit p) := Nat.card_congr (relabelOrbit r p)

lemma partialReversal_relabel (r a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) :
    partialReversal (relabelPerm r a) (relabelPerm_involutive r a ha) (relabelEdges r a A)=
      relabelPerm r (partialReversal a ha A) := by
  apply Equiv.ext
  intro d
  simp only [partialReversal_apply,mem_relabelEdges,relabelOrbit_apply,relabelPerm_apply]
  split_ifs <;> simp

lemma tourNumbering_relabel (p : Perm (Dart n)) (hp : ∀ d e,p.SameCycle d e) :
    relabelPerm (tourNumbering p hp) p=finRotate (2*(n+1)) := by
  apply Equiv.ext
  intro i
  apply (tourNumbering p hp).injective
  simpa only [relabelPerm_apply,Equiv.apply_symm_apply] using (tourNumbering_successor p hp i).symm

end FKCRT
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
open MapCycles Chords Inventory
variable {n : ℕ}

lemma opener_orbit_surjective (a : Perm (Dart n)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) : Function.Surjective (fun x : Opener a => orbit a x.val) := by
  intro e
  by_cases h : e.out < a e.out
  · exact ⟨⟨e.out,h⟩,Quotient.out_eq e⟩
  · refine ⟨⟨a e.out,?_⟩,?_⟩
    · rw [ha]
      exact lt_of_le_of_ne (le_of_not_gt h) (hf e.out)
    · change orbit a (a e.out)=e
      rw [orbit_perm]
      exact Quotient.out_eq e

def openerOrbitEquiv (a : Perm (Dart n)) (ha : Function.Involutive a) (hf : ∀ d,a d≠d) :
    Opener a ≃ Orbit a := Equiv.ofBijective _ ⟨orbit_opener_injective a ha,opener_orbit_surjective a ha hf⟩

end FKCRT
end


noncomputable section
open List Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
open MapCycles Inventory
variable {n : ℕ}

/-- Exact finite bimapping of the genuine canonical rooted planar tree maps
and successful typed words; no symmetry divisor and no assumed inverse. -/
def canonicalWordEquiv (n : ℕ) : CanonicalTreeMap n ≃ SuccessfulWord n :=
  Equiv.ofBijective CanonicalTreeMap.word
    ⟨CanonicalTreeMap.word_injective,CanonicalTreeMap.word_surjective⟩

end FKCRT
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SpineMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

def CriticalEvenOffspring.spineLaw (p : CriticalEvenOffspring) : Measure (ℕ×ℕ) :=
  p.streamLaw.map ladderType

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SpineBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
namespace PlaneTree

def toCode (t : PlaneTree) : Code t.degrees.length :=
  ⟨fun i => ⟨t.degrees[i],t.degree_lt_length (List.getElem_mem _)⟩,by
    rw [isTreeCode_iff]
    convert t.degrees_excursion using 1
    all_goals try with_reducible_and_instances rfl
    unfold degreeList incrementWord
    exact List.ofFn_getElem_eq_map t.degrees (fun k : ℕ => (k:ℤ)-1)⟩

lemma toCode_degrees_ofFn (t : PlaneTree) :
    List.ofFn (fun i => ((t.toCode.val i).val))=t.degrees := by
  exact List.ofFn_getElem

def ofCode {N : ℕ} (d : Code N) : PlaneTree :=
  Classical.choose (exists_tree_of_excursion (l := List.ofFn (fun i => (d.val i).val))
    (by rw [incrementWord_ofFn]; exact (isTreeCode_iff _).mp d.property))

lemma ofCode_degrees {N : ℕ} (d : Code N) :
    (ofCode d).degrees=List.ofFn (fun i => (d.val i).val) :=
  Classical.choose_spec (exists_tree_of_excursion (l := List.ofFn (fun i => (d.val i).val))
    (by rw [incrementWord_ofFn]; exact (isTreeCode_iff _).mp d.property))

lemma ofCode_size {N : ℕ} (d : Code N) : (ofCode d).degrees.length=N := by
  rw [ofCode_degrees,List.length_ofFn]

lemma ofCode_injective (N : ℕ) : Function.Injective (@ofCode N) := by
  intro d e h
  apply Subtype.ext
  funext i
  apply Fin.ext
  have he := congrArg degrees h
  rw [ofCode_degrees,ofCode_degrees] at he
  have he' := congrArg (fun l : List ℕ => l[i.val]?) he
  simpa using he'

lemma ofCode_toCode (t : PlaneTree) : ofCode t.toCode=t := by
  apply degrees_injective
  rw [ofCode_degrees,toCode_degrees_ofFn]

def sizedEquiv (N : ℕ) : Code N ≃ Sized N := Equiv.ofBijective
  (fun d => ⟨ofCode d,ofCode_size d⟩) ⟨fun d e h => ofCode_injective N (congrArg Subtype.val h),by
    rintro ⟨t,ht⟩
    subst N
    exact ⟨t.toCode,Subtype.ext (ofCode_toCode t)⟩⟩

def mirrored {N : ℕ} (d : Code N) : Code N :=
  (sizedEquiv N).symm ⟨(ofCode d).mirror,(ofCode d).mirror_size.trans (ofCode_size d)⟩

lemma ofCode_mirrored {N : ℕ} (d : Code N) : ofCode (mirrored d)=(ofCode d).mirror := by
  exact congrArg Subtype.val ((sizedEquiv N).apply_symm_apply _)

lemma mirrored_involutive (N : ℕ) : Function.Involutive (@mirrored N) := by
  intro d
  apply ofCode_injective N
  rw [ofCode_mirrored,ofCode_mirrored,mirror_mirror]

def mirrorEquiv (N : ℕ) : Equiv.Perm (Code N) := (mirrored_involutive N).toPerm

end PlaneTree
end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MarkedSpines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

variable {A : Type*} [MeasurableSpace A]

def codeMarkLaw (κ : ℕ → Measure A) {N : ℕ} (d : Code N) : Measure (Fin N → A) :=
  Measure.pi (fun i => κ (d.val i).val)

instance codeMarkLaw_probability (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    {N : ℕ} (d : Code N) : IsProbabilityMeasure (codeMarkLaw κ d) := by
  unfold codeMarkLaw; infer_instance

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CoreMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace FKCRT.Inventory
open MapCycles PermutationWedge TreeCoding
attribute [local instance] Classical.propDecidable

/-- Spine records index the chosen child from the right. Impossible arities
and slot labels are totalized by zero and never sampled by the actual law. -/
def coreIncrement (z : ℕ×ℕ) (a : CoreLabel) : ℝ :=
  match a with
  | none => 0
  | some c => if h : c.val.length=z.1 ∧ z.2<z.1 then
      (c.increment ⟨z.1-1-z.2,by omega⟩:ℝ) else 0

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open MapCycles PermutationWedge TreeCoding
attribute [local instance] Classical.propDecidable

abbrev oneLinkCore : Core := ⟨[.burger true,.order true],oneLink_core⟩

def oneLinkMatching : StackMatching oneLinkCore.val.get (List.finRange oneLinkCore.val.length) where
  first := [(0,1)]
  second := []
  first_arches := Arches.pair 0 1 Arches.nil Arches.nil
  second_arches := Arches.empty _
  covers := by decide
  first_types := by simp [oneLinkCore]
  second_types := by simp

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_NodeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace FKCRT.Inventory
open TreeCoding

def labelProfileSum (b : (ℕ×ℕ) → CoreLabel → ℝ) (l : List CoreLabel) : ℝ :=
  ∑ r ∈ weakRecords (integerSum (listStream (l.map CoreLabel.arity).reverse)) l.length,
    b (recordTypeAt (listStream (l.map CoreLabel.arity).reverse) r) (l.reverse[r-1]?.getD none)

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_RootedLaw
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

def spanningGraphRelabel (r a s : Perm (Dart n)) (A : Set (Orbit a)) :
    spanningGraph (relabelPerm r a) (relabelPerm r s) ((relabelOrbit r a) ⁻¹' A) ≃g
      spanningGraph a s A where
  toEquiv := relabelOrbit r s
  map_rel_iff' := by
    intro v w
    change (_≠_ ∧ _) ↔ (_≠_ ∧ _)
    constructor
    · rintro ⟨hne,(⟨d,hd,hv,hw⟩|⟨d,hd,hw,hv⟩)⟩
      · refine ⟨fun h => hne (by rw [h]),Or.inl ⟨r.symm d,?_,?_,?_⟩⟩
        · simpa using hd
        · apply (relabelOrbit r s).injective
          simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using hv
        · apply (relabelOrbit r s).injective
          simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using hw
      · refine ⟨fun h => hne (by rw [h]),Or.inr ⟨r.symm d,?_,?_,?_⟩⟩
        · simpa using hd
        · apply (relabelOrbit r s).injective
          simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using hw
        · apply (relabelOrbit r s).injective
          simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using hv
    · rintro ⟨hne,(⟨d,hd,hv,hw⟩|⟨d,hd,hw,hv⟩)⟩
      · refine ⟨fun h => hne ((relabelOrbit r s).injective h),Or.inl ⟨r d,hd,?_,?_⟩⟩
        · simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using congrArg (relabelOrbit r s) hv
        · simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using congrArg (relabelOrbit r s) hw
      · refine ⟨fun h => hne ((relabelOrbit r s).injective h),Or.inr ⟨r d,hd,?_,?_⟩⟩
        · simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using congrArg (relabelOrbit r s) hw
        · simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using congrArg (relabelOrbit r s) hv

lemma mapConditions_relabel (M : LabelledMap n) (r : Perm (Dart n)) :
    MapConditions (relabelPerm r M.val.1,relabelPerm r M.val.2) := by
  refine ⟨relabelPerm_involutive r _ M.property.1,relabelPerm_no_fixed r _ M.property.2.1,?_,?_⟩
  · have hi := spanningGraphRelabel r M.val.1 M.val.2 Set.univ
    have hc := hi.symm.connected_iff.mp M.property.2.2.1
    simpa using hc
  · change Nat.card (Orbit (relabelPerm r M.val.2))+
        Nat.card (Orbit (relabelPerm r M.val.2*relabelPerm r M.val.1))=n+3
    rw [← relabelPerm_mul,card_orbit_relabel,card_orbit_relabel]
    exact M.property.2.2.2

def relabelMap (M : LabelledMap n) (r : Perm (Dart n)) : LabelledMap n :=
  ⟨(relabelPerm r M.val.1,relabelPerm r M.val.2),mapConditions_relabel M r⟩

lemma relabelMap_iso (M : LabelledMap n) (r : Perm (Dart n)) (hr : r 0=0) :
    MapIso (relabelMap M r) M := by
  refine ⟨r,hr,?_,?_⟩ <;> intro d <;>
    simp only [relabelMap,relabelPerm_apply,Equiv.apply_symm_apply]

/-- Actual tree tours put every map/tree pair into the rooted normal form. -/
def canonicalizeTree (M : LabelledMap n) (T : Finset (Orbit M.val.1))
    (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ) : CanonicalTreeMap n := by
  let t := M.val.2*partialReversal M.val.1 M.property.1 T
  have ht := treeExtension_tour M.val.1 M.val.2 M.property.1 ∅ Finset.univ T hT
  let r := tourNumbering t ht
  refine ⟨relabelPerm r M.val.1,relabelPerm r M.val.2,relabelEdges r M.val.1 T,
    mapConditions_relabel M r,?_⟩
  rw [partialReversal_relabel r M.val.1 M.property.1 T,← relabelPerm_mul,
    tourNumbering_relabel,formPerm_finRange_eq_rotate]

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma partialReversal_intertwine (a b r : Perm (Dart n))
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    (hh : ∀ d,b (r d)=r (a d)) (A : Finset (Orbit a)) (B : Finset (Orbit b))
    (hAB : ∀ d,orbit a d∈A ↔ orbit b (r d)∈B) (d : Dart n) :
    partialReversal b hb B (r d)=r (partialReversal a ha A d) := by
  simp only [partialReversal_apply]
  by_cases hd : orbit a d∈A
  · rw [ite_eq_left hd,ite_eq_left ((hAB d).mp hd),hh]
  · rw [ite_eq_right hd,ite_eq_right (fun h => hd ((hAB d).mpr h))]

lemma treeExtension_of_tour (M : LabelledMap n) (A : Finset (Orbit M.val.1))
    (h : ∀ d e,(M.val.2*partialReversal M.val.1 M.property.1 A).SameCycle d e) :
    A∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ := by
  apply (mem_treeExtensions ..).mpr
  exact ⟨Finset.empty_subset _,by simp,multiforest_of_tour M A h,
    spanningGraph_connected_of_tour M.val.1 M.val.2 M.property.1 A h⟩

/-- Normalization respects a literal rooted map/tree isomorphism. The root
condition removes the cyclic seam ambiguity, rather than dividing by it. -/
lemma canonicalizeTree_of_iso (M : LabelledMap n) (T : Finset (Orbit M.val.1))
    (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ)
    (X : CanonicalTreeMap n) (r : Perm (Dart n)) (hr : r 0=0)
    (ha : ∀ d,M.val.1 (r d)=r (X.a d)) (hs : ∀ d,M.val.2 (r d)=r (X.s d))
    (hA : ∀ d,orbit X.a d∈X.A ↔ orbit M.val.1 (r d)∈T) :
    canonicalizeTree M T hT=X := by
  let t := M.val.2*partialReversal M.val.1 M.property.1 T
  have ht := treeExtension_tour M.val.1 M.val.2 M.property.1 ∅ Finset.univ T hT
  have hp : ∀ d,t (r d)=r ((X.s*partialReversal X.a X.valid.1 X.A) d) := by
    intro d
    change M.val.2 (partialReversal M.val.1 M.property.1 T (r d))=_
    rw [partialReversal_intertwine X.a M.val.1 r X.valid.1 M.property.1 ha X.A T hA,hs]
    rfl
  have he : r=tourNumbering t ht := by
    apply tourNumbering_unique t ht r hr
    intro i
    rw [hp,X.tour,formPerm_finRange_eq_rotate]
  have hea : relabelPerm r M.val.1=X.a := by
    apply Equiv.ext
    intro d
    simp only [relabelPerm_apply,ha,Equiv.symm_apply_apply]
  have hes : relabelPerm r M.val.2=X.s := by
    apply Equiv.ext
    intro d
    simp only [relabelPerm_apply,hs,Equiv.symm_apply_apply]
  subst r
  cases X with
  | mk a s A hv htX =>
    dsimp only at hea hes hA
    unfold canonicalizeTree
    dsimp only
    cases hea
    cases hes
    congr 1
    apply Finset.ext
    intro e
    induction e using Quotient.inductionOn with
    | _ d =>
      change orbit (relabelPerm (tourNumbering t ht) M.val.1) d∈relabelEdges (tourNumbering t ht) M.val.1 T ↔ orbit (relabelPerm (tourNumbering t ht) M.val.1) d∈A
      rw [mem_relabelEdges,relabelOrbit_apply]
      exact (hA d).symm

/-- Each rooted isomorphism class has its actual spanning trees as the fibre
of the canonical tree representation (existence half). -/
lemma canonical_root_fiber_surjective (M : LabelledMap n) (X : CanonicalTreeMap n)
    (h : MapIso X.toMap M) :
    ∃ (T : Finset (Orbit M.val.1)) (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ),
      canonicalizeTree M T hT=X := by
  obtain ⟨r,hr,ha,hs⟩ := h
  let e := isoOrbit X.a M.val.1 r ha
  let T := X.A.map e.toEmbedding
  have hA (d : Dart n) : orbit X.a d∈X.A ↔ orbit M.val.1 (r d)∈T := by
    change _ ↔ e (orbit X.a d)∈X.A.map e.toEmbedding
    simp
  have hp (d : Dart n) : (M.val.2*partialReversal M.val.1 M.property.1 T) (r d)=
      r ((X.s*partialReversal X.a X.valid.1 X.A) d) := by
    simp only [mul_apply,partialReversal_intertwine X.a M.val.1 r X.valid.1 M.property.1 ha X.A T hA,hs]
    rfl
  have ht : ∀ d e,(M.val.2*partialReversal M.val.1 M.property.1 T).SameCycle d e := by
    intro d f
    simpa using (sameCycle_intertwine _ _ r hp (r.symm d) (r.symm f)).mp
      (X.tour_connected (r.symm d) (r.symm f))
  have hT := treeExtension_of_tour M T ht
  exact ⟨T,hT,canonicalizeTree_of_iso M T hT X r hr ha hs hA⟩

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma canonicalizeTree_iso (M : LabelledMap n) (T : Finset (Orbit M.val.1))
    (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ) :
    MapIso (canonicalizeTree M T hT).toMap M := by
  apply relabelMap_iso M _ (tourNumbering_zero _ _)

lemma canonicalizeTree_class (M : RootedMap n) (T : Finset (Edge M))
    (hT : T∈treeExtensions (reversal M) (rotation M) ∅ Finset.univ) :
    (Quotient.mk _ (canonicalizeTree M.out T hT).toMap : RootedMap n)=M := by
  calc
    _=Quotient.mk _ M.out := Quotient.sound (Relation.EqvGen.rel _ _ (canonicalizeTree_iso M.out T hT))
    _=M := Quotient.out_eq M

lemma canonicalizeTree_mem (M : LabelledMap n) (T : Finset (Orbit M.val.1))
    (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ) (d : Dart n) :
    orbit (canonicalizeTree M T hT).a d∈(canonicalizeTree M T hT).A ↔
      orbit M.val.1 (tourNumbering (M.val.2*partialReversal M.val.1 M.property.1 T)
        (treeExtension_tour _ _ _ _ _ _ hT) d)∈T := by
  exact mem_relabelEdges _ _ _ _

lemma canonicalizeTree_injective (M : LabelledMap n)
    {T U : Finset (Orbit M.val.1)}
    (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ)
    (hU : U∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ)
    (hh : canonicalizeTree M T hT=canonicalizeTree M U hU) : T=U := by
  let X := canonicalizeTree M T hT
  let Y := canonicalizeTree M U hU
  let r := tourNumbering (M.val.2*partialReversal M.val.1 M.property.1 T)
    (treeExtension_tour _ _ _ _ _ _ hT)
  let s := tourNumbering (M.val.2*partialReversal M.val.1 M.property.1 U)
    (treeExtension_tour _ _ _ _ _ _ hU)
  have hr : r 0=0 := tourNumbering_zero _ _
  have hs : s 0=0 := tourNumbering_zero _ _
  have hra (d) : M.val.1 (r d)=r (X.a d) := by
    change _=r (relabelPerm r M.val.1 d)
    simp only [relabelPerm_apply,Equiv.apply_symm_apply]
  have hrs (d) : M.val.2 (r d)=r (X.s d) := by
    change _=r (relabelPerm r M.val.2 d)
    simp only [relabelPerm_apply,Equiv.apply_symm_apply]
  have hsa (d) : M.val.1 (s d)=s (X.a d) := by
    change _=s ((canonicalizeTree M T hT).a d)
    rw [hh]
    change _=s (relabelPerm s M.val.1 d)
    simp only [relabelPerm_apply,Equiv.apply_symm_apply]
  have hss (d) : M.val.2 (s d)=s (X.s d) := by
    change _=s ((canonicalizeTree M T hT).s d)
    rw [hh]
    change _=s (relabelPerm s M.val.2 d)
    simp only [relabelPerm_apply,Equiv.apply_symm_apply]
  have hrs' : r=s := root_isomorphism_unique (M:=X.toMap) (N:=M) hr hra hrs hs hsa hss
  apply Finset.ext
  intro e
  induction e using Quotient.inductionOn with
  | _ d =>
    have hm := congrArg (fun W : CanonicalTreeMap n => orbit W.a (r.symm d)∈W.A) hh
    have hm' : (orbit M.val.1 (r (r.symm d))∈T) ↔ (orbit M.val.1 (s (r.symm d))∈U) :=
      (canonicalizeTree_mem M T hT _).symm.trans ((Iff.of_eq hm).trans (canonicalizeTree_mem M U hU _))
    rw [← hrs'] at hm'
    change orbit M.val.1 d∈T ↔ orbit M.val.1 d∈U
    simpa only [Equiv.apply_symm_apply] using hm'

abbrev RootedSpanningTree (n : ℕ) :=
  Σ M : RootedMap n,{T : Finset (Edge M) // T∈treeExtensions (reversal M) (rotation M) ∅ Finset.univ}

def rootedTreeNormal (x : RootedSpanningTree n) : CanonicalTreeMap n :=
  canonicalizeTree x.1.out x.2.val x.2.property

lemma rootedTreeNormal_bijective : Function.Bijective (@rootedTreeNormal n) := by
  constructor
  · intro x y h
    have hM : x.1=y.1 := (canonicalizeTree_class x.1 x.2.val x.2.property).symm.trans
      ((congrArg (fun W => (Quotient.mk _ W.toMap : RootedMap n)) h).trans
        (canonicalizeTree_class y.1 y.2.val y.2.property))
    cases x with
    | mk M T =>
      cases y with
      | mk N U =>
        dsimp only at hM
        subst N
        have hh := canonicalizeTree_injective M.out T.property U.property h
        have he : T=U := Subtype.ext hh
        subst U
        rfl
  · intro X
    let M : RootedMap n := Quotient.mk _ X.toMap
    have hi : MapIso X.toMap M.out := by
      apply mapIso_eqvGen.mp
      exact @Quotient.exact _ (Relation.EqvGen.setoid (@MapIso n)) X.toMap M.out (Quotient.out_eq M).symm
    obtain ⟨T,hT,hh⟩ := canonical_root_fiber_surjective M.out X hi
    exact ⟨⟨M,⟨T,hT⟩⟩,hh⟩

/-- Actual root-isomorphism classes with actual spanning trees, not labelled
objects divided by an unproved automorphism factor. -/
def rootedCanonicalEquiv (n : ℕ) : RootedSpanningTree n ≃ CanonicalTreeMap n :=
  Equiv.ofBijective rootedTreeNormal rootedTreeNormal_bijective

/-- Exact finite rooted-map/spanning-tree to identified-word correspondence. -/
def rootedWordEquiv (n : ℕ) : RootedSpanningTree n ≃ SuccessfulWord n :=
  (rootedCanonicalEquiv n).trans (canonicalWordEquiv n)

end FKCRT
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CornerMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators ENNReal
namespace FKCRT.PermutationWedge
variable {α β : Type*} [Fintype α] [Fintype β]

/-- Exact quotient-graph relabelling for arbitrary finite dart carriers. -/
def dartVertexEquiv (f : α ≃ β) {p : Perm α} {q : Perm β}
    (hp : ∀ x,q (f x)=f (p x)) : Vertex p ≃ Vertex q :=
  Quotient.congr f (sameCycle_embedding f f.injective hp)

end FKCRT.PermutationWedge
namespace FKCRT
open Inventory MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

/-- The canonical inverse word has the literal, uniquely determined stack
matching edge and vertex permutations. -/
def matchingCanonical {n : ℕ} (w : SuccessfulWord n)
    (D : StackMatching w.val (List.finRange (2*(n+1)))) : CanonicalTreeMap n where
  a := turns (D.first++D.second)
  s := (List.finRange (2*(n+1))).formPerm*turns D.first
  A := matchingEdges D.first D.second
  valid := matching_map_conditions D.first D.second D.first_arches D.second_arches D.covers
  tour := by
    have hn := D.covers.nodup_iff.mpr (List.nodup_finRange (2*(n+1)))
    rw [partialReversal_matchingEdges D.first D.second hn,mul_assoc,
      turns_self (by rw [endpoints_append] at hn;exact hn.of_append_left),mul_one]

end FKCRT
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_FiniteLaw
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
open Inventory
variable {n : ℕ}

def treeActivity (x : RootedSpanningTree n) : ℕ :=
  explorationActivity (reversal x.1) (rotation x.1) (tourSelector (reversal x.1)
    (rotation x.1) x.1.out.property.1) ∅ Finset.univ x.2.val (n+1)

end FKCRT
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable
namespace FKCRT
open Inventory

/-- The finite functions and literal word lists encode exactly the same
successful words, including their fixed length. -/
def successfulListEquiv (n : ℕ) : SuccessfulWord n ≃ {v // v∈typedEmptyWords (2*(n+1))} where
  toFun w := ⟨List.ofFn w.val,Finset.mem_filter.mpr ⟨mem_wordsOfLength.mpr List.length_ofFn,
    by simpa only [List.ofFn_eq_map] using w.property⟩⟩
  invFun v := ⟨fun i => v.val[i.val]'(by
      have hl := mem_wordsOfLength.mp (Finset.mem_filter.mp v.property).1
      omega),by
    have hl := mem_wordsOfLength.mp (Finset.mem_filter.mp v.property).1
    have he : ((List.finRange (2*(n+1))).map (fun i => v.val[i.val]'(by omega)))=v.val := by
      apply List.ext_getElem
      · simp [hl]
      · intro i hi hj
        simp
    rw [he]
    exact (Finset.mem_filter.mp v.property).2⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    exact List.getElem_ofFn _
  right_inv v := by
    apply Subtype.ext
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using (mem_wordsOfLength.mp (Finset.mem_filter.mp v.property).1).symm
    · intro i hi hj
      simp only [List.getElem_ofFn]

end FKCRT
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace FKCRT
open Inventory

/-- Exact finite word normalizer for the map marginal. -/
def typedPartition (q : ℝ) (n : ℕ) : ℝ :=
  ∑ w : SuccessfulWord n,(1+Real.sqrt q)^flexibleCount (List.ofFn w.val) []

end FKCRT
end


end OAI
end


