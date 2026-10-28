-- Prove2me | Definitions.Def_OAIQ021F000
-- name    : OAIQ021F000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T18:05:22.398378+00:00
-- url     : https://prove2.me/theorems/f550a6c1-4b6e-45cc-b94f-302497d413e1
-- title:
--   Definitions bundle OAIQ021F000 of the split of OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt`, carved from OpenAI's openai/math development (OpenAI, *Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)*, OpenAI Math Release, September 24, 2026, result family 211, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 591 declarations of OpenAI's Lean: 164 definitions, 11 inductive types or structures, 14 instances and 402 theorems. The definitions and types are `OAI.FKCRT.BlockCritical.Weights`, `OAI.FKCRT.BlockCritical.Weights.abelMean`, `OAI.FKCRT.BlockCritical.Weights.pgf`, `OAI.FKCRT.BlockCritical.doubleMass`, `OAI.FKCRT.BlockCritical.evenOffspring`, `OAI.FKCRT.BlockCritical.geomPrefix`, `OAI.FKCRT.BlockCritical.triPrefix`, `OAI.FKCRT.CanonicalTreeMap`, `OAI.FKCRT.CanonicalTreeMap.toMap`, `OAI.FKCRT.CanonicalTreeMap.word`, `OAI.FKCRT.Chords.Cross`, `OAI.FKCRT.Chords.Inside`, `OAI.FKCRT.Chords.Opener`, `OAI.FKCRT.Chords.componentDarts`, `OAI.FKCRT.Chords.gapIndex`, `OAI.FKCRT.Chords.graph`, `OAI.FKCRT.Chords.graphHom`, `OAI.FKCRT.Chords.opener`, `OAI.FKCRT.Chords.openerEmbedding`, `OAI.FKCRT.Chords.partialGraphHom`, `OAI.FKCRT.Chords.partialOpener`, `OAI.FKCRT.Chords.rootSplit`, `OAI.FKCRT.CornerSplit.join`, `OAI.FKCRT.CornerSplit.split`, `OAI.FKCRT.CutOutput.Data`, `OAI.FKCRT.CutOutput.count`, `OAI.FKCRT.CutOutput.firstIndex`, `OAI.FKCRT.CutOutput.last`, `OAI.FKCRT.CutOutput.left`, `OAI.FKCRT.CutOutput.output`, `OAI.FKCRT.CutOutput.right`, `OAI.FKCRT.DefectHitting.alive`, `OAI.FKCRT.DefectHitting.past`, `OAI.FKCRT.DefectHitting.stopIndex`, `OAI.FKCRT.DefectHitting.stopPredicate`, `OAI.FKCRT.DefectHitting.stoppedLength`, `OAI.FKCRT.DefectHitting.stoppedSum`, `OAI.FKCRT.DefectHitting.totalLength`, `OAI.FKCRT.DefectHitting.walk`, `OAI.FKCRT.EdgeSelector` and 135 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/FKMaps, in whole or in part: `FKMaps_BlockCritical`, `FKMaps_BlockLaw`, `FKMaps_CanonicalBijection`, `FKMaps_CoreCompression`, `FKMaps_CoreMetric`, `FKMaps_CoreWords`, `FKMaps_CornerInsertion`, `FKMaps_CornerInverse`, `FKMaps_ExcursionKernel`, `FKMaps_GraphWedge`, `FKMaps_Inventory`, `FKMaps_InventoryRenewal`, `FKMaps_LadderRecords`, `FKMaps_MapCycles`, `FKMaps_MapEncoding`, `FKMaps_Matching`, `FKMaps_MetricLimit`, `FKMaps_NodeMetric`, `FKMaps_Noncrossing`, `FKMaps_Offspring`, `FKMaps_PieceLaws`, `FKMaps_PieceWalks`, `FKMaps_PlanarActivity`, `FKMaps_PlaneTrees`, `FKMaps_RootedLaw`, `FKMaps_SeamLengths`, `FKMaps_SimpleWalk`, `FKMaps_SpineMoments`, `FKMaps_StationaryCuts`, `FKMaps_TourActivity`, `FKMaps_TreeCode`, `FKMaps_WordCoefficients`, `FKMaps_WordLaw`, `FKMaps_WordMaps`.
--
--   **Imports.** It imports the published bundle `Def_FKCRT`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ021F002` and `OAIQ021F003`.
-- source:
--   OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 211; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/FKMaps at commit adc7f12

import Mathlib
import Definitions.Def_FKCRT

section
-- module Solutions.OAIQ021_FK.Compat
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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_Offspring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

structure CriticalEvenOffspring where
  mass : ℕ → ℝ
  nonneg : ∀ k, 0 ≤ mass k
  total : HasSum mass 1
  even_support : ∀ k, Odd k → mass k = 0
  zero_pos : 0 < mass 0
  two_pos : 0 < mass 2
  mean : HasSum (fun k : ℕ => (k : ℝ) * mass k) 1
  second : Summable (fun k : ℕ => (k : ℝ)^2 * mass k)


def CriticalEvenOffspring.law (p : CriticalEvenOffspring) : PMF ℕ :=
  ⟨fun k => ((NNReal.mk (p.mass k) (p.nonneg k)) : ℝ≥0∞), by
    apply ENNReal.hasSum_coe.mpr
    apply NNReal.hasSum_coe.mp
    exact p.total⟩


@[simp] lemma CriticalEvenOffspring.law_apply (p : CriticalEvenOffspring) (k : ℕ) :
    p.law k = ENNReal.ofReal (p.mass k) := by
  rw [ENNReal.ofReal_eq_coe_nnreal (p.nonneg k)]
  rfl


@[simp] lemma CriticalEvenOffspring.law_singleton (p : CriticalEvenOffspring) (k : ℕ) :
    p.law.toMeasure {k} = ENNReal.ofReal (p.mass k) := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k), p.law_apply]


@[simp] lemma CriticalEvenOffspring.law_real_singleton (p : CriticalEvenOffspring) (k : ℕ) :
    p.law.toMeasure.real {k} = p.mass k := by
  simp [measureReal_def, p.nonneg]


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_TreeCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

def walk {N : ℕ} (d : Fin N → Fin N) (j : ℕ) : ℤ :=
  ∑ i : Fin N, if i.val < j then ((d i).val : ℤ) - 1 else 0


def IsTreeCode {N : ℕ} (d : Fin N → Fin N) : Prop :=
  walk d N = -1 ∧ ∀ j < N, 0 ≤ walk d j


abbrev Code (N : ℕ) := {d : Fin N → Fin N // IsTreeCode d}


def height {N : ℕ} (d : Fin N → Fin N) (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun k : Fin N => k.val < j ∧
    ∀ r : Fin (N+1), k.val ≤ r.val → r.val ≤ j → walk d k.val ≤ walk d r.val)).card


@[simp] lemma walk_zero {N : ℕ} (d : Fin N → Fin N) : walk d 0 = 0 := by simp [walk]


@[simp] lemma height_terminal {N : ℕ} (d : Code N) : height d.val N = 0 := by
  unfold height
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k _ hk
  have h := hk.2 ⟨N, Nat.lt_succ_self N⟩ k.isLt.le le_rfl
  rw [d.property.1] at h
  have h' := d.property.2 k.val k.isLt
  omega


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_LadderRecords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


lemma tail_tsum_ite (f : ℕ → ℝ≥0∞) (k : ℕ) :
    (∑' j : ℕ, f (j+k+1))=∑' r : ℕ, if k < r then f r else 0 := by
  have hi : Function.Injective (fun j : ℕ => j+k+1) := by intro a b h; dsimp at h; omega
  have hs : Function.support (fun r => if k < r then f r else 0) ⊆
      Set.range (fun j : ℕ => j+k+1) := by
    intro r hr
    have hkr : k < r := by by_contra hn; simp [Function.support,hn] at hr
    exact ⟨r-k-1,by dsimp; omega⟩
  simpa only [show ∀ j : ℕ, k<j+k+1 from by omega,ite_true] using hi.tsum_eq hs


lemma tail_tsum_total (f : ℕ → ℝ≥0∞) :
    (∑' k : ℕ, ∑' j : ℕ, f (j+k+1))=∑' r : ℕ, (r:ℝ≥0∞)*f r := by
  simp_rw [tail_tsum_ite]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro r
  rw [tsum_eq_sum (s := Finset.range r) (fun k hk => by simp [show ¬ k < r from by simpa using hk])]
  calc
    (∑ k ∈ Finset.range r, if k < r then f r else 0) = ∑ _k ∈ Finset.range r, f r := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ite_eq_left (Finset.mem_range.mp hk)]
    _ = _ := by simp


lemma CriticalEvenOffspring.ladder_total (p : CriticalEvenOffspring) :
    (∑' k : ℕ, ∑' j : ℕ, p.law (j+k+1))=1 := by
  rw [tail_tsum_total]
  have h := ENNReal.ofReal_tsum_of_nonneg
    (fun k : ℕ => mul_nonneg (Nat.cast_nonneg k) (p.nonneg k)) p.mean.summable
  rw [p.mean.tsum_eq] at h
  simpa [ENNReal.ofReal_mul,Nat.cast_nonneg] using h.symm


def CriticalEvenOffspring.ladderLaw (p : CriticalEvenOffspring) : PMF ℕ :=
  ⟨fun k => ∑' j : ℕ, p.law (j+k+1), ENNReal.summable.hasSum_iff.mpr p.ladder_total⟩


@[simp] lemma CriticalEvenOffspring.ladderLaw_apply (p : CriticalEvenOffspring) (k : ℕ) :
    p.ladderLaw k=∑' j : ℕ, p.law (j+k+1) := rfl


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
namespace FKCRT.SimpleWalk

/-- The walk killed on first visiting -1, with both endpoints nonnegative. -/
def killed : ℕ → ℕ → ℕ → ℝ
  | 0,a,b => if a=b then 1 else 0
  | n+1,0,b => killed n 1 b/2
  | n+1,a+1,b => (killed n a b+killed n (a+2) b)/2

lemma killed_nonneg (n a b : ℕ) : 0≤killed n a b := by
  induction n generalizing a with
  | zero => simp only [killed]; split_ifs <;> norm_num
  | succ n ih => cases a with
    | zero => exact div_nonneg (ih _) (by norm_num)
    | succ a => exact div_nonneg (add_nonneg (ih _) (ih _)) (by norm_num)

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

def sign (s : Bool) : ℤ := if s then 1 else -1

abbrev Path (n : ℕ) := Fin n → Bool

def pathSum {n : ℕ} (d : Path n) (k : ℕ) : ℤ :=
  ∑ i : Fin n, if i.val<k then sign (d i) else 0

@[simp] lemma pathSum_zero {n : ℕ} (d : Path n) : pathSum d 0=0 := by simp [pathSum]

lemma pathSum_cons {n : ℕ} (s : Bool) (d : Path n) (k : ℕ) :
    pathSum (Fin.cons s d) (k+1)=sign s+pathSum d k := by
  simp [pathSum,Fin.sum_univ_succ]

def splitPath (n : ℕ) : Path (n+1) ≃ Bool × Path n where
  toFun d := (d 0,Fin.tail d)
  invFun d := Fin.cons d.1 d.2
  left_inv d := by ext i; exact Fin.cases (by simp) (fun j => rfl) i
  right_inv d := by ext <;> simp

lemma sum_path_succ (n : ℕ) (F : Path (n+1) → ℝ) :
    (∑ d,F d)=(∑ d : Path n,F (Fin.cons true d))+(∑ d : Path n,F (Fin.cons false d)) := by
  rw [Fintype.sum_equiv (splitPath n) F (fun d => F (Fin.cons d.1 d.2)) (by intro d; simp [splitPath])]
  rw [Fintype.sum_prod_type,Fintype.sum_bool]

/-- Uniform nearest-neighbour path counting probability. -/
def pathMass (n : ℕ) (P : Path n → Prop) : ℝ :=
  (∑ d : Path n, if P d then (1:ℝ) else 0)/(2:ℝ)^n

lemma pathMass_congr {n : ℕ} {P Q : Path n → Prop} (h : ∀ d,P d↔Q d) :
    pathMass n P=pathMass n Q := by congr 2; funext d; rw [h d]

lemma pathMass_succ (n : ℕ) (P : Path (n+1) → Prop) :
    pathMass (n+1) P=(pathMass n (fun d => P (Fin.cons true d))+
      pathMass n (fun d => P (Fin.cons false d)))/2 := by
  unfold pathMass
  rw [sum_path_succ,pow_succ]
  ring

def nonnegativePath {n : ℕ} (a : ℤ) (d : Path n) : Prop :=
  ∀ k≤n, 0≤a+pathSum d k

lemma nonnegativePath_cons {n : ℕ} (a : ℤ) (s : Bool) (d : Path n) :
    nonnegativePath a (Fin.cons s d) ↔ 0≤a ∧ nonnegativePath (a+sign s) d := by
  constructor
  · intro h
    constructor
    · simpa using h 0 (by omega)
    · intro k hk
      have hh := h (k+1) (by omega)
      rw [pathSum_cons] at hh
      linarith
  · rintro ⟨ha,h⟩ k hk
    cases k with
    | zero => simpa using ha
    | succ k => rw [pathSum_cons]; have hh := h k (by omega); linarith

lemma pathMass_killed (n a b : ℕ) :
    pathMass n (fun d => nonnegativePath a d ∧ (a:ℤ)+pathSum d n=b)=killed n a b := by
  induction n generalizing a with
  | zero =>
    have h : ∀ d : Path 0,(nonnegativePath (a:ℤ) d ∧ (a:ℤ)+pathSum d 0=b) ↔ a=b := by
      intro d; simp [nonnegativePath,pathSum]
    rw [pathMass_congr h]
    simp [pathMass,killed]
  | succ n ih =>
    rw [pathMass_succ]
    have h1 : pathMass n (fun d => nonnegativePath a (Fin.cons true d) ∧
        (a:ℤ)+pathSum (Fin.cons true d) (n+1)=b)=
        pathMass n (fun d => nonnegativePath (a+1:ℕ) d ∧ ((a+1:ℕ):ℤ)+pathSum d n=b) := by
      apply pathMass_congr; intro d
      rw [nonnegativePath_cons,pathSum_cons]
      simp [sign,add_assoc]
    rw [h1,ih]
    cases a with
    | zero =>
      have h2 : pathMass n (fun d => nonnegativePath (0:ℤ) (Fin.cons false d) ∧
          (0:ℤ)+pathSum (Fin.cons false d) (n+1)=b)=0 := by
        have hh : ∀ d : Path n,¬nonnegativePath (0:ℤ) (Fin.cons false d) := by
          intro d h
          have hh := h 1 (by omega)
          norm_num [pathSum_cons,sign] at hh
        simp only [pathMass,hh,false_and,ite_false,Finset.sum_const_zero,zero_div]
      simp only [Nat.cast_zero] at *
      rw [h2]
      simp [killed]
    | succ a =>
      have h2 : pathMass n (fun d => nonnegativePath (a+1:ℕ) (Fin.cons false d) ∧
          ((a+1:ℕ):ℤ)+pathSum (Fin.cons false d) (n+1)=b)=
          pathMass n (fun d => nonnegativePath a d ∧ (a:ℤ)+pathSum d n=b) := by
        apply pathMass_congr; intro d
        rw [nonnegativePath_cons,pathSum_cons]
        simp [sign,add_assoc]
        omega
      rw [h2,ih]
      simp only [killed]
      ring

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

instance instMeasurableSpaceBool_solutions : MeasurableSpace Bool := ⊤
instance instMeasurableSingletonClassBool_solutions : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩

def coinLaw : Measure Bool := (2:ℝ≥0∞)⁻¹ • Measure.count

lemma coinLaw_singleton (s : Bool) : coinLaw {s}=(2:ℝ≥0∞)⁻¹ := by
  simp [coinLaw]

instance instIsProbabilityMeasureBoolCoinLaw : IsProbabilityMeasure coinLaw := by
  constructor
  norm_num [coinLaw,Measure.count_apply_finite]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

lemma coinPath_singleton (N : ℕ) (d : SimpleWalk.Path N) :
    (Measure.pi (fun _ : Fin N => coinLaw)).real {d}=1/(2:ℝ)^N := by
  rw [measureReal_def,Measure.pi_singleton]
  simp only [coinLaw_singleton,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ENNReal.toReal_pow,ENNReal.toReal_inv,ENNReal.toReal_ofNat]
  simp only [one_div,inv_pow]

lemma coinPath_event (N : ℕ) (P : SimpleWalk.Path N → Prop) :
    (Measure.pi (fun _ : Fin N => coinLaw)).real {d | P d}=SimpleWalk.pathMass N P := by
  classical
  have he : ({d | P d} : Set (SimpleWalk.Path N))=(Finset.univ.filter P : Finset _):= by ext; simp
  rw [he,← sum_measureReal_singleton]
  simp only [coinPath_singleton,Finset.sum_filter,SimpleWalk.pathMass]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> simp

end FKCRT.TreeCoding
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
namespace FKCRT.Histogram
variable {ι : Type*} [Fintype ι]

def cube (δ : ℝ) (a : ι → ℝ) : Set (ι → ℝ) := pi univ (fun i => Ico (a i) (a i+δ))

lemma measurableSet_cube (δ : ℝ) (a : ι → ℝ) : MeasurableSet (cube δ a) :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Ico)

lemma volume_cube (δ : ℝ) (a : ι → ℝ) :
    volume (cube δ a)=ENNReal.ofReal δ ^ Fintype.card ι := by
  rw [cube,volume_pi,Measure.pi_pi]
  simp

def boxLaw (δ : ℝ) (a : ι → ℝ) : Measure (ι → ℝ) :=
  (ENNReal.ofReal δ ^ Fintype.card ι)⁻¹ • volume.restrict (cube δ a)

lemma boxLaw_probability {δ : ℝ} (hδ : 0<δ) (a : ι → ℝ) :
    IsProbabilityMeasure (boxLaw δ a) := by
  constructor
  simp only [boxLaw,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul,volume_cube]
  exact ENNReal.inv_mul_cancel (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr hδ)))
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

lemma boxLaw_withDensity (δ : ℝ) (a : ι → ℝ) :
    boxLaw δ a=volume.withDensity ((cube δ a).indicator
      (fun _ => (ENNReal.ofReal δ ^ Fintype.card ι)⁻¹)) := by
  rw [withDensity_indicator (measurableSet_cube δ a),withDensity_const]
  rfl

end FKCRT.Histogram
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Histogram
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [MeasurableSpace Ω]
  [MeasurableSingletonClass Ω]

def mixture (μ : Measure Ω) (φ : Ω → ι → ℝ) (δ : ℝ) : Measure (ι → ℝ) :=
  ∑ ω, μ {ω} • boxLaw δ (φ ω)

lemma mixture_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (φ : Ω → ι → ℝ) {δ : ℝ} (hδ : 0<δ) :
    IsProbabilityMeasure (mixture μ φ δ) := by
  have (ω : Ω) : IsProbabilityMeasure (boxLaw δ (φ ω)) := boxLaw_probability hδ (φ ω)
  constructor
  simp only [mixture,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,
    measure_univ,mul_one]
  rw [sum_measure_singleton,Finset.coe_univ,measure_univ]

def density (μ : Measure Ω) (φ : Ω → ι → ℝ) (δ : ℝ) (x : ι → ℝ) : ℝ≥0∞ :=
  ∑ ω,μ {ω} * (cube δ (φ ω)).indicator
    (fun _ => (ENNReal.ofReal δ ^ Fintype.card ι)⁻¹) x

omit [MeasurableSingletonClass Ω] in
lemma mixture_withDensity (μ : Measure Ω) (φ : Ω → ι → ℝ) (δ : ℝ) :
    mixture μ φ δ=volume.withDensity (density μ φ δ) := by
  ext s hs
  rw [withDensity_apply _ hs]
  simp only [mixture,Measure.finsetSum_apply,density]
  have hm (ω : Ω) : Measurable (fun x : ι → ℝ => μ {ω} * (cube δ (φ ω)).indicator
      (fun _ => (ENNReal.ofReal δ ^ Fintype.card ι)⁻¹) x) :=
    measurable_const.mul (measurable_const.indicator (measurableSet_cube δ (φ ω)))
  rw [lintegral_finsetSum _ (fun ω _ => hm ω)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Measure.smul_apply,smul_eq_mul,boxLaw_withDensity,
    withDensity_apply _ hs,lintegral_const_mul _
      (measurable_const.indicator (measurableSet_cube δ (φ ω)))]

end FKCRT.Histogram
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_Inventory
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

/-- `none` is the flexible order; a typed order is `some type`. -/
abbrev Order := Option Bool
inductive Letter where
  | burger : Bool → Letter
  | order : Order → Letter
  deriving DecidableEq, Fintype

/-- Internal stacks are freshest-first. The source's surviving-burger list
is `Evaluation.burgers.reverse`, so source chronology is unchanged. -/
def eligible (a : Order) (b : Bool) : Prop := a=none ∨ a=some b

instance instDecidableEligible (a : Order) (b : Bool) : Decidable (eligible a b) :=
  inferInstanceAs (Decidable (a=none ∨ a=some b))

def pop (a : Order) : List Bool → Option (List Bool)
  | [] => none
  | b::bs => if eligible a b then some bs else (pop a bs).map (b::·)

lemma pop_append (a : Order) (s t : List Bool) :
    pop a (s++t) = match pop a s with
      | some s' => some (s'++t)
      | none => (pop a t).map (s++·) := by
  induction s with
  | nil => simp [pop]
  | cons b bs ih =>
    simp only [List.cons_append,pop]
    split_ifs with h
    · rfl
    · rw [ih]
      cases pop a bs <;> cases pop a t <;> rfl

lemma pop_length {a : Order} {s t : List Bool} (h : pop a s=some t) :
    t.length+1=s.length := by
  induction s generalizing t with
  | nil => simp [pop] at h
  | cons b bs ih =>
    simp only [pop] at h
    split_ifs at h with he
    · cases h; rfl
    · cases hp : pop a bs with
      | none => simp [hp] at h
      | some s' =>
        simp only [hp,Option.map_some,Option.some.injEq] at h
        subst t
        simp only [List.length_cons]
        have := ih hp
        omega

structure Evaluation where
  orders : List Order
  burgers : List Bool
  deriving DecidableEq

def step (e : Evaluation) : Letter → Evaluation
  | .burger b => ⟨e.orders,b::e.burgers⟩
  | .order a => match pop a e.burgers with
    | some bs => ⟨e.orders,bs⟩
    | none => ⟨e.orders++[a],e.burgers⟩

def run : List Letter → Evaluation → Evaluation
  | [],e => e
  | a::w,e => run w (step e a)

def reduce (w : List Letter) : Evaluation := run w ⟨[],[]⟩

lemma run_append (w w' : List Letter) (e : Evaluation) :
    run (w++w') e=run w' (run w e) := by
  induction w generalizing e with
  | nil => rfl
  | cons a w ih => exact ih _

def Letter.increment : Letter → ℤ
  | .burger _ => 1
  | .order _ => -1

def imbalance (e : Evaluation) : ℤ := (e.burgers.length:ℤ)-e.orders.length

lemma step_imbalance (e : Evaluation) (a : Letter) :
    imbalance (step e a)=imbalance e+a.increment := by
  cases a with
  | burger b => simp [imbalance,step,Letter.increment]; ring
  | order a =>
    simp only [step,Letter.increment]
    cases hp : pop a e.burgers with
    | none => simp [imbalance]; ring
    | some bs =>
      have hlen := pop_length hp
      simp only [imbalance]
      omega

lemma run_imbalance (w : List Letter) (e : Evaluation) :
    imbalance (run w e)=(w.map Letter.increment).sum+imbalance e := by
  induction w generalizing e with
  | nil => simp [run]
  | cons a w ih =>
    simp only [run,ih,step_imbalance,List.map_cons,List.sum_cons]
    ring

lemma reduce_imbalance (w : List Letter) :
    imbalance (reduce w)=(w.map Letter.increment).sum := by
  rw [reduce,run_imbalance]
  simp [imbalance]

lemma orders_length_le_step (e : Evaluation) (a : Letter) :
    e.orders.length≤(step e a).orders.length := by
  cases a with
  | burger b => rfl
  | order a => simp only [step]; split <;> simp

lemma orders_length_le_run (w : List Letter) (e : Evaluation) :
    e.orders.length≤(run w e).orders.length := by
  induction w generalizing e with
  | nil => rfl
  | cons a w ih => exact (orders_length_le_step e a).trans (ih (step e a))

def EmptyReducing (w : List Letter) : Prop := reduce w=⟨[],[]⟩

/-- Exact necessary Dyck-path event, without invoking a map encoding. -/
theorem emptyReducing_dyck (w : List Letter) (h : EmptyReducing w) :
    (w.map Letter.increment).sum=0 ∧
      ∀ j,0≤((w.take j).map Letter.increment).sum := by
  have he : reduce w=⟨[],[]⟩ := h
  constructor
  · rw [← reduce_imbalance,he,imbalance]; simp
  · intro j
    have hle := orders_length_le_run (w.drop j) (reduce (w.take j))
    have hr : run (w.drop j) (reduce (w.take j))=reduce w := by
      rw [reduce,← run_append,List.take_append_drop]
      rfl
    rw [hr,he] at hle
    have ho : (reduce (w.take j)).orders=[] := List.length_eq_zero_iff.mp (by simpa using hle)
    rw [← reduce_imbalance,imbalance,ho]
    simp

end FKCRT.Inventory
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

instance instTopologicalSpaceLetter : TopologicalSpace Letter := ⊥
instance instMeasurableSpaceLetter : MeasurableSpace Letter := ⊤

structure Parameters where
  p : ℝ
  lower : 1/2<p
  upper : p<1

lemma Parameters.pos (P : Parameters) : 0<P.p := by linarith [P.lower]

def mass (P : Parameters) : Letter → ℝ
  | .burger _ => 1/4
  | .order none => P.p/2
  | .order (some _) => (1-P.p)/4

lemma mass_pos (P : Parameters) (a : Letter) : 0 < mass P a := by
  cases a with
  | burger b => norm_num [mass]
  | order a => cases a <;> dsimp [mass] <;> linarith [P.pos,P.upper]

lemma sum_letters {β : Type*} [AddCommMonoid β] (f : Letter → β) :
    ∑ a,f a = f (.burger false)+f (.burger true)+f (.order (some false))+
      f (.order (some true))+f (.order none) := by
  have h : (Finset.univ : Finset Letter)=
      {.burger false,.burger true,.order (some false),.order (some true),.order none} := by
    ext a; cases a with
    | burger b => cases b <;> simp
    | order a => cases a with
      | none => simp
      | some b => cases b <;> simp
  rw [h]
  simp [add_assoc]

lemma mass_sum (P : Parameters) : ∑ a,mass P a=1 := by
  rw [sum_letters]
  simp only [mass]
  ring

def law (P : Parameters) : PMF Letter := PMF.ofFintype (fun a => ENNReal.ofReal (mass P a)) (by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (mass_pos P a).le),mass_sum]
  simp)

lemma law_singleton (P : Parameters) (a : Letter) :
    (law P).toMeasure {a}=ENNReal.ofReal (mass P a) := by
  simp [law]

def streamLaw (P : Parameters) (ι : Type*) : Measure (ι → Letter) :=
  Measure.infinitePi (fun _ : ι => (law P).toMeasure)
instance instIsProbabilityMeasureForallLetterStreamLaw (P : Parameters) (ι : Type*) : IsProbabilityMeasure (streamLaw P ι) := by
  unfold streamLaw; infer_instance

def signSum (x : ℕ → Letter) (n : ℕ) : ℤ :=
  ∑ i∈Finset.range n,(x i).increment

end FKCRT.Inventory
end



noncomputable section
open scoped BigOperators
namespace FKCRT.Inventory

lemma pop_fixed (b : Bool) (s : List Bool) :
    pop (some b) s = if b∈s then some (s.erase b) else none := by
  induction s with
  | nil => simp [pop]
  | cons c s ih =>
    by_cases h : c=b
    · subst c; simp [pop,eligible]
    · have hc : b≠c := Ne.symm h
      simp [pop,eligible,h,hc,ih]

inductive TypedLetter where
  | burger : Bool → TypedLetter
  | order : Bool → TypedLetter
  deriving DecidableEq, Fintype

def TypedLetter.fixed : TypedLetter → Letter
  | .burger b => .burger b
  | .order b => .order (some b)

def stackTypedStep (s : List Bool) : TypedLetter → Option (List Bool)
  | .burger b => some (b::s)
  | .order b => pop (some b) s

def identifyOne (s : List Bool) : Letter → Option (TypedLetter × List Bool)
  | .burger b => some (.burger b,b::s)
  | .order (some b) => (pop (some b) s).map (fun t => (.order b,t))
  | .order none => match s with
      | [] => none
      | b::t => some (.order b,t)

def identify : List Letter → List Bool → Option (List TypedLetter × List Bool)
  | [],s => some ([],s)
  | a::w,s => do
      let (b,t) ← identifyOne s a
      let (v,r) ← identify w t
      pure (b::v,r)

def stackTypedRun : List TypedLetter → List Bool → Option (List Bool)
  | [],s => some s
  | a::w,s => (stackTypedStep s a).bind (stackTypedRun w)

lemma identifyOne_step {s t : List Bool} {a : Letter} {b : TypedLetter}
    (h : identifyOne s a = some (b,t)) : step ⟨[],s⟩ a = ⟨[],t⟩ ∧ stackTypedStep s b = some t := by
  cases a with
  | burger c => simp only [identifyOne,Option.some.injEq,Prod.mk.injEq] at h; rcases h with ⟨rfl,rfl⟩; exact ⟨rfl,rfl⟩
  | order x => cases x with
    | none => cases s with
      | nil => simp [identifyOne] at h
      | cons c r =>
        simp only [identifyOne,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        simp [step,stackTypedStep,pop,eligible]
    | some c =>
      cases hp : pop (some c) s with
      | none => simp [identifyOne,hp] at h
      | some r =>
        simp only [identifyOne,hp,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        simp [step,stackTypedStep,hp]

lemma identifyOne_none {s : List Bool} {a : Letter} (h : identifyOne s a = none) :
    (step ⟨[],s⟩ a).orders.length = 1 := by
  cases a with
  | burger b => simp [identifyOne] at h
  | order x => cases x with
    | none => cases s <;> simp_all [identifyOne,step,pop]
    | some b =>
      have hp : pop (some b) s = none := by simpa [identifyOne] using h
      simp [step,hp]

lemma identify_sound {w : List Letter} {s t : List Bool} {v : List TypedLetter}
    (h : identify w s=some (v,t)) :
    run w ⟨[],s⟩=⟨[],t⟩ ∧ stackTypedRun v s=some t ∧ v.length=w.length := by
  induction w generalizing s t v with
  | nil => simp only [identify,Option.some.injEq,Prod.mk.injEq] at h; rcases h with ⟨rfl,rfl⟩; exact ⟨rfl,rfl,rfl⟩
  | cons a w ih =>
    cases hx : identifyOne s a with
    | none => simp [identify,hx] at h
    | some x =>
      obtain ⟨b,r⟩ := x
      cases hy : identify w r with
      | none => simp [identify,hx,hy] at h
      | some y =>
        obtain ⟨u,z⟩ := y
        simp [identify,hx,hy] at h
        rcases h with ⟨rfl,rfl⟩
        obtain ⟨hr,ht,hl⟩ := ih hy
        obtain ⟨hs,hb⟩ := identifyOne_step hx
        exact ⟨by rw [run,hs,hr],by rw [stackTypedRun,hb,Option.bind_some,ht],by simp [hl]⟩

lemma identify_complete {w : List Letter} {s t : List Bool}
    (h : run w ⟨[],s⟩=⟨[],t⟩) : ∃ v, identify w s=some (v,t) := by
  induction w generalizing s t with
  | nil => cases h; exact ⟨[],rfl⟩
  | cons a w ih =>
    cases hx : identifyOne s a with
    | none =>
      have hle := orders_length_le_run w (step ⟨[],s⟩ a)
      rw [show run w (step ⟨[],s⟩ a)=⟨[],t⟩ from h, identifyOne_none hx] at hle
      simp at hle
    | some x =>
      obtain ⟨b,r⟩ := x
      have hs := (identifyOne_step hx).1
      rw [run,hs] at h
      obtain ⟨v,hv⟩ := ih h
      exact ⟨b::v,by simp [identify,hx,hv]⟩

lemma emptyReducing_iff_identify (w : List Letter) :
    EmptyReducing w ↔ ∃ v, identify w []=some (v,[]) := by
  constructor
  · exact identify_complete
  · rintro ⟨v,hv⟩; exact (identify_sound hv).1

lemma identify_fixed {w : List TypedLetter} {s t : List Bool} (h : stackTypedRun w s = some t) :
    identify (w.map TypedLetter.fixed) s = some (w,t) := by
  induction w generalizing s with
  | nil => simp only [stackTypedRun,Option.some.injEq] at h; subst s; rfl
  | cons a w ih =>
    cases hx : stackTypedStep s a with
    | none => simp [stackTypedRun,hx] at h
    | some r =>
      have hh : identifyOne s a.fixed=some (a,r) := by
        cases a <;> simp_all [stackTypedStep,TypedLetter.fixed,identifyOne]
      have hy := ih (by simpa only [stackTypedRun,hx,Option.bind_some] using h)
      simp [identify,hh,hy]

end FKCRT.Inventory
end


noncomputable section
open scoped BigOperators
namespace FKCRT.Inventory

/-- A fixed typed closing is flexible exactly when its type is the freshest
burger still present. This is a property of the identified word, not of marks. -/
def flexibleClosing (s : List Bool) : TypedLetter → Prop
  | .burger _ => False
  | .order b => s.head?=some b
instance instDecidableFlexibleClosing (s : List Bool) (a : TypedLetter) : Decidable (flexibleClosing s a) := by
  cases a <;> unfold flexibleClosing <;> infer_instance

def origins (s : List Bool) (a : TypedLetter) : Finset Letter :=
  {a.fixed} ∪ if flexibleClosing s a then {.order none} else ∅

lemma identifyOne_typedStep {s t : List Bool} {a : TypedLetter}
    (h : stackTypedStep s a=some t) :
    ∀ x : Letter, identifyOne s x=some (a,t) ↔ x∈origins s a := by
  intro x
  cases a with
  | burger b =>
    simp only [stackTypedStep,Option.some.injEq] at h
    subst t
    cases x with
    | burger c => simp [identifyOne,origins,flexibleClosing,TypedLetter.fixed]
    | order c =>
      cases c with
      | none => cases s <;> simp [identifyOne,origins,flexibleClosing,TypedLetter.fixed]
      | some c => cases pop (some c) s <;> simp [identifyOne,origins,flexibleClosing,TypedLetter.fixed]
  | order b =>
    change pop (some b) s=some t at h
    cases x with
    | burger c =>
      by_cases he : flexibleClosing s (.order b) <;> simp [identifyOne,origins,he,TypedLetter.fixed]
    | order c => cases c with
      | none =>
        cases s with
        | nil => simp [pop] at h
        | cons d r =>
          by_cases hd : d=b
          · subst d
            have ht : r=t := by simpa [pop,eligible] using h
            subst t
            simp [identifyOne,origins,flexibleClosing,TypedLetter.fixed]
          · simp [identifyOne,origins,flexibleClosing,TypedLetter.fixed,hd]
      | some c =>
        by_cases hc : c=b
        · subst c; simp [identifyOne,h,origins,flexibleClosing,TypedLetter.fixed]
        · cases pop (some c) s <;> simp [identifyOne,origins,TypedLetter.fixed,hc] <;> split_ifs <;> simp

def markings : List TypedLetter → List Bool → Finset (List Letter)
  | [],_ => {[]}
  | a::v,s => match stackTypedStep s a with
      | none => ∅
      | some t => (origins s a).biUnion (fun x => (markings v t).image (x::·))

lemma mem_markings {v : List TypedLetter} {s : List Bool} {w : List Letter} :
    w∈markings v s ↔ ∃ t, identify w s=some (v,t) := by
  induction v generalizing s w with
  | nil =>
    cases w with
    | nil => simp [markings,identify]
    | cons x w =>
      constructor
      · simp [markings]
      · rintro ⟨t,ht⟩
        have hh := (identify_sound ht).2.2
        simp at hh
  | cons a v ih =>
    cases hs : stackTypedStep s a with
    | none =>
      simp only [markings,hs,Finset.notMem_empty,false_iff,not_exists]
      intro t ht
      obtain ⟨_,hu,_⟩ := identify_sound ht
      simp [stackTypedRun,hs] at hu
    | some r =>
      constructor
      · simp only [markings,hs,Finset.mem_biUnion,Finset.mem_image]
        rintro ⟨x,hx,z,hz,rfl⟩
        obtain ⟨t,ht⟩ := ih.mp hz
        have hh := (identifyOne_typedStep hs x).mpr hx
        exact ⟨t,by simp [identify,hh,ht]⟩
      · rintro ⟨t,ht⟩
        cases w with
        | nil => simp [identify] at ht
        | cons x w =>
          cases hh : identifyOne s x with
          | none => simp [identify,hh] at ht
          | some z =>
            obtain ⟨b,u⟩ := z
            cases hw : identify w u with
            | none => simp [identify,hh,hw] at ht
            | some y =>
              obtain ⟨v',t'⟩ := y
              simp [identify,hh,hw] at ht
              obtain ⟨⟨rfl,rfl⟩,rfl⟩ := ht
              have hur := (identifyOne_step hh).2
              rw [hs,Option.some.injEq] at hur
              subst u
              rw [markings,hs]
              apply Finset.mem_biUnion.mpr
              refine ⟨x,(identifyOne_typedStep hs x).mp hh,?_⟩
              exact Finset.mem_image.mpr ⟨w,ih.mpr ⟨t',hw⟩,rfl⟩

def wordMass (P : Parameters) (w : List Letter) : ℝ := (w.map (mass P)).prod

def flexibleCount : List TypedLetter → List Bool → ℕ
  | [],_ => 0
  | a::v,s => match stackTypedStep s a with
      | none => 0
      | some t => (if flexibleClosing s a then 1 else 0)+flexibleCount v t

end FKCRT.Inventory
end


noncomputable section
open scoped BigOperators
namespace FKCRT.Inventory

lemma stack_pop_fixed_count {b : Bool} {s t : List Bool} (h : pop (some b) s=some t) (c : Bool) :
    t.count c + (if b=c then 1 else 0) = s.count c := by
  rw [pop_fixed] at h
  split_ifs at h with hb
  · cases h
    by_cases hc : b=c
    · subst c
      simp only [ite_true,List.count_erase_self]
      have hp := List.count_pos_iff.mpr hb
      omega
    · simp [List.count_erase_of_ne (Ne.symm hc),hc]

lemma typedRun_append (v w : List TypedLetter) (s : List Bool) :
    stackTypedRun (v++w) s = (stackTypedRun v s).bind (stackTypedRun w) := by
  induction v generalizing s with
  | nil => rfl
  | cons a v ih =>
    simp only [List.cons_append,stackTypedRun]
    cases stackTypedStep s a <;> simp_all

lemma typedRun_balance {v : List TypedLetter} {s t : List Bool} (h : stackTypedRun v s=some t)
    (c : Bool) : t.count c+v.count (.order c)=s.count c+v.count (.burger c) := by
  induction v generalizing s with
  | nil => simp only [stackTypedRun,Option.some.injEq] at h; subst t; simp
  | cons a v ih =>
    cases a with
    | burger b =>
      have hh := ih (s := b::s) (by simpa only [stackTypedRun,stackTypedStep,Option.bind_some] using h)
      by_cases hb : b=c <;> simp_all
      omega
    | order b =>
      cases hs : pop (some b) s with
      | none => simp [stackTypedRun,stackTypedStep,hs] at h
      | some r =>
        have hh := ih (s := r) (by simpa only [stackTypedRun,stackTypedStep,hs,Option.bind_some] using h)
        have hr := stack_pop_fixed_count hs c
        by_cases hb : b=c <;> simp_all
        omega

lemma typedRun_prefix {v w : List TypedLetter} {s t : List Bool}
    (h : stackTypedRun w s=some t) (hv : v<+:w) : ∃ r,stackTypedRun v s=some r := by
  obtain ⟨z,rfl⟩ := hv
  rw [typedRun_append] at h
  cases hh : stackTypedRun v s with
  | none => simp [hh] at h
  | some r => exact ⟨r,rfl⟩

lemma typedRun_prefix_count {w : List TypedLetter} {s t : List Bool}
    (h : stackTypedRun w s=some t) {v : List TypedLetter} (hv : v<+:w) (c : Bool) :
    v.count (.order c)≤ s.count c+v.count (.burger c) := by
  obtain ⟨r,hr⟩ := typedRun_prefix h hv
  have hh := typedRun_balance hr c
  omega

/-- Successful typed words are exactly the shuffles of two nonnegative paths;
final emptiness will make both paths Dyck words. -/
lemma typedRun_exists_iff (w : List TypedLetter) (s : List Bool) :
    (∃ t,stackTypedRun w s=some t) ↔
      ∀ v,v<+:w → ∀ c : Bool,v.count (.order c)≤ s.count c+v.count (.burger c) := by
  constructor
  · rintro ⟨t,ht⟩ v hv c
    exact typedRun_prefix_count ht hv c
  · intro h
    induction w generalizing s with
    | nil => exact ⟨s,rfl⟩
    | cons a w ih =>
      have ha (c : Bool) := h [a] (by exact ⟨w,rfl⟩) c
      have hs : ∃ r,stackTypedStep s a=some r := by
        cases a with
        | burger b => exact ⟨b::s,rfl⟩
        | order b =>
          have hb : b∈s := by
            apply List.count_pos_iff.mp
            have hh := ha b
            exact lt_of_lt_of_le (by norm_num : (0:ℕ)<1) (by simpa using hh)
          exact ⟨s.erase b,by simp [stackTypedStep,pop_fixed,hb]⟩
      obtain ⟨r,hr⟩ := hs
      have hstep (c : Bool) : r.count c+[a].count (.order c)=s.count c+[a].count (.burger c) :=
        typedRun_balance (by simpa [stackTypedRun] using hr : stackTypedRun [a] s=some r) c
      obtain ⟨t,ht⟩ := ih r (by
        intro v hv c
        have hh := h (a::v) (by obtain ⟨z,rfl⟩ := hv; exact ⟨z,rfl⟩) c
        have hs := hstep c
        simp only [List.count_cons,List.count_nil] at hh hs
        omega)
      exact ⟨t,by simp only [stackTypedRun,hr,Option.bind_some,ht]⟩

def colorStep (c : Bool) : TypedLetter → Option DyckStep
  | .burger b => if b=c then some .U else none
  | .order b => if b=c then some .D else none

def colorWord (c : Bool) (w : List TypedLetter) : List DyckStep := w.filterMap (colorStep c)

lemma colorWord_counts (c : Bool) (w : List TypedLetter) :
    (colorWord c w).count .U=w.count (.burger c) ∧
    (colorWord c w).count .D=w.count (.order c) := by
  induction w with
  | nil => simp [colorWord]
  | cons a w ih =>
    cases a with
    | burger b => by_cases hb : b=c <;> simp_all [colorWord,colorStep]
    | order b => by_cases hb : b=c <;> simp_all [colorWord,colorStep]

/-- The precise source identification: each type separately is a genuine
Mathlib Dyck word, with no assumption about flexible marks. -/
def identifiedDyck {w : List TypedLetter} (h : stackTypedRun w []=some []) (c : Bool) : DyckWord where
  toList := colorWord c w
  count_U_eq_count_D := by
    have hh := typedRun_balance h c
    simpa only [colorWord_counts,List.count_nil,zero_add] using hh.symm
  count_D_le_count_U i := by
    obtain ⟨v,hv,he⟩ := List.prefix_filterMap_iff.mp (List.take_prefix i (colorWord c w))
    rw [he]
    change (colorWord c v).count .D≤(colorWord c v).count .U
    rw [(colorWord_counts c v).1,(colorWord_counts c v).2]
    simpa only [List.count_nil,zero_add] using typedRun_prefix_count h hv c

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_InventoryRenewal
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.DefectHitting
variable {Ω : Type*}
attribute [local instance] Classical.propDecidable

def walk (X : ℕ → Ω → ℕ) (n : ℕ) (x : Ω) : ℤ := ∑ j∈Finset.range n,(1-(X j x:ℤ))
def alive (X : ℕ → Ω → ℕ) (n : ℕ) : Set Ω := {x | ∀ k  ≤  n,walk X k x  ≤  0}
def stoppedSum (X : ℕ → Ω → ℕ) (n : ℕ) (x : Ω) : ℝ :=
  ∑ j∈Finset.range n,(alive X j).indicator (fun x => 1-(X j x:ℝ)) x

lemma walk_succ (X : ℕ → Ω → ℕ) (n : ℕ) (x : Ω) :
    walk X (n+1) x=walk X n x+1-X n x := by simp [walk,Finset.sum_range_succ]; ring
lemma alive_zero (X : ℕ → Ω → ℕ) (x : Ω) : x∈alive X 0 := by simp [alive,walk]
lemma alive_succ {X : ℕ → Ω → ℕ} {n : ℕ} {x : Ω} :
    x∈alive X (n+1) ↔ x∈alive X n ∧ walk X (n+1) x ≤ 0 := by
  constructor
  · intro h; exact ⟨fun k hk => h k (by omega),h _ le_rfl⟩
  · rintro ⟨h,h'⟩ k hk
    rcases lt_or_eq_of_le hk with hh | rfl
    · exact h k (by omega)
    · exact h'
lemma stoppedSum_eq (X : ℕ → Ω → ℕ) (n : ℕ) (x : Ω) :
    stoppedSum X n x=if x∈alive X n then (walk X n x:ℝ) else 1 := by
  classical
  induction n with
  | zero => simp [stoppedSum,walk,alive_zero]
  | succ n ih =>
    rw [stoppedSum,Finset.sum_range_succ]
    change stoppedSum X n x+_= _
    rw [ih]
    by_cases hn : x∈alive X n
    · rw [ite_eq_left hn,Set.indicator_of_mem hn]
      by_cases hs : walk X (n+1) x ≤ 0
      · rw [ite_eq_left (alive_succ.mpr ⟨hn,hs⟩),walk_succ]
        push_cast; ring
      · rw [ite_eq_right (fun h => hs (alive_succ.mp h).2)]
        have hle := hn n le_rfl
        have hw := walk_succ X n x
        have he : walk X (n+1) x=1 := by omega
        have he' : walk X n x+1-(X n x:ℤ)=1 := hw.symm.trans he
        have hh := congrArg (fun z : ℤ => (z:ℝ)) he'
        push_cast at hh
        linarith
    · rw [ite_eq_right hn,Set.indicator_of_notMem hn,
        ite_eq_right (fun h => hn (alive_succ.mp h).1),add_zero]
lemma stoppedSum_le_one (X : ℕ → Ω → ℕ) (n : ℕ) (x : Ω) : stoppedSum X n x ≤ 1 := by
  rw [stoppedSum_eq]
  split_ifs with h
  · have hh := h n le_rfl
    exact (Int.cast_nonpos.mpr hh).trans (by norm_num)
  · exact le_rfl

variable [MeasurableSpace Ω]

@[instance_reducible] def past (X : ℕ → Ω → ℕ) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ j∈Set.Iio n,MeasurableSpace.comap (X j) inferInstance
lemma past_le {X : ℕ → Ω → ℕ} (hX : ∀ j,Measurable (X j)) (n : ℕ) : past X n ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup_le fun j => iSup_le fun _ => (hX j).comap_le
omit [MeasurableSpace Ω] in
lemma measurable_walk_prefix (X : ℕ → Ω → ℕ) (n k : ℕ) (hk : k ≤ n) : Measurable[past X n] (walk X k) := by
  apply Finset.measurable_sum
  intro j hj
  simp only [Finset.mem_range] at hj
  have hm : Measurable[past X n] (X j) := measurable_iff_comap_le.mpr
    (le_iSup_of_le j (le_iSup_of_le (show j∈Set.Iio n by simp only [Set.mem_Iio]; omega) le_rfl))
  exact measurable_const.sub ((measurable_of_countable (fun k : ℕ => (k:ℤ))).comp hm)
omit [MeasurableSpace Ω] in
lemma measurableSet_alive_prefix (X : ℕ → Ω → ℕ) (n : ℕ) : MeasurableSet[past X n] (alive X n) := by
  simp only [alive,Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun hk =>
    measurableSet_le (measurable_walk_prefix X n k hk) measurable_const
lemma measurableSet_alive {X : ℕ → Ω → ℕ} (hX : ∀ j,Measurable (X j)) (n : ℕ) : MeasurableSet (alive X n) :=
  past_le hX n _ (measurableSet_alive_prefix X n)
lemma alive_indep_next {X : ℕ → Ω → ℕ} {μ : Measure Ω}
    (hX : ∀ j,Measurable (X j)) (hi : iIndepFun X μ) (n : ℕ) :
    IndepFun ((alive X n).indicator (fun _ => (1:ℝ))) (X n) μ := by
  have h := indep_iSup_of_disjoint (fun j => (hX j).comap_le) hi
    (show Disjoint (Set.Iio n) ({n}:Set ℕ) by simp)
  have hh : Indep (past X n) (MeasurableSpace.comap (X n) inferInstance) μ := by
    simpa only [iSup_singleton,past] using h
  exact indep_of_indep_of_le_left hh (measurable_const.indicator (measurableSet_alive_prefix X n)).comap_le

lemma integral_alive_increment {X : ℕ → Ω → ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ j,Measurable (X j)) (hi : iIndepFun X μ)
    (hint : ∀ j,Integrable (fun x => (X j x:ℝ)) μ) (n : ℕ) :
    (∫ x,(alive X n).indicator (fun x => 1-(X n x:ℝ)) x ∂μ)=
      μ.real (alive X n)*(1-∫ x,(X n x:ℝ) ∂μ) := by
  have hind := (alive_indep_next hX hi n).comp measurable_id
    (measurable_of_countable (fun k : ℕ => (1:ℝ)-k))
  have hf : Integrable ((alive X n).indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const 1).indicator (measurableSet_alive hX n)
  have hg : Integrable (fun x => (1:ℝ)-X n x) μ := (integrable_const 1).sub (hint n)
  have h := hind.integral_mul_eq_mul_integral hf.aestronglyMeasurable hg.aestronglyMeasurable
  change (∫ x,(alive X n).indicator (fun _ => (1:ℝ)) x*(1-X n x) ∂μ)=
    (∫ x,(alive X n).indicator (fun _ => (1:ℝ)) x ∂μ)*(∫ x,(1:ℝ)-X n x ∂μ) at h
  have he : (fun x => (alive X n).indicator (fun _ => (1:ℝ)) x*(1-X n x))=
      (alive X n).indicator (fun x => (1:ℝ)-X n x) := by
    funext x
    by_cases hx : x∈alive X n <;> simp [hx]
  rw [he] at h
  rw [integral_indicator_const (1:ℝ) (measurableSet_alive hX n),integral_sub (integrable_const 1) (hint n)] at h
  simpa only [smul_eq_mul,mul_one,integral_const,probReal_univ,one_smul] using h

theorem bounded_wald_bound {X : ℕ → Ω → ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ j,Measurable (X j)) (hi : iIndepFun X μ)
    (hint : ∀ j,Integrable (fun x => (X j x:ℝ)) μ) {m : ℝ}
    (hmean : ∀ j,(∫ x,(X j x:ℝ) ∂μ)=m) (n : ℕ) :
    (1-m)*(∑ j∈Finset.range n,μ.real (alive X j)) ≤ 1 := by
  have hint' (j : ℕ) : Integrable ((alive X j).indicator (fun x => 1-(X j x:ℝ))) μ :=
    ((integrable_const 1).sub (hint j)).indicator (measurableSet_alive hX j)
  have he : (∫ x,stoppedSum X n x ∂μ)=(1-m)*(∑ j∈Finset.range n,μ.real (alive X j)) := by
    unfold stoppedSum
    rw [integral_finsetSum _ (fun j _ => hint' j)]
    simp_rw [integral_alive_increment hX hi hint,hmean]
    rw [← Finset.sum_mul,mul_comm]
  rw [← he]
  have h := integral_mono (integrable_finsetSum _ (fun j _ => hint' j)) (integrable_const 1)
    (stoppedSum_le_one X n)
  simpa only [stoppedSum,integral_const,probReal_univ,one_smul] using h

lemma integral_alive_length {X : ℕ → Ω → ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ j,Measurable (X j)) (hi : iIndepFun X μ)
    (hint : ∀ j,Integrable (fun x => (X j x:ℝ)) μ) (n : ℕ) :
    (∫ x,(alive X n).indicator (fun x => 1+(X n x:ℝ)) x ∂μ)=
      μ.real (alive X n)*(1+∫ x,(X n x:ℝ) ∂μ) := by
  have hind := (alive_indep_next hX hi n).comp measurable_id
    (measurable_of_countable (fun k : ℕ => (1:ℝ)+k))
  have hf : Integrable ((alive X n).indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const 1).indicator (measurableSet_alive hX n)
  have hg : Integrable (fun x => (1:ℝ)+X n x) μ := (integrable_const 1).add (hint n)
  have h := hind.integral_mul_eq_mul_integral hf.aestronglyMeasurable hg.aestronglyMeasurable
  change (∫ x,(alive X n).indicator (fun _ => (1:ℝ)) x*(1+X n x) ∂μ)=
    (∫ x,(alive X n).indicator (fun _ => (1:ℝ)) x ∂μ)*(∫ x,(1:ℝ)+X n x ∂μ) at h
  have he : (fun x => (alive X n).indicator (fun _ => (1:ℝ)) x*(1+X n x))=
      (alive X n).indicator (fun x => (1:ℝ)+X n x) := by
    funext x
    by_cases hx : x∈alive X n <;> simp [hx]
  rw [he] at h
  rw [integral_indicator_const (1:ℝ) (measurableSet_alive hX n),integral_add (integrable_const 1) (hint n)] at h
  simpa only [smul_eq_mul,mul_one,integral_const,probReal_univ,one_smul] using h

def totalLength (X : ℕ → Ω → ℕ) (x : Ω) : ℝ≥0∞ :=
  ∑' j : ℕ,(alive X j).indicator (fun x => (1+(X j x:ℝ≥0∞))) x

lemma measurable_totalLength {X : ℕ → Ω → ℕ} (hX : ∀ j,Measurable (X j)) : Measurable (totalLength X) := by
  exact Measurable.tsum (fun j =>
    (measurable_const.add ((measurable_of_countable (fun k : ℕ => (k:ℝ≥0∞))).comp (hX j))).indicator
      (measurableSet_alive hX j))

lemma totalLength_expectation {X : ℕ → Ω → ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ j,Measurable (X j)) (hi : iIndepFun X μ)
    (hint : ∀ j,Integrable (fun x => (X j x:ℝ)) μ) {m : ℝ}
    (hmean : ∀ j,(∫ x,(X j x:ℝ) ∂μ)=m) (hm : m<1) :
    (∫⁻ x,totalLength X x ∂μ) ≤ ENNReal.ofReal ((1+m)/(1-m)) := by
  have hn : 0  ≤  m := by rw [← hmean 0]; exact integral_nonneg (fun _ => Nat.cast_nonneg _)
  have hb (n : ℕ) : (∑ j∈Finset.range n,μ.real (alive X j)) ≤ 1/(1-m) := by
    apply (le_div_iff₀ (sub_pos.mpr hm)).mpr
    simpa [mul_comm] using bounded_wald_bound hX hi hint hmean n
  have hs := summable_of_sum_range_le (fun j => (measureReal_nonneg : 0 ≤ μ.real (alive X j))) hb
  have hs' := hs.mul_right (1+m)
  have he (j : ℕ) : (∫⁻ x,(alive X j).indicator (fun x => (1+(X j x:ℝ≥0∞))) x ∂μ)=
      ENNReal.ofReal (μ.real (alive X j)*(1+m)) := by
    rw [← hmean j,← integral_alive_length hX hi hint]
    rw [ofReal_integral_eq_lintegral_ofReal
      (f := fun x => (alive X j).indicator (fun x => (1:ℝ)+(X j x:ℝ)) x)
      (((integrable_const 1).add (hint j)).indicator (measurableSet_alive hX j))
      (Eventually.of_forall (fun x => by
        change (0:ℝ)  ≤  (alive X j).indicator (fun x => (1:ℝ)+(X j x:ℝ)) x
        by_cases hx : x∈alive X j
        · rw [Set.indicator_of_mem hx]; positivity
        · rw [Set.indicator_of_notMem hx]))]
    apply lintegral_congr
    intro x
    by_cases hx : x∈alive X j
    · simp [hx,ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ 1) (Nat.cast_nonneg _)]
    · simp [hx]
  unfold totalLength
  rw [lintegral_tsum (f := fun j x => (alive X j).indicator (fun x => (1+(X j x:ℝ≥0∞))) x) (fun j =>
    ((measurable_const.add ((measurable_of_countable (fun k : ℕ => (k:ℝ≥0∞))).comp (hX j))).indicator
      (measurableSet_alive hX j)).aemeasurable)]
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg measureReal_nonneg (by linarith)) hs',
    hs.tsum_mul_right]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∑' j,μ.real (alive X j))*(1+m)  ≤  (1/(1-m))*(1+m) :=
      mul_le_mul_of_nonneg_right (hs.tsum_le_of_sum_range_le hb) (by linarith)
    _ = (1+m)/(1-m) := by ring

lemma totalLength_finite {X : ℕ → Ω → ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ j,Measurable (X j)) (hi : iIndepFun X μ)
    (hint : ∀ j,Integrable (fun x => (X j x:ℝ)) μ) {m : ℝ}
    (hmean : ∀ j,(∫ x,(X j x:ℝ) ∂μ)=m) (hm : m<1) :
    ∀ᵐ x ∂μ,totalLength X x<∞ :=
  ae_lt_top (measurable_totalLength hX)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (totalLength_expectation hX hi hint hmean hm))

omit [MeasurableSpace Ω] in
lemma hit_of_totalLength_finite {X : ℕ → Ω → ℕ} {x : Ω} (h : totalLength X x<∞) :
    ∃ n,x∉alive X n := by
  by_contra hh
  push Not at hh
  have hle : (∑' _j : ℕ,(1:ℝ≥0∞)) ≤ totalLength X x :=
    ENNReal.tsum_le_tsum (fun j => by simp only [Set.indicator_of_mem (hh j)]; exact le_self_add)
  have he : (∑' _j : ℕ,(1:ℝ≥0∞))=∞ := by simp
  rw [he] at hle
  exact (not_le_of_gt h) hle

lemma integrable_totalLength {X : ℕ → Ω → ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ j,Measurable (X j)) (hi : iIndepFun X μ)
    (hint : ∀ j,Integrable (fun x => (X j x:ℝ)) μ) {m : ℝ}
    (hmean : ∀ j,(∫ x,(X j x:ℝ) ∂μ)=m) (hm : m<1) :
    Integrable (fun x => (totalLength X x).toReal) μ :=
  (integrable_toReal_iff (measurable_totalLength hX).aemeasurable
    ((totalLength_finite hX hi hint hmean hm).mono (fun _ h => h.ne))).mpr
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (totalLength_expectation hX hi hint hmean hm))

omit [MeasurableSpace Ω] in
lemma alive_antitone (X : ℕ → Ω → ℕ) {n k : ℕ} (h : n ≤ k) : alive X k ⊆ alive X n :=
  fun _ hx j hj => hx j (hj.trans h)

def stopPredicate (X : ℕ → Ω → ℕ) (x : Ω) (n : ℕ) : Prop :=
  x∉alive X n ∨ ∀ k,x∈alive X k
omit [MeasurableSpace Ω] in
lemma stop_exists (X : ℕ → Ω → ℕ) (x : Ω) : ∃ n,stopPredicate X x n := by
  by_cases h : ∃ n,x∉alive X n
  · obtain ⟨n,hn⟩ := h; exact ⟨n,Or.inl hn⟩
  · exact ⟨0,Or.inr (by simpa only [not_exists,not_not] using h)⟩
def stopIndex (X : ℕ → Ω → ℕ) (x : Ω) : ℕ := Nat.find (stop_exists X x)

lemma measurable_stopIndex {X : ℕ → Ω → ℕ} (hX : ∀ j,Measurable (X j)) : Measurable (stopIndex X) := by
  apply measurable_find (stop_exists X)
  intro n
  simp only [stopPredicate,Set.ofPred_or,Set.ofPred_forall]
  exact (measurableSet_alive hX n).compl.union (MeasurableSet.iInter (fun k => measurableSet_alive hX k))

omit [MeasurableSpace Ω] in
lemma stop_spec {X : ℕ → Ω → ℕ} {x : Ω} (hx : ∃ n,x∉alive X n) :
    x∉alive X (stopIndex X x) ∧ ∀ k < stopIndex X x,x∈alive X k := by
  have hn : ¬∀ k,x∈alive X k := by simpa only [not_forall] using hx
  refine ⟨(Nat.find_spec (stop_exists X x)).resolve_right hn,?_⟩
  intro k hk
  have hh := Nat.find_min (stop_exists X x) hk
  exact not_not.mp (fun h => hh (Or.inl h))

omit [MeasurableSpace Ω] in
lemma stop_eq_zero_of_no_hit {X : ℕ → Ω → ℕ} {x : Ω} (hx : ∀ n,x∈alive X n) : stopIndex X x=0 :=
  Nat.eq_zero_of_le_zero (Nat.find_min' (stop_exists X x) (Or.inr hx))

omit [MeasurableSpace Ω] in
lemma walk_at_stop {X : ℕ → Ω → ℕ} {x : Ω} (hx : ∃ n,x∉alive X n) :
    walk X (stopIndex X x) x=1 := by
  obtain ⟨hn,hbefore⟩ := stop_spec hx
  have hpos : 0 < stopIndex X x := by
    by_contra hh
    have he : stopIndex X x=0 := by omega
    exact hn (he ▸ alive_zero X x)
  obtain ⟨n,hn'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have ha : x∈alive X n := hbefore n (by omega)
  have hneg : ¬walk X (n+1) x ≤ 0 := by
    intro h; exact hn (hn' ▸ alive_succ.mpr ⟨ha,h⟩)
  have hh := ha n le_rfl
  rw [hn',walk_succ] at *
  omega

omit [MeasurableSpace Ω] in
lemma totalLength_eq_sum {X : ℕ → Ω → ℕ} {x : Ω} (hx : ∃ n,x∉alive X n) :
    totalLength X x=∑ j∈Finset.range (stopIndex X x),(1+(X j x:ℝ≥0∞)) := by
  obtain ⟨hn,hbefore⟩ := stop_spec hx
  unfold totalLength
  rw [tsum_eq_sum (s := Finset.range (stopIndex X x)) (fun j hj => ?_)]
  · exact Finset.sum_congr rfl (fun j hj => Set.indicator_of_mem (hbefore j (Finset.mem_range.mp hj)) _)
  · exact Set.indicator_of_notMem (fun h => hn (alive_antitone X (by simpa only [Finset.mem_range,not_lt] using hj) h)) _

def stoppedLength (X : ℕ → Ω → ℕ) (x : Ω) : ℕ :=
  ∑ j∈Finset.range (stopIndex X x),(1+X j x)

omit [MeasurableSpace Ω] in
lemma totalLength_toReal (X : ℕ → Ω → ℕ) (x : Ω) :
    (totalLength X x).toReal=(stoppedLength X x:ℝ) := by
  by_cases hx : ∃ n,x∉alive X n
  · rw [totalLength_eq_sum hx]
    have he : (∑ j∈Finset.range (stopIndex X x),(1+(X j x:ℝ≥0∞)))=(stoppedLength X x:ℝ≥0∞) := by
      simp only [stoppedLength,Nat.cast_sum,Nat.cast_add,Nat.cast_one]
    rw [he,ENNReal.toReal_natCast]
  · have hn : ∀ n,x∈alive X n := by simpa only [not_exists,not_not] using hx
    have he : totalLength X x=∞ := by
      apply eq_top_iff.mpr
      calc
        ∞ = ∑' _j : ℕ,(1:ℝ≥0∞) := by simp
        _  ≤  totalLength X x := ENNReal.tsum_le_tsum (fun j => by
          simp only [Set.indicator_of_mem (hn j)]; exact le_self_add)
    simp only [he,ENNReal.toReal_top,stoppedLength,stop_eq_zero_of_no_hit hn,Finset.range_zero,
      Finset.sum_empty,Nat.cast_zero]

lemma integrable_stoppedLength {X : ℕ → Ω → ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ j,Measurable (X j)) (hi : iIndepFun X μ)
    (hint : ∀ j,Integrable (fun x => (X j x:ℝ)) μ) {m : ℝ}
    (hmean : ∀ j,(∫ x,(X j x:ℝ) ∂μ)=m) (hm : m<1) :
    Integrable (fun x => (stoppedLength X x:ℝ)) μ := by
  simpa only [totalLength_toReal] using integrable_totalLength hX hi hint hmean hm

end FKCRT.DefectHitting
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

instance instMeasurableSpaceListLetter : MeasurableSpace (List Letter) := ⊤
instance instMeasurableSingletonClassListLetter : MeasurableSingletonClass (List Letter) := ⟨fun _ => trivial⟩

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
open scoped BigOperators
namespace FKCRT.MapCycles
variable {α : Type*} [DecidableEq α]

lemma formPerm_cut (a b : α) (L R : List α)
    (h : (a :: (L ++ b :: R)).Nodup) :
    (a :: (L ++ b :: R)).formPerm =
      swap a b * (a :: L).formPerm * (b :: R).formPerm := by
  induction L generalizing a with
  | nil => simp
  | cons c L ih =>
    have hab : a ≠ b := fun he => h.notMem (by simp [he])
    have hcb : c ≠ b := fun he => h.of_cons.notMem (by simp [he])
    have hcomm : swap a c * swap c b = swap a b * swap a c := by
      rw [mul_swap_eq_swap_mul]
      simp [swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hcb)]
    simp only [List.cons_append, List.formPerm_cons_cons]
    rw [ih c h.of_cons]
    simp only [← mul_assoc]
    rw [hcomm]

lemma swap_mul_formPerm_cut (a b : α) (L R : List α)
    (h : (a :: (L ++ b :: R)).Nodup) :
    swap a b * (a :: (L ++ b :: R)).formPerm =
      (a :: L).formPerm * (b :: R).formPerm := by
  rw [formPerm_cut a b L R h]
  simp [← mul_assoc]

lemma sameCycle_formPerm_of_mem {l : List α} (hn : l.Nodup)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l) : l.formPerm.SameCycle x y := by
  rcases l with _ | ⟨a, _ | ⟨b, L⟩⟩
  · simp at hx
  · simp only [List.mem_singleton] at hx hy
    exact (hx.trans hy.symm).sameCycle _
  · apply (List.isCycle_formPerm hn (by simp)).sameCycle
    · exact (List.formPerm_apply_mem_ne_self_iff _ hn _ hx).mpr (by simp)
    · exact (List.formPerm_apply_mem_ne_self_iff _ hn _ hy).mpr (by simp)

lemma pow_eq_on_list (p : Perm α) (l : List α)
    (hp : ∀ x ∈ l, p x = l.formPerm x) {x : α} (hx : x ∈ l) (k : ℕ) :
    (p ^ k) x = (l.formPerm ^ k) x ∧ (p ^ k) x ∈ l := by
  induction k with
  | zero => exact ⟨rfl, hx⟩
  | succ k ih =>
    simp only [pow_succ', mul_apply]
    exact ⟨(hp _ ih.2).trans (congrArg l.formPerm ih.1),
      hp _ ih.2 ▸ l.formPerm_apply_mem_of_mem ih.2⟩

lemma sameCycle_of_list [Finite α] (p : Perm α) {l : List α} (hn : l.Nodup)
    (hp : ∀ x ∈ l, p x = l.formPerm x) {x y : α} (hx : x ∈ l) (hy : y ∈ l) :
    p.SameCycle x y := by
  obtain ⟨k,hk⟩ := (sameCycle_formPerm_of_mem hn hx hy).exists_nat_pow_eq
  exact ⟨k, by simpa using (pow_eq_on_list p l hp hx k).1.trans hk⟩

abbrev Orbits (p : Perm α) := Quotient (SameCycle.setoid p)

/-- A partition into nonempty cyclic lists counts all orbits, including fixed
points. The local action condition makes this independent of a chosen
representative of the quotient. -/
lemma card_orbits_eq_of_lists [Finite α] {β : Type*} [Finite β]
    (p : Perm α) (l : β → List α) (hn : ∀ i, (l i).Nodup)
    (hne : ∀ i, ∃ x, x ∈ l i)
    (hc : ∀ x, ∃! i, x ∈ l i)
    (hp : ∀ i x, x ∈ l i → p x = (l i).formPerm x) :
    Nat.card (Orbits p) = Nat.card β := by
  classical
  let idx : α → β := fun x => (hc x).choose
  have hm (x : α) : x ∈ l (idx x) := (hc x).choose_spec.1
  have hu {x : α} {i : β} (hi : x ∈ l i) : idx x = i :=
    ((hc x).choose_spec.2 i hi).symm
  have he {x y : α} : p.SameCycle x y ↔ idx x = idx y := by
    constructor
    · intro h
      obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
      have hh := (pow_eq_on_list p (l (idx x)) (hp (idx x)) (hm x) k).2
      rw [hk] at hh
      exact (hu hh).symm
    · intro h
      exact sameCycle_of_list p (hn (idx x)) (hp (idx x)) (hm x) (h ▸ hm y)
  let e : Orbits p ≃ β :=
    { toFun := Quotient.lift idx (fun _ _ h => he.mp h)
      invFun := fun i => Quotient.mk _ ((hne i).choose)
      left_inv := by
        intro q
        induction q using Quotient.inductionOn with
        | h x =>
          apply Quotient.sound
          apply he.mpr
          exact hu ((hne (idx x)).choose_spec)
      right_inv := by
        intro i
        exact hu ((hne i).choose_spec) }
  exact Nat.card_congr e

/-- Canonical cyclic list, retaining one-element fixed cycles. -/
def orbitList [Fintype α] (p : Perm α) (x : α) : List α :=
  if p x = x then [x] else p.toList x

lemma nodup_orbitList [Fintype α] (p : Perm α) (x : α) :
    (orbitList p x).Nodup := by
  unfold orbitList
  split_ifs <;> simp [nodup_toList]

lemma mem_orbitList [Fintype α] (p : Perm α) (x y : α) :
    y ∈ orbitList p x ↔ p.SameCycle x y := by
  classical
  unfold orbitList
  split_ifs with h
  · simp only [List.mem_singleton]
    exact ⟨fun he => (he.symm).sameCycle p,fun he => (he.eq_of_left h).symm⟩
  · simp [mem_toList_iff,h]

lemma orbitList_action [Fintype α] (p : Perm α) (x y : α)
    (hy : y ∈ orbitList p x) : p y = (orbitList p x).formPerm y := by
  classical
  have hxy := (mem_orbitList p x y).mp hy
  unfold orbitList
  split_ifs with h
  · have he := hxy.eq_of_left h
    subst y
    simpa using h
  · rw [formPerm_toList,hxy.cycleOf_apply]

/-- Splitting one part of a finite list partition into two consecutive,
nonempty pieces adds exactly one block, without discarding fixed points. -/
def splitFamily {β : Type*} [DecidableEq β] (l : β → List α) (i₀ : β)
    (L R : List α) : ({i : β // i ≠ i₀} ⊕ Bool) → List α
  | Sum.inl i => l i
  | Sum.inr false => L
  | Sum.inr true => R

omit [DecidableEq α] in
lemma splitFamily_partition {β : Type*} [DecidableEq β] (l : β → List α)
    (hn : ∀ i, (l i).Nodup) (hc : ∀ x, ∃! i, x ∈ l i)
    (i₀ : β) (L R : List α) (he : l i₀ = L ++ R) :
    ∀ x, ∃! i, x ∈ splitFamily l i₀ L R i := by
  intro x
  have hd : List.Disjoint L R := List.disjoint_iff_ne.mpr (List.nodup_append.mp (he ▸ hn i₀)).2.2
  have hoff {i : β} (hi : i ≠ i₀) (hx : x ∈ l i) : x ∉ L ∧ x ∉ R := by
    constructor <;> intro h
    all_goals
      have hh : x ∈ l i₀ := by rw [he]; simp [h]
      exact hi (((hc x).unique hx hh))
  have hinj : ∀ i j, x ∈ splitFamily l i₀ L R i →
      x ∈ splitFamily l i₀ L R j → i = j := by
    intro i j hi hj
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Subtype.ext ((hc x).unique hi hj))
      | inr b => cases b
                 · exact ((hoff i.property hi).1 hj).elim
                 · exact ((hoff i.property hi).2 hj).elim
    | inr b =>
      cases j with
      | inl j => cases b
                 · exact ((hoff j.property hj).1 hi).elim
                 · exact ((hoff j.property hj).2 hi).elim
      | inr c =>
        cases b <;> cases c
        · rfl
        · exact (List.disjoint_left.mp hd hi hj).elim
        · exact (List.disjoint_left.mp hd hj hi).elim
        · rfl
  obtain ⟨i,hi,_⟩ := hc x
  by_cases h : i = i₀
  · subst i
    rw [he,List.mem_append] at hi
    rcases hi with hi | hi
    · exact ⟨Sum.inr false,hi,fun j hj => hinj j _ hj hi⟩
    · exact ⟨Sum.inr true,hi,fun j hj => hinj j _ hj hi⟩
  · exact ⟨Sum.inl ⟨i,h⟩,hi,fun j hj => hinj j _ hj hi⟩

lemma card_orbits_cut [Finite α] {β : Type*} [Finite β]
    (p : Perm α) (l : β → List α) (hn : ∀ i, (l i).Nodup)
    (hne : ∀ i, ∃ x, x ∈ l i) (hc : ∀ x, ∃! i, x ∈ l i)
    (hp : ∀ i x, x ∈ l i → p x = (l i).formPerm x)
    (i₀ : β) (a b : α) (L R : List α)
    (he : l i₀ = (a :: L) ++ (b :: R)) :
    Nat.card (Orbits (swap a b * p)) = Nat.card (Orbits p) + 1 := by
  classical
  have hn₀ : ((a :: L) ++ (b :: R)).Nodup := he ▸ hn i₀
  have hn₁ := (List.nodup_append.mp hn₀).1
  have hn₂ := (List.nodup_append.mp hn₀).2.1
  have hd : List.Disjoint (a :: L) (b :: R) :=
    List.disjoint_iff_ne.mpr (List.nodup_append.mp hn₀).2.2
  have ha : a ∈ l i₀ := by simp [he]
  have hb : b ∈ l i₀ := by simp [he]
  let ll := splitFamily l i₀ (a :: L) (b :: R)
  have hnn (i) : (ll i).Nodup := by
    cases i with
    | inl i => exact hn i
    | inr c => cases c <;> assumption
  have hnee (i) : ∃ x, x ∈ ll i := by
    cases i with
    | inl i => exact hne i
    | inr c => cases c
               · exact ⟨a, List.mem_cons_self⟩
               · exact ⟨b, List.mem_cons_self⟩
  have hcc := splitFamily_partition l hn hc i₀ (a :: L) (b :: R) he
  have hpp (i) (x : α) (hx : x ∈ ll i) :
      (swap a b * p) x = (ll i).formPerm x := by
    cases i with
    | inl i =>
      have hpx : p x ∈ l i := by rw [hp i x hx]; exact List.formPerm_apply_mem_of_mem hx
      have hpa : p x ≠ a := fun h => i.property ((hc a).unique (h ▸ hpx) ha)
      have hpb : p x ≠ b := fun h => i.property ((hc b).unique (h ▸ hpx) hb)
      rw [mul_apply,swap_apply_of_ne_of_ne hpa hpb]
      exact hp i x hx
    | inr c =>
      have hcut := congrArg (fun u : Perm α => u x) (swap_mul_formPerm_cut a b L R hn₀)
      cases c
      · have hpx : p x = ((a :: L) ++ (b :: R)).formPerm x := by
          rw [← he]; exact hp i₀ x (by rw [he]; exact List.mem_append_left _ hx)
        have hxr : x ∉ b :: R := fun h => List.disjoint_left.mp hd hx h
        simpa only [ll,splitFamily,List.cons_append,mul_apply,hpx,List.formPerm_apply_of_notMem hxr] using hcut
      · have hpx : p x = ((a :: L) ++ (b :: R)).formPerm x := by
          rw [← he]; exact hp i₀ x (by rw [he]; exact List.mem_append_right _ hx)
        have hxl : (b :: R).formPerm x ∉ a :: L := fun h =>
          List.disjoint_left.mp hd h (List.formPerm_apply_mem_of_mem hx)
        simpa only [ll,splitFamily,List.cons_append,mul_apply,hpx,List.formPerm_apply_of_notMem hxl] using hcut
  rw [card_orbits_eq_of_lists (swap a b * p) ll hnn hnee hcc hpp,
    card_orbits_eq_of_lists p l hn hne hc hp]
  let : Fintype β := Fintype.ofFinite β
  simp only [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_bool]
  have hh' : Fintype.card {i : β // i ≠ i₀} = Fintype.card β - 1 := by simp
  rw [hh']
  have hpos : 0 < Fintype.card β := Fintype.card_pos_iff.mpr ⟨i₀⟩
  omega

lemma orbitList_eq_cons [Fintype α] (p : Perm α) (a : α) :
    ∃ L, orbitList p a = a :: L := by
  classical
  by_cases ha : p a = a
  · exact ⟨[], by simp [orbitList,ha]⟩
  have hs : a ∈ p.support := mem_support.mpr ha
  have h := p.toList_getElem_zero a hs
  cases hl : p.toList a with
  | nil => exact ((toList_eq_nil_iff.mp hl) hs).elim
  | cons c L =>
    simp only [hl,List.getElem_cons_zero] at h
    subst c
    exact ⟨L,by simp [orbitList,ha,hl]⟩

/-- Swapping two distinct members of one orbit cuts that orbit into two.
In particular one-element vertex/face cycles are not lost in the count. -/
theorem card_orbits_swap_of_sameCycle [Fintype α] (p : Perm α) {a b : α}
    (hab : a ≠ b) (hs : p.SameCycle a b) :
    Nat.card (Orbits (swap a b * p)) = Nat.card (Orbits p) + 1 := by
  classical
  let q₀ : Orbits p := Quotient.mk _ a
  let r : Orbits p → α := fun q => if q = q₀ then a else q.out
  have hr (q : Orbits p) : Quotient.mk _ (r q) = q := by
    dsimp [r]
    split_ifs with h
    · exact h.symm
    · exact Quotient.out_eq q
  let l : Orbits p → List α := fun q => orbitList p (r q)
  have hmem (x : α) (q : Orbits p) : x ∈ l q ↔ Quotient.mk _ x = q := by
    change x ∈ orbitList p (r q) ↔ _
    rw [mem_orbitList]
    calc
      p.SameCycle (r q) x ↔ Quotient.mk _ x = (Quotient.mk _ (r q) : Orbits p) :=
        ⟨fun h => Quotient.sound h.symm,fun h => (Quotient.exact h).symm⟩
      _ ↔ _ := by rw [hr q]
  have hc (x : α) : ∃! q, x ∈ l q := by
    refine ⟨Quotient.mk _ x,(hmem x _).mpr rfl,?_⟩
    exact fun q h => ((hmem x q).mp h).symm
  have hne (q : Orbits p) : ∃ x, x ∈ l q := ⟨r q,(hmem _ _).mpr (hr q)⟩
  obtain ⟨K,hK⟩ := orbitList_eq_cons p a
  have hb : b ∈ K := by
    have hh := (mem_orbitList p a b).mpr hs
    rw [hK,List.mem_cons] at hh
    exact hh.resolve_left (Ne.symm hab)
  obtain ⟨L,R,hR⟩ := List.append_of_mem hb
  apply card_orbits_cut p l (fun q => nodup_orbitList p (r q)) hne hc
    (fun q x hx => orbitList_action p (r q) x hx) q₀ a b L R
  simp only [l,r,ite_true,hK,hR,List.cons_append]

lemma sameCycle_swap_of_not_sameCycle [Fintype α] (p : Perm α) {a b : α}
    (hs : ¬ p.SameCycle a b) : (swap a b * p).SameCycle a b := by
  classical
  obtain ⟨L,hL⟩ := orbitList_eq_cons p a
  obtain ⟨R,hR⟩ := orbitList_eq_cons p b
  have hnL : (a :: L).Nodup := hL ▸ nodup_orbitList p a
  have hnR : (b :: R).Nodup := hR ▸ nodup_orbitList p b
  have hd : List.Disjoint (a :: L) (b :: R) := by
    apply List.disjoint_left.mpr
    intro x hx hy
    have hx' := (mem_orbitList p a x).mp (hL ▸ hx)
    have hy' := (mem_orbitList p b x).mp (hR ▸ hy)
    exact hs (hx'.trans hy'.symm)
  have hn : ((a :: L) ++ (b :: R)).Nodup := by
    exact List.nodup_append.mpr ⟨hnL,hnR,List.disjoint_iff_ne.mp hd⟩
  apply sameCycle_of_list (swap a b * p) hn ?_ (by simp) (by simp)
  intro x hx
  have he := congrArg (fun u : Perm α => u x) (formPerm_cut a b L R hn)
  simp only [mul_apply,List.cons_append] at he ⊢
  rw [he]
  congr 1
  rcases List.mem_append.mp hx with hx | hx
  · have hxr : x ∉ b :: R := fun hh => List.disjoint_left.mp hd hx hh
    rw [List.formPerm_apply_of_notMem hxr]
    simpa only [hL] using orbitList_action p a x (hL ▸ hx)
  · have hxl : (b :: R).formPerm x ∉ a :: L := fun hh =>
      List.disjoint_left.mp hd hh (List.formPerm_apply_mem_of_mem hx)
    rw [List.formPerm_apply_of_notMem hxl]
    simpa only [hR] using orbitList_action p b x (hR ▸ hx)

/-- Swapping members of distinct orbits joins precisely those two orbits. -/
theorem card_orbits_swap_of_not_sameCycle [Fintype α] (p : Perm α) {a b : α}
    (hs : ¬ p.SameCycle a b) :
    Nat.card (Orbits (swap a b * p)) + 1 = Nat.card (Orbits p) := by
  have hab : a ≠ b := fun h => hs (h.sameCycle p)
  have h := card_orbits_swap_of_sameCycle (swap a b * p) hab
    (sameCycle_swap_of_not_sameCycle p hs)
  simpa only [← mul_assoc,swap_mul_self,one_mul] using h.symm

/-- Each edge transposition changes Euler's orbit count by exactly one. -/
theorem card_orbits_swap_le [Fintype α] (p : Perm α) (a b : α) :
    Nat.card (Orbits (swap a b * p)) ≤ Nat.card (Orbits p) + 1 := by
  classical
  by_cases hab : a = b
  · subst b
    have he : swap a a * p = p := by ext x; simp
    rw [he]
    omega
  by_cases h : p.SameCycle a b
  · exact (card_orbits_swap_of_sameCycle p hab h).le
  · have hh := card_orbits_swap_of_not_sameCycle p h
    omega

end FKCRT.MapCycles
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_GraphWedge
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal
namespace FKCRT.GraphWedge
variable {A B V : Type*} (G : SimpleGraph A) (K : SimpleGraph B) (H : SimpleGraph V)

/-- Combinatorial data of an actual one-vertex union. Distances are not
part of these hypotheses; they are derived from the adjacency data below. -/
structure Data where
  left : G→g H
  right : K→g H
  poleLeft : A
  poleRight : B
  shared : left poleLeft=right poleRight
  retractLeft : V→A
  retractRight : V→B
  left_left : ∀ x,retractLeft (left x)=x
  right_right : ∀ y,retractRight (right y)=y
  right_left : ∀ x,retractRight (left x)=poleRight
  left_right : ∀ y,retractLeft (right y)=poleLeft
  edge : ∀ {u v},H.Adj u v →
    (G.Adj (retractLeft u) (retractLeft v) ∧ retractRight u=retractRight v) ∨
    (retractLeft u=retractLeft v ∧ K.Adj (retractRight u) (retractRight v))

end FKCRT.GraphWedge
end


noncomputable section
open Equiv Equiv.Perm
namespace FKCRT.PermutationWedge
open MapCycles
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α] [Fintype α]

abbrev Vertex (p : Perm α) := Quotient (SameCycle.setoid p)
def vertex (p : Perm α) (d : α) : Vertex p := Quotient.mk _ d

def dartGraph (e p : Perm α) : SimpleGraph (Vertex p) :=
  SimpleGraph.fromRel (fun v w => ∃ d,vertex p d=v ∧ vertex p (e d)=w)

end FKCRT.PermutationWedge
end


noncomputable section
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT.Chords
variable {N : ℕ}

abbrev Opener (a : Perm (Fin N)) := { i : Fin N // i < a i }

def Cross (a : Perm (Fin N)) (x y : Opener a) : Prop :=
  (x.val < y.val ∧ y.val < a x.val ∧ a x.val < a y.val) ∨
  (y.val < x.val ∧ x.val < a y.val ∧ a y.val < a x.val)

def graph (a : Perm (Fin N)) : SimpleGraph (Opener a) where
  Adj := Cross a
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by intro x; simp [Cross]⟩

def Inside (a : Perm (Fin N)) (f x : Opener a) : Prop :=
  f.val < x.val ∧ a x.val < a f.val

lemma opener_endpoints_ne (a : Perm (Fin N)) (ha : Function.Involutive a)
    (x y : Opener a) (hxy : x≠y) :
    x.val≠y.val ∧ x.val≠a y.val ∧ a x.val≠y.val ∧ a x.val≠a y.val := by
  have h1 : x.val≠y.val := fun h => hxy (Subtype.ext h)
  have h2 : x.val≠a y.val := by
    intro h
    have hx := x.property
    have hy := y.property
    rw [h,ha] at hx
    exact (not_lt_of_ge hy.le) hx
  have h3 : a x.val≠y.val := by
    intro h
    have hh : x.val=a y.val := by rw [← h,ha]
    exact h2 hh
  exact ⟨h1,h2,h3,fun h => h1 (a.injective h)⟩

/-- A chord which crosses a chord strictly inside a third chord must either
be inside the third chord or cross it. Endpoint disjointness is explicit. -/
lemma inside_propagates (a : Perm (Fin N)) (ha : Function.Involutive a)
    (f x y : Opener a) (hyf : y≠f) (hc : Cross a x y)
    (hn : ¬Cross a f y) (hx : Inside a f x) : Inside a f y := by
  obtain ⟨h1,h2,h3,h4⟩ := opener_endpoints_ne a ha y f hyf
  have hp := y.property
  unfold Cross at hc hn
  unfold Inside at hx ⊢
  have hv1 := Fin.val_ne_of_ne h1
  have hv2 := Fin.val_ne_of_ne h2
  have hv3 := Fin.val_ne_of_ne h3
  have hv4 := Fin.val_ne_of_ne h4
  simp only [Fin.lt_def] at hc hn hx hp ⊢
  omega

/-- A chord outside the root crossing component has no root-component
endpoint in its interior. This is the algebraic corner-separation lemma:
it requires neither a Jordan-curve assumption nor a stipulated block law. -/
theorem component_gap (a : Perm (Fin N)) (ha : Function.Involutive a)
    (r f : Opener a) (hroot : r.val≤f.val) (hf : ¬(graph a).Reachable r f)
    (x : Opener a) (hx : (graph a).Reachable r x) :
    ¬(f.val < x.val ∧ x.val < a f.val) ∧
      ¬(f.val < a x.val ∧ a x.val < a f.val) := by
  have hne (y : Opener a) (hy : (graph a).Reachable r y) : y≠f := by
    rintro rfl
    exact hf hy
  have hno (y : Opener a) (hy : (graph a).Reachable r y) : ¬Cross a f y := by
    intro h
    exact hf (hy.trans (show (graph a).Adj y f from Or.symm h).reachable)
  have hinside : ¬Inside a f x := by
    have hp := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hx
    induction hp with
    | refl => exact fun h => not_lt_of_ge hroot h.1
    | @tail y z hp hadj ih =>
      intro hz
      have hy : (graph a).Reachable r y := (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hp
      exact ih hy (inside_propagates a ha f z y (hne y hy) (Or.symm hadj) (hno y hy) hz)
  have hnc := hno x hx
  obtain ⟨h1,h2,h3,h4⟩ := opener_endpoints_ne a ha x f (hne x hx)
  have hp := x.property
  have hv1 := Fin.val_ne_of_ne h1
  have hv2 := Fin.val_ne_of_ne h2
  have hv3 := Fin.val_ne_of_ne h3
  have hv4 := Fin.val_ne_of_ne h4
  unfold Cross at hnc
  unfold Inside at hinside
  simp only [Fin.lt_def] at hnc hinside hp ⊢
  omega

/-- Actual endpoint set of the root crossing component. -/
def componentDarts (a : Perm (Fin N)) (r : Opener a) : Finset (Fin N) :=
  Finset.univ.filter (fun d => ∃ x : Opener a, (graph a).Reachable r x ∧ (d=x.val ∨ d=a x.val))

lemma mem_componentDarts (a : Perm (Fin N)) (r : Opener a) (d : Fin N) :
    d∈componentDarts a r ↔ ∃ x : Opener a,(graph a).Reachable r x ∧ (d=x.val ∨ d=a x.val) := by
  classical
  simp [componentDarts]

lemma external_not_component (a : Perm (Fin N)) (ha : Function.Involutive a)
    (r f : Opener a) (hf : ¬(graph a).Reachable r f) :
    f.val∉componentDarts a r ∧ a f.val∉componentDarts a r := by
  have hne (x : Opener a) (hx : (graph a).Reachable r x) : f≠x := by
    rintro rfl
    exact hf hx
  constructor
  · intro h
    obtain ⟨x,hx,he|he⟩ := (mem_componentDarts a r _).mp h
    · exact (opener_endpoints_ne a ha f x (hne x hx)).1 he
    · exact (opener_endpoints_ne a ha f x (hne x hx)).2.1 he
  · intro h
    obtain ⟨x,hx,he|he⟩ := (mem_componentDarts a r _).mp h
    · exact (opener_endpoints_ne a ha f x (hne x hx)).2.2.1 he
    · exact (opener_endpoints_ne a ha f x (hne x hx)).2.2.2 he

/-- The gap index is determined solely by the ordered root-component darts.
The two ends of every exterior matched pair have the same gap index. -/
def gapIndex (a : Perm (Fin N)) (r : Opener a) (d : Fin N) : ℕ :=
  ((componentDarts a r).filter (·<d)).card

theorem exterior_same_gap (a : Perm (Fin N)) (ha : Function.Involutive a)
    (r f : Opener a) (hroot : r.val≤f.val) (hf : ¬(graph a).Reachable r f) :
    gapIndex a r f.val=gapIndex a r (a f.val) := by
  have hn := external_not_component a ha r f hf
  unfold gapIndex
  congr 1
  ext d
  simp only [Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1,h.2.trans f.property⟩
  · rintro ⟨hd,hlt⟩
    refine ⟨hd,?_⟩
    have hdne : d≠f.val := fun h => hn.1 (h ▸ hd)
    by_contra h
    have hfd : f.val < d := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hdne)
    obtain ⟨x,hx,rfl|rfl⟩ := (mem_componentDarts a r d).mp hd
    · exact (component_gap a ha r f hroot hf x hx).1 ⟨hfd,hlt⟩
    · exact (component_gap a ha r f hroot hf x hx).2 ⟨hfd,hlt⟩

end FKCRT.Chords
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_Noncrossing
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Equiv Equiv.Perm
open scoped BigOperators
namespace FKCRT.MapCycles
variable {α : Type*} [DecidableEq α]

/-- Ordered stack matching, with unpaired positions allowed. The skipped
positions will be endpoints of the other colour in the map tour. -/
inductive Arches : List α → List (α × α) → Prop
  | nil : Arches [] []
  | skip (a : α) {l E} : Arches l E → Arches (a :: l) E
  | pair (a b : α) {L R E F} : Arches L E → Arches R F →
      Arches (a :: (L ++ b :: R)) ((a,b) :: (E ++ F))

/-- Left transpositions in traversal order. -/
def turns : List (α × α) → Perm α
  | [] => 1
  | (a,b) :: E => turns E * swap a b

@[simp] lemma turns_nil : turns ([] : List (α × α)) = 1 := rfl
@[simp] lemma turns_cons (e : α × α) (E) :
    turns (e :: E) = turns E * swap e.1 e.2 := by cases e; rfl

lemma turns_append (E F : List (α × α)) :
    turns (E ++ F) = turns F * turns E := by
  induction E with
  | nil => simp
  | cons e E ih => simp only [List.cons_append,turns_cons,ih,mul_assoc]

omit [DecidableEq α] in
lemma Arches.endpoints {l : List α} {E} (h : Arches l E) :
    ∀ e ∈ E, e.1 ∈ l ∧ e.2 ∈ l := by
  induction h with
  | nil => simp
  | skip a h ih =>
    intro e he
    exact ⟨List.mem_cons_of_mem _ (ih e he).1,List.mem_cons_of_mem _ (ih e he).2⟩
  | pair a b hL hR ihL ihR =>
    intro e he
    rcases List.mem_cons.mp he with he | he
    · subst e
      simp
    · rcases List.mem_append.mp he with he | he
      · exact ⟨by simp [(ihL e he).1],by simp [(ihL e he).2]⟩
      · exact ⟨by simp [(ihR e he).1],by simp [(ihR e he).2]⟩

lemma turns_fixed (E : List (α × α)) {x : α}
    (hx : ∀ e ∈ E, x ≠ e.1 ∧ x ≠ e.2) : turns E x = x := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    rw [turns_cons,mul_apply,swap_apply_of_ne_of_ne (hx e List.mem_cons_self).1
      (hx e List.mem_cons_self).2]
    exact ih (fun e he => hx e (List.mem_cons_of_mem _ he))

lemma Arches.turns_fixed {l : List α} {E} (h : Arches l E) {x : α} (hx : x ∉ l) :
    turns E x = x := by
  apply FKCRT.MapCycles.turns_fixed
  intro e he
  exact ⟨fun hh => hx (hh ▸ (h.endpoints e he).1),
    fun hh => hx (hh ▸ (h.endpoints e he).2)⟩

lemma formPerm_append_comm (L R : List α) (hn : (L ++ R).Nodup) :
    (L ++ R).formPerm = (R ++ L).formPerm := by
  have h : (L ++ R).rotate L.length = R ++ L := by simp
  rw [← h,List.formPerm_rotate _ hn]

lemma cut_local_action (p : Perm α) (a b : α) (L R : List α)
    (hn : ((a :: L) ++ (b :: R)).Nodup)
    (hp : ∀ x ∈ (a :: L) ++ (b :: R), p x = ((a :: L) ++ (b :: R)).formPerm x) :
    (∀ x ∈ a :: L, (swap a b * p) x = (a :: L).formPerm x) ∧
    (∀ x ∈ b :: R, (swap a b * p) x = (b :: R).formPerm x) := by
  have hd : List.Disjoint (a :: L) (b :: R) :=
    List.disjoint_iff_ne.mpr (List.nodup_append.mp hn).2.2
  constructor
  · intro x hx
    have hxr : x ∉ b :: R := fun hh => List.disjoint_left.mp hd hx hh
    have hh := congrArg (fun u : Perm α => u x) (swap_mul_formPerm_cut a b L R hn)
    simpa only [mul_apply,hp x (List.mem_append_left _ hx),List.cons_append,
      List.formPerm_apply_of_notMem hxr] using hh
  · intro x hx
    have hxl : (b :: R).formPerm x ∉ a :: L := fun hh =>
      List.disjoint_left.mp hd hh (List.formPerm_apply_mem_of_mem hx)
    have hh := congrArg (fun u : Perm α => u x) (swap_mul_formPerm_cut a b L R hn)
    simpa only [mul_apply,hp x (List.mem_append_right _ hx),List.cons_append,
      List.formPerm_apply_of_notMem hxl] using hh

/-- Stack/noncrossing chords attain the maximum possible cycle count.
The unused initial string is arbitrary, so this also handles skipped darts
and the end/start seam of a rooted tour. -/
theorem Arches.card_orbits_turns [Fintype α] {l : List α} {E}
    (h : Arches l E) (Z : List α) (p : Perm α)
    (hn : (Z ++ l).Nodup)
    (hp : ∀ x ∈ Z ++ l, p x = (Z ++ l).formPerm x) :
    Nat.card (Orbits (turns E * p)) = Nat.card (Orbits p) + E.length := by
  induction h generalizing Z p with
  | nil => simp
  | @skip a l E h ih =>
    have he : Z ++ a :: l = (Z ++ [a]) ++ l := by simp
    exact ih (Z ++ [a]) p (he ▸ hn) (by simpa only [he] using hp)
  | @pair a b L R E F hL hR ihL ihR =>
    let C := (a :: L) ++ (b :: (R ++ Z))
    have hC : C.Nodup := by
      change ((a :: L) ++ (b :: (R ++ Z))).Nodup
      simpa only [List.cons_append,List.append_assoc] using
        (List.nodup_append_comm.mp hn)
    have he : (Z ++ a :: (L ++ b :: R)).formPerm = C.formPerm := by
      rw [formPerm_append_comm _ _ hn]
      simp only [C,List.cons_append,List.append_assoc]
    have hpC (x : α) (hx : x ∈ C) : p x = C.formPerm x := by
      rw [← he]
      apply hp
      simpa only [C,List.mem_append,List.mem_cons,or_assoc,or_comm,or_left_comm] using hx
    have hab : a ≠ b := fun h => hC.notMem (by simp [h])
    have hsame : p.SameCycle a b := sameCycle_of_list p hC hpC (by simp [C]) (by simp [C])
    have hzero := card_orbits_swap_of_sameCycle p hab hsame
    have hcut := cut_local_action p a b L (R ++ Z) hC hpC
    have hnL : ([a] ++ L).Nodup := (List.nodup_append.mp hC).1
    have hE := ihL [a] (swap a b * p) hnL hcut.1
    have hnR : ((Z ++ [b]) ++ R).Nodup := by
      have ht := (List.nodup_append.mp hC).2.1
      have hh : (b :: (R ++ Z)) = (b :: R) ++ Z := by simp
      rw [hh] at ht
      simpa only [List.append_assoc,List.singleton_append] using
        (List.nodup_append_comm.mp ht)
    have hother (x : α) (hx : x ∈ (Z ++ [b]) ++ R) :
        (turns E * (swap a b * p)) x = ((Z ++ [b]) ++ R).formPerm x := by
      have hxR : x ∈ b :: (R ++ Z) := by
        simpa only [List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,false_or,or_assoc,or_comm,
          or_left_comm] using hx
      have hpx := hcut.2 x hxR
      have hpxR : (swap a b * p) x ∈ b :: (R ++ Z) := by
        rw [hpx]; exact List.formPerm_apply_mem_of_mem hxR
      have hnLR := (List.nodup_append.mp hC).2.2
      have hnot : (swap a b * p) x ∉ L := fun hh =>
        hnLR _ (List.mem_cons_of_mem _ hh) _ hpxR rfl
      rw [mul_apply,hL.turns_fixed hnot,hpx]
      have ht : (Z ++ (b :: R)).Nodup := by simpa using hnR
      have hh := formPerm_append_comm Z (b :: R) ht
      simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
        (congrArg (fun u : Perm α => u x) hh).symm
    have hF := ihR (Z ++ [b]) (turns E * (swap a b * p)) hnR hother
    simp only [turns_cons,turns_append,List.length_cons,List.length_append]
    rw [mul_assoc,mul_assoc,hF,hE,hzero]
    omega

end FKCRT.MapCycles
end


noncomputable section
open List
namespace FKCRT.MapCycles
variable {α : Type*}

lemma Arches.append {l r : List α} {E F : List (α×α)}
    (h : Arches l E) (h' : Arches r F) : Arches (l++r) (E++F) := by
  induction h with
  | nil => simpa using h'
  | skip a h ih => simpa using Arches.skip a ih
  | pair a b hL hR ihL ihR =>
    simpa only [List.cons_append,List.append_assoc] using Arches.pair a b hL ihR

lemma Arches.empty (l : List α) : Arches l [] := by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .skip a ih

lemma cons_sublist_split {a : α} {l r : List α} (h : a::l<+r) :
    ∃ s t,r=s++a::t ∧ l<+t := by
  induction r with
  | nil => simp at h
  | cons b r ih =>
    cases h with
    | cons _ h =>
      obtain ⟨s,t,rfl,ht⟩ := ih h
      exact ⟨b::s,t,rfl,ht⟩
    | cons_cons _ h => exact ⟨[],r,rfl,h⟩

lemma Arches.mono {l r : List α} {E : List (α×α)} (h : Arches l E)
    (hlr : l<+r) : Arches r E := by
  induction h generalizing r with
  | nil => exact Arches.empty r
  | skip a h ih => exact ih (List.sublist_of_cons_sublist hlr)
  | pair a b hL hR ihL ihR =>
    obtain ⟨S,T,rfl,hT⟩ := cons_sublist_split hlr
    obtain ⟨U,V,rfl,hU,hV⟩ := List.append_sublist_iff.mp hT
    obtain ⟨Q,R,rfl,hR'⟩ := cons_sublist_split hV
    have hu := (ihL hU).append (Arches.empty Q)
    have hp := Arches.pair a b (by simpa using hu) (ihR hR')
    have hf := (Arches.empty S).append hp
    simpa only [List.nil_append,List.append_nil,List.append_assoc] using hf

/-- Flatten the pair endpoints without imposing an artificial pair order. -/
def endpoints (E : List (α×α)) : List α := E.flatMap (fun e => [e.1,e.2])

@[simp] lemma endpoints_nil : endpoints ([] : List (α×α))=[] := rfl
@[simp] lemma endpoints_cons (e : α×α) (E : List (α×α)) :
    endpoints (e::E)=e.1::e.2::endpoints E := rfl
lemma endpoints_append (E F : List (α×α)) : endpoints (E++F)=endpoints E++endpoints F := by
  simp [endpoints]

/-- Every Dyck path, on an arbitrary ordered list of positions, has a complete
noncrossing arch pairing. This is a constructive existence statement, not a
planarity assumption on a map. -/
theorem dyck_arches (p : DyckWord) (l : List α) (f : α→DyckStep)
    (hl : l.map f=p.toList) :
    ∃ E : List (α×α), Arches l E ∧ (endpoints E).Perm l ∧
      ∀ e∈E,f e.1=.U ∧ f e.2=.D := by
  induction hp : p.semilength using Nat.strong_induction_on generalizing p l with
  | h n ih =>
    by_cases hz : p=0
    · subst p
      have hm : l.map f=[] := hl
      have hn : l=[] := List.map_eq_nil_iff.mp hm
      subst l
      exact ⟨[],.nil,.refl _,by simp⟩
    · have hdec := p.nest_insidePart_add_outsidePart hz
      have he : p.toList = DyckStep.U::(p.insidePart.toList++DyckStep.D::p.outsidePart.toList) := by
        have hh := (congrArg DyckWord.toList hdec).symm
        change p.toList = ([DyckStep.U]++p.insidePart.toList++[DyckStep.D])++p.outsidePart.toList at hh
        simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using hh
      cases l with
      | nil => rw [he] at hl; simp at hl
      | cons a l =>
        rw [he,List.map_cons,List.cons.injEq] at hl
        obtain ⟨ha,hl⟩ := hl
        have hlen : p.insidePart.toList.length<l.length := by
          have hc := congrArg List.length hl
          simp only [List.length_map,List.length_append,List.length_cons] at hc
          omega
        let j := p.insidePart.toList.length
        let L := l.take j
        let b := l[j]
        let R := l.drop (j+1)
        have hl' : l=L++b::R := by
          dsimp [L,b,R,j]
          rw [← List.drop_eq_getElem_cons hlen,List.take_append_drop]
        have hL : L.map f=p.insidePart.toList := by
          dsimp [L,j]
          rw [List.map_take,hl,List.take_append_of_le_length (by rfl)]
          simp
        have hBR : (b::R).map f=DyckStep.D::p.outsidePart.toList := by
          rw [hl',List.map_append,hL] at hl
          exact List.append_cancel_left hl
        simp only [List.map_cons,List.cons.injEq] at hBR
        obtain ⟨hb,hR⟩ := hBR
        obtain ⟨E,hE,hEp,hEf⟩ := ih p.insidePart.semilength
          (by rw [← hp]; exact p.semilength_insidePart_lt hz) _ _ hL rfl
        obtain ⟨F,hF,hFp,hFf⟩ := ih p.outsidePart.semilength
          (by rw [← hp]; exact p.semilength_outsidePart_lt hz) _ _ hR rfl
        refine ⟨(a,b)::(E++F),?_,?_,?_⟩
        · rw [hl']; exact Arches.pair a b hE hF
        · rw [endpoints_cons,endpoints_append,hl']
          have hh := hEp.append hFp
          exact (hh.cons b |>.cons a).trans (List.Perm.cons a (List.perm_middle.symm))
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact ⟨ha,hb⟩
          · rcases List.mem_append.mp he with he | he
            · exact hEf e he
            · exact hFf e he

end FKCRT.MapCycles
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
lemma mem_endpoints {x : α} {E : List (α×α)} :
    x∈endpoints E ↔ ∃ e∈E,x=e.1 ∨ x=e.2 := by
  simp [endpoints,List.mem_flatMap]

lemma turns_fixed_of_notMem {E : List (α×α)} {x : α} (h : x∉endpoints E) :
    turns E x=x := by
  apply turns_fixed
  intro e he
  exact ⟨fun hh => h (mem_endpoints.mpr ⟨e,he,Or.inl hh⟩),
    fun hh => h (mem_endpoints.mpr ⟨e,he,Or.inr hh⟩)⟩

lemma turns_pair {E : List (α×α)} (hn : (endpoints E).Nodup) :
    ∀ e∈E,turns E e.1=e.2 ∧ turns E e.2=e.1 := by
  induction E with
  | nil => simp
  | cons e E ih =>
    obtain ⟨a,b⟩ := e
    simp only [endpoints_cons,List.nodup_cons] at hn
    have ha : a∉endpoints E := fun h => hn.1 (List.mem_cons_of_mem _ h)
    have hb : b∉endpoints E := hn.2.1
    intro e he
    rcases List.mem_cons.mp he with he | he
    · subst e
      constructor
      · rw [turns_cons,mul_apply,swap_apply_left,turns_fixed_of_notMem hb]
      · rw [turns_cons,mul_apply,swap_apply_right,turns_fixed_of_notMem ha]
    · have h1 := mem_endpoints.mpr ⟨e,he,Or.inl rfl⟩
      have h2 := mem_endpoints.mpr ⟨e,he,Or.inr rfl⟩
      have h1a : e.1≠a := fun hh => ha (hh ▸ h1)
      have h1b : e.1≠b := fun hh => hb (hh ▸ h1)
      have h2a : e.2≠a := fun hh => ha (hh ▸ h2)
      have h2b : e.2≠b := fun hh => hb (hh ▸ h2)
      simpa only [turns_cons,mul_apply,swap_apply_of_ne_of_ne h1a h1b,
        swap_apply_of_ne_of_ne h2a h2b] using ih hn.2.2 e he

omit [DecidableEq α] in
lemma endpoints_pair_ne {E : List (α×α)} (hn : (endpoints E).Nodup)
    {e : α×α} (he : e∈E) : e.1≠e.2 := by
  have hp : [e.1,e.2]<+endpoints E := by
    obtain ⟨L,R,rfl⟩ := List.mem_iff_append.mp he
    simp only [endpoints_append,endpoints_cons]
    exact (show [e.1,e.2] <+ [e.1,e.2]++endpoints R from List.sublist_append_left _ _).trans
      (show e.1::e.2::endpoints R <+ endpoints L++e.1::e.2::endpoints R from List.sublist_append_right _ _)
  have hh := hn.sublist hp
  simpa using hh

lemma turns_involutive {E : List (α×α)} (hn : (endpoints E).Nodup) :
    Function.Involutive (turns E) := by
  intro x
  by_cases hx : x∈endpoints E
  · obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hx
    · rw [(turns_pair hn e he).1,(turns_pair hn e he).2]
    · rw [(turns_pair hn e he).2,(turns_pair hn e he).1]
  · rw [turns_fixed_of_notMem hx,turns_fixed_of_notMem hx]

lemma turns_self {E : List (α×α)} (hn : (endpoints E).Nodup) : turns E*turns E=1 := by
  apply Equiv.ext
  exact turns_involutive hn

lemma turns_eq_self_iff {E : List (α×α)} (hn : (endpoints E).Nodup) (x : α) :
    turns E x=x ↔ x∉endpoints E := by
  constructor
  · intro h hx
    obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hx
    · exact endpoints_pair_ne hn he (h.symm.trans (turns_pair hn e he).1)
    · exact endpoints_pair_ne hn he ((turns_pair hn e he).2.symm.trans h)
  · exact turns_fixed_of_notMem

lemma turns_sublist_apply {E F : List (α×α)} (hn : (endpoints F).Nodup)
    (hEF : E<+F) {x : α} (hx : x∈endpoints E) : turns E x=turns F x := by
  have hs : (endpoints E)<+(endpoints F) := hEF.flatMap _
  have he := hn.sublist hs
  obtain ⟨e,he',rfl|rfl⟩ := mem_endpoints.mp hx
  · rw [(turns_pair he e he').1,(turns_pair hn e (hEF.subset he')).1]
  · rw [(turns_pair he e he').2,(turns_pair hn e (hEF.subset he')).2]

end FKCRT.MapCycles
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

lemma orbit_eq_iff {n : ℕ} (s : Equiv.Perm (Dart n)) (d e : Dart n) :
    orbit s d=orbit s e ↔ s.SameCycle d e := Quotient.eq

lemma orbit_perm {n : ℕ} (s : Equiv.Perm (Dart n)) (d : Dart n) :
    orbit s (s d)=orbit s d := by
  apply Quotient.sound
  exact (Equiv.Perm.sameCycle_apply_left).2 (Equiv.Perm.SameCycle.refl s d)

lemma closed_of_sameCycle {n : ℕ} {s : Equiv.Perm (Dart n)} {P : Dart n → Prop}
    (hs : ∀ d,P d → P (s d)) {d e : Dart n} (hd : P d) (h : s.SameCycle d e) : P e := by
  obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
  have hp (j : ℕ) : P ((s^j) d) := by
    induction j with
    | zero => simpa using hd
    | succ j ih => simpa only [pow_succ',Equiv.Perm.mul_apply] using hs _ ih
  exact hk ▸ hp k

/-- Graph connectivity propagates a dart property through the two generating
permutations. This is the precise permutation form of connected rooted-map
rigidity, including loops and repeated edges. -/
lemma connected_dart_induction {n : ℕ} {a s : Equiv.Perm (Dart n)}
    (ha : Function.Involutive a) (hc : (spanningGraph a s univ).Connected)
    {P : Dart n → Prop} {d₀ : Dart n} (h₀ : P d₀)
    (haP : ∀ d,P d → P (a d)) (hsP : ∀ d,P d → P (s d)) : ∀ d,P d := by
  have hcycle {d e : Dart n} (hd : P d) (he : orbit s d=orbit s e) : P e :=
    closed_of_sameCycle hsP hd ((orbit_eq_iff ..).1 he)
  have hstep {v w : Orbit s} (h : (spanningGraph a s univ).Adj v w)
      (hv : ∀ d,orbit s d=v → P d) : ∀ d,orbit s d=w → P d := by
    rcases h.2 with ⟨d,_,hd,he⟩ | ⟨d,_,he,hd⟩
    · intro e he'
      exact hcycle (haP d (hv d hd)) (he.trans he'.symm)
    · intro e he'
      have hh := haP (a d) (hv (a d) hd)
      rw [ha d] at hh
      exact hcycle hh (he.trans he'.symm)
  have hall (v : Orbit s) : ∀ d,orbit s d=v → P d := by
    have hp := (SimpleGraph.reachable_iff_reflTransGen ..).1 (hc (orbit s d₀) v)
    induction hp with
    | refl => exact fun d hd => hcycle h₀ hd.symm
    | tail hp hadj ih => exact hstep hadj ih
  exact fun d => hall (orbit s d) d rfl

end FKCRT
end


noncomputable section
open Set Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT.MapFinite

abbrev CycleQuot {α : Type*} (s : Equiv.Perm α) := Quotient (Equiv.Perm.SameCycle.setoid s)

instance instFintypeCycleQuotOfFinite {α : Type*} [Finite α] (s : Equiv.Perm α) : Fintype (CycleQuot s) := Fintype.ofFinite _

lemma sameCycle_involution {α : Type*} [Finite α] (s : Equiv.Perm α)
    (hs : Function.Involutive s) (x y : α) : s.SameCycle x y ↔ y=x ∨ y=s x := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
    rw [← hk]
    clear h hk y
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      rcases ih with he | he
      · exact Or.inr (congrArg s he)
      · exact Or.inl ((congrArg s he).trans (hs x))
  · intro h
    rcases h with h | h
    · simpa only [h] using Equiv.Perm.SameCycle.refl s x
    · rw [h]
      exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl s x)

lemma mk_eq_iff_involution {α : Type*} [Finite α] (s : Equiv.Perm α)
    (hs : Function.Involutive s) (d : α) (q : CycleQuot s) :
    Quotient.mk _ d=q ↔ d=q.out ∨ d=s q.out := by
  calc
    Quotient.mk _ d=q ↔ Quotient.mk _ d=Quotient.mk _ q.out := by rw [Quotient.out_eq]
    _ ↔ s.SameCycle d q.out := Quotient.eq
    _ ↔ s.SameCycle q.out d := ⟨Equiv.Perm.SameCycle.symm,Equiv.Perm.SameCycle.symm⟩
    _ ↔ d=q.out ∨ d=s q.out := sameCycle_involution s hs q.out d

lemma card_orbit_fiber {α : Type*} [Fintype α] (s : Equiv.Perm α)
    (hs : Function.Involutive s) (q : CycleQuot s) :
    Fintype.card {d : α // Quotient.mk (Equiv.Perm.SameCycle.setoid s) d=q}=
      if s q.out=q.out then 1 else 2 := by
  classical
  rw [Fintype.card_subtype]
  have he : Finset.univ.filter (fun d : α => Quotient.mk (Equiv.Perm.SameCycle.setoid s) d=q)=
      {q.out,s q.out} := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    exact mk_eq_iff_involution s hs d q
  rw [he]
  by_cases h : s q.out=q.out
  · simp [h]
  · simp [h,Ne.symm h]

lemma fixed_out_iff {α : Type*} [Finite α] (s : Equiv.Perm α)
    (hs : Function.Involutive s) (d : α) :
    s (Quotient.mk (Equiv.Perm.SameCycle.setoid s) d).out=
      (Quotient.mk (Equiv.Perm.SameCycle.setoid s) d).out ↔ s d=d := by
  have he := (mk_eq_iff_involution s hs d (Quotient.mk _ d)).mp rfl
  rcases he with he | he
  · conv_rhs => rw [he]
  · conv_rhs => rw [he,hs]
    exact eq_comm

def fixedOrbitEquiv {α : Type*} [Finite α] (s : Equiv.Perm α)
    (hs : Function.Involutive s) : {d : α // s d=d} ≃ {q : CycleQuot s // s q.out=q.out} where
  toFun d := ⟨Quotient.mk _ d.val,(fixed_out_iff s hs d.val).mpr d.property⟩
  invFun q := ⟨q.val.out,q.property⟩
  left_inv d := by
    apply Subtype.ext
    have he := (mk_eq_iff_involution s hs d.val (Quotient.mk _ d.val)).mp rfl
    rcases he with he | he
    · exact he.symm
    · have hh := congrArg s he
      rw [d.property,hs] at hh
      exact hh.symm
  right_inv q := Subtype.ext (Quotient.out_eq q.val)

/-- Orbit count for an involution, retaining its fixed points. A reversal
has no fixed darts, whereas the path-map vertex rotation has exactly two. -/
lemma twice_card_orbits {α : Type*} [Fintype α] (s : Equiv.Perm α)
    (hs : Function.Involutive s) :
    2*Fintype.card (CycleQuot s)=Fintype.card α+Fintype.card {d : α // s d=d} := by
  classical
  have hd : Fintype.card α=∑ q : CycleQuot s,if s q.out=q.out then 1 else 2 := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk (Equiv.Perm.SameCycle.setoid s))),
      Fintype.card_sigma]
    exact Finset.sum_congr rfl (fun q _ => card_orbit_fiber s hs q)
  have hf : Fintype.card {d : α // s d=d}=∑ q : CycleQuot s,if s q.out=q.out then 1 else 0 := by
    rw [Fintype.card_congr (fixedOrbitEquiv s hs),Fintype.card_subtype]
    simp only [Finset.sum_boole, Nat.cast_id]
  rw [hd,hf,← Finset.sum_add_distrib]
  calc
    2*Fintype.card (CycleQuot s)=∑ _q : CycleQuot s,2 := by simp [mul_comm]
    _ = _ := Finset.sum_congr rfl (fun q _ => by split_ifs <;> rfl)

end FKCRT.MapFinite
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT

lemma spanningGraph_reachable_reversal {n : ℕ} (a s : Equiv.Perm (Dart n)) (d : Dart n) :
    (spanningGraph a s univ).Reachable (orbit s d) (orbit s (a d)) := by
  classical
  by_cases h : orbit s d=orbit s (a d)
  · rw [h]
  · apply SimpleGraph.Adj.reachable
    exact ⟨h,Or.inl ⟨d,mem_univ _,rfl,rfl⟩⟩

end FKCRT
end



/-! The exact edge-reversal tour of the rotation-system maps. -/
noncomputable section
open Equiv Equiv.Perm Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma partial_involutive (a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) :
    Function.Involutive (fun d => if orbit a d ∈ A then a d else d) := by
  classical
  intro d
  by_cases hd : orbit a d ∈ A
  · simp only [orbit_perm, hd, ite_true]
    exact ha d
  · simp only [hd, ite_false]

def partialReversal (a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) : Perm (Dart n) := by
  classical
  exact (partial_involutive a ha A).toPerm _

lemma partialReversal_apply (a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (d : Dart n) :
    partialReversal a ha A d = if orbit a d ∈ A then a d else d := rfl

lemma partialReversal_involutive (a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) : Function.Involutive (partialReversal a ha A) :=
  partial_involutive a ha A

lemma partialReversal_empty (a : Perm (Dart n)) (ha : Function.Involutive a) :
    partialReversal a ha ∅ = 1 := by
  apply Equiv.ext
  intro d
  simp [partialReversal_apply]

lemma partialReversal_self (a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) : partialReversal a ha A * partialReversal a ha A = 1 := by
  apply Equiv.ext
  intro d
  exact partialReversal_involutive a ha A d

lemma partialReversal_compl (a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) : partialReversal a ha A * a = partialReversal a ha Aᶜ := by
  classical
  apply Equiv.ext
  intro d
  simp only [mul_apply, partialReversal_apply, orbit_perm, Finset.mem_compl]
  by_cases h : orbit a d ∈ A
  · simpa only [h, ite_true, not_true_eq_false, ite_false] using ha d
  · simp only [h, ite_false, not_false_eq_true, ite_true]

lemma partialReversal_insert (a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (e : Orbit a) (he : e ∉ A) :
    partialReversal a ha (insert e A) =
      partialReversal a ha A * swap e.out (a e.out) := by
  classical
  have heq (d : Dart n) : orbit a d = e ↔ d = e.out ∨ d = a e.out :=
    MapFinite.mk_eq_iff_involution a ha d e
  have ho : orbit a e.out = e := Quotient.out_eq e
  apply Equiv.ext
  intro d
  by_cases hd₁ : d = e.out
  · subst d
    simp only [mul_apply, swap_apply_left, partialReversal_apply, orbit_perm,
      ho, Finset.mem_insert_self, ite_true, he, ite_false]
  by_cases hd₂ : d = a e.out
  · subst d
    simp only [mul_apply, swap_apply_right, partialReversal_apply, orbit_perm,
      ho, Finset.mem_insert_self, ite_true, he, ite_false]
    exact ha e.out
  · have hd : orbit a d ≠ e := fun h => (heq d).mp h |>.elim hd₁ hd₂
    simp only [mul_apply, swap_apply_of_ne_of_ne hd₁ hd₂, partialReversal_apply,
      Finset.mem_insert, hd, false_or]

lemma card_orbit_mul_swap_le (p : Perm (Dart n)) (d e : Dart n) :
    Nat.card (Orbit (p * swap d e)) ≤ Nat.card (Orbit p) + 1 := by
  rw [mul_swap_eq_swap_mul]
  exact MapCycles.card_orbits_swap_le p (p d) (p e)

lemma card_orbit_partialReversal_le (a s : Perm (Dart n))
    (ha : Function.Involutive a) (A : Finset (Orbit a)) :
    Nat.card (Orbit (s * partialReversal a ha A)) ≤ Nat.card (Orbit s) + A.card := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [partialReversal_empty]
  | @insert e A he ih =>
    rw [partialReversal_insert a ha A e he, ← mul_assoc, Finset.card_insert_of_notMem he]
    have hh := card_orbit_mul_swap_le (s * partialReversal a ha A) e.out (a e.out)
    omega

lemma card_orbit_eq_one_iff (p : Perm (Dart n)) :
    Nat.card (Orbit p) = 1 ↔ ∀ d e, p.SameCycle d e := by
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · intro hh d e
    have : Subsingleton (Orbit p) := hh.1
    exact Quotient.exact (Subsingleton.elim (orbit p d) (orbit p e))
  · intro hh
    refine ⟨⟨fun v w => ?_⟩, ⟨orbit p 0⟩⟩
    induction v using Quotient.inductionOn with | h d =>
      induction w using Quotient.inductionOn with | h e =>
        exact Quotient.sound (hh d e)

lemma spanningGraph_reachable_partial (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (d : Dart n) :
    (spanningGraph a s (A : Set (Orbit a))).Reachable
      (orbit s d) (orbit s (partialReversal a ha A d)) := by
  classical
  rw [partialReversal_apply]
  split_ifs with h
  · by_cases hd : orbit s d = orbit s (a d)
    · rw [hd]
    · exact SimpleGraph.Adj.reachable ⟨hd, Or.inl ⟨d, h, rfl, rfl⟩⟩
  · exact SimpleGraph.Reachable.refl _

lemma spanningGraph_connected_of_tour (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (hc : ∀ d e, (s * partialReversal a ha A).SameCycle d e) :
    (spanningGraph a s (A : Set (Orbit a))).Connected := by
  refine {preconnected := ?_, nonempty := ⟨orbit s 0⟩}
  intro v w
  induction v using Quotient.inductionOn with | h d =>
    induction w using Quotient.inductionOn with | h e =>
      obtain ⟨k,hk⟩ := (hc d e).exists_nat_pow_eq
      rw [← hk]
      have hp (j : ℕ) : (spanningGraph a s (A : Set (Orbit a))).Reachable
          (orbit s d) (orbit s (((s * partialReversal a ha A)^j) d)) := by
        induction j with
        | zero => exact SimpleGraph.Reachable.refl _
        | succ j ih =>
          rw [pow_succ', mul_apply, mul_apply, orbit_perm]
          exact ih.trans (spanningGraph_reachable_partial a s ha A _)
      exact hp k

lemma reversal_card (a : Perm (Dart n)) (ha : Function.Involutive a)
    (hf : ∀ d, a d ≠ d) : Fintype.card (Orbit a) = n + 1 := by
  have hn : Fintype.card {d : Dart n // a d = d} = 0 := by
    have : IsEmpty {d : Dart n // a d = d} := ⟨fun d => hf d d.property⟩
    exact Fintype.card_eq_zero
  have hh := MapFinite.twice_card_orbits a ha
  rw [Fintype.card_eq_nat_card] at hn
  simp only [Fintype.card_eq_nat_card] at hh ⊢
  change 2*Nat.card (Orbit a)=Nat.card (Dart n)+Nat.card {d : Dart n // a d=d} at hh
  rw [hn] at hh
  simp only [Dart, Nat.card_fin, add_zero] at hh
  omega

/-- A one-cycle tour in a genuine planar map has exactly V-1 chosen edges.
The proof uses the Euler equality and the two complementary tour
bounds, so loops and parallel edges are fully retained. -/
theorem tour_edge_card (M : LabelledMap n) (A : Finset (Orbit M.val.1))
    (hc : ∀ d e, (M.val.2 * partialReversal M.val.1 M.property.1 A).SameCycle d e) :
    Nat.card (Orbit M.val.2) = A.card + 1 := by
  classical
  let a := M.val.1
  let s := M.val.2
  let ha := M.property.1
  let p := s * partialReversal a ha A
  have hp : Nat.card (Orbit p) = 1 := (card_orbit_eq_one_iff _).mpr hc
  have hv := card_orbit_partialReversal_le a p ha A
  have hf := card_orbit_partialReversal_le a p ha Aᶜ
  have hv_eq : p * partialReversal a ha A = s := by
    dsimp [p]
    rw [mul_assoc, partialReversal_self, mul_one]
  have hf_eq : p * partialReversal a ha Aᶜ = s * a := by
    dsimp [p]
    rw [← partialReversal_compl a ha A, ← mul_assoc, mul_assoc s,
      partialReversal_self, mul_one]
  rw [hv_eq, hp] at hv
  rw [hf_eq, hp, Finset.card_compl, reversal_card a ha M.property.2.1] at hf
  have he := M.property.2.2.2
  change Nat.card (Orbit s) + Nat.card (Orbit (s * a)) = n + 3 at he
  have ha_card : A.card ≤ n + 1 := by
    have hh := Finset.card_le_univ A
    change A.card ≤ Fintype.card (Orbit a) at hh
    rwa [reversal_card a ha M.property.2.1] at hh
  change Nat.card (Orbit s)=A.card+1
  omega

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma card_orbit_mul_comm (p q : Perm (Dart n)) :
    Nat.card (Orbit (p*q)) = Nat.card (Orbit (q*p)) := by
  apply Nat.card_congr
  apply Quotient.congr q
  intro d e
  change (p*q).SameCycle d e ↔ (q*p).SameCycle (q d) (q e)
  have he : q * (p*q) * q⁻¹ = q*p := by group
  rw [← he, sameCycle_conj]
  simp

lemma card_orbit_partialReversal_mul_le (a p : Perm (Dart n))
    (ha : Function.Involutive a) (A : Finset (Orbit a)) :
    Nat.card (Orbit (partialReversal a ha A * p)) ≤ Nat.card (Orbit p) + A.card := by
  rw [card_orbit_mul_comm]
  exact card_orbit_partialReversal_le a p ha A

lemma edgeSwap_eq (a : Perm (Dart n)) (ha : Function.Involutive a) (d : Dart n) :
    swap (orbit a d).out (a (orbit a d).out) = swap d (a d) := by
  have hh := (MapFinite.mk_eq_iff_involution a ha d (orbit a d)).mp rfl
  rcases hh with hh | hh
  · conv_rhs => rw [hh]
  · conv_rhs => rw [hh, ha]
    exact swap_comm _ _

lemma partialReversal_insert_orbit (a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (d : Dart n) (hd : orbit a d ∉ A) :
    partialReversal a ha (insert (orbit a d) A) = partialReversal a ha A * swap d (a d) := by
  rw [partialReversal_insert a ha A (orbit a d) hd, edgeSwap_eq a ha d]

/-- Alternating chords first split and then rejoin a tour cycle. -/
lemma crossing_two_swaps (p : Perm (Dart n)) (x y z w : Dart n)
    (L M N R : List (Dart n))
    (he : MapCycles.orbitList p x = x :: (L ++ y :: (M ++ z :: (N ++ w :: R)))) :
    Nat.card (Orbit (swap y w * (swap x z * p))) = Nat.card (Orbit p) := by
  have hn := MapCycles.nodup_orbitList p x
  rw [he] at hn
  have hxz : x ≠ z := fun h => hn.notMem (by simp [h])
  have hcycle : p.SameCycle x z := by
    apply (MapCycles.mem_orbitList p x z).mp
    rw [he]
    simp
  have hcount := MapCycles.card_orbits_swap_of_sameCycle p hxz hcycle
  let U := x :: (L ++ y :: M)
  let V := z :: (N ++ w :: R)
  have hnodup : (U ++ V).Nodup := by simpa [U,V,List.append_assoc] using hn
  have hdisj := (List.nodup_append.mp hnodup).2.2
  have hyU : y ∈ U := by simp [U]
  have hwV : w ∈ V := by simp [V]
  have hp (d : Dart n) (hd : d ∈ U ++ V) : p d = (U ++ V).formPerm d := by
    have he' : MapCycles.orbitList p x = U ++ V := by simpa [U,V,List.append_assoc] using he
    simpa only [he'] using MapCycles.orbitList_action p x d (he' ▸ hd)
  have hq (d : Dart n) (hd : d ∈ U) : (swap x z * p) d = U.formPerm d := by
    change swap x z (p d) = U.formPerm d
    rw [hp d (List.mem_append_left _ hd)]
    have hh := congrArg (fun r : Perm (Dart n) => r d)
      (MapCycles.swap_mul_formPerm_cut x z (L ++ y :: M) (N ++ w :: R) hnodup)
    change swap x z ((U ++ V).formPerm d) = U.formPerm (V.formPerm d) at hh
    have hdV : d ∉ V := fun hv =>
      List.disjoint_left.mp (List.disjoint_iff_ne.mpr hdisj) hd hv
    rw [hh, List.formPerm_apply_of_notMem hdV]
  have hnot : ¬ (swap x z * p).SameCycle y w := by
    intro h
    obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
    have hh := (MapCycles.pow_eq_on_list (swap x z * p) U hq hyU k).2
    rw [hk] at hh
    exact hdisj w hh w hwV rfl
  have hh := MapCycles.card_orbits_swap_of_not_sameCycle (swap x z * p) hnot
  change Nat.card (Orbit (swap x z * p)) = Nat.card (Orbit p) + 1 at hcount
  change Nat.card (Orbit (swap y w * (swap x z * p))) + 1 =
    Nat.card (Orbit (swap x z * p)) at hh
  omega

/-- An orbit-count-maximal matching on a tour has no alternating pair of
selected edges. This is the exact combinatorial planarity criterion needed
for the two parenthesis families, rather than a topological picture. -/
theorem no_crossing_of_maximal_orbits (a p : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a))
    (hmax : Nat.card (Orbit (partialReversal a ha A * p)) = Nat.card (Orbit p) + A.card)
    (x y : Dart n) (hx : orbit a x ∈ A) (hy : orbit a y ∈ A)
    (hxy : orbit a x ≠ orbit a y) (L M N R : List (Dart n)) :
    MapCycles.orbitList p x ≠ x :: (L ++ y :: (M ++ a x :: (N ++ a y :: R))) := by
  classical
  intro he
  let B := (A.erase (orbit a x)).erase (orbit a y)
  have hxB : orbit a x ∉ B := by simp [B]
  have hyB : orbit a y ∉ B := by simp [B]
  have hyxB : orbit a y ∉ insert (orbit a x) B := by simp [hyB, Ne.symm hxy]
  have hA : A = insert (orbit a y) (insert (orbit a x) B) := by
    ext e
    simp only [B,Finset.mem_insert,Finset.mem_erase]
    constructor
    · intro hh
      by_cases he₁ : e=orbit a y
      · exact Or.inl he₁
      by_cases he₂ : e=orbit a x
      · exact Or.inr (Or.inl he₂)
      · exact Or.inr (Or.inr ⟨he₁,he₂,hh⟩)
    · rintro (rfl | rfl | ⟨_,_,hh⟩) <;> assumption
  have hcard : A.card = B.card + 2 := by
    rw [hA,Finset.card_insert_of_notMem hyxB,Finset.card_insert_of_notMem hxB]
  have hP : partialReversal a ha A * p =
      partialReversal a ha B * (swap y (a y) * (swap x (a x) * p)) := by
    have hx_yB : orbit a x ∉ insert (orbit a y) B := by simp [hxB,hxy]
    have hA' : A = insert (orbit a x) (insert (orbit a y) B) := by
      rw [hA,Finset.insert_comm]
    rw [hA',partialReversal_insert_orbit a ha _ x hx_yB,
      partialReversal_insert_orbit a ha _ y hyB]
    group
  have hle := card_orbit_partialReversal_mul_le a
    (swap y (a y) * (swap x (a x) * p)) ha B
  rw [← hP,crossing_two_swaps p x y (a x) (a y) L M N R he,hmax,hcard] at hle
  omega

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma dualRotation_mul (a s : Perm (Dart n)) (ha : Function.Involutive a) :
    s*a*a=s := by
  apply Equiv.ext
  intro d
  exact congrArg s (ha d)

lemma spanningGraph_dual_connected (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (hc : (spanningGraph a s univ).Connected) : (spanningGraph a (s*a) univ).Connected := by
  let t := s*a
  have hreach : ∀ d, (spanningGraph a t univ).Reachable (orbit t 0) (orbit t d) := by
    apply connected_dart_induction ha hc (P := fun d =>
      (spanningGraph a t univ).Reachable (orbit t 0) (orbit t d))
      (SimpleGraph.Reachable.refl _)
    · exact fun d hd => hd.trans (spanningGraph_reachable_reversal a t d)
    · intro d hd
      have he : s d = t (a d) := (congrArg s (ha d)).symm
      rw [he,orbit_perm]
      exact hd.trans (spanningGraph_reachable_reversal a t d)
  refine {preconnected := ?_, nonempty := ⟨orbit t 0⟩}
  intro v w
  induction v using Quotient.inductionOn with | h d =>
    induction w using Quotient.inductionOn with | h e =>
      exact (hreach d).symm.trans (hreach e)

/-- The combinatorial dual in the dart convention. Choosing the
inverse face orientation is unnecessary: this rotation gives the same
planar oriented dual after reversing edge darts. -/
def dualLabelledMap (M : LabelledMap n) : LabelledMap n :=
  ⟨(M.val.1,M.val.2*M.val.1),M.property.1,M.property.2.1,
    spanningGraph_dual_connected M.val.1 M.val.2 M.property.1 M.property.2.2.1,by
      rw [dualRotation_mul _ _ M.property.1]
      exact (Nat.add_comm _ _).trans M.property.2.2.2⟩

lemma dual_tour (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) :
    (s*a)*partialReversal a ha Aᶜ=s*partialReversal a ha A := by
  rw [← partialReversal_compl a ha A]
  apply Equiv.ext
  intro d
  simp only [mul_apply,partialReversal_apply,orbit_perm]
  by_cases h : orbit a d ∈ A
  · simp only [h,ite_true]
    rw [ha]
  · simp only [h,ite_false]
    rw [ha]

theorem planar_tour_compl_card (M : LabelledMap n) (A : Finset (Orbit M.val.1))
    (hc : ∀ d e, (M.val.2 * partialReversal M.val.1 M.property.1 A).SameCycle d e) :
    Nat.card (Orbit (M.val.2*M.val.1))=Aᶜ.card+1 := by
  apply tour_edge_card (dualLabelledMap M) Aᶜ
  change ∀ d e, (M.val.2*M.val.1*partialReversal M.val.1 M.property.1 Aᶜ).SameCycle d e
  rw [dual_tour M.val.1 M.val.2 M.property.1 A]
  exact hc

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

lemma spanningGraph_mono (a s : Perm (Dart n)) {A B : Set (Orbit a)} (h : A ⊆ B) :
    spanningGraph a s A ≤ spanningGraph a s B := by
  rintro v w ⟨hne, hh | hh⟩
  · obtain ⟨d,hd,hv,hw⟩ := hh
    exact ⟨hne,Or.inl ⟨d,h hd,hv,hw⟩⟩
  · obtain ⟨d,hd,hw,hv⟩ := hh
    exact ⟨hne,Or.inr ⟨d,h hd,hw,hv⟩⟩

end FKCRT
end



/-! Exact reconstruction in the rotation-system convention. The
Euler equalities on the two coloured matchings are equivalent to their
noncrossing property; maximum orbit counts are proved for stack matchings
in `WorkNoncrossing`, rather than postulated for a map. -/
noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma reconstructed_tour (a t : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) :
    (t * partialReversal a ha A) * partialReversal a ha A = t := by
  rw [mul_assoc,partialReversal_self,mul_one]

lemma reconstructed_face (a t : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) :
    (t * partialReversal a ha A) * a = t * partialReversal a ha Aᶜ := by
  rw [mul_assoc,partialReversal_compl]

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
open MapCycles
variable {n : ℕ}

/-- Edges of the first colour, in the edge-orbit quotient of the complete
matching. -/
def matchingEdges (E F : List (Dart n × Dart n)) : Finset (Orbit (turns (E++F))) :=
  E.toFinset.image (fun e => orbit (turns (E++F)) e.1)

lemma mem_matchingEdges (E F : List (Dart n × Dart n))
    (hn : (endpoints (E++F)).Nodup) (d : Dart n) :
    orbit (turns (E++F)) d ∈ matchingEdges E F ↔ d∈endpoints E := by
  classical
  simp only [matchingEdges,Finset.mem_image,List.mem_toFinset]
  constructor
  · rintro ⟨e,he,hde⟩
    have hh : (turns (E++F)).SameCycle e.1 d := Quotient.exact hde
    rw [MapFinite.sameCycle_involution _ (turns_involutive hn),
      (turns_pair hn e (List.mem_append_left _ he)).1] at hh
    exact mem_endpoints.mpr ⟨e,he,hh⟩
  · intro hd
    obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hd
    · exact ⟨e,he,rfl⟩
    · refine ⟨e,he,?_⟩
      apply Quotient.sound
      apply (MapFinite.sameCycle_involution _ (turns_involutive hn) _ _).mpr
      exact Or.inr (turns_pair hn e (List.mem_append_left _ he)).1.symm

lemma partialReversal_matchingEdges (E F : List (Dart n × Dart n))
    (hn : (endpoints (E++F)).Nodup) :
    partialReversal (turns (E++F)) (turns_involutive hn) (matchingEdges E F)=turns E := by
  apply Equiv.ext
  intro d
  simp only [partialReversal_apply,mem_matchingEdges E F hn]
  split_ifs with hd
  · exact (turns_sublist_apply hn (List.sublist_append_left _ _) hd).symm
  · exact (turns_fixed_of_notMem hd).symm

lemma turns_mul_complete (E F : List (Dart n × Dart n))
    (hn : (endpoints (E++F)).Nodup) : turns E * turns (E++F)=turns F := by
  have hE : turns E*turns E=1 := turns_self ((by rw [endpoints_append] at hn; exact hn.of_append_left))
  have hF : turns F*turns F=1 := turns_self ((by rw [endpoints_append] at hn; exact hn.of_append_right))
  have hEF := turns_self hn
  have he : turns (E++F)=turns E*turns F := by
    have h1 : (turns (E++F))⁻¹=turns (E++F) := inv_eq_of_mul_eq_one_left hEF
    have h2 : (turns E)⁻¹=turns E := inv_eq_of_mul_eq_one_left hE
    have h3 : (turns F)⁻¹=turns F := inv_eq_of_mul_eq_one_left hF
    rw [turns_append,mul_inv_rev,h2,h3] at h1
    simpa only [turns_append] using h1.symm
  rw [he,← mul_assoc,hE,one_mul]

/-- Two complete noncrossing colour matchings construct an actual planar
rotation system in the map model, with no topological assumptions. -/
theorem matching_map_conditions (E F : List (Dart n × Dart n))
    (hE : Arches (List.finRange (2*(n+1))) E)
    (hF : Arches (List.finRange (2*(n+1))) F)
    (hc : (endpoints (E++F)).Perm (List.finRange (2*(n+1)))) :
    MapConditions (turns (E++F),(List.finRange (2*(n+1))).formPerm * turns E) := by
  classical
  let l := List.finRange (2*(n+1))
  let t := l.formPerm
  have hn : (endpoints (E++F)).Nodup := hc.nodup_iff.mpr (List.nodup_finRange _)
  have ha := turns_involutive hn
  have hf (d : Dart n) : turns (E++F) d≠d := by
    intro hh
    exact (turns_eq_self_iff hn d).mp hh (hc.mem_iff.mpr (List.mem_finRange d))
  have ht : ∀ d e,t.SameCycle d e := by
    intro d e
    exact sameCycle_of_list t (List.nodup_finRange _) (fun _ _ => rfl)
      (List.mem_finRange d) (List.mem_finRange e)
  have htcard : Nat.card (Orbit t)=1 := (card_orbit_eq_one_iff t).mpr ht
  have hturn : (t*turns E)*partialReversal (turns (E++F)) ha (matchingEdges E F)=t := by
    rw [partialReversal_matchingEdges E F hn,mul_assoc,turns_self (by rw [endpoints_append] at hn; exact hn.of_append_left)]
    simp
  have hconn := spanningGraph_connected_of_tour (turns (E++F)) (t*turns E) ha
    (matchingEdges E F) (by simpa only [hturn] using ht)
  refine ⟨ha,hf,hconn.mono (spanningGraph_mono _ _ (Set.subset_univ _)),?_⟩
  have he := hE.card_orbits_turns [] t (by simpa using List.nodup_finRange (2*(n+1)))
    (fun _ _ => rfl)
  have hff := hF.card_orbits_turns [] t (by simpa using List.nodup_finRange (2*(n+1)))
    (fun _ _ => rfl)
  change Nat.card (Orbit (t*turns E)) + Nat.card (Orbit ((t*turns E)*turns (E++F)))=n+3
  rw [mul_assoc,turns_mul_complete E F hn,card_orbit_mul_comm t (turns E),
    card_orbit_mul_comm t (turns F),he,hff,htcard]
  have hlen := hc.length_eq
  have hl (Q : List (Dart n × Dart n)) : (endpoints Q).length=2*Q.length := by
    induction Q with
    | nil => rfl
    | cons e Q ih => simp only [endpoints_cons,List.length_cons,ih]; omega
  rw [hl,List.length_append,List.length_finRange] at hlen
  omega

end FKCRT
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_WordMaps
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List
namespace FKCRT.Inventory
open MapCycles

def TypedLetter.color : TypedLetter → Bool
  | .burger c => c
  | .order c => c

def TypedLetter.step : TypedLetter → DyckStep
  | .burger _ => .U
  | .order _ => .D

lemma colorWord_map {α : Type*} (f : α→TypedLetter) (l : List α) (c : Bool) :
    colorWord c (l.map f) = (l.filter (fun i => (f i).color == c)).map (fun i => (f i).step) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hf : f a with
    | burger b => by_cases hb : b=c <;> simp_all [colorWord,colorStep,TypedLetter.color,TypedLetter.step]
    | order b => by_cases hb : b=c <;> simp_all [colorWord,colorStep,TypedLetter.color,TypedLetter.step]

/-- Actual identified words produce a complete pair of noncrossing matchings;
the labels on each pair are the matching burger and fixed order. -/
theorem identified_matchings {n : ℕ} (w : Dart n→TypedLetter)
    (hw : stackTypedRun ((List.finRange (2*(n+1))).map w) []=some []) :
    ∃ E F : List (Dart n × Dart n),
      Arches (List.finRange (2*(n+1))) E ∧
      Arches (List.finRange (2*(n+1))) F ∧
      (endpoints (E++F)).Perm (List.finRange (2*(n+1))) ∧
      (∀ e∈E,w e.1=.burger true ∧ w e.2=.order true) ∧
      (∀ e∈F,w e.1=.burger false ∧ w e.2=.order false) := by
  let l := List.finRange (2*(n+1))
  let L (c : Bool) := l.filter (fun i => (w i).color == c)
  have hh (c : Bool) : (L c).map (fun i => (w i).step)=(identifiedDyck hw c).toList :=
    (colorWord_map w l c).symm
  obtain ⟨E,hE,hEp,hEf⟩ := dyck_arches (identifiedDyck hw true) (L true) _ (hh true)
  obtain ⟨F,hF,hFp,hFf⟩ := dyck_arches (identifiedDyck hw false) (L false) _ (hh false)
  have hp : (L true++L false).Perm l := by
    have hp := List.filter_append_perm (fun i => (w i).color) l
    simpa [L] using hp
  refine ⟨E,F,hE.mono (List.filter_sublist),hF.mono (List.filter_sublist),?_,?_,?_⟩
  · rw [endpoints_append]
    exact (hEp.append hFp).trans hp
  · intro e he
    have he' := hE.endpoints e he
    have h1 : (w e.1).color=true := by simpa [L] using (List.mem_filter.mp he'.1).2
    have h2 : (w e.2).color=true := by simpa [L] using (List.mem_filter.mp he'.2).2
    have hs := hEf e he
    constructor
    · cases hh : w e.1 <;> simp_all [TypedLetter.color,TypedLetter.step]
    · cases hh : w e.2 <;> simp_all [TypedLetter.color,TypedLetter.step]
  · intro e he
    have he' := hF.endpoints e he
    have h1 : (w e.1).color=false := by simpa [L] using (List.mem_filter.mp he'.1).2
    have h2 : (w e.2).color=false := by simpa [L] using (List.mem_filter.mp he'.2).2
    have hs := hFf e he
    constructor
    · cases hh : w e.1 <;> simp_all [TypedLetter.color,TypedLetter.step]
    · cases hh : w e.2 <;> simp_all [TypedLetter.color,TypedLetter.step]

end FKCRT.Inventory
end


noncomputable section
open List
namespace FKCRT.MapCycles
variable {α : Type*} 

/-- Deterministic stack matching of one colour; `none` skips the other colour. -/
def scanArches (f : α→Option Bool) : List α → List α → Option (List α × List (α×α))
  | [],S => some (S,[])
  | a::l,S => match f a with
      | none => scanArches f l S
      | some true => scanArches f l (a::S)
      | some false => match S with
        | [] => none
        | b::S => (scanArches f l S).map (fun z => (z.1,(b,a)::z.2))

lemma scanArches_append (f : α→Option Bool) (l r S : List α) :
    scanArches f (l++r) S=(scanArches f l S).bind (fun z =>
      (scanArches f r z.1).map (fun w => (w.1,z.2++w.2))) := by
  induction l generalizing S with
  | nil => simp [scanArches]
  | cons a l ih =>
    cases hf : f a with
    | none => simpa [scanArches,hf] using ih S
    | some b =>
      cases b with
      | true => simpa [scanArches,hf] using ih (a::S)
      | false =>
        cases S with
        | nil => simp [scanArches,hf]
        | cons b S =>
          simp only [List.cons_append,scanArches,hf,ih]
          cases h1 : scanArches f l S with
          | none => rfl
          | some z => cases h2 : scanArches f r z.1 <;> simp [h2]

lemma Arches.mem_endpoints {l : List α} {E : List (α×α)} (h : Arches l E)
    {x : α} (hx : x∈MapCycles.endpoints E) : x∈l := by
  obtain ⟨e,he,hx⟩ := MapCycles.mem_endpoints.mp hx
  rcases hx with rfl|rfl
  · exact (h.endpoints e he).1
  · exact (h.endpoints e he).2

/-- Noncrossing typed pairings are uniquely recovered by the stack. In
particular no hidden choice of an arch pairing enters the map inverse. -/
theorem Arches.scan {l : List α} {E : List (α×α)} (h : Arches l E)
    (hn : l.Nodup) (f : α→Option Bool)
    (hp : ∀ e∈E,f e.1=some true ∧ f e.2=some false)
    (hc : ∀ x∈l,f x≠none → x∈MapCycles.endpoints E) (S : List α) :
    ∃ F,scanArches f l S=some (S,F) ∧ F.Perm E := by
  induction h generalizing S with
  | nil => exact ⟨[],rfl,.refl _⟩
  | @skip a l E h ih =>
    have ha : f a=none := by
      by_contra ha
      exact hn.notMem (h.mem_endpoints (hc a (by simp) ha))
    obtain ⟨F,hF,hFE⟩ := ih hn.of_cons (fun e he => hp e he)
      (fun x hx ht => hc x (List.mem_cons_of_mem _ hx) ht) S
    exact ⟨F,by simpa [scanArches,ha] using hF,hFE⟩
  | @pair a b L R E G hL hR ihL ihR =>
    have hab := hp (a,b) (by simp)
    have hLsub : ∀ x∈L,f x≠none → x∈MapCycles.endpoints E := by
      intro x hx hfx
      have hh := hc x (by simp [hx]) hfx
      simp only [endpoints_cons,endpoints_append,List.mem_cons,List.mem_append] at hh
      rcases hh with rfl|rfl|he|hg
      · exact False.elim (hn.notMem (by simp [hx]))
      · have hb : x∉L := by
          have hh := (List.nodup_append.mp hn.of_cons).2.2
          exact fun h => hh x h x (by simp) rfl
        exact False.elim (hb hx)
      · exact he
      · have hxR := hR.mem_endpoints hg
        have hh := (List.nodup_append.mp hn.of_cons).2.2
        exact False.elim (hh x hx x (by simp [hxR]) rfl)
    have hRsub : ∀ x∈R,f x≠none → x∈MapCycles.endpoints G := by
      intro x hx hfx
      have hh := hc x (by simp [hx]) hfx
      simp only [endpoints_cons,endpoints_append,List.mem_cons,List.mem_append] at hh
      rcases hh with rfl|rfl|he|hg
      · exact False.elim (hn.notMem (by simp [hx]))
      · exact False.elim (hn.of_cons.of_append_right.notMem hx)
      · have hxL := hL.mem_endpoints he
        have hh := (List.nodup_append.mp hn.of_cons).2.2
        exact False.elim (hh x hxL x (by simp [hx]) rfl)
      · exact hg
    obtain ⟨F,hF,hFE⟩ := ihL hn.of_cons.of_append_left (fun e he => hp e (by simp [he])) hLsub (a::S)
    obtain ⟨H,hH,hHG⟩ := ihR hn.of_cons.of_append_right.of_cons (fun e he => hp e (by simp [he])) hRsub S
    refine ⟨F++(a,b)::H,?_,?_⟩
    · simp only [scanArches,hab.1,scanArches_append,hF,Option.bind_some,hab.2,hH,Option.map_some]
    · exact (List.perm_middle).trans ((hFE.append hHG).cons (a,b))

/-- Uniqueness is literal up to the irrelevant order of disjoint pairs. -/
theorem arches_unique {l : List α} {E F : List (α×α)}
    (hE : Arches l E) (hF : Arches l F) (hn : l.Nodup) (f : α→Option Bool)
    (hpE : ∀ e∈E,f e.1=some true ∧ f e.2=some false)
    (hpF : ∀ e∈F,f e.1=some true ∧ f e.2=some false)
    (hcE : ∀ x∈l,f x≠none → x∈MapCycles.endpoints E)
    (hcF : ∀ x∈l,f x≠none → x∈MapCycles.endpoints F) : E.Perm F := by
  obtain ⟨G,hG,hGE⟩ := hE.scan hn f hpE hcE []
  obtain ⟨H,hH,hHF⟩ := hF.scan hn f hpF hcF []
  have he : G=H := by simpa only [hG,Option.some.injEq,Prod.mk.injEq,true_and] using hH
  exact hGE.symm.trans (he.symm ▸ hHF)

end FKCRT.MapCycles
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT
namespace MapCycles
variable {α : Type*}

lemma endpoints_perm {E F : List (α×α)} (h : E.Perm F) :
    (endpoints E).Perm (endpoints F) := h.flatMap (fun _ _ => List.Perm.refl _)

variable [DecidableEq α]

lemma turns_perm {E F : List (α×α)} (h : E.Perm F) (hn : (endpoints E).Nodup) :
    turns E=turns F := by
  have hnF := h |> endpoints_perm |>.nodup_iff.mp hn
  apply Equiv.ext
  intro x
  by_cases hx : x∈endpoints E
  · obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hx
    · exact (turns_pair hn e he).1.trans (turns_pair hnF e (h.mem_iff.mp he)).1.symm
    · exact (turns_pair hn e he).2.trans (turns_pair hnF e (h.mem_iff.mp he)).2.symm
  · rw [turns_fixed_of_notMem hx,turns_fixed_of_notMem (fun hh => hx ((endpoints_perm h).mem_iff.mpr hh))]

end MapCycles
namespace Inventory
open MapCycles
variable {α : Type*}

/-- The one-colour stack instruction attached to a typed inventory symbol. -/
def colorInstruction (c : Bool) : TypedLetter→Option Bool
  | .burger b => if b=c then some true else none
  | .order b => if b=c then some false else none

lemma matching_color_coverage (w : α→TypedLetter) (l : List α)
    (E F : List (α×α)) (hc : (endpoints (E++F)).Perm l)
    (hE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (hF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false) :
    (∀ x∈l,colorInstruction true (w x)≠none → x∈endpoints E) ∧
    (∀ x∈l,colorInstruction false (w x)≠none → x∈endpoints F) := by
  constructor
  · intro x hx hw
    have hh := hc.mem_iff.mpr hx
    rw [endpoints_append,List.mem_append] at hh
    rcases hh with hh|hh
    · exact hh
    · obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hh
      · exact False.elim (hw (by simp [colorInstruction,(hF e he).1]))
      · exact False.elim (hw (by simp [colorInstruction,(hF e he).2]))
  · intro x hx hw
    have hh := hc.mem_iff.mpr hx
    rw [endpoints_append,List.mem_append] at hh
    rcases hh with hh|hh
    · obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hh
      · exact False.elim (hw (by simp [colorInstruction,(hE e he).1]))
      · exact False.elim (hw (by simp [colorInstruction,(hE e he).2]))
    · exact hh

/-- Literal uniqueness of the inverse map's two matchings, including empty
colour classes. This removes all pairing choices in `identified_map_exists`. -/
theorem typed_matchings_unique (w : α→TypedLetter) (l : List α) (hn : l.Nodup)
    (E F E' F' : List (α×α))
    (hE : Arches l E) (hF : Arches l F) (hE' : Arches l E') (hF' : Arches l F')
    (hc : (endpoints (E++F)).Perm l) (hc' : (endpoints (E'++F')).Perm l)
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false)
    (htE' : ∀ e∈E',w e.1=.burger true ∧ w e.2=.order true)
    (htF' : ∀ e∈F',w e.1=.burger false ∧ w e.2=.order false) :
    E.Perm E' ∧ F.Perm F' := by
  have hcov := matching_color_coverage w l E F hc htE htF
  have hcov' := matching_color_coverage w l E' F' hc' htE' htF'
  constructor
  · apply arches_unique hE hE' hn (colorInstruction true ∘ w)
    · intro e he
      simp [colorInstruction,(htE e he).1,(htE e he).2]
    · intro e he
      simp [colorInstruction,(htE' e he).1,(htE' e he).2]
    · exact hcov.1
    · exact hcov'.1
  · apply arches_unique hF hF' hn (colorInstruction false ∘ w)
    · intro e he
      simp [colorInstruction,(htF e he).1,(htF e he).2]
    · intro e he
      simp [colorInstruction,(htF' e he).1,(htF' e he).2]
    · exact hcov.2
    · exact hcov'.2

variable [DecidableEq α]

/-- In particular the reconstructed edge and vertex permutations are
independent of the proof/choice of Dyck pairing. -/
theorem typed_map_unique (w : α→TypedLetter) (l : List α) (hn : l.Nodup)
    (E F E' F' : List (α×α))
    (hE : Arches l E) (hF : Arches l F) (hE' : Arches l E') (hF' : Arches l F')
    (hc : (endpoints (E++F)).Perm l) (hc' : (endpoints (E'++F')).Perm l)
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false)
    (htE' : ∀ e∈E',w e.1=.burger true ∧ w e.2=.order true)
    (htF' : ∀ e∈F',w e.1=.burger false ∧ w e.2=.order false) :
    turns (E++F)=turns (E'++F') ∧ l.formPerm*turns E=l.formPerm*turns E' := by
  obtain ⟨he,hf⟩ := typed_matchings_unique w l hn E F E' F' hE hF hE' hF' hc hc' htE htF htE' htF'
  have hnod : (endpoints (E++F)).Nodup := hc.nodup_iff.mpr hn
  refine ⟨turns_perm (he.append hf) hnod,?_⟩
  rw [turns_perm he (by rw [endpoints_append] at hnod; exact hnod.of_append_left)]

end Inventory
end FKCRT
end


noncomputable section
open List
namespace FKCRT.MapCycles
variable {α : Type*} [LinearOrder α]

/-- A closed involutive noncrossing colour matching admits exactly the
recursive arch decomposition. No Jordan-curve principle is assumed. -/
theorem arches_of_noncrossing (a : α→α) (ha : Function.Involutive a)
    (P : α→Bool) (hP : ∀ x,P (a x)=P x) (l : List α)
    (hs : l.Pairwise (·<·))
    (hc : ∀ x∈l,P x=true → a x∈l)
    (hf : ∀ x∈l,P x=true → a x≠x)
    (hn : ∀ x∈l,∀ y∈l,P x=true → P y=true → x<y → y<a x → a x<a y → False) :
    ∃ E,Arches l E ∧ (endpoints E).Perm (l.filter P) ∧
      ∀ e∈E,e.2=a e.1 ∧ P e.1=true := by
  cases l with
  | nil => exact ⟨[],.nil,by simp,by simp⟩
  | cons x l =>
    have hs' := List.pairwise_cons.mp hs
    by_cases hx : P x=true
    · have hax : a x∈l := (List.mem_cons.mp (hc x (by simp) hx)).resolve_left (hf x (by simp) hx)
      obtain ⟨L,R,rfl⟩ := List.mem_iff_append.mp hax
      have hL := (List.pairwise_append.mp hs'.2).1
      have hbR := (List.pairwise_append.mp hs'.2).2.1
      have hR := (List.pairwise_cons.mp hbR).2
      have hLR := (List.pairwise_append.mp hs'.2).2.2
      have hxL (y) (hy : y∈L) : x<y := hs'.1 y (List.mem_append_left _ hy)
      have hxR (y) (hy : y∈R) : x<y := hs'.1 y (by simp [hy])
      have hxb : x<a x := hs'.1 (a x) (by simp)
      have hbR' (y) (hy : y∈R) : a x<y := (List.pairwise_cons.mp hbR).1 y hy
      have hLb (y) (hy : y∈L) : y<a x := hLR y hy (a x) (by simp)
      have hcL : ∀ y∈L,P y=true → a y∈L := by
        intro y hy hpy
        have hh := hc y (by simp [hy]) hpy
        simp only [List.mem_cons,List.mem_append] at hh
        rcases hh with h|h|h|h
        · have he : y=a x := (ha y).symm.trans (congrArg a h)
          exact False.elim ((ne_of_lt (hLb y hy)) he)
        · exact h
        · have he : y=x := ha.injective h
          exact False.elim ((ne_of_lt (hxL y hy)) he.symm)
        · exact False.elim (hn x (by simp) y (by simp [hy]) hx hpy
            (hxL y hy) (hLb y hy) (hbR' (a y) h))
      have hcR : ∀ y∈R,P y=true → a y∈R := by
        intro y hy hpy
        have hh := hc y (by simp [hy]) hpy
        simp only [List.mem_cons,List.mem_append] at hh
        rcases hh with h|h|h|h
        · have he : y=a x := (ha y).symm.trans (congrArg a h)
          exact False.elim ((ne_of_lt (hbR' y hy)) he.symm)
        · exact False.elim (hn x (by simp) (a y) (by simp [h]) hx (by rw [hP]; exact hpy)
            (hxL (a y) h) (hLb (a y) h) (by rw [ha]; exact hbR' y hy))
        · have he : y=x := ha.injective h
          exact False.elim ((ne_of_lt (hxR y hy)) he.symm)
        · exact h
      obtain ⟨E,hE,he,hpe⟩ := arches_of_noncrossing a ha P hP L hL hcL
        (fun y hy hpy => hf y (by simp [hy]) hpy)
        (fun y hy z hz => hn y (by simp [hy]) z (by simp [hz]))
      obtain ⟨F,hF,hf',hpf⟩ := arches_of_noncrossing a ha P hP R hR hcR
        (fun y hy hpy => hf y (by simp [hy]) hpy)
        (fun y hy z hz => hn y (by simp [hy]) z (by simp [hz]))
      refine ⟨(x,a x)::(E++F),.pair x (a x) hE hF,?_,?_⟩
      · simp only [endpoints_cons,endpoints_append,List.filter_cons,List.filter_append,hx,hP,
          ite_true]
        exact (((he.append hf').cons (a x)).cons x).trans (List.perm_middle.symm.cons x)
      · intro e he'
        simp only [List.mem_cons,List.mem_append] at he'
        rcases he' with rfl|h|h
        · exact ⟨rfl,hx⟩
        · exact hpe e h
        · exact hpf e h
    · have hc' : ∀ y∈l,P y=true → a y∈l := by
        intro y hy hpy
        apply (List.mem_cons.mp (hc y (by simp [hy]) hpy)).resolve_left
        intro he
        apply hx
        rw [← he,hP]
        exact hpy
      obtain ⟨E,hE,he,hpe⟩ := arches_of_noncrossing a ha P hP l hs'.2 hc'
        (fun y hy hpy => hf y (by simp [hy]) hpy)
        (fun y hy z hz => hn y (by simp [hy]) z (by simp [hz]))
      exact ⟨E,.skip x hE,by simpa [List.filter_cons,hx] using he,hpe⟩
termination_by l.length
decreasing_by
  all_goals
    subst_vars
    simp only [List.length_cons, List.length_append]
    omega

end FKCRT.MapCycles
end


noncomputable section
open List Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
namespace MapCycles
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma orbitList_formPerm (x : α) (l : List α) (hn : (x::l).Nodup) :
    orbitList (x::l).formPerm x=x::l := by
  cases l with
  | nil => simp [orbitList]
  | cons y l =>
    have ht : (x::y::l).formPerm.toList x=x::y::l := by
      simpa using toList_formPerm_nontrivial (x::y::l) (by simp) hn
    have hp : (x::y::l).formPerm x≠x := by
      intro h
      have hh := toList_eq_nil_iff.mpr (notMem_support.mpr h)
      rw [ht] at hh
      cases hh
    simpa only [orbitList,ite_eq_right hp] using ht

end MapCycles
namespace MapCycles
variable {α : Type*} [LinearOrder α]

lemma ordered_four_sublist {l : List α} (hs : l.Pairwise (·<·))
    {x y z w : α} (hx : x∈l) (hy : y∈l) (hz : z∈l) (hw : w∈l)
    (hxy : x<y) (hyz : y<z) (hzw : z<w) : [x,y,z,w]<+l := by
  have hh : [x,y,z,w].Pairwise (·<·) := by simp; exact ⟨⟨hxy,hxy.trans hyz,(hxy.trans hyz).trans hzw⟩,⟨hyz,hyz.trans hzw⟩,hzw⟩
  apply List.sublist_of_subperm_of_pairwise (r := (·≤·))
  · apply List.subperm_of_subset (hh.imp (fun h => ne_of_lt h))
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl <;> assumption
  · exact hh.imp (fun h => le_of_lt h)
  · exact hs.imp (fun h => le_of_lt h)

end MapCycles
open MapCycles
variable {n : ℕ}

/-- The orbit-maximal planar matching has the ordinary increasing-position
noncrossing property, with root/end seam retained exactly. -/
theorem ordered_no_crossing (a : Perm (Dart n)) (ha : Function.Involutive a)
    (l : List (Dart n)) (hs : l.Pairwise (·<·)) (hc : ∀ x,x∈l)
    (A : Finset (Orbit a))
    (hmax : Nat.card (Orbit (partialReversal a ha A*l.formPerm))=Nat.card (Orbit l.formPerm)+A.card)
    (x y : Dart n) (hx : orbit a x∈A) (hy : orbit a y∈A)
    (hxy : x<y) (hyx : y<a x) (haxy : a x<a y) : False := by
  have hn : l.Nodup := hs.imp (fun h => ne_of_lt h)
  have hsub := ordered_four_sublist hs (hc x) (hc y) (hc (a x)) (hc (a y)) hxy hyx haxy
  obtain ⟨U,L,hL,hsub⟩ := cons_sublist_split hsub
  obtain ⟨V,M,hM,hsub⟩ := cons_sublist_split hsub
  obtain ⟨W,N,hN,hsub⟩ := cons_sublist_split hsub
  obtain ⟨X,R,hR,_⟩ := cons_sublist_split hsub
  have he : l=U++x::(V++y::(W++a x::(X++a y::R))) := by rw [hL,hM,hN,hR]
  have hp : l.formPerm=(x::(V++y::(W++a x::(X++a y::(R++U))))).formPerm := by
    rw [he,formPerm_append_comm U _ (he ▸ hn)]
    simp only [List.cons_append,List.append_assoc]
  have hrot : MapCycles.orbitList l.formPerm x=x::(V++y::(W++a x::(X++a y::(R++U)))) := by
    rw [hp,orbitList_formPerm]
    have hh := (List.perm_append_comm (l₁ := U) (l₂ := x::(V++y::(W++a x::(X++a y::R))))).nodup_iff.mp (he ▸ hn)
    simpa only [List.cons_append,List.append_assoc] using hh
  have hne : orbit a x≠orbit a y := by
    intro heq
    have hh : a.SameCycle x y := Quotient.exact heq
    rcases (MapFinite.sameCycle_involution a ha x y).mp hh with hh|hh
    · exact (ne_of_lt hxy) hh.symm
    · exact (ne_of_lt hyx) hh
  exact no_crossing_of_maximal_orbits a l.formPerm ha A hmax x y hx hy hne V W X (R++U) hrot

/-- Every orbit-maximal one-colour matching is an actual stack matching. -/
theorem maximal_matching_arches (a : Perm (Dart n)) (ha : Function.Involutive a)
    (hf : ∀ x,a x≠x) (A : Finset (Orbit a))
    (hmax : Nat.card (Orbit (partialReversal a ha A*(List.finRange (2*(n+1))).formPerm))=
      Nat.card (Orbit (List.finRange (2*(n+1))).formPerm)+A.card) :
    ∃ E,Arches (List.finRange (2*(n+1))) E ∧
      (endpoints E).Perm ((List.finRange (2*(n+1))).filter (fun x => decide (orbit a x∈A))) ∧
      ∀ e∈E,e.2=a e.1 ∧ orbit a e.1∈A := by
  classical
  obtain ⟨E,hE,hc,hp⟩ := arches_of_noncrossing a ha (fun x => decide (orbit a x∈A))
    (fun x => by rw [orbit_perm]) (List.finRange (2*(n+1))) (List.pairwise_lt_finRange _)
    (fun x hx hpx => List.mem_finRange _) (fun x hx hpx => hf x)
    (by
      intro x hx y hy hpx hpy hxy hyx hax
      exact ordered_no_crossing a ha _ (List.pairwise_lt_finRange _) List.mem_finRange A hmax x y
        (of_decide_eq_true hpx) (of_decide_eq_true hpy) hxy hyx hax)
  exact ⟨E,hE,hc,fun e he => ⟨(hp e he).1,of_decide_eq_true (hp e he).2⟩⟩

end FKCRT
end


noncomputable section
open List
namespace FKCRT.Inventory
open MapCycles
variable {α : Type*}

lemma scanArches_prefix (f : α→Option Bool) {l v S T : List α} {E : List (α×α)}
    (h : scanArches f l S=some (T,E)) (hv : v<+:l) :
    ∃ R F,scanArches f v S=some (R,F) := by
  obtain ⟨z,rfl⟩ := hv
  rw [scanArches_append] at h
  cases hh : scanArches f v S with
  | none => simp [hh] at h
  | some p => exact ⟨p.1,p.2,rfl⟩

lemma scanArches_color_balance (w : α→TypedLetter) (c : Bool)
    {l S T : List α} {E : List (α×α)}
    (h : scanArches (fun x => colorInstruction c (w x)) l S=some (T,E)) :
    T.length+(l.map w).count (.order c)=S.length+(l.map w).count (.burger c) := by
  induction l generalizing S E with
  | nil => simp only [scanArches,Option.some.injEq,Prod.mk.injEq] at h; simp [h.1]
  | cons x l ih =>
    cases hx : w x with
    | burger b =>
      by_cases hb : b=c
      · subst b
        have hh : scanArches (fun x => colorInstruction c (w x)) l (x::S)=some (T,E) := by
          simpa [scanArches,hx,colorInstruction] using h
        have ht := ih hh
        simpa [hx,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht
      · have hh : scanArches (fun x => colorInstruction c (w x)) l S=some (T,E) := by
          simpa [scanArches,hx,colorInstruction,hb] using h
        simpa [hx,hb] using ih hh
    | order b =>
      by_cases hb : b=c
      · subst b
        cases S with
        | nil => simp [scanArches,hx,colorInstruction] at h
        | cons y S =>
          simp only [scanArches,hx,colorInstruction,ite_true] at h
          obtain ⟨p,hp,hpe⟩ := Option.map_eq_some_iff.mp h
          have hpT : p.1=T := congrArg Prod.fst hpe
          have hp' : scanArches (fun x => colorInstruction c (w x)) l S=some (T,p.2) := by
            simpa only [← hpT,Prod.eta,colorInstruction] using hp
          have ht := congrArg (fun k : ℕ => k+1) (ih hp')
          simpa [hx,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht
      · have hh : scanArches (fun x => colorInstruction c (w x)) l S=some (T,E) := by
          simpa [scanArches,hx,colorInstruction,hb] using h
        simpa [hx,hb] using ih hh

/-- Complete noncrossing matchings give successful typed inventory reduction,
not merely two balanced endpoint counts. -/
theorem typedRun_of_matchings (w : α→TypedLetter) (l : List α) (hn : l.Nodup)
    (E F : List (α×α)) (hE : Arches l E) (hF : Arches l F)
    (hc : (endpoints (E++F)).Perm l)
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false) :
    stackTypedRun (l.map w) []=some [] := by
  have hcov := matching_color_coverage w l E F hc htE htF
  have hscan (c : Bool) : ∃ G,scanArches (fun x => colorInstruction c (w x)) l []=some ([],G) := by
    cases c with
    | true =>
      obtain ⟨G,hG,_⟩ := hE.scan hn (fun x => colorInstruction true (w x))
        (fun e he => by simp [colorInstruction,(htE e he).1,(htE e he).2]) hcov.1 []
      exact ⟨G,hG⟩
    | false =>
      obtain ⟨G,hG,_⟩ := hF.scan hn (fun x => colorInstruction false (w x))
        (fun e he => by simp [colorInstruction,(htF e he).1,(htF e he).2]) hcov.2 []
      exact ⟨G,hG⟩
  have hex : ∃ t,stackTypedRun (l.map w) []=some t := by
    apply (typedRun_exists_iff _ _).mpr
    intro v hv c
    obtain ⟨u,hu,rfl⟩ := List.prefix_map_iff.mp hv
    obtain ⟨G,hG⟩ := hscan c
    obtain ⟨R,H,hH⟩ := scanArches_prefix _ hG hu
    have hh := scanArches_color_balance w c hH
    simp only [List.length_nil,List.count_nil,zero_add] at hh ⊢
    omega
  obtain ⟨t,ht⟩ := hex
  have hc0 (c : Bool) : t.count c=0 := by
    obtain ⟨G,hG⟩ := hscan c
    have hh := scanArches_color_balance w c hG
    have hb := typedRun_balance ht c
    simp only [List.length_nil,List.count_nil,zero_add] at hh hb
    omega
  have ht0 : t=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro c hc
    have hh := List.count_pos_iff.mpr hc
    rw [hc0] at hh
    omega
  simpa only [ht0] using ht

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
namespace MapCycles
variable {α : Type*} [LinearOrder α]

lemma Arches.increasing {l : List α} {E : List (α×α)} (h : Arches l E)
    (hs : l.Pairwise (·<·)) : ∀ e∈E,e.1<e.2 := by
  induction h with
  | nil => simp
  | skip x h ih => exact ih (List.pairwise_cons.mp hs).2
  | pair x y hL hR ihL ihR =>
    have hh := List.pairwise_cons.mp hs
    have ha := List.pairwise_append.mp hh.2
    intro e he
    rcases List.mem_cons.mp he with rfl|he
    · exact hh.1 _ (by simp)
    · rcases List.mem_append.mp he with he|he
      · exact ihL ha.1 e he
      · exact ihR (List.pairwise_cons.mp ha.2.1).2 e he

end MapCycles
namespace Inventory
open MapCycles
variable {n : ℕ}

/-- The actual two-colour opening/closing word in canonical rooted tour order. -/
def matchingWord (a : Perm (Dart n)) (A : Finset (Orbit a)) (i : Dart n) : TypedLetter :=
  if i<a i then .burger (decide (orbit a i∈A)) else .order (decide (orbit a i∈A))

/-- Surjectivity of the stack correspondence on canonical two-colour tours,
with the complete literal inverse pairing and rotation. -/
theorem maximal_matching_word (a : Perm (Dart n)) (ha : Function.Involutive a)
    (hf : ∀ i,a i≠i) (A : Finset (Orbit a))
    (hE : Nat.card (Orbit (partialReversal a ha A*(List.finRange (2*(n+1))).formPerm))=
      Nat.card (Orbit (List.finRange (2*(n+1))).formPerm)+A.card)
    (hF : Nat.card (Orbit (partialReversal a ha Aᶜ*(List.finRange (2*(n+1))).formPerm))=
      Nat.card (Orbit (List.finRange (2*(n+1))).formPerm)+Aᶜ.card) :
    stackTypedRun ((List.finRange (2*(n+1))).map (matchingWord a A)) []=some [] ∧
    ∃ E F,Arches (List.finRange (2*(n+1))) E ∧ Arches (List.finRange (2*(n+1))) F ∧
      (endpoints (E++F)).Perm (List.finRange (2*(n+1))) ∧
      (∀ e∈E,matchingWord a A e.1=.burger true ∧ matchingWord a A e.2=.order true) ∧
      (∀ e∈F,matchingWord a A e.1=.burger false ∧ matchingWord a A e.2=.order false) ∧
      turns (E++F)=a ∧ turns E=partialReversal a ha A := by
  obtain ⟨E,he,hce,hpe⟩ := maximal_matching_arches a ha hf A hE
  obtain ⟨F,hf',hcf,hpf⟩ := maximal_matching_arches a ha hf Aᶜ hF
  have hien := he.increasing (List.pairwise_lt_finRange _)
  have hifn := hf'.increasing (List.pairwise_lt_finRange _)
  have hc : (endpoints (E++F)).Perm (List.finRange (2*(n+1))) := by
    rw [endpoints_append]
    apply (hce.append hcf).trans
    simpa only [Finset.mem_compl,decide_not] using
      List.filter_append_perm (fun x => decide (orbit a x∈A)) (List.finRange (2*(n+1)))
  have htE : ∀ e∈E,matchingWord a A e.1=.burger true ∧ matchingWord a A e.2=.order true := by
    intro e he'
    obtain ⟨hei,hmem⟩ := hpe e he'
    have hlt := hien e he'
    have heii : a e.2=e.1 := by rw [hei,ha]
    have hm2 : orbit a e.2∈A := by rw [hei,orbit_perm]; exact hmem
    simp only [matchingWord,← hei,heii,ite_eq_left hlt,ite_eq_right (not_lt_of_ge hlt.le),
      decide_eq_true hmem,decide_eq_true hm2,and_self]
  have htF : ∀ e∈F,matchingWord a A e.1=.burger false ∧ matchingWord a A e.2=.order false := by
    intro e he'
    obtain ⟨hei,hmem⟩ := hpf e he'
    have hlt := hifn e he'
    have heii : a e.2=e.1 := by rw [hei,ha]
    have hm1 : orbit a e.1∉A := Finset.mem_compl.mp hmem
    have hm2 : orbit a e.2∉A := by rw [hei,orbit_perm]; exact hm1
    simp only [matchingWord,← hei,heii,ite_eq_left hlt,ite_eq_right (not_lt_of_ge hlt.le),
      decide_eq_false hm1,decide_eq_false hm2,and_self]
  have hn : (endpoints (E++F)).Nodup := hc.nodup_iff.mpr (List.nodup_finRange _)
  have ha' : turns (E++F)=a := by
    apply Equiv.ext
    intro i
    obtain ⟨e,he',rfl|rfl⟩ := mem_endpoints.mp (hc.mem_iff.mpr (List.mem_finRange i))
    · rw [(turns_pair hn e he').1]
      rcases List.mem_append.mp he' with he'|he'
      · exact (hpe e he').1
      · exact (hpf e he').1
    · rw [(turns_pair hn e he').2]
      have hh : e.2=a e.1 := by
        rcases List.mem_append.mp he' with he'|he'
        · exact (hpe e he').1
        · exact (hpf e he').1
      rw [hh,ha]
  have hpart : turns E=partialReversal a ha A := by
    apply Equiv.ext
    intro i
    rw [partialReversal_apply]
    have hmem : i∈endpoints E ↔ orbit a i∈A := by
      rw [hce.mem_iff,List.mem_filter]
      simp
    split_ifs with hi
    · rw [turns_sublist_apply hn (List.sublist_append_left _ _) (hmem.mpr hi),ha']
    · exact turns_fixed_of_notMem (fun h => hi (hmem.mp h))
  exact ⟨typedRun_of_matchings _ _ (List.nodup_finRange _) E F he hf' hc htE htF,
    E,F,he,hf',hc,htE,htF,ha',hpart⟩

end Inventory
end FKCRT
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_Matching
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
namespace Chords
variable {N : ℕ}

lemma componentDarts_mate (a : Perm (Fin N)) (ha : Function.Involutive a)
    (r : Opener a) (d : Fin N) :
    a d∈componentDarts a r ↔ d∈componentDarts a r := by
  have hd (i : Fin N) : i∈componentDarts a r → a i∈componentDarts a r := by
    intro hi
    obtain ⟨x,hx,rfl|rfl⟩ := (mem_componentDarts a r i).mp hi
    · exact (mem_componentDarts a r _).mpr ⟨x,hx,Or.inr rfl⟩
    · rw [ha]
      exact (mem_componentDarts a r _).mpr ⟨x,hx,Or.inl rfl⟩
  constructor
  · intro h
    have hh := hd (a d) h
    rw [ha] at hh
    exact hh
  · exact hd d

def opener (a : Perm (Fin N)) (ha : Function.Involutive a) (hf : ∀ d,a d≠d)
    (d : Fin N) : Opener a :=
  if h : d<a d then ⟨d,h⟩ else ⟨a d,by rw [ha]; exact lt_of_le_of_ne (le_of_not_gt h) (hf d)⟩

lemma opener_endpoints (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) (d : Fin N) :
    d=(opener a ha hf d).val ∨ d=a (opener a ha hf d).val := by
  unfold opener
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (ha d).symm

lemma gapIndex_mate (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) (r : Opener a) (hr : r.val.val=0)
    (d : Fin N) (hd : d∉componentDarts a r) : gapIndex a r (a d)=gapIndex a r d := by
  let f := opener a ha hf d
  have hroot : r.val≤f.val := by change r.val.val≤f.val.val; rw [hr]; omega
  have he := opener_endpoints a ha hf d
  have hn : ¬(graph a).Reachable r f := fun h => hd ((mem_componentDarts a r d).mpr ⟨f,h,he⟩)
  have hh := exterior_same_gap a ha r f hroot hn
  rcases he with he|he
  · rw [he]; exact hh.symm
  · rw [he,ha]; exact hh

end Chords
end FKCRT
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CornerInsertion
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List
open scoped BigOperators
namespace FKCRT.Inventory

lemma typedStep_suffix {s t r : List Bool} {a : TypedLetter}
    (h : stackTypedStep s a=some t) : stackTypedStep (s++r) a=some (t++r) := by
  cases a with
  | burger b => simpa only [stackTypedStep,Option.some.injEq,List.cons_append] using congrArg (·++r) (Option.some.inj h)
  | order b =>
    simp only [stackTypedStep,pop_fixed] at h ⊢
    split_ifs at h with hb
    · cases h
      rw [ite_eq_left (List.mem_append_left _ hb),List.erase_append_left r hb]

lemma flexibleClosing_suffix {s t r : List Bool} {a : TypedLetter}
    (h : stackTypedStep s a=some t) : flexibleClosing (s++r) a ↔ flexibleClosing s a := by
  cases a with
  | burger b => rfl
  | order b =>
    cases s with
    | nil => simp [stackTypedStep,pop] at h
    | cons c s => rfl

lemma typedRun_suffix {w : List TypedLetter} {s t : List Bool}
    (h : stackTypedRun w s=some t) (r : List Bool) :
    stackTypedRun w (s++r)=some (t++r) ∧ flexibleCount w (s++r)=flexibleCount w s := by
  induction w generalizing s with
  | nil =>
    simp only [stackTypedRun,Option.some.injEq] at h
    subst t
    simp [stackTypedRun,flexibleCount]
  | cons a w ih =>
    cases hs : stackTypedStep s a with
    | none => simp [stackTypedRun,hs] at h
    | some s' =>
      simp only [stackTypedRun,hs,Option.bind_some] at h
      obtain ⟨hr,hf⟩ := ih h
      have hS := typedStep_suffix (r:=r) hs
      constructor
      · simpa [stackTypedRun,hS] using hr
      · simp only [flexibleCount,hS,hs,hf,flexibleClosing_suffix hs]

lemma flexibleCount_append {u : List TypedLetter} (v : List TypedLetter) {s t : List Bool}
    (h : stackTypedRun u s=some t) : flexibleCount (u++v) s=flexibleCount u s+flexibleCount v t := by
  induction u generalizing s with
  | nil =>
    simp only [stackTypedRun,Option.some.injEq] at h
    subst t
    simp [flexibleCount]
  | cons a u ih =>
    cases hs : stackTypedStep s a with
    | none => simp [stackTypedRun,hs] at h
    | some s' =>
      simp only [stackTypedRun,hs,Option.bind_some] at h
      simp only [List.cons_append,flexibleCount,hs,ih h,Nat.add_assoc]

lemma empty_word_context {w : List TypedLetter} (h : stackTypedRun w []=some []) (s : List Bool) :
    stackTypedRun w s=some s ∧ flexibleCount w s=flexibleCount w [] := by
  simpa using typedRun_suffix h s

/-- Literal corner insertion, keeping the root skeleton letters in order. -/
def cornerInsert (l : List (TypedLetter×List TypedLetter)) : List TypedLetter :=
  l.flatMap (fun x => x.1::x.2)

/-- Successful corner words preserve the current stack and have exactly the
same flexible exponent there as from the empty stack. This proves weight
multiplicativity, including empty inserts, with no independence hypothesis. -/
theorem cornerInsert_run_count (l : List (TypedLetter×List TypedLetter))
    (hg : ∀ x∈l,stackTypedRun x.2 []=some []) {s t : List Bool}
    (h : stackTypedRun (l.map Prod.fst) s=some t) :
    stackTypedRun (cornerInsert l) s=some t ∧
      flexibleCount (cornerInsert l) s=flexibleCount (l.map Prod.fst) s+
        (l.map (fun x => flexibleCount x.2 [])).sum := by
  induction l generalizing s with
  | nil => simpa [cornerInsert,stackTypedRun,flexibleCount] using h
  | cons x l ih =>
    cases hs : stackTypedStep s x.1 with
    | none => simp [stackTypedRun,hs] at h
    | some s' =>
      simp only [List.map_cons,stackTypedRun,hs,Option.bind_some] at h
      obtain ⟨hr,hc⟩ := ih (fun y hy => hg y (List.mem_cons_of_mem _ hy)) h
      obtain ⟨hgr,hgc⟩ := empty_word_context (hg x (List.mem_cons_self)) s'
      constructor
      · simp only [cornerInsert,List.flatMap_cons,List.cons_append,stackTypedRun,hs,Option.bind_some]
        rw [typedRun_append,hgr,Option.bind_some]
        exact hr
      · simp only [cornerInsert,List.flatMap_cons,List.cons_append,flexibleCount,hs,
          List.map_cons,List.sum_cons]
        rw [flexibleCount_append _ hgr,hgc]
        change _+(_+flexibleCount (cornerInsert l) s')=_
        rw [hc]
        omega

end FKCRT.Inventory
end


noncomputable section
open List
namespace FKCRT.CornerSplit
variable {α : Type*}

/-- Split at marked letters, retaining every letter and the possibly empty
prefix before the first mark. The marks themselves label the corners. -/
def split (p : α→Bool) : List α→List α × List (α×List α)
  | [] => ([],[])
  | a::w => let r := split p w
    if p a then ([],(a,r.1)::r.2) else (a::r.1,r.2)

def join (l : List (α×List α)) : List α := l.flatMap (fun x => x.1::x.2)

lemma reassemble (p : α→Bool) (w : List α) :
    (split p w).1++join (split p w).2=w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases hp : p a <;> simpa [split,hp,join] using congrArg (a::·) ih

lemma skeleton (p : α→Bool) (w : List α) :
    ((split p w).2.map Prod.fst)=w.filter p := by
  induction w with
  | nil => rfl
  | cons a w ih => cases hp : p a <;> simp [split,hp,ih]

lemma unmarked_prefix (p : α→Bool) (w : List α) :
    ∀ a∈(split p w).1,p a=false := by
  induction w with
  | nil => simp [split]
  | cons a w ih =>
    cases hp : p a with
    | false => simpa [split,hp] using ih
    | true => simp [split,hp]

lemma marked_corners (p : α→Bool) (w : List α) :
    ∀ x∈(split p w).2,p x.1=true ∧ ∀ a∈x.2,p a=false := by
  induction w with
  | nil => simp [split]
  | cons a w ih =>
    cases hp : p a with
    | false => simpa [split,hp] using ih
    | true =>
      simp only [split,hp,ite_true,List.mem_cons]
      intro x hx
      rcases hx with rfl|hx
      · exact ⟨hp,unmarked_prefix p w⟩
      · exact ih x hx

lemma prefix_nil (p : α→Bool) {a : α} {w : List α} (h : p a=true) :
    (split p (a::w)).1=[] := by simp [split,h]

lemma split_unmarked_append (p : α→Bool) {u : List α}
    (hu : ∀ a∈u,p a=false) (v : List α) :
    split p (u++v)=(u++(split p v).1,(split p v).2) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    have ha := hu a (List.mem_cons_self)
    have hh := ih (fun b hb => hu b (List.mem_cons_of_mem _ hb))
    simp [split,ha,hh]

/-- Exact inverse, including empty corner inserts and the final corner. -/
lemma split_join (p : α→Bool) (l : List (α×List α))
    (h : ∀ x∈l,p x.1=true ∧ ∀ a∈x.2,p a=false) :
    split p (join l)=([],l) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨hx,hu⟩ := h x (List.mem_cons_self)
    have hh := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [join,List.flatMap_cons,List.cons_append,split,hx,ite_true]
    rw [split_unmarked_append p hu]
    change ([],(x.1,x.2++(split p (join l)).1)::(split p (join l)).2)=([],x::l)
    simp [hh]

lemma join_first_marked (p : α→Bool) (l : List (α×List α))
    (h : ∀ x∈l,p x.1=true) :
    join l=[] ∨ ∃ a v,join l=a::v ∧ p a=true := by
  cases l with
  | nil => exact Or.inl rfl
  | cons x l =>
    exact Or.inr ⟨x.1,x.2++join l,rfl,h x (List.mem_cons_self)⟩

/-- Every extracted corner is an actual consecutive interval, bounded on
its right by the next marked letter (or the end of the word). -/
lemma located (p : α→Bool) (w : List α) (x : α×List α) (hx : x∈(split p w).2) :
    ∃ u v,w=u++x.1::(x.2++v) ∧
      (v=[] ∨ ∃ b t,v=b::t ∧ p b=true) := by
  induction w with
  | nil => simp [split] at hx
  | cons a w ih =>
    cases hp : p a with
    | false =>
      simp only [split,hp,Bool.false_eq_true,ite_false] at hx
      obtain ⟨u,v,hw,hv⟩ := ih hx
      exact ⟨a::u,v,by simp only [hw,List.cons_append],hv⟩
    | true =>
      simp only [split,hp,ite_true,List.mem_cons] at hx
      rcases hx with rfl|hx
      · refine ⟨[],join (split p w).2,?_,?_⟩
        · simpa only [List.nil_append] using congrArg (a::·) (reassemble p w).symm
        · exact join_first_marked p _ (fun y hy => (marked_corners p w y hy).1)
      · obtain ⟨u,v,hw,hv⟩ := ih hx
        exact ⟨a::u,v,by simp only [hw,List.cons_append],hv⟩



end FKCRT.CornerSplit
end


noncomputable section
open List
namespace FKCRT.MapCycles
variable {α : Type*}

/-- Empty corner scans preserve the pre-existing stack while contributing
exactly their own pairs. Thus insertion creates no cross-corner matching. -/
theorem scanArches_corners (f : α→Option Bool) (l : List (α×List α))
    (G : α×List α→List (α×α))
    (hg : ∀ x∈l,∀ S,scanArches f x.2 S=some (S,G x))
    {S T : List α} {E : List (α×α)}
    (h : scanArches f (l.map Prod.fst) S=some (T,E)) :
    ∃ F,scanArches f (CornerSplit.join l) S=some (T,F) ∧
      F.Perm (E++l.flatMap G) := by
  induction l generalizing S E with
  | nil =>
    simp only [List.map_nil,scanArches,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    exact ⟨[],rfl,.refl _⟩
  | cons x l ih =>
    have hcore : scanArches f ([x.1]++l.map Prod.fst) S=some (T,E) := h
    rw [scanArches_append] at hcore
    cases hs : scanArches f [x.1] S with
    | none => simp [hs] at hcore
    | some V =>
      cases ht : scanArches f (l.map Prod.fst) V.1 with
      | none => simp [hs,ht] at hcore
      | some W =>
        simp only [hs,Option.bind_some,ht,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hcore
        have hw : scanArches f (l.map Prod.fst) V.1=some (T,W.2) := by
          rw [ht,← hcore.1]
        obtain ⟨F,hF,hperm⟩ := ih (fun y hy => hg y (List.mem_cons_of_mem _ hy)) hw
        refine ⟨V.2++G x++F,?_,?_⟩
        · change scanArches f ([x.1]++(x.2++CornerSplit.join l)) S=_
          simp only [scanArches_append,hs,Option.bind_some,hg x List.mem_cons_self,
            hF,Option.map_some]
          simp only [List.append_assoc]
        · rw [← hcore.2,List.flatMap_cons]
          simp only [List.append_assoc]
          apply ((hperm.append_left (G x)).append_left V.2).trans
          simpa only [List.append_assoc] using
            ((List.perm_append_comm (l₁:=G x) (l₂:=W.2)).append_right (l.flatMap G)).append_left V.2

/-- A standalone empty scan is unchanged by an arbitrary underlying stack. -/
lemma scanArches_suffix (f : α→Option Bool) {l S T : List α} {E : List (α×α)}
    (h : scanArches f l S=some (T,E)) (R : List α) :
    scanArches f l (S++R)=some (T++R,E) := by
  induction l generalizing S E with
  | nil =>
    simp only [scanArches,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    rfl
  | cons a l ih =>
    cases hf : f a with
    | none =>
      simp only [scanArches,hf] at h ⊢
      exact ih h
    | some b =>
      cases b with
      | true =>
        simp only [scanArches,hf] at h
        simpa only [scanArches,hf,List.cons_append] using ih h
      | false =>
        cases S with
        | nil => simp [scanArches,hf] at h
        | cons s S =>
          simp only [scanArches,hf] at h
          obtain ⟨p,hp,he⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨hT,hE⟩ := Prod.mk.inj he
          have hp' : scanArches f l S=some (T,p.2) := by
            rw [hp,← hT]
          have hh := ih hp'
          simp only [scanArches,hf,List.cons_append,hh,Option.map_some,hE]

end FKCRT.MapCycles

namespace FKCRT.Inventory
open MapCycles
variable {α : Type*}

/-- Matchings on an arbitrary ordered subword. The original positions are
retained, so this lemma can be applied inside a larger inventory word. -/
theorem ordered_matchings (w : α→TypedLetter) (l : List α)
    (hw : stackTypedRun (l.map w) []=some []) :
    ∃ E F : List (α×α),Arches l E ∧ Arches l F ∧
      (endpoints (E++F)).Perm l ∧
      (∀ e∈E,w e.1=.burger true ∧ w e.2=.order true) ∧
      (∀ e∈F,w e.1=.burger false ∧ w e.2=.order false) := by
  let L (c : Bool) := l.filter (fun i => (w i).color == c)
  have hh (c : Bool) : (L c).map (fun i => (w i).step)=(identifiedDyck hw c).toList :=
    (colorWord_map w l c).symm
  obtain ⟨E,hE,hEp,hEf⟩ := dyck_arches (identifiedDyck hw true) (L true) _ (hh true)
  obtain ⟨F,hF,hFp,hFf⟩ := dyck_arches (identifiedDyck hw false) (L false) _ (hh false)
  have hp : (L true++L false).Perm l := by
    have hp := List.filter_append_perm (fun i => (w i).color) l
    simpa [L] using hp
  refine ⟨E,F,hE.mono (List.filter_sublist),hF.mono (List.filter_sublist),?_,?_,?_⟩
  · rw [endpoints_append]
    exact (hEp.append hFp).trans hp
  · intro e he
    have he' := hE.endpoints e he
    have h1 : (w e.1).color=true := by simpa [L] using (List.mem_filter.mp he'.1).2
    have h2 : (w e.2).color=true := by simpa [L] using (List.mem_filter.mp he'.2).2
    have hs := hEf e he
    constructor
    · cases hh : w e.1 <;> simp_all [TypedLetter.color,TypedLetter.step]
    · cases hh : w e.2 <;> simp_all [TypedLetter.color,TypedLetter.step]
  · intro e he
    have he' := hF.endpoints e he
    have h1 : (w e.1).color=false := by simpa [L] using (List.mem_filter.mp he'.1).2
    have h2 : (w e.2).color=false := by simpa [L] using (List.mem_filter.mp he'.2).2
    have hs := hFf e he
    constructor
    · cases hh : w e.1 <;> simp_all [TypedLetter.color,TypedLetter.step]
    · cases hh : w e.2 <;> simp_all [TypedLetter.color,TypedLetter.step]


/-- An actually empty typed subword has a deterministic one-colour
matching which is unchanged by any underlying stack. -/
theorem empty_typed_scan (w : α→TypedLetter) (l : List α) (hn : l.Nodup)
    (hw : stackTypedRun (l.map w) []=some []) (c : Bool) :
    ∃ E, (∀ S,scanArches (fun x => colorInstruction c (w x)) l S=some (S,E)) ∧
      (endpoints E).Perm (l.filter (fun x => (w x).color == c)) := by
  obtain ⟨E,F,hE,hF,hc,htE,htF⟩ := ordered_matchings w l hw
  have hcov := matching_color_coverage w l E F hc htE htF
  have hscan : ∃ G,scanArches (fun x => colorInstruction c (w x)) l []=some ([],G) := by
    cases c with
    | true =>
      obtain ⟨G,hG,_⟩ := hE.scan hn (fun x => colorInstruction true (w x))
        (fun e he => by simp [colorInstruction,(htE e he).1,(htE e he).2]) hcov.1 []
      exact ⟨G,hG⟩
    | false =>
      obtain ⟨G,hG,_⟩ := hF.scan hn (fun x => colorInstruction false (w x))
        (fun e he => by simp [colorInstruction,(htF e he).1,(htF e he).2]) hcov.2 []
      exact ⟨G,hG⟩
  obtain ⟨G,hG⟩ := hscan
  refine ⟨G,(fun S => by simpa using scanArches_suffix _ hG S),?_⟩
  have hcG : (endpoints G).Nodup := by
    cases c with
    | true =>
      obtain ⟨H,hH,hHE⟩ := hE.scan hn (fun x => colorInstruction true (w x))
        (fun e he => by simp [colorInstruction,(htE e he).1,(htE e he).2]) hcov.1 []
      have he : G=H := congrArg Prod.snd (Option.some.inj (hG.symm.trans hH))
      rw [he]
      exact (endpoints_perm hHE).nodup_iff.mpr (by
        have hh := hc.nodup_iff.mpr hn
        rw [endpoints_append] at hh
        exact hh.of_append_left)
    | false =>
      obtain ⟨H,hH,hHF⟩ := hF.scan hn (fun x => colorInstruction false (w x))
        (fun e he => by simp [colorInstruction,(htF e he).1,(htF e he).2]) hcov.2 []
      have he : G=H := congrArg Prod.snd (Option.some.inj (hG.symm.trans hH))
      rw [he]
      exact (endpoints_perm hHF).nodup_iff.mpr (by
        have hh := hc.nodup_iff.mpr hn
        rw [endpoints_append] at hh
        exact hh.of_append_right)
  apply List.perm_ext_iff_of_nodup hcG (hn.filter _)|>.mpr
  intro x
  cases c with
  | true =>
    obtain ⟨H,hH,hHE⟩ := hE.scan hn (fun x => colorInstruction true (w x))
      (fun e he => by simp [colorInstruction,(htE e he).1,(htE e he).2]) hcov.1 []
    have he : G=H := congrArg Prod.snd (Option.some.inj (hG.symm.trans hH))
    rw [he,(endpoints_perm hHE).mem_iff]
    constructor
    · intro hx
      obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hx
      · simp [List.mem_filter,(hE.endpoints e he).1,(htE e he).1,TypedLetter.color]
      · simp [List.mem_filter,(hE.endpoints e he).2,(htE e he).2,TypedLetter.color]
    · intro hx
      obtain ⟨hx,hcol⟩ := List.mem_filter.mp hx
      apply hcov.1 x hx
      cases h : w x <;> simpa [h,TypedLetter.color,colorInstruction] using hcol
  | false =>
    obtain ⟨H,hH,hHF⟩ := hF.scan hn (fun x => colorInstruction false (w x))
      (fun e he => by simp [colorInstruction,(htF e he).1,(htF e he).2]) hcov.2 []
    have he : G=H := congrArg Prod.snd (Option.some.inj (hG.symm.trans hH))
    rw [he,(endpoints_perm hHF).mem_iff]
    constructor
    · intro hx
      obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hx
      · simp [List.mem_filter,(hF.endpoints e he).1,(htF e he).1,TypedLetter.color]
      · simp [List.mem_filter,(hF.endpoints e he).2,(htF e he).2,TypedLetter.color]
    · intro hx
      obtain ⟨hx,hcol⟩ := List.mem_filter.mp hx
      apply hcov.2 x hx
      cases h : w x <;> simpa [h,TypedLetter.color,colorInstruction] using hcol

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*}

/-- Exact locality of the actual stack matching on an empty interval. -/
lemma scanArches_interval_subset (f : α→Option Bool) (u v z S T : List α)
    {E G : List (α×α)} (h : scanArches f (u++(v++z)) S=some (T,E))
    (hv : scanArches f v []=some ([],G)) : ∀ e∈G,e∈E := by
  rw [scanArches_append] at h
  cases hu : scanArches f u S with
  | none => simp [hu] at h
  | some U =>
    have hv' : scanArches f v U.1=some (U.1,G) := by simpa using scanArches_suffix f hv U.1
    simp only [hu,Option.bind_some,scanArches_append,hv'] at h
    cases hz : scanArches f z U.1 with
    | none => simp [hz] at h
    | some Z =>
      simp only [hz,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
      intro e he
      rw [← h.2]
      exact List.mem_append_right _ (List.mem_append_left _ he)

end FKCRT.MapCycles
namespace FKCRT.Inventory
open MapCycles
variable {α : Type*} [DecidableEq α]

/-- Any actual successful consecutive subword is closed under the *full*
word's matching. In particular successful corner inserts do not rematch an
old endpoint to a new one. -/
theorem empty_interval_matching_closed (w : α→TypedLetter) (u v z : List α)
    (hn : (u++(v++z)).Nodup) (E F : List (α×α))
    (hE : Arches (u++(v++z)) E) (hF : Arches (u++(v++z)) F)
    (hcov : (endpoints (E++F)).Perm (u++(v++z)))
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false)
    (hv : stackTypedRun (v.map w) []=some []) :
    ∀ d∈v,turns (E++F) d∈v := by
  obtain ⟨E',F',hE',hF',hc',htE',htF'⟩ := ordered_matchings w v hv
  have hfullcov := matching_color_coverage w (u++(v++z)) E F hcov htE htF
  have hlocalcov := matching_color_coverage w v E' F' hc' htE' htF'
  have hnv : v.Nodup := hn.of_append_right.of_append_left
  have hsubE : ∀ e∈E',e∈E := by
    obtain ⟨G,hG,hGE⟩ := hE.scan hn (fun x => colorInstruction true (w x))
      (fun e he => by simp [colorInstruction,(htE e he).1,(htE e he).2]) hfullcov.1 []
    obtain ⟨G',hG',hGE'⟩ := hE'.scan hnv (fun x => colorInstruction true (w x))
      (fun e he => by simp [colorInstruction,(htE' e he).1,(htE' e he).2]) hlocalcov.1 []
    intro e he
    exact hGE.mem_iff.mp (scanArches_interval_subset _ u v z [] [] hG hG' e (hGE'.mem_iff.mpr he))
  have hsubF : ∀ e∈F',e∈F := by
    obtain ⟨G,hG,hGF⟩ := hF.scan hn (fun x => colorInstruction false (w x))
      (fun e he => by simp [colorInstruction,(htF e he).1,(htF e he).2]) hfullcov.2 []
    obtain ⟨G',hG',hGF'⟩ := hF'.scan hnv (fun x => colorInstruction false (w x))
      (fun e he => by simp [colorInstruction,(htF' e he).1,(htF' e he).2]) hlocalcov.2 []
    intro e he
    exact hGF.mem_iff.mp (scanArches_interval_subset _ u v z [] [] hG hG' e (hGF'.mem_iff.mpr he))
  have hnE : (endpoints (E++F)).Nodup := hcov.nodup_iff.mpr hn
  intro d hd
  obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp (hc'.mem_iff.mpr hd)
  · rcases List.mem_append.mp he with he|he
    · rw [(turns_pair hnE e (List.mem_append_left _ (hsubE e he))).1]
      exact (hE'.endpoints e he).2
    · rw [(turns_pair hnE e (List.mem_append_right _ (hsubF e he))).1]
      exact (hF'.endpoints e he).2
  · rcases List.mem_append.mp he with he|he
    · rw [(turns_pair hnE e (List.mem_append_left _ (hsubE e he))).2]
      exact (hE'.endpoints e he).1
    · rw [(turns_pair hnE e (List.mem_append_right _ (hsubF e he))).2]
      exact (hF'.endpoints e he).1

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT.Chords
variable {N : ℕ}

lemma gapIndex_strict (a : Perm (Fin N)) (r : Opener a)
    {i j c : Fin N} (hc : c∈componentDarts a r) (hic : i ≤ c) (hcj : c<j) :
    gapIndex a r i<gapIndex a r j := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro d hd
    obtain ⟨hd,hdi⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨hd,(hdi.trans_le hic).trans hcj⟩
  · intro h
    have hmem : c∈(componentDarts a r).filter (·<j) := Finset.mem_filter.mpr ⟨hc,hcj⟩
    rw [← h] at hmem
    exact not_lt_of_ge hic (Finset.mem_filter.mp hmem).2

def rootSplit (a : Perm (Fin N)) (r : Opener a) : List (Fin N×List (Fin N)) :=
  (CornerSplit.split (fun d => decide (d∈componentDarts a r)) (List.finRange N)).2

lemma rootSplit_prefix (a : Perm (Fin N)) (r : Opener a) (hr : r.val.val=0) :
    (CornerSplit.split (fun d => decide (d∈componentDarts a r)) (List.finRange N)).1=[] := by
  cases N with
  | zero => exact Fin.elim0 r.val
  | succ N =>
    rw [List.finRange_succ]
    apply CornerSplit.prefix_nil
    apply decide_eq_true
    have hr0 : r.val=0 := Fin.ext hr
    exact (mem_componentDarts a r 0).mpr ⟨r,SimpleGraph.Reachable.refl r,Or.inl hr0.symm⟩

lemma rootSplit_join (a : Perm (Fin N)) (r : Opener a) (hr : r.val.val=0) :
    CornerSplit.join (rootSplit a r)=List.finRange N := by
  have h := CornerSplit.reassemble (fun d => decide (d∈componentDarts a r)) (List.finRange N)
  simpa only [rootSplit_prefix a r hr,List.nil_append,rootSplit] using h

/-- The literal interval chunks extracted from a root crossing component
are closed under the actual edge pairing. No fresh independent matching
is substituted at the corners. -/
theorem rootSplit_closed (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) (r : Opener a) (hr : r.val.val=0)
    (x : Fin N×List (Fin N)) (hx : x∈rootSplit a r) :
    ∀ d∈x.2,a d∈x.2 := by
  let p := fun d => decide (d∈componentDarts a r)
  have hx' : x∈(CornerSplit.split p (List.finRange N)).2 := hx
  obtain ⟨hmark,hunmark⟩ := CornerSplit.marked_corners p (List.finRange N) x hx'
  obtain ⟨u,v,he,hv⟩ := CornerSplit.located p (List.finRange N) x hx'
  have hcm : x.1∈componentDarts a r := of_decide_eq_true hmark
  have hs : (u++x.1::(x.2++v)).Pairwise (·<·) := he ▸ List.pairwise_lt_finRange N
  obtain ⟨_,hrest,hleft⟩ := List.pairwise_append.mp hs
  obtain ⟨hfirst,htail⟩ := List.pairwise_cons.mp hrest
  obtain ⟨_,_,hright⟩ := List.pairwise_append.mp htail
  intro d hd
  have hdn : d∉componentDarts a r := of_decide_eq_false (hunmark d hd)
  have han : a d∉componentDarts a r := fun h => hdn ((componentDarts_mate a ha r d).mp h)
  have hgap := gapIndex_mate a ha hf r hr d hdn
  have hm : a d∈u++x.1::(x.2++v) := by rw [← he]; exact List.mem_finRange _
  rcases List.mem_append.mp hm with hu|hm
  · have hlt := hleft (a d) hu x.1 (List.mem_cons_self)
    have hlt' := hfirst d (List.mem_append_left _ hd)
    have hh := gapIndex_strict a r hcm hlt.le hlt'
    omega
  · rcases List.mem_cons.mp hm with h|hm
    · exact False.elim (han (h ▸ hcm))
    · rcases List.mem_append.mp hm with hm|hh
      · exact hm
      · rcases hv with rfl|⟨b,t,rfl,hb⟩
        · simp at hh
        · have hbm : b∈componentDarts a r := of_decide_eq_true hb
          have hdb : d<b := hright d hd b (List.mem_cons_self)
          rcases List.mem_cons.mp hh with hab|hab
          · exact False.elim (han (hab ▸ hbm))
          · have hbt : b<a d := (List.pairwise_cons.mp (List.pairwise_append.mp htail).2.1).1 _ hab
            have hg := gapIndex_strict a r hbm hdb.le hbt
            omega

lemma rootSplit_length_lt (a : Perm (Fin N)) (r : Opener a)
    (x : Fin N×List (Fin N)) (hx : x∈rootSplit a r) : x.2.length<N := by
  obtain ⟨u,v,he,_⟩ := CornerSplit.located (fun d => decide (d∈componentDarts a r))
    (List.finRange N) x hx
  have h := congrArg List.length he
  simp only [List.length_finRange,List.length_append,List.length_cons] at h
  omega

end FKCRT.Chords

namespace FKCRT.Inventory
open Chords
variable {N : ℕ}

lemma cornerInsert_map {α : Type*} (f : α→TypedLetter) (l : List (α×List α)) :
    cornerInsert (l.map (fun x => (f x.1,x.2.map f)))=(CornerSplit.join l).map f := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa [cornerInsert,CornerSplit.join] using congrArg (fun z => f x.1::(x.2.map f++z)) ih

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Chords
variable {N : ℕ}

/-- Consecutive chunks are order-convex in the actual dart tour. -/
lemma chunk_convex (p : Fin N→Bool) (x : Fin N×List (Fin N))
    (hx : x∈(CornerSplit.split p (List.finRange N)).2)
    {i j k : Fin N} (hi : i∈x.2) (hj : j∈x.2) (hik : i≤k) (hkj : k≤j) : k∈x.2 := by
  obtain ⟨u,v,he,_⟩ := CornerSplit.located p (List.finRange N) x hx
  have hs : (u++x.1::(x.2++v)).Pairwise (·<·) := he ▸ List.pairwise_lt_finRange N
  obtain ⟨_,hs',hleft⟩ := List.pairwise_append.mp hs
  obtain ⟨hfirst,hs''⟩ := List.pairwise_cons.mp hs'
  obtain ⟨_,_,hright⟩ := List.pairwise_append.mp hs''
  have hk : k∈u++x.1::(x.2++v) := by rw [← he]; exact List.mem_finRange _
  rcases List.mem_append.mp hk with hk|hk
  · have hlt := hleft k hk i (List.mem_cons_of_mem _ (List.mem_append_left _ hi))
    exact False.elim ((not_lt_of_ge hik) hlt)
  · rcases List.mem_cons.mp hk with rfl|hk
    · exact False.elim ((not_lt_of_ge hik) (hfirst i (List.mem_append_left _ hi)))
    · rcases List.mem_append.mp hk with hk|hk
      · exact hk
      · exact False.elim ((not_lt_of_ge hkj) (hright j hj k hk))

lemma unmarked_in_chunk (p : Fin N→Bool) (hN : 0<N) (hp : p ⟨0,hN⟩=true)
    {d : Fin N} (hd : p d=false) :
    ∃ x∈(CornerSplit.split p (List.finRange N)).2,d∈x.2 := by
  have hpref : (CornerSplit.split p (List.finRange N)).1=[] := by
    cases N with
    | zero => omega
    | succ N => rw [List.finRange_succ]; exact CornerSplit.prefix_nil p hp
  have he := CornerSplit.reassemble p (List.finRange N)
  rw [hpref,List.nil_append] at he
  have hm : d∈CornerSplit.join (CornerSplit.split p (List.finRange N)).2 := by
    rw [he]; exact List.mem_finRange _
  obtain ⟨x,hx,hdx⟩ := List.mem_flatMap.mp hm
  refine ⟨x,hx,?_⟩
  rcases List.mem_cons.mp hdx with rfl|hdx
  · have ht := (CornerSplit.marked_corners p (List.finRange N) x hx).1
    simp [ht] at hd
  · exact hdx

/-- Matching edges in distinct empty corners cannot cross a core edge. -/
theorem no_cross_core_corner (a : Perm (Fin N)) (p : Fin N→Bool)
    (hcore : ∀ d,p (a d)=p d)
    (hchunks : ∀ x∈(CornerSplit.split p (List.finRange N)).2,∀ d∈x.2,a d∈x.2)
    (hp : ∀ d : Fin N,d.val=0 → p d=true)
    (x y : Opener a) (hx : p x.val=true) (hy : p y.val=false) : ¬Cross a x y := by
  have hN : 0<N := y.val.pos
  obtain ⟨z,hz,hyz⟩ := unmarked_in_chunk p hN (hp ⟨0,hN⟩ rfl) hy
  have hayz := hchunks z hz y.val hyz
  have hn := (CornerSplit.marked_corners p (List.finRange N) z hz).2
  intro hc
  rcases hc with h|h
  · have hm := chunk_convex p z hz hyz hayz h.2.1.le h.2.2.le
    have hf := hn (a x.val) hm
    rw [hcore,hx] at hf
    cases hf
  · have hm := chunk_convex p z hz hyz hayz h.1.le h.2.1.le
    have hf := hn x.val hm
    rw [hx] at hf
    cases hf

/-- Insertion cannot enlarge a connected root core. Reachability here is
inside the finite crossing graph, not a probabilistic limiting assertion. -/
theorem root_component_of_core (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) (p : Fin N→Bool) (r : Opener a) (hr : r.val.val=0)
    (hp : p r.val=true) (hcore : ∀ d,p (a d)=p d)
    (hchunks : ∀ x∈(CornerSplit.split p (List.finRange N)).2,∀ d∈x.2,a d∈x.2)
    (hconnected : ∀ x : Opener a,p x.val=true → (graph a).Reachable r x) :
    componentDarts a r=Finset.univ.filter (fun d => p d=true) := by
  have hp0 : ∀ d : Fin N,d.val=0 → p d=true := by
    intro d hd
    have he : d=r.val := Fin.ext (hd.trans hr.symm)
    simpa only [he] using hp
  have hreach : ∀ x : Opener a,(graph a).Reachable r x → p x.val=true := by
    intro x hx
    have h := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hx
    induction h with
    | refl => exact hp
    | @tail y z hpath hadj ih =>
      have hy : (graph a).Reachable r y := (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hpath
      cases hh : p z.val with
      | true => rfl
      | false => exact False.elim (no_cross_core_corner a p hcore hchunks hp0 y z (ih hy) hh hadj)
  ext d
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_componentDarts]
  constructor
  · rintro ⟨x,hx,rfl|rfl⟩
    · exact hreach x hx
    · rw [hcore]; exact hreach x hx
  · intro hd
    let x := opener a ha hf d
    have hends := opener_endpoints a ha hf d
    have hx : p x.val=true := by
      rcases hends with h|h
      · exact (congrArg p h.symm).trans hd
      · exact (hcore x.val).symm.trans ((congrArg p h.symm).trans hd)
    exact ⟨x,hconnected x hx,hends⟩

end FKCRT.Chords
end

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
open Equiv Equiv.Perm
namespace FKCRT.Chords
variable {N K : ℕ}

/-- Transport a core matching through its strictly increasing position map. -/
def openerEmbedding (a : Perm (Fin N)) (b : Perm (Fin K))
    (e : Fin K ↪o Fin N) (h : ∀ i,a (e i)=e (b i)) : Opener b ↪ Opener a where
  toFun x := ⟨e x.val,by rw [h]; exact e.strictMono x.property⟩
  inj' := by intro x y hxy; exact Subtype.ext (e.injective (congrArg Subtype.val hxy))

lemma cross_embedding (a : Perm (Fin N)) (b : Perm (Fin K))
    (e : Fin K ↪o Fin N) (h : ∀ i,a (e i)=e (b i)) (x y : Opener b) :
    Cross a (openerEmbedding a b e h x) (openerEmbedding a b e h y) ↔ Cross b x y := by
  change ((e x.val<e y.val ∧ e y.val<a (e x.val) ∧ a (e x.val)<a (e y.val)) ∨
    (e y.val<e x.val ∧ e x.val<a (e y.val) ∧ a (e y.val)<a (e x.val))) ↔ _
  simp only [h,e.lt_iff_lt,Cross]

def graphHom (a : Perm (Fin N)) (b : Perm (Fin K))
    (e : Fin K ↪o Fin N) (h : ∀ i,a (e i)=e (b i)) : graph b →g graph a where
  toFun := openerEmbedding a b e h
  map_rel' := fun hx => (cross_embedding a b e h _ _).mpr hx

lemma opener_range (a : Perm (Fin N)) (b : Perm (Fin K))
    (e : Fin K ↪o Fin N) (h : ∀ i,a (e i)=e (b i)) (x : Opener a)
    (hx : x.val∈Set.range e) : ∃ y : Opener b,openerEmbedding a b e h y=x := by
  obtain ⟨i,hi⟩ := hx
  have hp : i<b i := by
    apply e.lt_iff_lt.mp
    rw [← h,hi]
    exact x.property
  exact ⟨⟨i,hp⟩,Subtype.ext hi⟩

/-- Once every unmarked interval is matched internally, the core mask is
also matched internally; this is forced by the actual involution. -/
lemma core_closed_of_chunks (a : Perm (Fin N)) (ha : Function.Involutive a)
    (p : Fin N→Bool) (hN : 0<N) (hp : p ⟨0,hN⟩=true)
    (hchunks : ∀ x∈(CornerSplit.split p (List.finRange N)).2,∀ d∈x.2,a d∈x.2) :
    ∀ d,p (a d)=p d := by
  have hunmarked : ∀ d,p d=false → p (a d)=false := by
    intro d hd
    obtain ⟨x,hx,hdx⟩ := unmarked_in_chunk p hN hp hd
    exact (CornerSplit.marked_corners p (List.finRange N) x hx).2 _ (hchunks x hx d hdx)
  intro d
  cases hd : p d with
  | false => exact hunmarked d hd
  | true =>
    cases had : p (a d) with
    | true => rfl
    | false =>
      have hh := hunmarked (a d) had
      rw [ha,hd] at hh
      cases hh

end FKCRT.Chords
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.CornerSplit
lemma skeleton_sublist {α : Type*} (l : List (α×List α)) :
    (l.map Prod.fst).Sublist (join l) := by
  induction l with
  | nil => exact .refl _
  | cons x l ih =>
    change (x.1::l.map Prod.fst).Sublist (x.1::(x.2++join l))
    exact (ih.trans (List.sublist_append_right _ _)).cons_cons _
end FKCRT.CornerSplit
namespace FKCRT.MapCycles
variable {α : Type*}

lemma scanArches_corners_subset (f : α→Option Bool) (l : List (α×List α))
    (G : α×List α→List (α×α))
    (hg : ∀ x∈l,∀ S,scanArches f x.2 S=some (S,G x))
    {E F : List (α×α)}
    (hcore : scanArches f (l.map Prod.fst) []=some ([],E))
    (hfull : scanArches f (CornerSplit.join l) []=some ([],F)) :
    ∀ e∈E,e∈F := by
  obtain ⟨H,hH,hperm⟩ := scanArches_corners f l G hg hcore
  have he : H=F := congrArg Prod.snd (Option.some.inj (hH.symm.trans hfull))
  rw [he] at hperm
  intro e he
  exact hperm.mem_iff.mpr (List.mem_append_left _ he)

end FKCRT.MapCycles
namespace FKCRT.Inventory
open MapCycles
variable {α : Type*} [DecidableEq α]

lemma typed_corner_scans (w : α→TypedLetter) (l : List (α×List α))
    (hn : (CornerSplit.join l).Nodup)
    (hw : ∀ x∈l,stackTypedRun (x.2.map w) []=some []) (c : Bool) :
    ∃ G : α×List α→List (α×α),
      ∀ x∈l,∀ S,scanArches (fun a => colorInstruction c (w a)) x.2 S=some (S,G x) := by
  have hex : ∀ x∈l,∃ E,∀ S,scanArches (fun a => colorInstruction c (w a)) x.2 S=some (S,E) := by
    intro x hx
    have hxnodup : x.2.Nodup := (List.nodup_cons.mp ((List.nodup_flatMap.mp hn).1 x hx)).2
    obtain ⟨E,hE,_⟩ := empty_typed_scan w x.2 hxnodup (hw x hx) c
    exact ⟨E,hE⟩
  classical
  let G := fun x => if hx : x∈l then Classical.choose (hex x hx) else []
  refine ⟨G,?_⟩
  intro x hx S
  simpa only [G,dite_eq_left hx] using (Classical.choose_spec (hex x hx)) S

/-- Actual core pairs remain the same pairs after inserting *arbitrary*
successful corner words. This controls the adaptive matching itself. -/
theorem corner_core_pairs (w : α→TypedLetter) (l : List (α×List α))
    (hn : (CornerSplit.join l).Nodup)
    (hw : ∀ x∈l,stackTypedRun (x.2.map w) []=some [])
    (E F C D : List (α×α))
    (hE : Arches (CornerSplit.join l) E) (hF : Arches (CornerSplit.join l) F)
    (hc : (endpoints (E++F)).Perm (CornerSplit.join l))
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false)
    (hC : Arches (l.map Prod.fst) C) (hD : Arches (l.map Prod.fst) D)
    (hd : (endpoints (C++D)).Perm (l.map Prod.fst))
    (htC : ∀ e∈C,w e.1=.burger true ∧ w e.2=.order true)
    (htD : ∀ e∈D,w e.1=.burger false ∧ w e.2=.order false) :
    (∀ e∈C,e∈E) ∧ (∀ e∈D,e∈F) := by
  have hfull := matching_color_coverage w (CornerSplit.join l) E F hc htE htF
  have hcore := matching_color_coverage w (l.map Prod.fst) C D hd htC htD
  have hncore := hn.sublist (CornerSplit.skeleton_sublist l)
  constructor
  · obtain ⟨G,hG⟩ := typed_corner_scans w l hn hw true
    obtain ⟨Ec,hEc,hEcC⟩ := hC.scan hncore (fun x => colorInstruction true (w x))
      (fun e he => by simp [colorInstruction,(htC e he).1,(htC e he).2]) hcore.1 []
    obtain ⟨Ef,hEf,hEfE⟩ := hE.scan hn (fun x => colorInstruction true (w x))
      (fun e he => by simp [colorInstruction,(htE e he).1,(htE e he).2]) hfull.1 []
    intro e he
    exact hEfE.mem_iff.mp (scanArches_corners_subset _ l G hG hEc hEf e (hEcC.mem_iff.mpr he))
  · obtain ⟨G,hG⟩ := typed_corner_scans w l hn hw false
    obtain ⟨Dc,hDc,hDcD⟩ := hD.scan hncore (fun x => colorInstruction false (w x))
      (fun e he => by simp [colorInstruction,(htD e he).1,(htD e he).2]) hcore.2 []
    obtain ⟨Df,hDf,hDfF⟩ := hF.scan hn (fun x => colorInstruction false (w x))
      (fun e he => by simp [colorInstruction,(htF e he).1,(htF e he).2]) hfull.2 []
    intro e he
    exact hDfF.mem_iff.mp (scanArches_corners_subset _ l G hG hDc hDf e (hDcD.mem_iff.mpr he))

/-- The exact matching restriction, stated on every actual core endpoint. -/
theorem corner_core_turns (w : α→TypedLetter) (l : List (α×List α))
    (hn : (CornerSplit.join l).Nodup)
    (hw : ∀ x∈l,stackTypedRun (x.2.map w) []=some [])
    (E F C D : List (α×α))
    (hE : Arches (CornerSplit.join l) E) (hF : Arches (CornerSplit.join l) F)
    (hc : (endpoints (E++F)).Perm (CornerSplit.join l))
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false)
    (hC : Arches (l.map Prod.fst) C) (hD : Arches (l.map Prod.fst) D)
    (hd : (endpoints (C++D)).Perm (l.map Prod.fst))
    (htC : ∀ e∈C,w e.1=.burger true ∧ w e.2=.order true)
    (htD : ∀ e∈D,w e.1=.burger false ∧ w e.2=.order false) :
    ∀ a∈l.map Prod.fst,turns (E++F) a=turns (C++D) a := by
  obtain ⟨hCE,hDF⟩ := corner_core_pairs w l hn hw E F C D hE hF hc htE htF hC hD hd htC htD
  have hsub : ∀ e∈C++D,e∈E++F := by
    intro e he
    rcases List.mem_append.mp he with he|he
    · exact List.mem_append_left _ (hCE e he)
    · exact List.mem_append_right _ (hDF e he)
  have hnp := hc.nodup_iff.mpr hn
  have hncore : (endpoints (C++D)).Nodup :=
    hd.nodup_iff.mpr (hn.sublist (CornerSplit.skeleton_sublist l))
  intro a ha
  obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp (hd.mem_iff.mpr ha)
  · rw [(turns_pair hnp e (hsub e he)).1,(turns_pair hncore e he).1]
  · rw [(turns_pair hnp e (hsub e he)).2,(turns_pair hncore e he).2]

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.CornerSplit
variable {α : Type*}

lemma join_perm_parts (l : List (α×List α)) :
    (join l).Perm (l.map Prod.fst++l.flatMap Prod.snd) := by
  induction l with
  | nil => exact .refl _
  | cons x l ih =>
    change (x.1::(x.2++join l)).Perm (x.1::(l.map Prod.fst++(x.2++l.flatMap Prod.snd)))
    apply List.Perm.cons
    apply (ih.append_left x.2).trans
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁:=x.2) (l₂:=l.map Prod.fst)).append_right (l.flatMap Prod.snd)

lemma own_mask {α : Type*} [DecidableEq α] (l : List (α×List α)) (hn : (join l).Nodup) :
    ∀ x∈l,decide (x.1∈l.map Prod.fst)=true ∧
      ∀ d∈x.2,decide (d∈l.map Prod.fst)=false := by
  have hh := (join_perm_parts l).nodup_iff.mp hn
  intro x hx
  refine ⟨decide_eq_true (List.mem_map.mpr ⟨x,hx,rfl⟩),?_⟩
  intro d hd
  apply decide_eq_false
  intro hm
  exact (List.nodup_append.mp hh).2.2 d hm d (List.mem_flatMap.mpr ⟨x,hx,hd⟩) rfl

end FKCRT.CornerSplit
namespace FKCRT.Chords
variable {N : ℕ}

def partialOpener (a b : Perm (Fin N)) (p : Fin N→Bool)
    (hsupport : ∀ d,b d≠d → p d=true)
    (hmatch : ∀ d,p d=true → a d=b d) (x : Opener b) : Opener a :=
  ⟨x.val,by rw [hmatch _ (hsupport _ (ne_of_gt x.property))];exact x.property⟩

def partialGraphHom (a b : Perm (Fin N)) (p : Fin N→Bool)
    (hsupport : ∀ d,b d≠d → p d=true)
    (hmatch : ∀ d,p d=true → a d=b d) : graph b →g graph a where
  toFun := partialOpener a b p hsupport hmatch
  map_rel' := by
    intro x y h
    change Cross a (partialOpener a b p hsupport hmatch x) (partialOpener a b p hsupport hmatch y)
    change (x.val<y.val ∧ y.val<a x.val ∧ a x.val<a y.val) ∨
      (y.val<x.val ∧ x.val<a y.val ∧ a y.val<a x.val)
    rw [hmatch _ (hsupport _ (ne_of_gt x.property)),hmatch _ (hsupport _ (ne_of_gt y.property))]
    exact h

theorem root_component_partial (a b : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) (p : Fin N→Bool)
    (hsupport : ∀ d,b d≠d → p d=true) (hmatch : ∀ d,p d=true → a d=b d)
    (r : Opener b) (hr : r.val.val=0)
    (hconnected : ∀ x : Opener b,(graph b).Reachable r x)
    (hchunks : ∀ x∈(CornerSplit.split p (List.finRange N)).2,∀ d∈x.2,a d∈x.2) :
    componentDarts a (partialOpener a b p hsupport hmatch r)=Finset.univ.filter (fun d => p d=true) := by
  have hp := hsupport r.val (ne_of_gt r.property)
  have hN : 0<N := r.val.pos
  have hp0 : p ⟨0,hN⟩=true := by
    have he : (⟨0,hN⟩ : Fin N)=r.val := Fin.ext hr.symm
    rw [he];exact hp
  apply root_component_of_core a ha hf p (partialOpener a b p hsupport hmatch r) hr hp
    (core_closed_of_chunks a ha p hN hp0 hchunks) hchunks
  intro x hx
  let y : Opener b := ⟨x.val,by rw [← hmatch _ hx];exact x.property⟩
  exact (hconnected y).map (partialGraphHom a b p hsupport hmatch)

end FKCRT.Chords
namespace FKCRT.Inventory
open MapCycles Chords
variable {N : ℕ}

/-- Exact inverse of root-component extraction. Connectivity here specifies
which finite words are cores; all corner matching and separation facts are
proved from the original stack algorithm. -/
theorem connected_corner_inverse (w : Fin N→TypedLetter)
    (l : List (Fin N×List (Fin N))) (hjoin : CornerSplit.join l=List.finRange N)
    (hw : ∀ x∈l,stackTypedRun (x.2.map w) []=some [])
    (E F C D : List (Fin N×Fin N))
    (hE : Arches (List.finRange N) E) (hF : Arches (List.finRange N) F)
    (hc : (endpoints (E++F)).Perm (List.finRange N))
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false)
    (hC : Arches (l.map Prod.fst) C) (hD : Arches (l.map Prod.fst) D)
    (hd : (endpoints (C++D)).Perm (l.map Prod.fst))
    (htC : ∀ e∈C,w e.1=.burger true ∧ w e.2=.order true)
    (htD : ∀ e∈D,w e.1=.burger false ∧ w e.2=.order false)
    (r : Opener (turns (C++D))) (hr : r.val.val=0)
    (hconnected : ∀ x : Opener (turns (C++D)),(Chords.graph (turns (C++D))).Reachable r x) :
    ∃ R : Opener (turns (E++F)),R.val=r.val ∧ rootSplit (turns (E++F)) R=l := by
  classical
  let a := turns (E++F)
  let b := turns (C++D)
  let p : Fin N→Bool := fun d => decide (d∈l.map Prod.fst)
  have hn : (CornerSplit.join l).Nodup := hjoin.symm ▸ List.nodup_finRange N
  have hnp : (endpoints (E++F)).Nodup := hc.nodup_iff.mpr (List.nodup_finRange N)
  have hnc : (endpoints (C++D)).Nodup := hd.nodup_iff.mpr (hn.sublist (CornerSplit.skeleton_sublist l))
  have hs : CornerSplit.split p (List.finRange N)=([],l) := by
    rw [← hjoin];exact CornerSplit.split_join p l (CornerSplit.own_mask l hn)
  have hmatch : ∀ d,p d=true → a d=b d := by
    intro d hd'
    exact corner_core_turns w l hn hw E F C D (hjoin.symm ▸ hE) (hjoin.symm ▸ hF)
      (hjoin.symm ▸ hc) htE htF hC hD hd htC htD d (of_decide_eq_true hd')
  have hsupport : ∀ d,b d≠d → p d=true := by
    intro d hbd
    apply decide_eq_true
    apply hd.mem_iff.mp
    by_contra hh
    exact hbd (turns_fixed_of_notMem hh)
  have hchunks : ∀ x∈(CornerSplit.split p (List.finRange N)).2,∀ d∈x.2,a d∈x.2 := by
    intro x hx
    have hxl : x∈l := by simpa only [hs] using hx
    obtain ⟨u,v,he,_⟩ := CornerSplit.located p (List.finRange N) x hx
    have he' : List.finRange N=(u++[x.1])++(x.2++v) := by simpa only [List.append_assoc,List.singleton_append] using he
    exact empty_interval_matching_closed w (u++[x.1]) x.2 v
      (he' ▸ List.nodup_finRange N) E F (he' ▸ hE) (he' ▸ hF) (he' ▸ hc) htE htF (hw x hxl)
  have hf : ∀ d,a d≠d := by
    intro d hh
    exact (turns_eq_self_iff hnp d).mp hh (hc.mem_iff.mpr (List.mem_finRange d))
  let R := partialOpener a b p hsupport hmatch r
  have hcomp := root_component_partial a b (turns_involutive hnp) hf p hsupport hmatch r hr hconnected hchunks
  refine ⟨R,rfl,?_⟩
  have hmask : (fun d => decide (d∈componentDarts a R))=p := by
    funext d
    rw [hcomp]
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Bool.decide_eq_true]
  change (CornerSplit.split (fun d => decide (d∈componentDarts a R)) (List.finRange N)).2=l
  rw [hmask,hs]

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α β : Type*}

lemma Arches.map {l : List α} {E : List (α×α)} (h : Arches l E) (f : α→β) :
    Arches (l.map f) (E.map (Prod.map f f)) := by
  induction h with
  | nil => exact .nil
  | skip a h ih => exact .skip (f a) ih
  | pair a b hL hR ihL ihR =>
    simpa only [List.map_cons,List.map_append,Prod.map_apply] using Arches.pair (f a) (f b) ihL ihR

lemma endpoints_map (f : α→β) (E : List (α×α)) :
    endpoints (E.map (Prod.map f f))=(endpoints E).map f := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    rcases e with ⟨a,b⟩
    simp only [List.map_cons,endpoints_cons,Prod.map_apply,ih]

lemma Arches.filter {l : List α} {E : List (α×α)} (h : Arches l E) (p : α→Bool)
    (hp : ∀ e∈E,p e.1=p e.2) :
    Arches (l.filter p) (E.filter (fun e => p e.1)) := by
  induction h with
  | nil => exact .nil
  | @skip a l E h ih =>
    cases ha : p a with
    | true => simpa only [List.filter_cons,ha,ite_true] using Arches.skip a (ih hp)
    | false => simpa only [List.filter_cons,ha,Bool.false_eq_true,ite_false] using ih hp
  | @pair a b L R E F hL hR ihL ihR =>
    have hab := hp (a,b) (List.mem_cons_self)
    have hE := ihL (fun e he => hp e (List.mem_cons_of_mem _ (List.mem_append_left _ he)))
    have hF := ihR (fun e he => hp e (List.mem_cons_of_mem _ (List.mem_append_right _ he)))
    cases ha : p a with
    | true =>
      have hb : p b=true := hab.symm.trans ha
      simpa only [List.filter_cons,List.filter_append,ha,hb,ite_true] using Arches.pair a b hE hF
    | false =>
      have hb : p b=false := hab.symm.trans ha
      simpa only [List.filter_cons,List.filter_append,ha,hb,Bool.false_eq_true,ite_false] using hE.append hF

lemma endpoints_filter (p : α→Bool) (E : List (α×α))
    (hp : ∀ e∈E,p e.1=p e.2) :
    endpoints (E.filter (fun e => p e.1))=(endpoints E).filter p := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    have he := hp e (List.mem_cons_self)
    have hh := ih (fun f hf => hp f (List.mem_cons_of_mem _ hf))
    cases ha : p e.1 <;> have hb := he.symm.trans ha <;>
      simp only [List.filter_cons,endpoints_cons,ha,hb,Bool.false_eq_true,ite_true,ite_false,hh]

end FKCRT.MapCycles
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma turns_map_on (f : α→β) (hf : Function.Injective f) (E : List (α×α))
    (hn : (endpoints E).Nodup) (i : α) (hi : i∈endpoints E) :
    turns (E.map (Prod.map f f)) (f i)=f (turns E i) := by
  have hn' : (endpoints (E.map (Prod.map f f))).Nodup := by
    rw [endpoints_map];exact hn.map hf
  obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hi
  · have hh := (turns_pair hn' (Prod.map f f e) (List.mem_map.mpr ⟨e,he,rfl⟩)).1
    simpa only [Prod.map_fst,Prod.map_snd,(turns_pair hn e he).1] using hh
  · have hh := (turns_pair hn' (Prod.map f f e) (List.mem_map.mpr ⟨e,he,rfl⟩)).2
    simpa only [Prod.map_fst,Prod.map_snd,(turns_pair hn e he).2] using hh

end FKCRT.MapCycles
namespace FKCRT.Inventory
open MapCycles Chords
variable {α β : Type*}

/-- A certificate for the actual two stack matchings of a finite typed word.
The matching uniqueness theorem makes its induced mate choice-independent. -/
structure StackMatching (w : α→TypedLetter) (l : List α) where
  first : List (α×α)
  second : List (α×α)
  first_arches : Arches l first
  second_arches : Arches l second
  covers : (endpoints (first++second)).Perm l
  first_types : ∀ e∈first,w e.1=.burger true ∧ w e.2=.order true
  second_types : ∀ e∈second,w e.1=.burger false ∧ w e.2=.order false

namespace StackMatching
variable {w : α→TypedLetter} {l : List α}

def ofEmpty (hw : stackTypedRun (l.map w) []=some []) : StackMatching w l :=
  let h := ordered_matchings w l hw
  ⟨h.choose,h.choose_spec.choose,h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2.1,h.choose_spec.choose_spec.2.2.1,
    h.choose_spec.choose_spec.2.2.2.1,h.choose_spec.choose_spec.2.2.2.2⟩

def mate [DecidableEq α] (M : StackMatching w l) : Perm α := turns (M.first++M.second)

lemma empty [DecidableEq α] (M : StackMatching w l) (hn : l.Nodup) :
    stackTypedRun (l.map w) []=some [] :=
  typedRun_of_matchings w l hn M.first M.second M.first_arches M.second_arches
    M.covers M.first_types M.second_types

lemma unique_mate [DecidableEq α] (M P : StackMatching w l) (hn : l.Nodup) : M.mate=P.mate := by
  obtain ⟨hE,hF⟩ := typed_matchings_unique w l hn M.first M.second P.first P.second
    M.first_arches M.second_arches P.first_arches P.second_arches M.covers P.covers
    M.first_types M.second_types P.first_types P.second_types
  exact turns_perm (hE.append hF) (M.covers.nodup_iff.mpr hn)

lemma involutive [DecidableEq α] (M : StackMatching w l) (hn : l.Nodup) :
    Function.Involutive M.mate := turns_involutive (M.covers.nodup_iff.mpr hn)

lemma no_fixed [DecidableEq α] (M : StackMatching w l) (hn : l.Nodup) (i : α) (hi : i∈l) :
    M.mate i≠i := by
  intro hh
  exact (turns_eq_self_iff (M.covers.nodup_iff.mpr hn) i).mp hh (M.covers.mem_iff.mpr hi)

lemma endpoints_mem (M : StackMatching w l) (e : α×α) (he : e∈M.first++M.second) :
    e.1∈l ∧ e.2∈l :=
  ⟨M.covers.mem_iff.mp (mem_endpoints.mpr ⟨e,he,Or.inl rfl⟩),
   M.covers.mem_iff.mp (mem_endpoints.mpr ⟨e,he,Or.inr rfl⟩)⟩

def map (M : StackMatching w l) (f : α→β) (v : β→TypedLetter)
    (hv : ∀ i∈l,v (f i)=w i) : StackMatching v (l.map f) where
  first := M.first.map (Prod.map f f)
  second := M.second.map (Prod.map f f)
  first_arches := M.first_arches.map f
  second_arches := M.second_arches.map f
  covers := by rw [← List.map_append,endpoints_map];exact M.covers.map f
  first_types := by
    intro e he
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
    have hh := M.endpoints_mem x (List.mem_append_left _ hx)
    simpa only [Prod.map_fst,Prod.map_snd,hv _ hh.1,hv _ hh.2] using M.first_types x hx
  second_types := by
    intro e he
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
    have hh := M.endpoints_mem x (List.mem_append_right _ hx)
    simpa only [Prod.map_fst,Prod.map_snd,hv _ hh.1,hv _ hh.2] using M.second_types x hx

lemma map_mate [DecidableEq α] [DecidableEq β] (M : StackMatching w l)
    (hn : l.Nodup) (f : α→β) (hf : Function.Injective f) (v : β→TypedLetter)
    (hv : ∀ i∈l,v (f i)=w i) (i : α) (hi : i∈l) :
    (M.map f v hv).mate (f i)=f (M.mate i) := by
  change turns (List.map (Prod.map f f) M.first++List.map (Prod.map f f) M.second) (f i)=_
  rw [← List.map_append]
  exact turns_map_on f hf _ (M.covers.nodup_iff.mpr hn) i (M.covers.mem_iff.mpr hi)

lemma cast_mate [DecidableEq α] {l' : List α} (h : l=l') (M : StackMatching w l) :
    (h ▸ M).mate=M.mate := by cases h; rfl

end StackMatching

variable [LinearOrder α]
/-- The literal increasing compression map, not a fresh random matching. -/
def positionEmbedding (l : List α) (hs : l.Pairwise (·<·)) : Fin l.length ↪o α :=
  OrderEmbedding.ofStrictMono l.get (fun _ _ h => hs.rel_get_of_lt h)

omit [LinearOrder α] in
lemma positions_word (w : α→TypedLetter) (l : List α) :
    (List.finRange l.length).map (w ∘ l.get)=l.map w := by
  rw [← List.map_map,List.map_get_finRange]

/-- Normalization preserves the actual mate permutation on all positions. -/
theorem normalized_matching_mate (w : α→TypedLetter) (l : List α) (hs : l.Pairwise (·<·))
    (M : StackMatching w l) :
    ∃ P : StackMatching (w ∘ l.get) (List.finRange l.length),
      ∀ i,M.mate (l.get i)=l.get (P.mate i) := by
  have hn : l.Nodup := hs.nodup
  have hw : stackTypedRun ((List.finRange l.length).map (w ∘ l.get)) []=some [] := by
    rw [positions_word];exact M.empty hn
  let P := StackMatching.ofEmpty hw
  let Q := P.map l.get w (fun _ _ => rfl)
  have hQ : (List.finRange l.length).map l.get=l := List.map_get_finRange l
  let R : StackMatching w l := hQ ▸ Q
  have hmate := M.unique_mate R hn
  refine ⟨P,fun i => ?_⟩
  rw [hmate]
  have hR : R.mate=Q.mate := StackMatching.cast_mate hQ Q
  rw [hR]
  exact P.map_mate (List.nodup_finRange _) l.get (List.nodup_iff_injective_get.mp hn)
    w (fun _ _ => rfl) i (List.mem_finRange i)

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CoreCompression
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Chords
variable {N K : ℕ}

/-- Reachability lifts through a strictly increasing matching embedding
whenever its image contains the whole component being lifted. -/
theorem reachable_lift (a : Perm (Fin N)) (b : Perm (Fin K))
    (e : Fin K ↪o Fin N) (hmatch : ∀ i,a (e i)=e (b i))
    (r : Opener b)
    (himage : ∀ x : Opener a,(graph a).Reachable (openerEmbedding a b e hmatch r) x →
      x.val∈Set.range e) :
    ∀ x : Opener a,(graph a).Reachable (openerEmbedding a b e hmatch r) x →
      ∃ y : Opener b,openerEmbedding a b e hmatch y=x ∧ (graph b).Reachable r y := by
  intro x hx
  have hh := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hx
  induction hh with
  | refl => exact ⟨r,rfl,SimpleGraph.Reachable.refl r⟩
  | @tail x z hpath hadj ih =>
    obtain ⟨y,hy,hry⟩ := ih ((SimpleGraph.reachable_iff_reflTransGen _ _).mpr hpath)
    have hz : (graph a).Reachable (openerEmbedding a b e hmatch r) z :=
      ((SimpleGraph.reachable_iff_reflTransGen _ _).mpr hpath).trans hadj.reachable
    obtain ⟨v,hv⟩ := opener_range a b e hmatch z (himage z hz)
    refine ⟨v,hv,hry.trans ?_⟩
    apply SimpleGraph.Adj.reachable
    exact (cross_embedding a b e hmatch y v).mp (by rw [hy,hv];exact hadj)

theorem component_compression (a : Perm (Fin N)) (ha : Function.Involutive a) (b : Perm (Fin K))
    (e : Fin K ↪o Fin N) (hmatch : ∀ i,a (e i)=e (b i))
    (r : Opener b)
    (himage : Set.range e={d | d∈componentDarts a (openerEmbedding a b e hmatch r)}) :
    ∀ x : Opener b,(graph b).Reachable r x := by
  intro x
  have hx : (e x.val)∈componentDarts a (openerEmbedding a b e hmatch r) := by
    change e x.val∈({d | d∈componentDarts a (openerEmbedding a b e hmatch r)} : Set (Fin N))
    rw [← himage];exact Set.mem_range_self _
  have hxa : (graph a).Reachable (openerEmbedding a b e hmatch r)
      (openerEmbedding a b e hmatch x) := by
    obtain ⟨y,hy,he|he⟩ := (mem_componentDarts _ _ _).mp hx
    · have hy' : y=openerEmbedding a b e hmatch x := Subtype.ext he.symm
      exact hy' ▸ hy
    · have hxp := e.strictMono x.property
      rw [← hmatch,he] at hxp
      rw [ha] at hxp
      exact False.elim ((not_lt_of_ge y.property.le) hxp)
  obtain ⟨v,hv,hrv⟩ := reachable_lift a b e hmatch r (by
    intro y hy
    rw [himage]
    exact (mem_componentDarts _ _ _).mpr ⟨y,hy,Or.inl rfl⟩)
    (openerEmbedding a b e hmatch x) hxa
  exact (openerEmbedding a b e hmatch).injective hv ▸ hrv

end FKCRT.Chords
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.StackMatching
open MapCycles
variable {α : Type*} [DecidableEq α] {w : α→TypedLetter} {l : List α}

lemma pair_mask (M : StackMatching w l) (hn : l.Nodup) (p : α→Bool)
    (hp : ∀ d∈l,p (M.mate d)=p d) : ∀ e∈M.first++M.second,p e.1=p e.2 := by
  intro e he
  have hh := hp e.1 (M.endpoints_mem e he).1
  rw [mate,(turns_pair (M.covers.nodup_iff.mpr hn) e he).1] at hh
  exact hh.symm

def filter (M : StackMatching w l) (hn : l.Nodup) (p : α→Bool)
    (hp : ∀ d∈l,p (M.mate d)=p d) : StackMatching w (l.filter p) where
  first := M.first.filter (fun e => p e.1)
  second := M.second.filter (fun e => p e.1)
  first_arches := M.first_arches.filter p (fun e he =>
    M.pair_mask hn p hp e (List.mem_append_left _ he))
  second_arches := M.second_arches.filter p (fun e he =>
    M.pair_mask hn p hp e (List.mem_append_right _ he))
  covers := by
    rw [← List.filter_append,endpoints_filter p _ (M.pair_mask hn p hp)]
    exact M.covers.filter p
  first_types := fun e he => M.first_types e (List.mem_filter.mp he).1
  second_types := fun e he => M.second_types e (List.mem_filter.mp he).1

lemma filter_mate (M : StackMatching w l) (hn : l.Nodup) (p : α→Bool)
    (hp : ∀ d∈l,p (M.mate d)=p d) (i : α) (hi : i∈l) (hpi : p i=true) :
    (M.filter hn p hp).mate i=M.mate i := by
  have hnp := M.covers.nodup_iff.mpr hn
  have hnf := (M.filter hn p hp).covers.nodup_iff.mpr (hn.filter p)
  obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp (M.covers.mem_iff.mpr hi)
  · have hmem : e∈(M.filter hn p hp).first++(M.filter hn p hp).second := by
      change e∈M.first.filter (fun e => p e.1)++M.second.filter (fun e => p e.1)
      rw [← List.filter_append]
      exact List.mem_filter.mpr ⟨he,hpi⟩
    exact (turns_pair hnf e hmem).1.trans (turns_pair hnp e he).1.symm
  · have hmem : e∈(M.filter hn p hp).first++(M.filter hn p hp).second := by
      change e∈M.first.filter (fun e => p e.1)++M.second.filter (fun e => p e.1)
      rw [← List.filter_append]
      exact List.mem_filter.mpr ⟨he,(M.pair_mask hn p hp e he).trans hpi⟩
    exact (turns_pair hnf e hmem).2.trans (turns_pair hnp e he).2.symm

end FKCRT.Inventory.StackMatching
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CoreWords
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles Chords
variable {N : ℕ}

/-- A connected nonempty typed core, expressed without an arbitrary pairing
choice: any matching certificate is the unique literal stack matching. -/
def CoreWord (w : List TypedLetter) : Prop :=
  ∃ (K : ℕ) (v : Fin K→TypedLetter) (M : StackMatching v (List.finRange K)),
    (List.finRange K).map v=w ∧
    ∃ r : Opener M.mate,r.val.val=0 ∧ ∀ x : Opener M.mate,(Chords.graph M.mate).Reachable r x

lemma coreWord_empty (w : List TypedLetter) (h : CoreWord w) : stackTypedRun w []=some [] := by
  obtain ⟨K,v,M,rfl,_⟩ := h
  exact M.empty (List.nodup_finRange K)

lemma coreWord_pos (w : List TypedLetter) (h : CoreWord w) : 0<w.length := by
  obtain ⟨K,v,M,rfl,r,_,_⟩ := h
  simpa only [List.length_map,List.length_finRange] using r.val.pos

lemma filter_finRange_eq (l : List (Fin N)) (hs : l.Pairwise (·<·)) :
    (List.finRange N).filter (fun d => decide (d∈l))=l := by
  apply ((List.pairwise_lt_finRange N).filter _).eq_of_mem_iff hs
  intro d
  simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]

lemma StackMatching.closed_subword (w : Fin N→TypedLetter)
    (M : StackMatching w (List.finRange N)) (l : List (Fin N)) (hs : l.Pairwise (·<·))
    (hclosed : ∀ d∈l,M.mate d∈l) : stackTypedRun (l.map w) []=some [] := by
  let p : Fin N→Bool := fun d => decide (d∈l)
  have hn := List.nodup_finRange N
  have hp : ∀ d∈List.finRange N,p (M.mate d)=p d := by
    intro d _
    simp only [p,decide_eq_decide]
    constructor
    · intro hd
      have hh := hclosed (M.mate d) hd
      rwa [M.involutive hn] at hh
    · exact hclosed d
  have hh := (M.filter hn p hp).empty (hn.filter p)
  simpa only [p,filter_finRange_eq l hs] using hh

/-- The actual root component becomes a connected finite core after order
compression. No independence law or substituted matching is used. -/
theorem normalized_root_core (w : Fin N→TypedLetter)
    (M : StackMatching w (List.finRange N)) (r : Opener M.mate) (hr : r.val.val=0) :
    CoreWord (((List.finRange N).filter (fun d => decide (d∈componentDarts M.mate r))).map w) := by
  let p : Fin N→Bool := fun d => decide (d∈componentDarts M.mate r)
  let l := (List.finRange N).filter p
  have hn := List.nodup_finRange N
  have ha := M.involutive hn
  have hp : ∀ d∈List.finRange N,p (M.mate d)=p d := by
    intro d _
    simp only [p,decide_eq_decide]
    exact componentDarts_mate M.mate ha r d
  let Q := M.filter hn p hp
  have hs : l.Pairwise (·<·) := (List.pairwise_lt_finRange N).filter p
  obtain ⟨P,hP⟩ := normalized_matching_mate w l hs Q
  let e := positionEmbedding l hs
  have hmatch : ∀ i,M.mate (e i)=e (P.mate i) := by
    intro i
    have hi : l.get i∈l := l.get_mem i
    have hpi : p (l.get i)=true := (List.mem_filter.mp hi).2
    exact (M.filter_mate hn p hp _ (List.mem_finRange _) hpi).symm.trans (hP i)
  have hrange : Set.range e={d | d∈componentDarts M.mate r} := by
    ext d
    change (∃ i,l.get i=d) ↔ d∈componentDarts M.mate r
    rw [← List.mem_iff_get]
    simp only [l,p,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
  have hrmem : r.val∈Set.range e := by
    rw [hrange]
    exact (mem_componentDarts _ _ _).mpr ⟨r,SimpleGraph.Reachable.refl r,Or.inl rfl⟩
  obtain ⟨s,hsr⟩ := opener_range M.mate P.mate e hmatch r hrmem
  have hs0 : s.val.val=0 := by
    have he : (e s.val).val=0 := (congrArg (fun x : Opener M.mate => x.val.val) hsr).trans hr
    by_contra hne
    have hlt : (⟨0,s.val.pos⟩ : Fin l.length) < s.val := by change 0 < s.val.val;omega
    have hh := e.strictMono hlt
    have hv : (e ⟨0,s.val.pos⟩).val<(e s.val).val := hh
    omega
  refine ⟨l.length,w ∘ l.get,P,positions_word w l,s,hs0,?_⟩
  apply component_compression M.mate ha P.mate e hmatch s
  rw [hsr]
  exact hrange

/-- Canonical decomposition of every genuine nonempty successful word into
its root connected core and its literal successful corner words. -/
theorem successful_core_decomposition (w : Fin N→TypedLetter)
    (M : StackMatching w (List.finRange N)) (r : Opener M.mate) (hr : r.val.val=0) :
    let l := (rootSplit M.mate r).map (fun x => (w x.1,x.2.map w))
    cornerInsert l=(List.finRange N).map w ∧ CoreWord (l.map Prod.fst) ∧
    (∀ x∈l,stackTypedRun x.2 []=some [] ∧ x.2.length<N) ∧
    flexibleCount ((List.finRange N).map w) []=
      flexibleCount (l.map Prod.fst) []+(l.map (fun x => flexibleCount x.2 [])).sum := by
  dsimp only
  let l := (rootSplit M.mate r).map (fun x => (w x.1,x.2.map w))
  have hjoin : cornerInsert l=(List.finRange N).map w := by
    rw [cornerInsert_map,rootSplit_join M.mate r hr]
  have hske : l.map Prod.fst=
      ((List.finRange N).filter (fun d => decide (d∈componentDarts M.mate r))).map w := by
    change ((rootSplit M.mate r).map _).map _=_
    rw [List.map_map]
    have hh := congrArg (List.map w)
      (CornerSplit.skeleton (fun d => decide (d∈componentDarts M.mate r)) (List.finRange N))
    simpa only [List.map_map,Function.comp_def,rootSplit] using hh
  have hcore : CoreWord (l.map Prod.fst) := hske ▸ normalized_root_core w M r hr
  have hchunks : ∀ x∈l,stackTypedRun x.2 []=some [] ∧ x.2.length<N := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    refine ⟨?_,by rw [List.length_map];exact rootSplit_length_lt M.mate r y hy⟩
    apply M.closed_subword w y.2
    · obtain ⟨u,v,he,_⟩ := CornerSplit.located (fun d => decide (d∈componentDarts M.mate r))
        (List.finRange N) y hy
      have hs : (u++y.1::(y.2++v)).Pairwise (·<·) := he ▸ List.pairwise_lt_finRange N
      exact (List.pairwise_append.mp (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).2).1
    · exact rootSplit_closed M.mate (M.involutive (List.nodup_finRange N))
        (fun d => M.no_fixed (List.nodup_finRange N) d (List.mem_finRange d)) r hr y hy
  refine ⟨hjoin,hcore,hchunks,?_⟩
  rw [← hjoin]
  exact (cornerInsert_run_count l (fun x hx => (hchunks x hx).1) (coreWord_empty _ hcore)).2

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.CornerSplit
variable {α β : Type*}

lemma lift_join (f : α→β) (l : List (β×List β)) (u : List α)
    (hu : u.map f=join l) :
    ∃ L : List (α×List α),join L=u ∧ L.map (fun x => (f x.1,x.2.map f))=l := by
  induction l generalizing u with
  | nil =>
    have hu' : u=[] := List.map_eq_nil_iff.mp hu
    subst u
    exact ⟨[],rfl,rfl⟩
  | cons x l ih =>
    cases u with
    | nil => simp [join] at hu
    | cons a u =>
      change f a::u.map f=x.1::(x.2++join l) at hu
      obtain ⟨hx,hu⟩ := List.cons.inj hu
      obtain ⟨u1,u2,rfl,h1,h2⟩ := List.map_eq_append_iff.mp hu
      obtain ⟨L,hL,hm⟩ := ih u2 h2
      refine ⟨(a,u1)::L,?_,?_⟩
      · change a::(u1++join L)=a::(u1++u2)
        rw [hL]
      · simp only [List.map_cons,hx,h1,hm,Prod.eta]

lemma join_first_zero {N : ℕ} (l : List (Fin N×List (Fin N)))
    (hjoin : join l=List.finRange N) (i : Fin (l.map Prod.fst).length) (hi : i.val=0) :
    ((l.map Prod.fst).get i).val=0 := by
  cases l with
  | nil => exact Fin.elim0 i
  | cons x l =>
    cases N with
    | zero => exact Fin.elim0 x.1
    | succ N =>
      have hh : x.1=0 := by
        have hh := congrArg List.head? hjoin
        simpa only [join,List.flatMap_cons,List.cons_append,List.head?_cons,List.finRange_succ,
          List.map_cons,List.head?_map,Option.map_some,Fin.castSucc_zero,Option.some.injEq] using hh
      have hi' : i=⟨0,by simp⟩ := Fin.ext hi
      simp only [hi',List.map_cons,List.get_eq_getElem,List.getElem_cons_zero,hh,Fin.val_zero]

end FKCRT.CornerSplit
namespace FKCRT.Inventory
open MapCycles Chords
variable {N : ℕ}

/-- A genuinely connected typed core remains connected when its positions
are stretched by the actual corner inserts, including empty inserts. -/
theorem core_matching_at_positions (w : Fin N→TypedLetter)
    (l : List (Fin N×List (Fin N))) (hjoin : CornerSplit.join l=List.finRange N)
    (hcore : CoreWord ((l.map Prod.fst).map w)) :
    ∃ C : StackMatching w (l.map Prod.fst),∃ r : Opener C.mate,
      r.val.val=0 ∧ ∀ x : Opener C.mate,(Chords.graph C.mate).Reachable r x := by
  obtain ⟨K,v,P,he,r,hr,hconnected⟩ := hcore
  have hk : K=(l.map Prod.fst).length := by
    have hh := congrArg List.length he
    simpa only [List.length_map,List.length_finRange] using hh
  subst K
  let L := l.map Prod.fst
  have hnjoin : (CornerSplit.join l).Nodup := hjoin.symm ▸ List.nodup_finRange N
  have hn : L.Nodup := hnjoin.sublist (CornerSplit.skeleton_sublist l)
  have hs : L.Pairwise (·<·) :=
    (hjoin.symm ▸ List.pairwise_lt_finRange N).sublist (CornerSplit.skeleton_sublist l)
  have hv : ∀ i,w (L.get i)=v i := by
    have hh : (List.finRange L.length).map v=(List.finRange L.length).map (w ∘ L.get) := by
      rw [positions_word];exact he
    intro i
    exact (List.map_inj_left.mp hh i (List.mem_finRange i)).symm
  let Q := P.map L.get w (fun i _ => hv i)
  have hL : (List.finRange L.length).map L.get=L := List.map_get_finRange L
  let C : StackMatching w L := hL ▸ Q
  have hC : C.mate=Q.mate := StackMatching.cast_mate hL Q
  let e := positionEmbedding L hs
  have hmatch : ∀ i,C.mate (e i)=e (P.mate i) := by
    intro i
    rw [hC]
    exact P.map_mate (List.nodup_finRange _) L.get (List.nodup_iff_injective_get.mp hn)
      w (fun i _ => hv i) i (List.mem_finRange i)
  let R := openerEmbedding C.mate P.mate e hmatch r
  refine ⟨C,R,CornerSplit.join_first_zero l hjoin r.val hr,?_⟩
  intro x
  have hx : x.val∈L := by
    apply C.covers.mem_iff.mp
    by_contra hx
    exact (ne_of_gt x.property) (turns_fixed_of_notMem hx)
  have hxr : x.val∈Set.range e := by
    change ∃ i,L.get i=x.val
    exact List.mem_iff_get.mp hx
  obtain ⟨y,hy⟩ := opener_range C.mate P.mate e hmatch x hxr
  rw [← hy]
  exact (hconnected y).map (Chords.graphHom C.mate P.mate e hmatch)

/-- Literal inverse with *normalized connected words* as cores. The graph
connectivity and the full matching are constructed from the words. -/
theorem core_word_insertion_inverse (w : Fin N→TypedLetter)
    (l : List (Fin N×List (Fin N))) (hjoin : CornerSplit.join l=List.finRange N)
    (hcore : CoreWord ((l.map Prod.fst).map w))
    (hw : ∀ x∈l,stackTypedRun (x.2.map w) []=some [])
    (M : StackMatching w (List.finRange N)) :
    ∃ r : Opener M.mate,r.val.val=0 ∧ rootSplit M.mate r=l := by
  obtain ⟨C,r,hr,hconn⟩ := core_matching_at_positions w l hjoin hcore
  obtain ⟨R,hR,hsplit⟩ := connected_corner_inverse w l hjoin hw
    M.first M.second C.first C.second M.first_arches M.second_arches M.covers
    M.first_types M.second_types C.first_arches C.second_arches C.covers
    C.first_types C.second_types r hr hconn
  exact ⟨R,(congrArg Fin.val hR).trans hr,hsplit⟩

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles Chords

abbrev EmptyTypedWord := {w : List TypedLetter // stackTypedRun w []=some []}
abbrev NonemptyTypedWord := {w : EmptyTypedWord // w.val≠[]}

def ValidCorners (l : List (TypedLetter×List TypedLetter)) : Prop :=
  CoreWord (l.map Prod.fst) ∧ ∀ x∈l,stackTypedRun x.2 []=some []

lemma ValidCorners.empty {l : List (TypedLetter×List TypedLetter)} (h : ValidCorners l) :
    stackTypedRun (cornerInsert l) []=some [] :=
  (cornerInsert_run_count l h.2 (coreWord_empty _ h.1)).1

lemma ValidCorners.nonempty {l : List (TypedLetter×List TypedLetter)} (h : ValidCorners l) :
    cornerInsert l≠[] := by
  have hp := coreWord_pos _ h.1
  cases l with
  | nil => simp at hp
  | cons x l => simp [cornerInsert]

lemma core_lift_valid (l : List (TypedLetter×List TypedLetter)) (hl : ValidCorners l)
    {N : ℕ} (w : Fin N→TypedLetter) (L : List (Fin N×List (Fin N)))
    (hL : L.map (fun x => (w x.1,x.2.map w))=l) :
    CoreWord ((L.map Prod.fst).map w) ∧ ∀ x∈L,stackTypedRun (x.2.map w) []=some [] := by
  have he : (L.map Prod.fst).map w=l.map Prod.fst := by
    have hh := congrArg (List.map Prod.fst) hL
    simpa only [List.map_map,Function.comp_def] using hh
  refine ⟨he ▸ hl.1,?_⟩
  intro x hx
  exact hl.2 (w x.1,x.2.map w) (hL ▸ List.mem_map.mpr ⟨x,hx,rfl⟩)

/-- Rooted corner substitution is injective for the actual typed-word
inventory model, with every corner individually identified. -/
theorem valid_corner_injective {l r : List (TypedLetter×List TypedLetter)}
    (hl : ValidCorners l) (hr : ValidCorners r) (he : cornerInsert l=cornerInsert r) : l=r := by
  let w := cornerInsert l
  have hw := hl.empty
  have hwm : stackTypedRun ((List.finRange w.length).map w.get) []=some [] := by
    rw [List.map_get_finRange];exact hw
  let M := StackMatching.ofEmpty hwm
  obtain ⟨L,hL,hLm⟩ := CornerSplit.lift_join w.get l (List.finRange w.length) (List.map_get_finRange w)
  obtain ⟨R,hR,hRm⟩ := CornerSplit.lift_join w.get r (List.finRange w.length)
    ((List.map_get_finRange w).trans he)
  obtain ⟨hlc,hlw⟩ := core_lift_valid l hl w.get L hLm
  obtain ⟨hrc,hrw⟩ := core_lift_valid r hr w.get R hRm
  obtain ⟨a,ha,hsa⟩ := core_word_insertion_inverse w.get L hL hlc hlw M
  obtain ⟨b,hb,hsb⟩ := core_word_insertion_inverse w.get R hR hrc hrw M
  have hab : a=b := Subtype.ext (Fin.ext (ha.trans hb.symm))
  have hLR : L=R := by rw [← hsa,← hsb,hab]
  rw [← hLm,← hRm,hLR]

/-- Every nonempty successful typed word has its actual unique connected
core decomposition; children are strictly shorter, enabling recursion. -/
theorem exists_valid_corners (w : List TypedLetter) (hw : stackTypedRun w []=some [])
    (hne : w≠[]) :
    ∃ l : List (TypedLetter×List TypedLetter),ValidCorners l ∧ cornerInsert l=w ∧
      ∀ x∈l,x.2.length<w.length := by
  have hpos : 0<w.length := List.length_pos_iff.mpr hne
  have hwm : stackTypedRun ((List.finRange w.length).map w.get) []=some [] := by
    rw [List.map_get_finRange];exact hw
  let M := StackMatching.ofEmpty hwm
  let i : Fin w.length := ⟨0,hpos⟩
  have hni := M.no_fixed (List.nodup_finRange _) i (List.mem_finRange i)
  have hlt : i<M.mate i := by
    have hv := Fin.val_ne_of_ne hni
    change 0<(M.mate i).val
    change (M.mate i).val≠0 at hv
    omega
  let r : Opener M.mate := ⟨i,hlt⟩
  obtain ⟨hjoin,hcore,hchunks,_⟩ := successful_core_decomposition w.get M r rfl
  refine ⟨(rootSplit M.mate r).map (fun x => (w.get x.1,x.2.map w.get)),
    ⟨hcore,fun x hx => (hchunks x hx).1⟩,?_,fun x hx => (hchunks x hx).2⟩
  simpa only [List.map_get_finRange] using hjoin

abbrev CornerWords := {l : List (TypedLetter×List TypedLetter) // ValidCorners l}

def insertCornerWords (l : CornerWords) : NonemptyTypedWord :=
  ⟨⟨cornerInsert l.val,l.property.empty⟩,l.property.nonempty⟩

lemma insertCornerWords_bijective : Function.Bijective insertCornerWords := by
  constructor
  · intro l r h
    apply Subtype.ext
    exact valid_corner_injective l.property r.property (congrArg (fun w => w.val.val) h)
  · intro w
    obtain ⟨l,hl,he,_⟩ := exists_valid_corners w.val.val w.val.property w.property
    exact ⟨⟨l,hl⟩,Subtype.ext (Subtype.ext he)⟩

/-- Exact finite rooted corner-substitution bijection. This is not an
assumed block law, and it preserves all zero-size corner inserts. -/
def wordCornerEquiv : CornerWords ≃ NonemptyTypedWord :=
  Equiv.ofBijective insertCornerWords insertCornerWords_bijective

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory

abbrev Core := {w : List TypedLetter // CoreWord w}
abbrev CornerData := Σ c : Core,Fin c.val.length→EmptyTypedWord

def cornerList (c : Core) (f : Fin c.val.length→List TypedLetter) :
    List (TypedLetter×List TypedLetter) := List.ofFn (fun i => (c.val.get i,f i))

lemma cornerList_fst (c : Core) (f : Fin c.val.length→List TypedLetter) :
    (cornerList c f).map Prod.fst=c.val := by
  rw [cornerList,List.map_ofFn]
  exact List.ofFn_get c.val

lemma cornerList_valid (c : Core) (f : Fin c.val.length→EmptyTypedWord) :
    ValidCorners (cornerList c (fun i => (f i).val)) := by
  refine ⟨?_,?_⟩
  · rw [cornerList_fst];exact c.property
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (f i).property

def cornersOfData (d : CornerData) : CornerWords :=
  ⟨cornerList d.1 (fun i => (d.2 i).val),cornerList_valid d.1 d.2⟩

def dataOfCorners (l : CornerWords) : CornerData :=
  ⟨⟨l.val.map Prod.fst,l.property.1⟩,fun i =>
    ⟨l.val[i.val].2,l.property.2 l.val[i.val] (List.getElem_mem _)⟩⟩

lemma cornersOfData_dataOfCorners (l : CornerWords) : cornersOfData (dataOfCorners l)=l := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp [cornersOfData,cornerList,dataOfCorners]
  · intro i hi hi'
    simp only [cornersOfData,cornerList,dataOfCorners,List.getElem_ofFn,
      List.get_eq_getElem,List.getElem_map,Prod.eta]

lemma cornerList_congr_core {c d : Core} {f : Fin c.val.length→List TypedLetter}
    {g : Fin d.val.length→List TypedLetter} (h : cornerList c f=cornerList d g) : c=d := by
  apply Subtype.ext
  have hh := congrArg (List.map Prod.fst) h
  simpa only [cornerList_fst] using hh

lemma cornerList_injective (c : Core) : Function.Injective (cornerList c) := by
  intro f g h
  have hh := List.ofFn_injective h
  funext i
  exact congrArg Prod.snd (congrFun hh i)

lemma cornersOfData_injective : Function.Injective cornersOfData := by
  rintro ⟨c,f⟩ ⟨d,g⟩ h
  have hh : cornerList c (fun i => (f i).val)=cornerList d (fun i => (g i).val) := congrArg Subtype.val h
  have hcd := cornerList_congr_core hh
  subst d
  have hfg := cornerList_injective c hh
  have hfg' : f=g := by
    funext i
    exact Subtype.ext (congrFun hfg i)
  subst g
  rfl

lemma dataOfCorners_cornersOfData (d : CornerData) : dataOfCorners (cornersOfData d)=d :=
  cornersOfData_injective (cornersOfData_dataOfCorners (cornersOfData d))

def cornerDataEquiv : CornerData ≃ CornerWords where
  toFun := cornersOfData
  invFun := dataOfCorners
  left_inv := dataOfCorners_cornersOfData
  right_inv := cornersOfData_dataOfCorners

/-- An exact product description of all nonempty genuine words. -/
def coreChildrenEquiv : CornerData ≃ NonemptyTypedWord := cornerDataEquiv.trans wordCornerEquiv

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PlaneTrees
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

abbrev CoreLabel := Option Core
namespace CoreLabel

def arity : CoreLabel → ℕ
  | none => 0
  | some c => c.val.length

end CoreLabel

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_WordCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

/-- Bounded discrete Green supersolution for the walk killed at -1. -/
def greenMajorant (a b : ℕ) : ℝ := 2*(min (a+1) (b+1):ℕ)
lemma greenMajorant_nonneg (a b : ℕ) : 0 ≤ greenMajorant a b := by unfold greenMajorant; positivity
lemma greenMajorant_zero (b : ℕ) :
    greenMajorant 0 b=(if 0=b then 1 else 0)+greenMajorant 1 b/2 := by
  cases b with
  | zero => norm_num [greenMajorant]
  | succ b => simp [greenMajorant]
lemma greenMajorant_succ (a b : ℕ) :
    greenMajorant (a+1) b=(if a+1=b then 1 else 0)+(greenMajorant a b+greenMajorant (a+2) b)/2 := by
  unfold greenMajorant
  by_cases he : a+1=b
  · subst b
    rw [ite_eq_left rfl]
    simp only [min_eq_left (show a+1 ≤ a+1+1 by omega),min_eq_right (show a+1+1 ≤ a+2+1 by omega),min_self]
    push_cast
    ring
  · rw [ite_eq_right he]
    rcases lt_or_gt_of_ne he with hlt | hgt
    · have h1 : a+1+1 ≤ b+1 := by omega
      have h2 : a+1 ≤ b+1 := by omega
      have h3 : a+2+1 ≤ b+1 := by omega
      rw [min_eq_left h1,min_eq_left h2,min_eq_left h3]
      push_cast
      ring
    · have h1 : b+1 ≤ a+1+1 := by omega
      have h2 : b+1 ≤ a+1 := by omega
      have h3 : b+1 ≤ a+2+1 := by omega
      rw [min_eq_right h1,min_eq_right h2,min_eq_right h3]
      ring

lemma killed_green_partial (N a b : ℕ) :
    (∑ n∈Finset.range N,killed n a b) ≤ greenMajorant a b := by
  induction N generalizing a with
  | zero => simpa only [Finset.range_zero,Finset.sum_empty] using greenMajorant_nonneg a b
  | succ N ih =>
    rw [Finset.sum_range_succ']
    cases a with
    | zero =>
      simp only [killed]
      rw [← Finset.sum_div,greenMajorant_zero]
      linarith [ih 1]
    | succ a =>
      simp only [killed]
      rw [← Finset.sum_div,Finset.sum_add_distrib,greenMajorant_succ]
      linarith [ih a,ih (a+2)]

lemma killed_summable (a b : ℕ) : Summable (fun n => killed n a b) := by
  exact summable_of_sum_range_le (fun n => killed_nonneg n a b) (fun N => killed_green_partial N a b)

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def burgerSign : Letter → Bool
  | .burger _ => true
  | .order _ => false
lemma burgerSign_increment (a : Letter) : SimpleWalk.sign (burgerSign a)=a.increment := by
  cases a <;> rfl
lemma burgerSign_preserving (P : Parameters) :
    MeasurePreserving burgerSign (law P).toMeasure TreeCoding.coinLaw := by
  refine ⟨measurable_of_countable _,?_⟩
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),TreeCoding.coinLaw_singleton]
  have he : burgerSign ⁻¹' {b}=Finset.univ.filter (fun a => burgerSign a=b) := by ext a; simp
  rw [he,← sum_measure_singleton]
  simp only [Finset.sum_filter,law_singleton]
  rw [sum_letters]
  cases b <;> simp only [burgerSign,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,mass]
  · simp only [zero_add]
    rw [← ENNReal.ofReal_add (by linarith [P.upper] : 0 ≤ (1-P.p)/4) (by linarith [P.upper]),
      ← ENNReal.ofReal_add (by linarith [P.upper]) (by linarith [P.pos])]
    norm_num [show (1-P.p)/4+(1-P.p)/4+P.p/2=(1:ℝ)/2 by ring,ENNReal.ofReal_div_of_pos]
  · simp only [add_zero]
    rw [← ENNReal.ofReal_add (by norm_num : 0 ≤ (1:ℝ)/4) (by norm_num)]
    norm_num [ENNReal.ofReal_div_of_pos]

def rawPrefix (n : ℕ) (x : ℕ → Letter) : Fin n → Letter := fun i => x i
lemma rawPrefix_measurable (n : ℕ) : Measurable (rawPrefix n) :=
  Measurable.of_eval (fun index => measurable_pi_apply (index:ℕ))
lemma rawPrefix_preserving (P : Parameters) (n : ℕ) :
    MeasurePreserving (rawPrefix n) (streamLaw P ℕ) (Measure.pi (fun _ : Fin n => (law P).toMeasure)) := by
  have hi : iIndepFun (fun k (x : ℕ → Letter) => x k) (streamLaw P ℕ) :=
    iIndepFun_infinitePi (X := fun _ (a : Letter) => a) (fun _ => measurable_id)
  refine ⟨rawPrefix_measurable n,?_⟩
  have hh := (hi.precomp Fin.val_injective).map_fun_eq_pi_map (fun i : Fin n => (measurable_pi_apply (i:ℕ)).aemeasurable)
  change (streamLaw P ℕ).map (fun x (i : Fin n) => x i)=_
  rw [hh]
  congr 1
  funext i
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) (i:ℕ)).map_eq

def rawWord (x : ℕ → Letter) (n : ℕ) : List Letter := List.ofFn (rawPrefix n x)

def finiteSigns {n : ℕ} (x : Fin n → Letter) : SimpleWalk.Path n := fun i => burgerSign (x i)
lemma finiteSigns_preserving (P : Parameters) (n : ℕ) :
    MeasurePreserving finiteSigns (Measure.pi (fun _ : Fin n => (law P).toMeasure))
      (Measure.pi (fun _ : Fin n => TreeCoding.coinLaw)) := by
  refine ⟨measurable_of_countable _,?_⟩
  change (Measure.pi _).map (fun x i => burgerSign (x i))=Measure.pi _
  rw [Measure.pi_map_pi (fun _ => (measurable_of_countable _).aemeasurable)]
  simp only [(burgerSign_preserving P).map_eq]
lemma raw_sign_pathSum (x : ℕ → Letter) (n k : ℕ) (hk : k ≤ n) :
    SimpleWalk.pathSum (finiteSigns (rawPrefix n x)) k=signSum x k := by
  unfold SimpleWalk.pathSum finiteSigns rawPrefix signSum
  simp only [burgerSign_increment]
  rw [← Finset.sum_filter]
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_bij (fun i hi => ⟨i.val,(Finset.mem_filter.mp hi).2⟩)
    (by intro i hi; simp) (by intro i hi j hj he; exact Fin.ext (congrArg (fun z : Fin k => z.val) he))
    (by intro j hj; exact ⟨⟨j.val,lt_of_lt_of_le j.isLt hk⟩,by simp [j.isLt],rfl⟩)
    (by intro i hi; rfl)

def rawKilled (a b n : ℕ) : Set (ℕ → Letter) :=
  {x | (∀ j ≤ n,0 ≤ (a:ℤ)+signSum x j) ∧ (a:ℤ)+signSum x n=b}
lemma rawKilled_measure (P : Parameters) (a b n : ℕ) :
    (streamLaw P ℕ).real (rawKilled a b n)=SimpleWalk.killed n a b := by
  have hp := (finiteSigns_preserving P n).comp (rawPrefix_preserving P n)
  have he : rawKilled a b n=(fun x => finiteSigns (rawPrefix n x)) ⁻¹'
      {d | SimpleWalk.nonnegativePath a d ∧ (a:ℤ)+SimpleWalk.pathSum d n=b} := by
    ext x
    simp only [rawKilled,Set.mem_ofPred_eq,Set.mem_preimage,SimpleWalk.nonnegativePath]
    simp_rw [raw_sign_pathSum x n n le_rfl]
    apply and_congr_left
    intro _
    apply forall_congr'
    intro j
    apply forall_congr'
    intro hj
    rw [raw_sign_pathSum x n j hj]
  rw [he,measureReal_def]
  change ((streamLaw P ℕ) ((finiteSigns ∘ rawPrefix n) ⁻¹' _)).toReal=_
  rw [hp.measure_preimage (Set.to_countable _).measurableSet.nullMeasurableSet,
    ← measureReal_def,TreeCoding.coinPath_event,SimpleWalk.pathMass_killed]

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable
namespace FKCRT.Inventory

lemma typed_fixed_balance {v : List TypedLetter} (h : stackTypedRun v []=some []) :
    ((v.map TypedLetter.fixed).map Letter.increment).sum=0 := by
  apply ((emptyReducing_dyck _ ((emptyReducing_iff_identify _).mpr ⟨v,identify_fixed h⟩)).1)

def burgerCount (v : List TypedLetter) : ℕ :=
  (v.filter (fun a => match a with | .burger _ => true | .order _ => false)).length

def orderCount (v : List TypedLetter) : ℕ :=
  (v.filter (fun a => match a with | .burger _ => false | .order _ => true)).length

lemma typed_counts (v : List TypedLetter) :
    burgerCount v+orderCount v=v.length ∧
    ((v.map TypedLetter.fixed).map Letter.increment).sum=(burgerCount v:ℤ)-orderCount v := by
  induction v with
  | nil => simp [burgerCount,orderCount]
  | cons a v ih =>
    cases a <;> simp [burgerCount,orderCount,TypedLetter.fixed,Letter.increment] at * <;> omega

def wordsOfLength (α : Type*) [Fintype α] [DecidableEq α] (N : ℕ) : Finset (List α) :=
  Finset.univ.image (List.ofFn : (Fin N→α)→List α)

lemma mem_wordsOfLength {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ} {w : List α} :
    w∈wordsOfLength α N ↔ w.length=N := by
  constructor
  · intro h
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp h
    exact List.length_ofFn
  · intro h
    subst N
    apply Finset.mem_image.mpr
    exact ⟨fun i => w[i],Finset.mem_univ _,by simp⟩

def emptyWords (N : ℕ) : Finset (List Letter) := (wordsOfLength Letter N).filter EmptyReducing

def typedEmptyWords (N : ℕ) : Finset (List TypedLetter) :=
  (wordsOfLength TypedLetter N).filter (fun v => stackTypedRun v []=some [])

lemma emptyWords_markings (N : ℕ) :
    emptyWords N=(typedEmptyWords N).biUnion (fun v => markings v []) := by
  ext w
  simp only [emptyWords,Finset.mem_filter,mem_wordsOfLength,Finset.mem_biUnion,
    typedEmptyWords,mem_markings]
  constructor
  · rintro ⟨hl,hw⟩
    obtain ⟨v,hv⟩ := (emptyReducing_iff_identify _).mp hw
    obtain ⟨_,hr,he⟩ := identify_sound hv
    exact ⟨v,⟨he.trans hl,hr⟩,[],hv⟩
  · rintro ⟨v,⟨hl,hr⟩,t,ht⟩
    obtain ⟨_,hr',he⟩ := identify_sound ht
    have htt : t=[] := by rw [hr] at hr'; exact Option.some.inj hr'.symm
    subst t
    exact ⟨he.symm.trans hl,(emptyReducing_iff_identify _).mpr ⟨v,ht⟩⟩

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators ENNReal
namespace FKCRT.Inventory

lemma cornerInsert_length (l : List (TypedLetter×List TypedLetter)) :
    (cornerInsert l).length=l.length+(l.map (fun x => x.2.length)).sum := by
  induction l with
  | nil => simp [cornerInsert]
  | cons x l ih =>
    simp only [cornerInsert,List.flatMap_cons,List.length_append,List.length_cons] at *
    simp only [List.map_cons,List.sum_cons]
    omega

lemma cornerList_length (c : Core) (f : Fin c.val.length→List TypedLetter) :
    (cornerInsert (cornerList c f)).length=c.val.length+∑ i,(f i).length := by
  rw [cornerInsert_length]
  simp only [cornerList,List.length_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply]

lemma cornerList_flexible (c : Core) (f : Fin c.val.length→EmptyTypedWord) :
    flexibleCount (cornerInsert (cornerList c (fun i => (f i).val))) []=
      flexibleCount c.val []+∑ i,flexibleCount (f i).val [] := by
  have h := (cornerInsert_run_count _ (cornerList_valid c f).2
    (coreWord_empty _ (cornerList_valid c f).1)).2
  rw [cornerList_fst] at h
  simpa only [cornerList,List.map_ofFn,List.sum_ofFn,Function.comp_apply] using h

lemma empty_length_even (w : EmptyTypedWord) : Even w.val.length := by
  have h := typed_fixed_balance w.property
  obtain ⟨ha,hb⟩ := typed_counts w.val
  refine ⟨burgerCount w.val,?_⟩
  omega

/-- Literal weight in the letter-size variable. Specializing r²=u gives
exactly the source weight t^flex u^edges. -/
def wordMonomial {R : Type*} [CommMonoid R] (t r : R) (w : List TypedLetter) : R :=
  t^flexibleCount w []*r^w.length

lemma wordMonomial_nil {R : Type*} [CommMonoid R] (t r : R) : wordMonomial t r []=1 := by
  simp [wordMonomial,flexibleCount]

lemma wordMonomial_corners {R : Type*} [CommMonoid R] (t r : R) (c : Core)
    (f : Fin c.val.length→EmptyTypedWord) :
    wordMonomial t r (cornerInsert (cornerList c (fun i => (f i).val)))=
      wordMonomial t r c.val * ∏ i,wordMonomial t r (f i).val := by
  simp only [wordMonomial,cornerList_length,cornerList_flexible,pow_add,Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  ac_rfl

/-- The full genuine word generating series, with no convergence premise. -/
def wordSeries (t r : ℝ≥0∞) : ℝ≥0∞ := ∑' w : EmptyTypedWord,wordMonomial t r w.val

lemma tsum_fin_product {α : Type*} (f : α→ℝ≥0∞) (n : ℕ) :
    (∑' g : Fin n→α,∏ i,f (g i))=(∑' a,f a)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => α)).tsum_eq]
    simp only [Fin.consEquiv_apply,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left,ih]
    rw [ENNReal.tsum_mul_right,pow_succ']

lemma coreChildrenEquiv_weight (t r : ℝ≥0∞) (d : CornerData) :
    wordMonomial t r (coreChildrenEquiv d).val.val=
      wordMonomial t r d.1.val*∏ i,wordMonomial t r (d.2 i).val :=
  wordMonomial_corners t r d.1 d.2

/-- The nonempty part of T is exactly the nonnegative connected-core
substitution series. No independence or coefficient identity is assumed. -/
theorem nonempty_word_series (t r : ℝ≥0∞) :
    (∑' w : NonemptyTypedWord,wordMonomial t r w.val.val)=
      ∑' c : Core,t^flexibleCount c.val []*(r*wordSeries t r)^c.val.length := by
  rw [← coreChildrenEquiv.tsum_eq]
  simp_rw [coreChildrenEquiv_weight]
  rw [ENNReal.tsum_sigma (fun (c : Core) (f : Fin c.val.length→EmptyTypedWord) => wordMonomial t r c.val*∏ i,wordMonomial t r (f i).val)]
  apply tsum_congr
  intro c
  rw [ENNReal.tsum_mul_left,tsum_fin_product (fun w : EmptyTypedWord => wordMonomial t r w.val) c.val.length,wordMonomial,mul_pow]
  exact mul_assoc _ _ _

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PieceWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

lemma wordSeries_substitution (t r : ℝ≥0∞) :
    wordSeries t r=1+∑' c : Core,t^flexibleCount c.val []*(r*wordSeries t r)^c.val.length := by
  let : DecidableEq EmptyTypedWord := fun _ _ => Classical.propDecidable _
  let e : EmptyTypedWord := ⟨[],rfl⟩
  have hne : (∑' w : EmptyTypedWord,if w=e then 0 else wordMonomial t r w.val)=
      ∑' w : NonemptyTypedWord,wordMonomial t r w.val.val := by
    calc
      _=∑' w : EmptyTypedWord,
          Set.indicator {w : EmptyTypedWord | w.val≠[]} (fun w => wordMonomial t r w.val) w := by
        apply tsum_congr
        intro w
        by_cases hw : w.val=[]
        · have hwe : w=e := Subtype.ext hw
          simp [hwe,e,Set.indicator]
        · have hwe : w≠e := fun h => hw (congrArg Subtype.val h)
          simp [hw,hwe,Set.indicator]
      _ = _ := (tsum_subtype {w : EmptyTypedWord | w.val≠[]} (fun w => wordMonomial t r w.val)).symm
  calc
    wordSeries t r=wordMonomial t r e.val+
        ∑' w : EmptyTypedWord,if w=e then 0 else wordMonomial t r w.val :=
      by simpa only [wordSeries] using (ENNReal.tsum_eq_add_tsum_ite
        (f := fun w : EmptyTypedWord => wordMonomial t r w.val) e)
    _=1+∑' w : NonemptyTypedWord,wordMonomial t r w.val.val :=
      congrArg₂ (·+·) (wordMonomial_nil t r) hne
    _ = _ := by rw [nonempty_word_series]

def emptyAtSizeEquiv (m : ℕ) :
    {w : EmptyTypedWord // w.val.length/2=m} ≃ {w // w∈typedEmptyWords (2*m)} where
  toFun w := ⟨w.val.val,Finset.mem_filter.mpr ⟨mem_wordsOfLength.mpr (by
      obtain ⟨k,hk⟩ := empty_length_even w.val
      have hm := w.property
      omega),w.val.property⟩⟩
  invFun w := ⟨⟨w.val,(Finset.mem_filter.mp w.property).2⟩,by
    have h := mem_wordsOfLength.mp (Finset.mem_filter.mp w.property).1
    change w.val.length/2=m
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Arbitrary nonnegative observables partition by the actual even length. -/
lemma empty_tsum_by_size (f : List TypedLetter→ℝ≥0∞) :
    (∑' w : EmptyTypedWord,f w.val)=∑' m : ℕ,∑ w∈typedEmptyWords (2*m),f w := by
  rw [← (Equiv.sigmaFiberEquiv (fun w : EmptyTypedWord => w.val.length/2)).tsum_eq]
  change (∑' d : Σ m : ℕ,{w : EmptyTypedWord // w.val.length/2=m},f d.2.val.val)=_
  rw [ENNReal.tsum_sigma (fun (m : ℕ) (w : {w : EmptyTypedWord // w.val.length/2=m}) => f w.val.val)]
  apply tsum_congr
  intro m
  rw [← (emptyAtSizeEquiv m).symm.tsum_eq]
  change (∑' w : {w // w∈typedEmptyWords (2*m)},f w.val)=_
  rw [tsum_fintype]
  exact (Finset.sum_subtype (typedEmptyWords (2*m)) (fun _ => Iff.rfl) f).symm

def typedCoefficient (t : ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  ∑ w∈typedEmptyWords (2*m),t^flexibleCount w []

def coreSubtypeEquiv : Core ≃ {w : EmptyTypedWord // CoreWord w.val} where
  toFun c := ⟨⟨c.val,coreWord_empty _ c.property⟩,c.property⟩
  invFun w := ⟨w.val.val,w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma core_tsum_by_size (f : List TypedLetter→ℝ≥0∞) :
    (∑' c : Core,f c.val)=
      ∑' m : ℕ,∑ w∈(typedEmptyWords (2*m)).filter CoreWord,f w := by
  rw [← coreSubtypeEquiv.symm.tsum_eq]
  change (∑' c : {w : EmptyTypedWord // CoreWord w.val},f c.val.val)=_
  calc
    _=∑' w : EmptyTypedWord,Set.indicator {w : EmptyTypedWord | CoreWord w.val}
        (fun w => f w.val) w := tsum_subtype _ _
    _=∑' w : EmptyTypedWord,if CoreWord w.val then f w.val else 0 := rfl
    _=∑' m : ℕ,∑ w∈typedEmptyWords (2*m),if CoreWord w then f w else 0 :=
      empty_tsum_by_size (fun w => if CoreWord w then f w else 0)
    _=_ := by
      apply tsum_congr
      intro m
      simp only [Finset.sum_filter]

def coreCoefficient (t : ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  ∑ w∈(typedEmptyWords (2*m)).filter CoreWord,t^flexibleCount w []

lemma core_series_coefficients (t r : ℝ≥0∞) :
    (∑' c : Core,t^flexibleCount c.val []*r^c.val.length)=
      ∑' m : ℕ,coreCoefficient t m*(r^2)^m := by
  rw [core_tsum_by_size (fun w => t^flexibleCount w []*r^w.length)]
  apply tsum_congr
  intro m
  rw [coreCoefficient,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  have hl := mem_wordsOfLength.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
  rw [hl,pow_mul]

/-- Exact source T=1+Phi_+(u*T²), now for the actual connected-core
coefficients extracted from the original inventory words. -/
theorem wordSeries_core_coefficients (t r : ℝ≥0∞) :
    wordSeries t r=1+∑' m : ℕ,coreCoefficient t m*(r^2*wordSeries t r^2)^m := by
  calc
    wordSeries t r=1+∑' c : Core,t^flexibleCount c.val []*(r*wordSeries t r)^c.val.length :=
      wordSeries_substitution t r
    _=_ := by rw [core_series_coefficients,mul_pow]

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

@[instance_reducible] def pieceCoords (S : Set ℕ) : MeasurableSpace (ℕ → List Letter) :=
  ⨆ j∈S,MeasurableSpace.comap (fun x : ℕ → List Letter => x j) inferInstance

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_StationaryCuts
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.CutOutput

/-- Totalized first index; on nonempty predicates this is the ordinary least index. -/
def firstIndex (p : ℕ → Prop) : ℕ := by
  classical
  exact Nat.find (show ∃ n,p n ∨ ¬∃ k,p k from by
    by_cases h : ∃ k,p k
    · obtain ⟨k,hk⟩ := h; exact ⟨k,Or.inl hk⟩
    · exact ⟨0,Or.inr h⟩)
lemma firstIndex_spec {p : ℕ → Prop} (hp : ∃ k,p k) : p (firstIndex p) := by
  classical
  exact (Nat.find_spec (show ∃ n,p n ∨ ¬∃ k,p k from by
    obtain ⟨k,hk⟩ := hp; exact ⟨k,Or.inl hk⟩)).resolve_right (by simpa using hp)
lemma firstIndex_le {p : ℕ → Prop} {k : ℕ} (hk : p k) : firstIndex p ≤ k := by
  classical
  exact Nat.find_min' _ (Or.inl hk)
lemma firstIndex_measurable {Ω : Type*} [MeasurableSpace Ω] (p : Ω → ℕ → Prop)
    (hm : ∀ k,MeasurableSet {x | p x k}) : Measurable (fun x => firstIndex (p x)) := by
  classical
  unfold firstIndex
  apply measurable_find
  intro k
  have hh : MeasurableSet {x | ∃ j,p x j} := by
    simp only [Set.ofPred_exists]; exact MeasurableSet.iUnion hm
  exact (hm k).union hh.compl

structure Data (β : Type*) where
  cut : ℤ → Prop
  word : ℤ → ℕ → List β
  length : ∀ (a : ℤ) (n : ℕ),cut a → cut (a+n) → (word a n).length=n
  append : ∀ (a : ℤ) (m n : ℕ),cut a → cut (a+m) → cut (a+m+n) →
    word a (m+n)=word a m++word (a+m) n

variable {β : Type*}
def left (C : ℤ → Prop) (i : ℤ) : ℕ := firstIndex (fun k => C (i-k))
def right (C : ℤ → Prop) (i : ℤ) : ℕ := firstIndex (fun k => C (i+1+k))
def output (C : ℤ → Prop) (W : ℤ → ℕ → List β) (d : β) (i : ℤ) : β :=
  ((W (i-left C i) (left C i+1+right C i))[left C i]?).getD d

lemma Data.output_eq_get (D : Data β) (d : β) (a : ℤ) (n : ℕ) (i : ℤ)
    (ha : D.cut a) (hb : D.cut (a+n)) (hai : a ≤ i) (hib : i<a+n) :
    output D.cut D.word d i=(D.word a n)[(i-a).toNat]'(by rw [D.length a n ha hb]; omega) := by
  let l := left D.cut i
  let r := right D.cut i
  have hl : l ≤ (i-a).toNat := by
    apply firstIndex_le
    have he : i-((i-a).toNat:ℤ)=a := by omega
    rw [he]
    exact ha
  have hr : r ≤ (a+n-i-1).toNat := by
    apply firstIndex_le
    have he : i+1+((a+n-i-1).toNat:ℤ)=a+n := by omega
    rw [he]
    exact hb
  have hc : D.cut (i-l) := firstIndex_spec (p := fun k => D.cut (i-k)) ⟨(i-a).toNat,by
    have he : i-((i-a).toNat:ℤ)=a := by omega
    rw [he]; exact ha⟩
  have hd : D.cut (i+1+r) := firstIndex_spec (p := fun k => D.cut (i+1+k)) ⟨(a+n-i-1).toNat,by
    have he : i+1+((a+n-i-1).toNat:ℤ)=a+n := by omega
    rw [he]; exact hb⟩
  let u := (i-a).toNat-l
  let v := l+1+r
  let t := n-u-v
  have hn : n=u+v+t := by dsimp [u,v,t]; omega
  have hac : a+u=i-l := by dsimp [u]; omega
  have hcd : a+u+v=i+1+r := by dsimp [u,v]; omega
  have he : D.word a n=D.word a u++D.word (a+u) v++D.word (a+u+v) t := by
    have hd' : D.cut (a+(u+v:ℕ)) := by
      rw [show a+((u+v:ℕ):ℤ)=i+1+r by omega]; exact hd
    have hb' : D.cut (a+(u+v:ℕ)+t) := by
      rw [show a+((u+v:ℕ):ℤ)+t=a+n by omega]; exact hb
    rw [hn,D.append a (u+v) t ha hd' hb']
    rw [D.append a u v ha (by simpa only [hac] using hc) (by simpa only [hcd] using hd)]
    simp only [Nat.cast_add,add_assoc]
  have hu : (D.word a u).length=u := D.length a u ha (by simpa only [hac] using hc)
  have hv : (D.word (a+u) v).length=v := D.length _ _ (by simpa only [hac] using hc) (by simpa only [hcd] using hd)
  have hget : (D.word a n)[(i-a).toNat]?=(D.word (i-l) v)[l]? := by
    rw [he,List.getElem?_append]
    have hii : (i-a).toNat<(D.word a u++D.word (a+u) v).length := by simp only [List.length_append,hu,hv]; dsimp [u,v]; omega
    rw [ite_eq_left hii,List.getElem?_append,hu,ite_eq_right (by dsimp [u]; omega)]
    have hidx : (i-a).toNat-u=l := by dsimp [u]; omega
    rw [hidx,hac]
  have hni : (i-a).toNat<(D.word a n).length := by rw [D.length a n ha hb]; omega
  have hh := congrArg (fun o : Option β => o.getD d) hget
  simpa only [List.getElem?_eq_getElem hni,Option.getD_some,output,l,r,v] using hh.symm

lemma Data.output_segment (D : Data β) (d : β) (a : ℤ) (n : ℕ)
    (ha : D.cut a) (hb : D.cut (a+n)) :
    List.ofFn (fun j : Fin n => output D.cut D.word d (a+j))=D.word a n := by
  apply List.ext_getElem
  · simp [D.length a n ha hb]
  · intro j hj hk
    have hj' : j<n := by simpa using hj
    simp only [List.getElem_ofFn]
    simpa only [add_sub_cancel_left,Int.toNat_natCast] using D.output_eq_get d a n (a+j) ha hb (by omega) (by omega)

lemma output_translate (C : ℤ → Prop) (W : ℤ → ℕ → List β) (d : β) (a i : ℤ) :
    output (fun j => C (j+a)) (fun j n => W (j+a) n) d i=output C W d (i+a) := by
  have hl : left (fun j => C (j+a)) i=left C (i+a) := by
    unfold left
    congr 1
    funext k
    dsimp only
    rw [show i-(k:ℤ)+a=i+a-k by omega]
  have hr : right (fun j => C (j+a)) i=right C (i+a) := by
    unfold right
    congr 1
    funext k
    dsimp only
    rw [show i+1+(k:ℤ)+a=i+a+1+k by omega]
  unfold output
  rw [hl,hr]
  dsimp only
  rw [show i-(left C (i+a):ℤ)+a=i+a-left C (i+a) by omega]

lemma output_measurable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (C : Ω → ℤ → Prop) (W : Ω → ℤ → ℕ → List β) (d : β) (i : ℤ)
    [MeasurableSpace (List β)] [MeasurableSingletonClass (List β)] [Countable (List β)]
    (hC : ∀ j,MeasurableSet {x | C x j}) (hW : ∀ a n,Measurable (fun x => W x a n)) :
    Measurable (fun x => output (C x) (W x) d i) := by
  have hl : Measurable (fun x => left (C x) i) := firstIndex_measurable _ (fun k => hC (i-k))
  have hr : Measurable (fun x => right (C x) i) := firstIndex_measurable _ (fun k => hC (i+1+k))
  have hw : Measurable (fun x => W x (i-left (C x) i) (left (C x) i+1+right (C x) i)) := by
    let f : Ω × (ℤ × ℕ) → List β := fun p => W p.1 p.2.1 p.2.2
    have hf : Measurable f := measurable_from_prod_countable_left (fun p => hW p.1 p.2)
    exact hf.comp (measurable_id.prodMk (((measurable_of_countable (fun n : ℕ => i-(n:ℤ))).comp hl).prodMk ((hl.add_const 1).add hr)))
  exact (measurable_of_countable (fun p : List β × ℕ => (p.1[p.2]?).getD d)).comp (hw.prodMk hl)

end FKCRT.CutOutput
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PieceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.CutOutput
open Classical

/-- Number of marked boundaries before n. -/
def count (C : ℕ → Prop) (n : ℕ) : ℕ := by
  classical
  exact ∑ i∈Finset.range n,if C i then 1 else 0
def last (C : ℕ → Prop) (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest C n
lemma last_le (C : ℕ → Prop) (n : ℕ) : last C n ≤ n := Nat.findGreatest_le _
lemma last_spec {C : ℕ → Prop} (hC : C 0) (n : ℕ) : C (last C n) := Nat.findGreatest_spec (Nat.zero_le n) hC
lemma count_le (C : ℕ → Prop) (n : ℕ) : count C n ≤ n := by
  classical
  calc
    _ ≤ ∑ _ ∈ Finset.range n,1 := Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
    _ = n := by simp
lemma count_at_last (C : ℕ → Prop) (n : ℕ) : count C (last C n+1)=count C (n+1) := by
  classical
  apply Finset.sum_subset (Finset.range_mono (by have := last_le C n; omega))
  intro j hj hj'
  have hjle : j ≤ n := by have := Finset.mem_range.mp hj; omega
  have hjgt : last C n<j := by have := Finset.mem_range.not.mp hj'; omega
  have hn : ¬C j := Nat.findGreatest_is_greatest hjgt hjle
  simp [hn]
lemma countReal (C : ℕ → Prop) (n : ℕ) :
    (count C n:ℝ)=∑ i∈Finset.range n,if C i then (1:ℝ) else 0 := by
  classical
  simp only [count,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> norm_num

/-- Positive density is enough; no independence between cuts is used. -/
lemma last_tendsto (C : ℕ → Prop) {δ : ℝ} (hδ : 0<δ)
    (hd : Tendsto (fun n => (count C n:ℝ)/(n:ℝ)) atTop (𝓝 δ)) :
    Tendsto (fun n => last C n+1) atTop atTop := by
  have hshift : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
  have hc : Tendsto (fun n => (count C (n+1):ℝ)) atTop atTop := by
    have hm := (hd.comp hshift).pos_mul_atTop hδ (tendsto_natCast_atTop_atTop.comp hshift)
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact (div_mul_cancel₀ _ (by positivity : ((n+1:ℕ):ℝ)≠0)).symm
  rw [← tendsto_natCast_atTop_iff (R := ℝ)]
  apply tendsto_atTop_mono (fun n => ?_) hc
  rw [← count_at_last C n]
  exact_mod_cast count_le C (last C n+1)

lemma last_ratio (C : ℕ → Prop) {δ : ℝ} (hδ : 0<δ)
    (hd : Tendsto (fun n => (count C n:ℝ)/(n:ℝ)) atTop (𝓝 δ)) :
    Tendsto (fun n => ((last C n+1:ℕ):ℝ)/((n+1:ℕ):ℝ)) atTop (𝓝 1) := by
  have hshift : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
  have ha := hd.comp hshift
  have hb := hd.comp (last_tendsto C hδ hd)
  have hdiv := ha.div hb (ne_of_gt hδ)
  rw [div_self (ne_of_gt hδ)] at hdiv
  apply hdiv.congr'
  have hp := (tendsto_order.mp ha).1 0 hδ
  filter_upwards [hp] with n hn
  dsimp only [Function.comp_def,Pi.div_apply] at hn ⊢
  have hc : (count C (n+1):ℝ)≠0 := by intro hz; rw [hz,zero_div] at hn; exact lt_irrefl _ hn
  rw [count_at_last]
  field_simp

lemma last_gap_ratio (C : ℕ → Prop) {δ : ℝ} (hδ : 0<δ)
    (hd : Tendsto (fun n => (count C n:ℝ)/(n:ℝ)) atTop (𝓝 δ)) :
    Tendsto (fun n => ((n-last C n:ℕ):ℝ)/((n+1:ℕ):ℝ)) atTop (𝓝 0) := by
  have hh := (tendsto_const_nhds (x := (1:ℝ)) (f := (atTop : Filter ℕ))).sub (last_ratio C hδ hd)
  rw [sub_self (1:ℝ)] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [Nat.cast_sub (last_le C n)]
  push_cast
  field_simp
  ring

lemma last_gap_div (C : ℕ → Prop) {δ : ℝ} (hδ : 0<δ)
    (hd : Tendsto (fun n => (count C n:ℝ)/(n:ℝ)) atTop (𝓝 δ)) :
    Tendsto (fun n => ((n-last C n:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 0) := by
  have hh := (last_gap_ratio C hδ hd).div (tendsto_natCast_div_add_atTop (1:ℝ)) (by norm_num : (1:ℝ)≠0)
  simp only [zero_div] at hh
  apply hh.congr'
  filter_upwards [eventually_ne_atTop (0:ℕ)] with n hn
  dsimp only [Pi.div_apply]
  push_cast
  field_simp

lemma last_div (C : ℕ → Prop) {δ : ℝ} (hδ : 0<δ)
    (hd : Tendsto (fun n => (count C n:ℝ)/(n:ℝ)) atTop (𝓝 δ)) :
    Tendsto (fun n => (last C n:ℝ)/(n:ℝ)) atTop (𝓝 1) := by
  have hh := (tendsto_const_nhds (x := (1:ℝ)) (f := (atTop : Filter ℕ))).sub (last_gap_div C hδ hd)
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ne_atTop (0:ℕ)] with n hn
  rw [Nat.cast_sub (last_le C n)]
  have hne : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn
  field_simp
  ring

end FKCRT.CutOutput
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SeamLengths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def emptyProb (P : Parameters) (N : ℕ) : ℝ := (streamLaw P ℕ).real {x | EmptyReducing (rawWord x N)}
lemma emptyProb_nonneg (P : Parameters) (N : ℕ) : 0≤emptyProb P N := measureReal_nonneg

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_BlockCritical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Analysis

lemma log_lower_near_one {x : ℝ} (hx : (1:ℝ)/2≤x) (hx1 : x≤1) : -2*(1-x)≤Real.log x := by
  have hx0 : 0<x := by linarith
  apply le_trans _ (Real.one_sub_inv_le_log_of_pos hx0)
  have hi : x*x⁻¹=1 := mul_inv_cancel₀ hx0.ne'
  have hp := mul_nonneg (show 0≤1-x by linarith) (show 0≤2*x-1 by linarith)
  apply (mul_le_mul_iff_right₀ hx0).mp
  nlinarith

/-- A square-root lower bound on quadratic partial sums implies the exact
Abel square-root divergence, without an unproved Tauberian principle. -/
theorem quadratic_partial_abel_lower (b : ℕ → ℝ) (hb : ∀ n,0≤b n)
    (δ : ℝ) (hδ : 0<δ) (A : ℕ)
    (hpartial : ∀ H : ℕ,δ*H≤∑ n∈Finset.range (2*A*H^2+1),b n) :
    ∃ c : ℝ,0 < c ∧ ∀ x : ℝ,(3:ℝ)/4≤x → x<1 →
      Summable (fun n => b n*x^n) → c/Real.sqrt (1-x)≤∑' n,b n*x^n := by
  let c := δ*Real.exp (-4*A)/2
  refine ⟨c,by dsimp [c]; positivity,?_⟩
  intro x hx hx1 hsum
  have hx0 : 0<x := by linarith
  have hu : 0<1-x := by linarith
  have hs : 0<Real.sqrt (1-x) := Real.sqrt_pos.mpr hu
  have hs2 : Real.sqrt (1-x)^2=1-x := Real.sq_sqrt hu.le
  have hsbound : Real.sqrt (1-x)≤1/2 := by nlinarith [Real.sqrt_nonneg (1-x)]
  let r := 1/Real.sqrt (1-x)
  let H := ⌊r⌋₊
  have hrpos : 0 ≤ r := by dsimp [r]; positivity
  have hr2 : 2 ≤ r := by dsimp [r]; apply (le_div_iff₀ hs).mpr; linarith
  have hHle : (H:ℝ) ≤ r := Nat.floor_le hrpos
  have hrlt : r<(H:ℝ)+1 := Nat.lt_floor_add_one r
  have hHhalf : r/2≤(H:ℝ) := by linarith
  have hHr : (H:ℝ)*Real.sqrt (1-x)≤1 := by
    have he := (le_div_iff₀ hs).mp hHle
    exact he
  have hHsq : (H:ℝ)^2*(1-x)≤1 := by
    have he := pow_le_pow_left₀ (show 0≤(H:ℝ)*Real.sqrt (1-x) by positivity) hHr 2
    simpa only [mul_pow,hs2,one_pow] using he
  let M := 2*A*H^2
  have hM : (M:ℝ)*(1-x)≤2*(A:ℝ) := by
    have he := mul_le_mul_of_nonneg_left hHsq (show 0≤2*(A:ℝ) by positivity)
    dsimp [M]
    push_cast
    nlinarith
  have hlog := log_lower_near_one (x := x) (by linarith) hx1.le
  have hpow : Real.exp (-4*A)≤x^M := by
    rw [← Real.exp_log hx0,← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hlog (show 0≤(M:ℝ) by positivity)
    nlinarith
  have hpart : δ*(H:ℝ)*x^M≤∑ n∈Finset.range (M+1),b n*x^n := by
    calc
      _ ≤ (∑ n∈Finset.range (M+1),b n)*x^M := mul_le_mul_of_nonneg_right (hpartial H) (pow_nonneg hx0.le _)
      _ = ∑ n∈Finset.range (M+1),b n*x^M := Finset.sum_mul _ _ _
      _ ≤ _ := Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hx0.le hx1.le (by have := Finset.mem_range.mp hn; omega)) (hb n))
  have htsum := hsum.sum_le_tsum (Finset.range (M+1)) (fun n _ => mul_nonneg (hb n) (pow_nonneg hx0.le _))
  apply le_trans _ (hpart.trans htsum)
  have he1 := mul_le_mul_of_nonneg_left hpow (show 0≤δ*(H:ℝ) by positivity)
  have he2 := mul_le_mul_of_nonneg_left hHhalf (show 0≤δ*Real.exp (-4*A) by positivity)
  dsimp [c,r] at *
  calc
    _ = (δ*Real.exp (-4*A))*((1/Real.sqrt (1-x))/2) := by ring
    _ ≤ (δ*Real.exp (-4*A))*(H:ℝ) := he2
    _ = δ*(H:ℝ)*Real.exp (-4*A) := by ring
    _ ≤ _ := he1

end FKCRT.Analysis
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.BlockCritical

def geomPrefix (k : ℕ) (x : ℝ) : ℝ := ∑ i ∈ Finset.range k,x^i

def triPrefix (k : ℕ) (x : ℝ) : ℝ := ∑ i ∈ Finset.range k,geomPrefix i x

lemma geomPrefix_nonneg (k : ℕ) {x : ℝ} (hx : 0≤x) : 0≤geomPrefix k x := by
  exact Finset.sum_nonneg (fun _ _ => pow_nonneg hx _)

lemma geomPrefix_mul (k : ℕ) (x : ℝ) : (1-x)*geomPrefix k x=1-x^k := by
  induction k with
  | zero => simp [geomPrefix]
  | succ k ih =>
    simp only [geomPrefix,Finset.sum_range_succ] at ih ⊢
    rw [mul_add,ih,pow_succ]
    ring

lemma geomPrefix_le_nat (k : ℕ) {x : ℝ} (hx : 0≤x) (hx' : x≤1) :
    geomPrefix k x≤k := by
  calc
    geomPrefix k x ≤ ∑ _i ∈ Finset.range k,(1:ℝ) :=
      Finset.sum_le_sum fun _ _ => pow_le_one₀ hx hx'
    _ = k := by simp

lemma geomPrefix_le_inv (k : ℕ) {x : ℝ} (hx : 0≤x) (hx' : x<1) :
    geomPrefix k x≤1/(1-x) := by
  apply (le_div_iff₀ (sub_pos.mpr hx')).2
  rw [mul_comm,geomPrefix_mul]
  linarith [pow_nonneg hx k]

@[simp] lemma geomPrefix_one (k : ℕ) : geomPrefix k 1=k := by simp [geomPrefix]

lemma continuous_geomPrefix (k : ℕ) : Continuous (geomPrefix k) := by
  unfold geomPrefix
  fun_prop

lemma triPrefix_nonneg (k : ℕ) {x : ℝ} (hx : 0≤x) : 0≤triPrefix k x :=
  Finset.sum_nonneg (fun _ _ => geomPrefix_nonneg _ hx)

lemma triPrefix_mul (k : ℕ) (x : ℝ) :
    (1-x)^2*triPrefix k x=x^k-1+(k:ℝ)*(1-x) := by
  induction k with
  | zero => simp [triPrefix]
  | succ k ih =>
    change (1-x)^2*(∑ i ∈ Finset.range (k+1),geomPrefix i x)=_
    rw [Finset.sum_range_succ,mul_add]
    change (1-x)^2*triPrefix k x+(1-x)^2*geomPrefix k x=_
    rw [ih,show (1-x)^2*geomPrefix k x=(1-x)*((1-x)*geomPrefix k x) by ring,
      geomPrefix_mul,pow_succ,Nat.cast_add,Nat.cast_one]
    ring

lemma triPrefix_le_div (k : ℕ) {x : ℝ} (hx : 0≤x) (hx' : x<1) :
    triPrefix k x≤(k:ℝ)/(1-x) := by
  calc
    triPrefix k x≤∑ _i ∈ Finset.range k,1/(1-x) :=
      Finset.sum_le_sum fun _ _ => geomPrefix_le_inv _ hx hx'
    _ = (k:ℝ)/(1-x) := by simp [div_eq_mul_inv]

lemma square_eq_triPrefix (k : ℕ) : (k:ℝ)^2=(k:ℝ)+2*triPrefix k 1 := by
  induction k with
  | zero => simp [triPrefix]
  | succ k ih =>
    change ((k+1:ℕ):ℝ)^2=((k+1:ℕ):ℝ)+2*(∑ i ∈ Finset.range (k+1),geomPrefix i 1)
    rw [Finset.sum_range_succ,geomPrefix_one,Nat.cast_add,Nat.cast_one]
    change ((k:ℝ)+1)^2=(k:ℝ)+1+2*(triPrefix k 1+(k:ℝ))
    nlinarith

lemma continuous_triPrefix (k : ℕ) : Continuous (triPrefix k) := by
  exact continuous_finsetSum _ (fun i _ => continuous_geomPrefix i)

structure Weights where
  mass : ℕ → ℝ
  nonneg : ∀ k,0 ≤ mass k
  total : HasSum mass 1

def Weights.pgf (p : Weights) (x : ℝ) : ℝ := ∑' k,p.mass k*x^k

lemma Weights.summable_pgf (p : Weights) {x : ℝ} (hx : 0≤x) (hx' : x≤1) :
    Summable (fun k => p.mass k*x^k) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (p.nonneg k) (pow_nonneg hx k))
    (fun k => ?_) p.total.summable
  exact mul_le_of_le_one_right (p.nonneg k) (pow_le_one₀ hx hx')

lemma Weights.pgf_nonneg (p : Weights) {x : ℝ} (hx : 0≤x) : 0≤p.pgf x :=
  tsum_nonneg (fun k => mul_nonneg (p.nonneg k) (pow_nonneg hx k))

lemma Weights.pgf_le_one (p : Weights) {x : ℝ} (hx : 0≤x) (hx' : x≤1) : p.pgf x≤1 := by
  rw [← p.total.tsum_eq]
  exact (p.summable_pgf hx hx').tsum_le_tsum
    (fun k => mul_le_of_le_one_right (p.nonneg k) (pow_le_one₀ hx hx')) p.total.summable

lemma Weights.summable_geom (p : Weights) {x : ℝ} (hx : 0≤x) (hx' : x<1) :
    Summable (fun k => p.mass k*geomPrefix k x) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (p.nonneg k) (geomPrefix_nonneg k hx))
    (fun k => mul_le_mul_of_nonneg_left (geomPrefix_le_inv k hx hx') (p.nonneg k))
    (p.total.summable.mul_right _)

lemma Weights.geom_identity (p : Weights) {x : ℝ} (hx : 0≤x) (hx' : x<1) :
    (1-x)*(∑' k,p.mass k*geomPrefix k x)=1-p.pgf x := by
  have hh := p.total.sub (p.summable_pgf hx hx'.le).hasSum
  have hi : ∀ k,p.mass k-p.mass k*x^k=(1-x)*(p.mass k*geomPrefix k x) := by
    intro k
    rw [show (1-x)*(p.mass k*geomPrefix k x)=p.mass k*((1-x)*geomPrefix k x) by ring,geomPrefix_mul]
    ring
  simp_rw [hi] at hh
  exact ((p.summable_geom hx hx').hasSum.mul_left (1-x)).unique hh

lemma Weights.tendsto_pgf (p : Weights) {x : ℕ → ℝ} (hx : ∀ n,0≤x n ∧ x n≤1)
    (ht : Tendsto x atTop (𝓝 1)) : Tendsto (fun n => p.pgf (x n)) atTop (𝓝 1) := by
  have hd := tendsto_tsum_of_dominated_convergence p.total.summable
    (fun k => (tendsto_const_nhds.mul (ht.pow k)))
    (Eventually.of_forall (fun n k => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (p.nonneg k) (pow_nonneg (hx n).1 k))]
      exact mul_le_of_le_one_right (p.nonneg k) (pow_le_one₀ (hx n).1 (hx n).2)))
  simpa only [one_pow,mul_one,p.total.tsum_eq,Weights.pgf] using hd

/-- A quadratic inverse gap is enough for the exact critical first moment and
finite second moment. No analyticity past the endpoint or third moment occurs.
The hypotheses are the normalized source inverse bound, not moment assumptions. -/
theorem Weights.moments_of_quadratic (p : Weights) {x : ℕ → ℝ}
    (hx : ∀ n,0≤x n ∧ x n<1) (ht : Tendsto x atTop (𝓝 1))
    {C : ℝ} (_hC : 0≤C)
    (hgap : ∀ n,0≤(p.pgf (x n))^2-x n ∧
      (p.pgf (x n))^2-x n≤C*(1-x n)^2) :
    HasSum (fun k : ℕ => (k:ℝ)*p.mass k) (1/2) ∧
      Summable (fun k : ℕ => (k:ℝ)^2*p.mass k) := by
  have hb (n) : (∑' k,p.mass k*geomPrefix k (x n))≤1 := by
    have hi := p.geom_identity (hx n).1 (hx n).2
    have hp := p.pgf_le_one (hx n).1 (hx n).2.le
    have hpos := p.pgf_nonneg (hx n).1
    have hg := (hgap n).1
    have hl : x n≤p.pgf (x n) := by nlinarith
    nlinarith [(sub_pos.mpr (hx n).2)]
  have hf (s : Finset ℕ) : (∑ k ∈ s,p.mass k*(k:ℝ))≤1 := by
    have hlim : Tendsto (fun n => ∑ k ∈ s,p.mass k*geomPrefix k (x n)) atTop
        (𝓝 (∑ k ∈ s,p.mass k*(k:ℝ))) := by
      apply tendsto_finsetSum
      intro k _
      simpa only [geomPrefix_one,Function.comp_def] using tendsto_const_nhds.mul ((continuous_geomPrefix k).tendsto 1 |>.comp ht)
    apply le_of_tendsto hlim
    exact Eventually.of_forall (fun n =>
      (Summable.sum_le_tsum s (fun k _ => mul_nonneg (p.nonneg k) (geomPrefix_nonneg k (hx n).1))
        (p.summable_geom (hx n).1 (hx n).2)).trans (hb n))
  have hm : Summable (fun k => p.mass k*(k:ℝ)) :=
    summable_of_sum_le (fun k => mul_nonneg (p.nonneg k) (Nat.cast_nonneg k)) hf
  let μ := ∑' k,p.mass k*(k:ℝ)
  have hD : Tendsto (fun n => ∑' k,p.mass k*geomPrefix k (x n)) atTop (𝓝 μ) := by
    apply tendsto_tsum_of_dominated_convergence hm
    · intro k
      simpa only [geomPrefix_one,Function.comp_def] using tendsto_const_nhds.mul ((continuous_geomPrefix k).tendsto 1 |>.comp ht)
    · exact Eventually.of_forall (fun n k => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (p.nonneg k) (geomPrefix_nonneg k (hx n).1))]
        exact mul_le_mul_of_nonneg_left (geomPrefix_le_nat k (hx n).1 (hx n).2.le) (p.nonneg k))
  have hp := p.tendsto_pgf (fun n => ⟨(hx n).1,(hx n).2.le⟩) ht
  have hprod : Tendsto (fun n => (1+p.pgf (x n))*(∑' k,p.mass k*geomPrefix k (x n))) atTop (𝓝 ((1+1)*μ)) := (tendsto_const_nhds.add hp).mul hD
  have he (n) : (1-x n)*(1-(1+p.pgf (x n))*(∑' k,p.mass k*geomPrefix k (x n)))=
      (p.pgf (x n))^2-x n := by
    rw [show (1-x n)*(1-(1+p.pgf (x n))*(∑' k,p.mass k*geomPrefix k (x n)))=
      1-x n-(1+p.pgf (x n))*((1-x n)*(∑' k,p.mass k*geomPrefix k (x n))) by ring,
      p.geom_identity (hx n).1 (hx n).2]
    ring
  have heBounds (n) : 0≤1-(1+p.pgf (x n))*(∑' k,p.mass k*geomPrefix k (x n)) ∧
      1-(1+p.pgf (x n))*(∑' k,p.mass k*geomPrefix k (x n))≤C*(1-x n) := by
    have hid := he n
    have h := hgap n
    have hxpos : 0<1-x n := sub_pos.mpr (hx n).2
    constructor <;> nlinarith
  have hμ : μ=1/2 := by
    have hl : 0≤1-(1+1)*μ := ge_of_tendsto (tendsto_const_nhds.sub hprod)
      (Eventually.of_forall (fun n => (heBounds n).1))
    have hz : Tendsto (fun n => C*(1-x n)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.sub ht) : Tendsto (fun n => C*(1-x n)) atTop (𝓝 (C*(1-1))))
    have hu : 1-(1+1)*μ≤0 := le_of_tendsto_of_tendsto (tendsto_const_nhds.sub hprod)
      hz
      (Eventually.of_forall (fun n => (heBounds n).2))
    linarith
  have hts (n) : Summable (fun k => p.mass k*triPrefix k (x n)) := by
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (p.nonneg k) (triPrefix_nonneg k (hx n).1))
      (fun k => ?_) (hm.mul_right (1/(1-x n)))
    simpa only [div_eq_mul_inv,one_mul,mul_assoc] using mul_le_mul_of_nonneg_left (triPrefix_le_div k (hx n).1 (hx n).2) (p.nonneg k)
  have htri (n) : (1-x n)^2*(∑' k,p.mass k*triPrefix k (x n))=
      p.pgf (x n)-1+(1-x n)/2 := by
    have hh := ((p.summable_pgf (hx n).1 (hx n).2.le).hasSum.sub p.total).add (hm.hasSum.mul_left (1-x n))
    have hid (k) : p.mass k*(x n)^k-p.mass k+(1-x n)*(p.mass k*(k:ℝ))=
        (1-x n)^2*(p.mass k*triPrefix k (x n)) := by
      rw [show (1-x n)^2*(p.mass k*triPrefix k (x n))=
        p.mass k*((1-x n)^2*triPrefix k (x n)) by ring,triPrefix_mul]
      ring
    simp_rw [hid] at hh
    have hu := ((hts n).hasSum.mul_left ((1-x n)^2)).unique hh
    change (1-x n)^2*(∑' k,p.mass k*triPrefix k (x n))=p.pgf (x n)-1+(1-x n)*μ at hu
    rw [hμ] at hu
    simpa only [mul_one_div] using hu
  have hbtri (n) : (∑' k,p.mass k*triPrefix k (x n))≤2*C := by
    have hp0 := p.pgf_nonneg (hx n).1
    have hxn := (hx n).1
    have hxp : 0<1-x n := sub_pos.mpr (hx n).2
    have hs0 : 0≤∑' k,p.mass k*triPrefix k (x n) := tsum_nonneg (fun k => mul_nonneg (p.nonneg k) (triPrefix_nonneg k hxn))
    have hrem : 0≤p.pgf (x n)-1+(1-x n)/2 := by rw [← htri n]; positivity
    have htpos : 0<(1-x n)^2 := sq_pos_of_pos hxp
    have hmul : (p.pgf (x n)-1+(1-x n)/2)*(p.pgf (x n)+(1+x n)/2)=
      (p.pgf (x n))^2-x n-(1-x n)^2/4 := by ring
    have hhalf : 1/2≤p.pgf (x n)+(1+x n)/2 := by linarith
    have hbound := (hgap n).2
    have hrf : (p.pgf (x n)-1+(1-x n)/2)/2≤C*(1-x n)^2 := by nlinarith
    rw [← htri n] at hrf
    nlinarith
  have htriSum : Summable (fun k => p.mass k*triPrefix k 1) := by
    apply summable_of_sum_le (fun k => mul_nonneg (p.nonneg k) (triPrefix_nonneg k (by norm_num)))
    intro s
    apply le_of_tendsto (tendsto_finsetSum s (fun k _ =>
      tendsto_const_nhds.mul ((continuous_triPrefix k).tendsto 1 |>.comp ht)))
    exact Eventually.of_forall (fun n =>
      (Summable.sum_le_tsum s (fun k _ => mul_nonneg (p.nonneg k) (triPrefix_nonneg k (hx n).1))
        (hts n)).trans (hbtri n))
  constructor
  · have hm' : HasSum (fun k => p.mass k*(k:ℝ)) μ := hm.hasSum
    rw [hμ] at hm'
    simpa only [mul_comm] using hm'
  · apply (hm.add (htriSum.mul_left 2)).congr
    intro k
    rw [square_eq_triPrefix]
    ring

end FKCRT.BlockCritical
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.BlockCritical

lemma Weights.mass_le_one (p : Weights) (k : ℕ) : p.mass k≤1 := by
  rw [← p.total.tsum_eq]
  exact p.total.summable.le_tsum k (fun i _ => p.nonneg i)

def Weights.abelMean (p : Weights) (x : ℝ) : ℝ := ∑' k : ℕ,(k:ℝ)*p.mass k*x^k

lemma Weights.summable_abelMean (p : Weights) {x : ℝ} (hx : 0≤x) (hx' : x<1) :
    Summable (fun k : ℕ => (k:ℝ)*p.mass k*x^k) := by
  have hs : Summable (fun k : ℕ => (k:ℝ)*x^k) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1
      (by simpa only [Real.norm_eq_abs,abs_of_nonneg hx] using hx')
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (p.nonneg k)) (pow_nonneg hx k)) (fun k => ?_) hs
  nlinarith [mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hx k),p.mass_le_one k]

lemma geomPrefix_lower (k : ℕ) {x : ℝ} (hx : 0≤x) (hx' : x≤1) :
    (k:ℝ)*x^k≤geomPrefix k x := by
  calc
    (k:ℝ)*x^k = ∑ _i ∈ Finset.range k,x^k := by simp
    _ ≤ geomPrefix k x := Finset.sum_le_sum (fun i hi =>
      pow_le_pow_of_le_one hx hx' (Finset.mem_range.mp hi).le)

lemma Weights.abelMean_gap (p : Weights) {x : ℝ} (hx : 0≤x) (hx' : x<1) :
    (1-x)*p.abelMean x≤1-p.pgf x := by
  rw [← p.geom_identity hx hx']
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hx'.le)
  apply (p.summable_abelMean hx hx').tsum_le_tsum _ (p.summable_geom hx hx')
  intro k
  nlinarith [mul_le_mul_of_nonneg_left (geomPrefix_lower k hx hx'.le) (p.nonneg k)]

/-- Endpoint passage for nonnegative coefficients. This supplies the endpoint
normalization of Phi from the actual interior substitution equation; it does
not assume the desired probability normalization. -/
lemma hasSum_of_pgf_limit {b : ℕ → ℝ} (hb : ∀ k,0≤b k)
    {x t : ℕ → ℝ} (hx : ∀ n,0≤x n ∧ x n≤1)
    (hxt : Tendsto x atTop (𝓝 1)) (ht : Tendsto t atTop (𝓝 1))
    (heq : ∀ n,HasSum (fun k => b k*(x n)^k) (t n)) : HasSum b 1 := by
  have hf (s : Finset ℕ) : (∑ k ∈ s,b k)≤1 := by
    have hl : Tendsto (fun n => ∑ k ∈ s,b k*(x n)^k) atTop (𝓝 (∑ k ∈ s,b k)) := by
      simpa only [one_pow,mul_one] using tendsto_finsetSum s
        (fun k _ => tendsto_const_nhds.mul (hxt.pow k))
    apply le_of_tendsto_of_tendsto hl ht
    exact Eventually.of_forall (fun n => by
      rw [← (heq n).tsum_eq]
      exact Summable.sum_le_tsum s (fun k _ => mul_nonneg (hb k) (pow_nonneg (hx n).1 k)) (heq n).summable)
  have hs := summable_of_sum_le hb hf
  have hp : Tendsto (fun n => ∑' k,b k*(x n)^k) atTop (𝓝 (∑' k,b k)) := by
    have hh := tendsto_tsum_of_dominated_convergence hs
      (fun k => tendsto_const_nhds.mul (hxt.pow k))
      (Eventually.of_forall (fun n k => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hb k) (pow_nonneg (hx n).1 k))]
        exact mul_le_of_le_one_right (hb k) (pow_le_one₀ (hx n).1 (hx n).2)))
    simpa only [one_pow,mul_one] using hh
  have he : (fun n => ∑' k,b k*(x n)^k)=t := funext (fun n => (heq n).tsum_eq)
  rw [he] at hp
  exact tendsto_nhds_unique hp ht ▸ hs.hasSum

/-- Source block:critical in normalized variables. Only the original
nonnegative generating-function substitution and Abel lower bound are used.
The mean/variance conclusions are proved, not included as assumptions. -/
theorem normalized_inverse_critical (p : Weights) {b : ℕ → ℝ}
    (hb : ∀ k,0≤b k) {x : ℕ → ℝ} (hx : ∀ n,0≤x n ∧ x n<1)
    (ht : Tendsto x atTop (𝓝 1))
    (heq : ∀ n,HasSum (fun k => b k*(x n*(p.pgf (x n))^2)^k) (p.pgf (x n)))
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ n,c≤Real.sqrt (1-x n)*p.abelMean (x n)) :
    HasSum b 1 ∧ HasSum (fun k : ℕ => (k:ℝ)*b k) (1/2) ∧
      Summable (fun k : ℕ => (k:ℝ)^2*b k) := by
  let y := fun n => x n*(p.pgf (x n))^2
  have hpn (n) := p.pgf_nonneg (hx n).1
  have hpu (n) := p.pgf_le_one (hx n).1 (hx n).2.le
  have hyp (n) : 0≤y n ∧ y n<1 := by
    dsimp [y]
    have hp2 : (p.pgf (x n))^2≤1 := by nlinarith [hpn n,hpu n]
    constructor
    · exact mul_nonneg (hx n).1 (sq_nonneg _)
    · nlinarith [(hx n).1,(hx n).2]
  have hpt := p.tendsto_pgf (fun n => ⟨(hx n).1,(hx n).2.le⟩) ht
  have hyt : Tendsto y atTop (𝓝 1) := by
    simpa only [one_pow,mul_one] using ht.mul (hpt.pow 2)
  have hbtotal : HasSum b 1 := hasSum_of_pgf_limit hb
    (fun n => ⟨(hyp n).1,(hyp n).2.le⟩) hyt hpt heq
  let q : Weights := ⟨b,hb,hbtotal⟩
  have hq (n) : q.pgf (y n)=p.pgf (x n) := (heq n).tsum_eq
  have hgap (n) : c*Real.sqrt (1-x n)≤1-p.pgf (x n) := by
    have hgap := p.abelMean_gap (hx n).1 (hx n).2
    have hmul := mul_le_mul_of_nonneg_left (hlower n) (Real.sqrt_nonneg (1-x n))
    have hs := Real.sq_sqrt (sub_nonneg.mpr (hx n).2.le)
    rw [← mul_assoc,← sq,hs] at hmul
    linarith
  have hyl (n) : y n≤p.pgf (x n) := by
    dsimp [y]
    calc
      x n*(p.pgf (x n))^2≤(p.pgf (x n))^2 :=
        mul_le_of_le_one_left (sq_nonneg _) (hx n).2.le
      _ ≤ p.pgf (x n) := by nlinarith [hpn n,hpu n]
  have hquad (n) : 0≤(q.pgf (y n))^2-y n ∧
      (q.pgf (y n))^2-y n≤(1/c^2)*(1-y n)^2 := by
    rw [hq n]
    have hid : (p.pgf (x n))^2-y n=(1-x n)*(p.pgf (x n))^2 := by dsimp [y]; ring
    rw [hid]
    constructor
    · exact mul_nonneg (sub_nonneg.mpr (hx n).2.le) (sq_nonneg _)
    · have hg : c^2*(1-x n)≤(1-y n)^2 := by
        have h := hgap n
        have hs := Real.sq_sqrt (sub_nonneg.mpr (hx n).2.le)
        have hds : c*Real.sqrt (1-x n)≤1-y n := h.trans (by linarith [hyl n])
        have hnon := mul_nonneg hc.le (Real.sqrt_nonneg (1-x n))
        nlinarith [sq_nonneg (1-y n-c*Real.sqrt (1-x n))]
      have hp2 : (p.pgf (x n))^2≤1 := by nlinarith [hpn n,hpu n]
      have hle : (1-x n)*(p.pgf (x n))^2≤1-x n :=
        mul_le_of_le_one_right (sub_nonneg.mpr (hx n).2.le) hp2
      apply hle.trans
      rw [one_div,← div_eq_inv_mul]
      exact (le_div_iff₀ (sq_pos_of_pos hc)).2 (by nlinarith)
  exact ⟨hbtotal,q.moments_of_quadratic hyp hyt (by positivity) hquad⟩

end FKCRT.BlockCritical
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_BlockLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma rawWord_signSum (x : ℕ → Letter) (n : ℕ) :
    ((rawWord x n).map Letter.increment).sum=signSum x n := by
  simp only [rawWord,List.map_ofFn,List.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (fun i => (x i).increment) n
lemma rawWord_take {n j : ℕ} (h : j≤n) (x : ℕ → Letter) : (rawWord x n).take j=rawWord x j := by
  unfold rawWord
  rw [← Fin.ofFn_take_eq_take_ofFn h]
  rfl
lemma emptyProb_le_killed (P : Parameters) (n : ℕ) : emptyProb P n≤SimpleWalk.killed n 0 0 := by
  rw [← rawKilled_measure P 0 0 n]
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  obtain ⟨hz,hn⟩ := emptyReducing_dyck _ hx
  constructor
  · intro j hj
    have hh := hn j
    rw [rawWord_take hj,rawWord_signSum] at hh
    simpa only [Nat.cast_zero,zero_add] using hh
  · simpa only [rawWord_signSum,Nat.cast_zero,zero_add] using hz

/-- Finiteness of the endpoint inventory generating function follows from the
actual killed walk Green sum; no coefficient asymptotic is assumed. -/
theorem emptyProb_summable (P : Parameters) : Summable (emptyProb P) :=
  Summable.of_nonneg_of_le (emptyProb_nonneg P) (emptyProb_le_killed P) (SimpleWalk.killed_summable 0 0)
theorem emptyProb_even_summable (P : Parameters) : Summable (fun n => emptyProb P (2*n)) :=
  (emptyProb_summable P).comp_injective (by intro i j h; omega)
lemma emptyProb_zero (P : Parameters) : emptyProb P 0=1 := by
  have h : EmptyReducing ([] : List Letter) := rfl
  simp [emptyProb,rawWord,h]

def emptyTotal (P : Parameters) : ℝ := ∑' n,emptyProb P (2*n)
lemma emptyTotal_ge_one (P : Parameters) : 1≤emptyTotal P := by
  have h := (emptyProb_even_summable P).le_tsum 0 (fun n _ => emptyProb_nonneg P (2*n))
  change 1≤∑' n,emptyProb P (2*n)
  simpa only [mul_zero,emptyProb_zero] using h
lemma emptyTotal_pos (P : Parameters) : 0<emptyTotal P := lt_of_lt_of_le zero_lt_one (emptyTotal_ge_one P)

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm Filter
open scoped BigOperators ENNReal Topology
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

def flexParameter (P : Parameters) : ℝ := 1+2*P.p/(1-P.p)
def radiusParameter (P : Parameters) : ℝ := (1-P.p)/16

lemma flexParameter_pos (P : Parameters) : 0<flexParameter P := by
  have hp := P.lower
  have hu := P.upper
  dsimp [flexParameter]
  have h : 0<2*P.p/(1-P.p) := div_pos (by linarith) (by linarith)
  linarith

lemma radiusParameter_pos (P : Parameters) : 0 < radiusParameter P :=
  div_pos (sub_pos.mpr P.upper) (by norm_num)

def inventorySeries (P : Parameters) (x : ℝ) : ℝ := ∑' m,emptyProb P (2*m)*x^m

lemma inventorySeries_summable (P : Parameters) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    Summable (fun m => emptyProb P (2*m)*x^m) := by
  apply Summable.of_nonneg_of_le (fun m => mul_nonneg (emptyProb_nonneg P _) (pow_nonneg hx _))
    (fun m => mul_le_of_le_one_right (emptyProb_nonneg P _) (pow_le_one₀ hx hx'))
    (emptyProb_even_summable P)

lemma inventorySeries_nonneg (P : Parameters) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ inventorySeries P x := tsum_nonneg (fun _ => mul_nonneg (emptyProb_nonneg P _) (pow_nonneg hx _))

def coreCoefficientReal (t : ℝ) (m : ℕ) : ℝ :=
  ∑ w∈(typedEmptyWords (2*m)).filter CoreWord,t^flexibleCount w []

lemma coreCoefficientReal_nonneg {t : ℝ} (ht : 0 ≤ t) (m : ℕ) : 0 ≤ coreCoefficientReal t m :=
  Finset.sum_nonneg (fun _ _ => pow_nonneg ht _)

lemma coreCoefficient_ofReal {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    coreCoefficient (ENNReal.ofReal t) m=ENNReal.ofReal (coreCoefficientReal t m) := by
  rw [coreCoefficientReal,ENNReal.ofReal_sum_of_nonneg (fun _ _ => pow_nonneg ht _)]
  unfold coreCoefficient
  apply Finset.sum_congr rfl
  intro w _
  exact (ENNReal.ofReal_pow ht _).symm

lemma coreCoefficientReal_zero (t : ℝ) : coreCoefficientReal t 0=0 := by
  apply Finset.sum_eq_zero
  intro w hw
  obtain ⟨hw,hcore⟩ := Finset.mem_filter.mp hw
  have hl := mem_wordsOfLength.mp (Finset.mem_filter.mp hw).1
  have hp := coreWord_pos w hcore
  omega

end FKCRT.Inventory
end


noncomputable section
open Filter
open scoped BigOperators Topology
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

def blockCoefficientReal (t : ℝ) (m : ℕ) : ℝ :=
  (if m=0 then 1 else 0)+coreCoefficientReal t m

def actualBlockMass (P : Parameters) (m : ℕ) : ℝ :=
  blockCoefficientReal (flexParameter P) m*
    (radiusParameter P*(emptyTotal P)^2)^m/emptyTotal P

lemma blockCoefficientReal_nonneg {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    0 ≤ blockCoefficientReal t m := by
  apply add_nonneg _ (coreCoefficientReal_nonneg ht m)
  split_ifs <;> norm_num

lemma actualBlockMass_nonneg (P : Parameters) (m : ℕ) : 0 ≤ actualBlockMass P m :=
  div_nonneg (mul_nonneg (blockCoefficientReal_nonneg (flexParameter_pos P).le _)
    (pow_nonneg (mul_nonneg (radiusParameter_pos P).le (sq_nonneg _)) _))
    (emptyTotal_pos P).le

lemma actualBlockMass_zero (P : Parameters) : actualBlockMass P 0=1/emptyTotal P := by
  simp [actualBlockMass,blockCoefficientReal,coreCoefficientReal_zero]

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.BlockCritical

def doubleMass (b : ℕ → ℝ) (k : ℕ) : ℝ := if Even k then b (k/2) else 0

lemma doubleMass_even (b : ℕ → ℝ) (k : ℕ) : doubleMass b (2*k)=b k := by
  simp [doubleMass,even_two]

lemma doubleMass_outside (b : ℕ → ℝ) (k : ℕ) (hk : k ∉ Set.range (fun n : ℕ => 2*n)) :
    doubleMass b k=0 := by
  rw [doubleMass,ite_eq_right]
  rintro ⟨j,hj⟩
  exact hk ⟨j,by dsimp only; omega⟩

lemma doubleMass_nonneg {b : ℕ → ℝ} (hb : ∀ k,0≤b k) (k : ℕ) : 0≤doubleMass b k := by
  unfold doubleMass
  split_ifs
  · exact hb _
  · exact le_rfl

lemma hasSum_doubleMass {b : ℕ → ℝ} {a : ℝ} (h : HasSum b a) : HasSum (doubleMass b) a := by
  apply (Function.Injective.hasSum_iff (by intro i j hij; dsimp only at hij; omega : Function.Injective (fun k : ℕ => 2*k))
    (doubleMass_outside b)).1
  simpa only [Function.comp_def,doubleMass_even] using h

lemma hasSum_doubleMean {b : ℕ → ℝ} {a : ℝ} (h : HasSum (fun k : ℕ => (k:ℝ)*b k) a) :
    HasSum (fun k : ℕ => (k:ℝ)*doubleMass b k) (2*a) := by
  apply (Function.Injective.hasSum_iff (f := fun k : ℕ => (k:ℝ)*doubleMass b k)
    (by intro i j hij; dsimp only at hij; omega : Function.Injective (fun k : ℕ => 2*k))
    (fun k hk => by rw [doubleMass_outside b k hk,mul_zero])).1
  simpa only [Function.comp_def,doubleMass_even,Nat.cast_mul,Nat.cast_ofNat,mul_assoc] using h.mul_left 2

lemma summable_doubleSecond {b : ℕ → ℝ} (h : Summable (fun k : ℕ => (k:ℝ)^2*b k)) :
    Summable (fun k : ℕ => (k:ℝ)^2*doubleMass b k) := by
  apply (Function.Injective.summable_iff (f := fun k : ℕ => (k:ℝ)^2*doubleMass b k)
    (by intro i j hij; dsimp only at hij; omega : Function.Injective (fun k : ℕ => 2*k))
    (fun k hk => by rw [doubleMass_outside b k hk,mul_zero])).1
  refine (h.mul_left 4).congr (fun k => ?_)
  simp only [Function.comp_def,doubleMass_even,Nat.cast_mul,Nat.cast_ofNat]
  ring

/-- Doubling block edge counts gives exactly the corner offspring law.
The support span is two, and sizes in the tree theorem are all 2n+1. -/
def evenOffspring (b : Weights) (h₀ : 0<b.mass 0) (h₁ : 0<b.mass 1)
    (hm : HasSum (fun k : ℕ => (k:ℝ)*b.mass k) (1/2))
    (hs : Summable (fun k : ℕ => (k:ℝ)^2*b.mass k)) : TreeCoding.CriticalEvenOffspring where
  mass := doubleMass b.mass
  nonneg := doubleMass_nonneg b.nonneg
  total := hasSum_doubleMass b.total
  even_support k hk := by
    rw [doubleMass,ite_eq_right]
    exact Nat.not_even_iff_odd.mpr hk
  zero_pos := by simpa [doubleMass] using h₀
  two_pos := by simpa [doubleMass] using h₁
  mean := by simpa using hasSum_doubleMean hm
  second := summable_doubleSecond hs

end FKCRT.BlockCritical
end


noncomputable section
open List
open scoped BigOperators
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

namespace CoreLabel

def mass (t r τ : ℝ) : CoreLabel → ℝ
  | none => 1/τ
  | some c => wordMonomial t (r*τ) c.val/τ

end CoreLabel
end FKCRT.Inventory
end


noncomputable section
open List MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

/-- The actual connected-core contribution in each fixed edge-size fiber. -/
lemma coreMass_finite_sum (P : Parameters) (m : ℕ) :
    (∑ w∈(typedEmptyWords (2*m)).filter CoreWord,
      ENNReal.ofReal (wordMonomial (flexParameter P)
        (Real.sqrt (radiusParameter P)*emptyTotal P) w/emptyTotal P))=
    ENNReal.ofReal (coreCoefficientReal (flexParameter P) m*
      (radiusParameter P*(emptyTotal P)^2)^m/emptyTotal P) := by
  have hn : ∀ w∈(typedEmptyWords (2*m)).filter CoreWord,
      0≤wordMonomial (flexParameter P)
        (Real.sqrt (radiusParameter P)*emptyTotal P) w/emptyTotal P := by
    intro w _
    exact div_nonneg
      (mul_nonneg (pow_nonneg (flexParameter_pos P).le _) (pow_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (emptyTotal_pos P).le) _)) (emptyTotal_pos P).le
  rw [← ENNReal.ofReal_sum_of_nonneg hn]
  congr 1
  rw [← Finset.sum_div]
  congr 1
  rw [coreCoefficientReal,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  have hl := mem_wordsOfLength.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
  have hs : (Real.sqrt (radiusParameter P)*emptyTotal P)^(2*m)=
      (radiusParameter P*(emptyTotal P)^2)^m := by
    rw [pow_mul,mul_pow,Real.sq_sqrt (radiusParameter_pos P).le]
  rw [wordMonomial,hl,hs]

/-- Grouping is over genuine normalized connected cores, with no abstract
counting coefficients left in the summands. -/
lemma coreMass_by_size (P : Parameters) (F : ℕ→ℝ≥0∞) :
    (∑' c : Core,ENNReal.ofReal (wordMonomial (flexParameter P)
      (Real.sqrt (radiusParameter P)*emptyTotal P) c.val/emptyTotal P)*F c.val.length)=
    ∑' m : ℕ,ENNReal.ofReal (coreCoefficientReal (flexParameter P) m*
      (radiusParameter P*(emptyTotal P)^2)^m/emptyTotal P)*F (2*m) := by
  rw [core_tsum_by_size (fun w => ENNReal.ofReal (wordMonomial (flexParameter P)
    (Real.sqrt (radiusParameter P)*emptyTotal P) w/emptyTotal P)*F w.length)]
  apply tsum_congr
  intro m
  rw [← coreMass_finite_sum P m,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  have hl := mem_wordsOfLength.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
  rw [hl]

end FKCRT.Inventory
end


noncomputable section
open List MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

namespace CoreLabel

def rootMass (P : Parameters) (c : CoreLabel) : ℝ :=
  mass (flexParameter P) (Real.sqrt (radiusParameter P)) (emptyTotal P) c

lemma rootMass_by_size (P : Parameters) (F : ℕ→ℝ≥0∞) :
    (∑' c : CoreLabel,ENNReal.ofReal (rootMass P c)*F c.arity)=
      ∑' m : ℕ,ENNReal.ofReal (actualBlockMass P m)*F (2*m) := by
  have hs := (Equiv.optionEquivSumPUnit.{0} Core).symm.tsum_eq
    (fun c : CoreLabel => ENNReal.ofReal (rootMass P c)*F c.arity)
  rw [← hs,Summable.tsum_sum ENNReal.summable ENNReal.summable]
  simp only [Equiv.optionEquivSumPUnit_symm_inl,Equiv.optionEquivSumPUnit_symm_inr,
    rootMass,mass,arity,tsum_fintype,Fintype.univ_punit,Finset.sum_singleton]
  rw [coreMass_by_size]
  have hi (m : ℕ) : ENNReal.ofReal (actualBlockMass P m)=
      ENNReal.ofReal (coreCoefficientReal (flexParameter P) m*
        (radiusParameter P*(emptyTotal P)^2)^m/emptyTotal P)+
      (if m=0 then ENNReal.ofReal (1/emptyTotal P) else 0) := by
    by_cases hm : m=0
    · simp [hm,actualBlockMass_zero,coreCoefficientReal_zero]
    · simp [hm,actualBlockMass,blockCoefficientReal]
  simp_rw [hi,add_mul]
  rw [ENNReal.tsum_add]
  congr 1
  simp

end CoreLabel
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
open Set
namespace FKCRT.GraphMerge
variable {V : Type*} (G : SimpleGraph V)

lemma reachable_eq_of_adj_eq {C : Type*} (f : V→C)
    (h : ∀ u v,G.Adj u v → f u=f v) {u v : V} (hr : G.Reachable u v) : f u=f v := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons ha p ih => exact (h _ _ ha).trans ih

def componentEquiv {C : Type*} (f : V→C) (hf : Function.Surjective f)
    (he : ∀ u v,G.Reachable u v ↔ f u=f v) : G.ConnectedComponent ≃ C :=
  Equiv.ofBijective (Quot.lift f (fun u v h => (he u v).mp h)) ⟨by
    intro x y h
    refine SimpleGraph.ConnectedComponent.ind₂ (fun u v hh => ?_) x y h
    exact SimpleGraph.ConnectedComponent.sound ((he u v).mpr hh),by
    intro c
    obtain ⟨v,rfl⟩ := hf c
    exact ⟨G.connectedComponentMk v,rfl⟩⟩

/-- Adding one edge between distinct components merges precisely those two
components, including graphs with other isolated vertices. -/
lemma card_sup_edge_of_not_reachable [Finite V] {u v : V} (h : ¬G.Reachable u v) :
    Nat.card (G⊔SimpleGraph.edge u v).ConnectedComponent+1=Nat.card G.ConnectedComponent := by
  classical
  let cu := G.connectedComponentMk u
  let cv := G.connectedComponentMk v
  have hne : cu≠cv := fun hh => h (SimpleGraph.ConnectedComponent.eq.mp hh)
  let f : V → {c : G.ConnectedComponent // c≠cv} := fun x =>
    if hx : G.connectedComponentMk x=cv then ⟨cu,hne⟩ else ⟨G.connectedComponentMk x,hx⟩
  have hf (x : V) : (f x).val=if G.connectedComponentMk x=cv then cu else G.connectedComponentMk x := by
    simp only [f]
    split_ifs <;> rfl
  have hfu : (f u).val=cu := by rw [hf]; simp [cu,hne]
  have hfv : (f v).val=cu := by rw [hf]; simp [cv]
  have he : ∀ x y,(G⊔SimpleGraph.edge u v).Reachable x y ↔ f x=f y := by
    intro x y
    constructor
    · apply reachable_eq_of_adj_eq
      intro a b hab
      apply Subtype.ext
      rcases hab with hab | hab
      · have hh := SimpleGraph.ConnectedComponent.sound hab.reachable
        simp only [hf,hh]
      · rcases (SimpleGraph.edge_adj _ _ _ _).mp hab with ⟨⟨rfl,rfl⟩ | ⟨rfl,rfl⟩,hne'⟩
        · exact hfu.trans hfv.symm
        · exact hfv.trans hfu.symm
    · intro hh
      have hh' := congrArg Subtype.val hh
      simp only [hf] at hh'
      have hedge : (G⊔SimpleGraph.edge u v).Reachable u v := by
        exact (show (G⊔SimpleGraph.edge u v).Adj u v from Or.inr (by
          exact (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,fun huv => h (huv ▸ SimpleGraph.Reachable.refl u)⟩)).reachable
      by_cases hx : G.connectedComponentMk x=cv <;>
        by_cases hy : G.connectedComponentMk y=cv <;>
        simp only [hx,hy,ite_true,ite_false] at hh'
      · exact (SimpleGraph.ConnectedComponent.eq.mp (hx.trans hy.symm)).mono le_sup_left
      · have hxu : (G⊔SimpleGraph.edge u v).Reachable x v :=
          (SimpleGraph.ConnectedComponent.eq.mp hx).mono le_sup_left
        have huy : (G⊔SimpleGraph.edge u v).Reachable u y :=
          (SimpleGraph.ConnectedComponent.eq.mp hh').mono le_sup_left
        exact hxu.trans (hedge.symm.trans huy)
      · have hxu : (G⊔SimpleGraph.edge u v).Reachable x u :=
          (SimpleGraph.ConnectedComponent.eq.mp hh').mono le_sup_left
        have hvy : (G⊔SimpleGraph.edge u v).Reachable v y :=
          (SimpleGraph.ConnectedComponent.eq.mp hy.symm).mono le_sup_left
        exact hxu.trans (hedge.trans hvy)
      · exact (SimpleGraph.ConnectedComponent.eq.mp hh').mono le_sup_left
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨x,hx⟩ := Quot.mk_surjective c.val
    change G.connectedComponentMk x=c.val at hx
    refine ⟨x,Subtype.ext ?_⟩
    rw [hf,hx,ite_eq_right c.property]
  have hc := Nat.card_congr (componentEquiv _ f hsurj he)
  rw [hc]
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp only [Fintype.card_unique]
  have hp : 0 < Fintype.card G.ConnectedComponent := by
    exact Fintype.card_pos_iff.mpr ⟨cu⟩
  omega

end FKCRT.GraphMerge
end


noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

abbrev EdgeSelector (a : Perm (Dart n)) :=
  ∀ (_C R : Finset (Orbit a)), R.Nonempty → {e : Orbit a // e∈R}

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

lemma oneCycle_isCycleOn (p : Perm (Dart n)) (h : ∀ d e,p.SameCycle d e) :
    p.IsCycleOn (Finset.univ : Finset (Dart n)) :=
  ⟨by simp, fun _ _ _ _ => h _ _⟩

lemma oneCycle_numbering_bijective (p : Perm (Dart n)) (h : ∀ d e,p.SameCycle d e) :
    Function.Bijective (fun i : Dart n => (p^i.val) 0) := by
  have hh := oneCycle_isCycleOn p h
  constructor
  · intro i j hij
    have hm := (hh.pow_apply_eq_pow_apply (Finset.mem_univ (0 : Dart n))).mp hij
    have hm' : i.val % (2*(n+1)) = j.val % (2*(n+1)) := by
      simpa only [Finset.card_univ,Fintype.card_fin,Nat.ModEq] using hm
    rw [Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] at hm'
    exact Fin.ext hm'
  · intro d
    obtain ⟨k,hk,hkd⟩ := hh.exists_pow_eq (Finset.mem_univ (0 : Dart n)) (Finset.mem_univ d)
    refine ⟨⟨k,?_⟩,hkd⟩
    simpa only [Finset.card_univ,Fintype.card_fin] using hk

/-- Tour positions with initial position the original root dart. -/
def tourNumbering (p : Perm (Dart n)) (h : ∀ d e,p.SameCycle d e) : Perm (Dart n) :=
  Equiv.ofBijective _ (oneCycle_numbering_bijective p h)

@[simp] lemma tourNumbering_apply (p : Perm (Dart n)) (h : ∀ d e,p.SameCycle d e)
    (i : Dart n) : tourNumbering p h i = (p^i.val) 0 := rfl

@[simp] lemma tourNumbering_zero (p : Perm (Dart n)) (h : ∀ d e,p.SameCycle d e) :
    tourNumbering p h 0 = 0 := by simp

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

/-- Symmetric fundamental-cut incidence. For distinct edges of a planar tree
tour this is precisely alternation of their two darts. -/
def FundamentalCross (a s : Perm (Dart n)) (T : Finset (Orbit a)) (e f : Orbit a) : Prop :=
  (e∈T ∧ ¬(spanningGraph a s ((T.erase e : Finset (Orbit a)) : Set (Orbit a))).Reachable
      (orbit s f.out) (orbit s (a f.out))) ∨
  (f∈T ∧ ¬(spanningGraph a s ((T.erase f : Finset (Orbit a)) : Set (Orbit a))).Reachable
      (orbit s e.out) (orbit s (a e.out)))

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
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

def relabelPerm (r p : Perm (Dart n)) : Perm (Dart n) := r⁻¹*p*r

def relabelOrbit (r p : Perm (Dart n)) : Orbit (relabelPerm r p) ≃ Orbit p :=
  Quotient.congr r (by
    intro d e
    change (r⁻¹*p*r).SameCycle d e ↔ p.SameCycle (r d) (r e)
    simpa only [inv_inv] using (sameCycle_conj (g := r⁻¹) (f := p) (x := d) (y := e)))

@[simp] lemma relabelOrbit_apply (r p : Perm (Dart n)) (d : Dart n) :
    relabelOrbit r p (orbit (relabelPerm r p) d)=orbit p (r d) := rfl

def relabelEdges (r a : Perm (Dart n)) (A : Finset (Orbit a)) : Finset (Orbit (relabelPerm r a)) :=
  A.map (relabelOrbit r a).symm.toEmbedding

@[simp] lemma mem_relabelEdges (r a : Perm (Dart n)) (A : Finset (Orbit a))
    (e : Orbit (relabelPerm r a)) : e∈relabelEdges r a A ↔ relabelOrbit r a e∈A := by
  simp [relabelEdges]

@[simp] lemma card_relabelEdges (r a : Perm (Dart n)) (A : Finset (Orbit a)) :
    (relabelEdges r a A).card=A.card := Finset.card_map _

end FKCRT
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
open MapCycles Chords Inventory
variable {n : ℕ}

lemma canonical_tour_maximal (M : LabelledMap n) (T : Finset (Orbit M.val.1))
    (ht : M.val.2*partialReversal M.val.1 M.property.1 T=(List.finRange (2*(n+1))).formPerm) :
    Nat.card (Orbit (partialReversal M.val.1 M.property.1 T*(List.finRange (2*(n+1))).formPerm))=
      Nat.card (Orbit (List.finRange (2*(n+1))).formPerm)+T.card ∧
    Nat.card (Orbit (partialReversal M.val.1 M.property.1 Tᶜ*(List.finRange (2*(n+1))).formPerm))=
      Nat.card (Orbit (List.finRange (2*(n+1))).formPerm)+Tᶜ.card := by
  let a := M.val.1
  let s := M.val.2
  let t := s*partialReversal a M.property.1 T
  have hp : ∀ d e,t.SameCycle d e := by
    rw [show t=(List.finRange (2*(n+1))).formPerm from ht]
    intro d e
    exact sameCycle_of_list _ (List.nodup_finRange _) (fun _ _ => rfl) (List.mem_finRange d) (List.mem_finRange e)
  have hct : Nat.card (Orbit t)=1 := (card_orbit_eq_one_iff _).mpr hp
  constructor
  · rw [← ht,card_orbit_mul_comm,reconstructed_tour,hct]
    exact (tour_edge_card M T hp).trans (Nat.add_comm _ _)
  · rw [← ht,card_orbit_mul_comm,hct]
    have hc := planar_tour_compl_card M T hp
    have hface := reconstructed_face a t M.property.1 T
    have hrec : t*partialReversal a M.property.1 T=s := reconstructed_tour a s M.property.1 T
    rw [hrec] at hface
    rw [← hface]
    exact hc.trans (Nat.add_comm _ _)

end FKCRT
end


noncomputable section
open List Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
open MapCycles Inventory
variable {n : ℕ}

/-- Literal rooted-tour normal form, not a map with an assumed word inverse. -/
structure CanonicalTreeMap (n : ℕ) where
  a : Perm (Dart n)
  s : Perm (Dart n)
  A : Finset (Orbit a)
  valid : MapConditions (a,s)
  tour : s*partialReversal a valid.1 A=(List.finRange (2*(n+1))).formPerm

abbrev SuccessfulWord (n : ℕ) := {w : Dart n→TypedLetter //
  stackTypedRun ((List.finRange (2*(n+1))).map w) []=some []}

def CanonicalTreeMap.word (X : CanonicalTreeMap n) : SuccessfulWord n :=
  ⟨matchingWord X.a X.A,by
    have hh := canonical_tour_maximal ⟨(X.a,X.s),X.valid⟩ X.A X.tour
    exact (maximal_matching_word X.a X.valid.1 X.valid.2.1 X.A hh.1 hh.2).1⟩

lemma matchingWord_color (a : Perm (Dart n)) (A : Finset (Orbit a)) (i : Dart n) :
    (matchingWord a A i).color=decide (orbit a i∈A) := by
  unfold matchingWord
  split_ifs <;> rfl

lemma matchingWord_set_injective (a : Perm (Dart n)) :
    Function.Injective (matchingWord a) := by
  intro A B h
  apply Finset.ext
  intro e
  induction e using Quotient.inductionOn with
  | _ i =>
    have hh := congrArg (fun w => (w i).color) h
    change orbit a i∈A ↔ orbit a i∈B
    simpa only [matchingWord_color,decide_eq_decide] using hh

lemma CanonicalTreeMap.word_injective : Function.Injective (@CanonicalTreeMap.word n) := by
  intro X Y h
  have hw : matchingWord X.a X.A=matchingWord Y.a Y.A := congrArg Subtype.val h
  have hX := canonical_tour_maximal ⟨(X.a,X.s),X.valid⟩ X.A X.tour
  have hY := canonical_tour_maximal ⟨(Y.a,Y.s),Y.valid⟩ Y.A Y.tour
  obtain ⟨_,E,F,he,hf,hc,htE,htF,ha,hp⟩ :=
    maximal_matching_word X.a X.valid.1 X.valid.2.1 X.A hX.1 hX.2
  obtain ⟨_,E',F',he',hf',hc',htE',htF',ha',hp'⟩ :=
    maximal_matching_word Y.a Y.valid.1 Y.valid.2.1 Y.A hY.1 hY.2
  rw [← hw] at htE' htF'
  have hu := typed_map_unique (matchingWord X.a X.A) _ (List.nodup_finRange _) E F E' F'
    he hf he' hf' hc hc' htE htF htE' htF'
  have haeq : X.a=Y.a := ha.symm.trans (hu.1.trans ha')
  cases X with
  | mk a s A hv ht =>
    cases Y with
    | mk a' s' A' hv' ht' =>
      dsimp only at haeq hw
      subst a'
      have hA : A=A' := matchingWord_set_injective a hw
      subst A'
      have hs : s=s' := mul_right_cancel (ht.trans ht'.symm)
      subst s'
      rfl

lemma matchingWord_of_matchings (w : Dart n→TypedLetter)
    (E F : List (Dart n×Dart n))
    (hE : Arches (List.finRange (2*(n+1))) E)
    (hF : Arches (List.finRange (2*(n+1))) F)
    (hc : (endpoints (E++F)).Perm (List.finRange (2*(n+1))))
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false) :
    matchingWord (turns (E++F)) (matchingEdges E F)=w := by
  have hn : (endpoints (E++F)).Nodup := hc.nodup_iff.mpr (List.nodup_finRange _)
  have hdis : List.Disjoint (endpoints E) (endpoints F) := by
    rw [endpoints_append,List.nodup_append] at hn
    exact fun d hd hd' => hn.2.2 d hd d hd' rfl
  funext i
  obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp (hc.mem_iff.mpr (List.mem_finRange i))
  · simp only [matchingWord,(turns_pair hn e he).1,mem_matchingEdges E F hn]
    rcases List.mem_append.mp he with he|he
    · rw [ite_eq_left (hE.increasing (List.pairwise_lt_finRange _) e he),
        decide_eq_true (mem_endpoints.mpr ⟨e,he,Or.inl rfl⟩), (htE e he).1]
    · rw [ite_eq_left (hF.increasing (List.pairwise_lt_finRange _) e he),
        decide_eq_false (fun hx => hdis hx (mem_endpoints.mpr ⟨e,he,Or.inl rfl⟩)),(htF e he).1]
  · simp only [matchingWord,(turns_pair hn e he).2,mem_matchingEdges E F hn]
    rcases List.mem_append.mp he with he|he
    · rw [ite_eq_right (not_lt_of_ge (hE.increasing (List.pairwise_lt_finRange _) e he).le),
        decide_eq_true (mem_endpoints.mpr ⟨e,he,Or.inr rfl⟩),(htE e he).2]
    · rw [ite_eq_right (not_lt_of_ge (hF.increasing (List.pairwise_lt_finRange _) e he).le),
        decide_eq_false (fun hx => hdis hx (mem_endpoints.mpr ⟨e,he,Or.inr rfl⟩)),(htF e he).2]

lemma CanonicalTreeMap.word_surjective : Function.Surjective (@CanonicalTreeMap.word n) := by
  intro w
  obtain ⟨E,F,hE,hF,hc,htE,htF⟩ := identified_matchings w.val w.property
  have hv := matching_map_conditions E F hE hF hc
  have hn : (endpoints (E++F)).Nodup := hc.nodup_iff.mpr (List.nodup_finRange _)
  have ht : ((List.finRange (2*(n+1))).formPerm*turns E)*
      partialReversal (turns (E++F)) hv.1 (matchingEdges E F)=
      (List.finRange (2*(n+1))).formPerm := by
    rw [partialReversal_matchingEdges E F hn,mul_assoc,
      turns_self (by rw [endpoints_append] at hn; exact hn.of_append_left),mul_one]
  refine ⟨⟨_,_,_,hv,ht⟩,Subtype.ext ?_⟩
  exact matchingWord_of_matchings w.val E F hE hF hc htE htF

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
open List MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable
namespace CoreLabel

instance instMeasurableSpace : MeasurableSpace CoreLabel := ⊤
instance instMeasurableSingletonClass : MeasurableSingletonClass CoreLabel := ⟨fun _ => trivial⟩

end CoreLabel
end FKCRT.Inventory
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

namespace Core

def matching (c : Core) : StackMatching c.val.get (List.finRange c.val.length) :=
  StackMatching.ofEmpty (by
    rw [List.map_get_finRange]
    exact coreWord_empty _ c.property)

def rotation (c : Core) : Perm (Fin c.val.length) :=
  (List.finRange c.val.length).formPerm*turns c.matching.first

def graph (c : Core) : SimpleGraph (PermutationWedge.Vertex c.rotation) :=
  dartGraph c.matching.mate c.rotation

instance instFintypeVertexFinLengthTypedLetterValListCoreWordRotation (c : Core) : Fintype (PermutationWedge.Vertex c.rotation) := Fintype.ofFinite _

def entry (c : Core) : Fin c.val.length := ⟨0,coreWord_pos _ c.property⟩

/-- Entry-to-child-corner distance in the actual isolated core map. -/
def increment (c : Core) (j : Fin c.val.length) : ℕ :=
  c.graph.dist (vertex c.rotation c.entry)
    (vertex c.rotation ((List.finRange c.val.length).formPerm j))

end Core

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

lemma sameCycle_intertwine (a b r : Perm (Dart n))
    (hh : ∀ d,b (r d)=r (a d)) (d e : Dart n) :
    a.SameCycle d e ↔ b.SameCycle (r d) (r e) := by
  have hp (k : ℕ) (x : Dart n) : (b^k) (r x)=r ((a^k) x) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ',pow_succ',mul_apply,mul_apply,ih,hh]
  constructor
  · intro h
    obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
    refine ⟨(k:ℤ),?_⟩
    simp only [zpow_natCast,hp,hk]
  · intro h
    obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
    refine ⟨(k:ℤ),?_⟩
    rw [zpow_natCast]
    apply r.injective
    rwa [← hp]

def isoOrbit (a b r : Perm (Dart n)) (hh : ∀ d,b (r d)=r (a d)) : Orbit a ≃ Orbit b :=
  Quotient.congr r (sameCycle_intertwine a b r hh)

@[simp] lemma isoOrbit_apply (a b r : Perm (Dart n)) (hh : ∀ d,b (r d)=r (a d)) (d : Dart n) :
    isoOrbit a b r hh (orbit a d)=orbit b (r d) := rfl

def CanonicalTreeMap.toMap (X : CanonicalTreeMap n) : LabelledMap n :=
  ⟨(X.a,X.s),X.valid⟩

lemma CanonicalTreeMap.tour_connected (X : CanonicalTreeMap n) :
    ∀ d e,(X.s*partialReversal X.a X.valid.1 X.A).SameCycle d e := by
  rw [X.tour]
  intro d e
  exact MapCycles.sameCycle_of_list _ (List.nodup_finRange _) (fun _ _ => rfl)
    (List.mem_finRange d) (List.mem_finRange e)

end FKCRT
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_NodeMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

namespace Core

def realDistance (c : Core) (i j : Fin c.val.length) : ℝ :=
  c.graph.dist (vertex c.rotation i) (vertex c.rotation j)

end Core
end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MetricLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open FKCRT.TreeCoding

abbrev ActualDraw (n : ℕ) := Code (2*(n+1)+1) × (Fin (2*(n+1)+1) → CoreLabel)

end FKCRT.Inventory
end


end OAI
end


