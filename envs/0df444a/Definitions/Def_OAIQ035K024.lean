-- Prove2me | Definitions.Def_OAIQ035K024
-- name    : OAIQ035K024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:57:39.573983+00:00
-- url     : https://prove2.me/theorems/abc35b7d-6ec9-46f2-a8fa-ff75c2851696
-- title:
--   Definitions bundle OAIQ035K024 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 68 declarations of OpenAI's Lean: 31 definitions, 3 inductive types or structures and 34 theorems. The definitions and types are `OAI.MetricKMedian.LPBinary.Dual.affine`, `OAI.MetricKMedian.LPBinary.Dual.best`, `OAI.MetricKMedian.LPBinary.Dual.candidates`, `OAI.MetricKMedian.LPBinary.Dual.value`, `OAI.MetricKMedian.LPBinary.Repair.dominated`, `OAI.MetricKMedian.LPBinary.Repair.dot`, `OAI.MetricKMedian.LPBinary.Scale.argmin`, `OAI.MetricKMedian.LPBinary.level`, `OAI.MetricKMedian.LPBinary.maximum`, `OAI.MetricKMedian.LPBinary.project`, `OAI.MetricKMedian.LPBinary.selectMinimum`, `OAI.MetricKMedian.LPBinary.threshold`, `OAI.MetricKMedian.LPBinary.thresholds`, `OAI.MetricKMedian.LPBinary.upper`, `OAI.MetricKMedian.PhysicalBatchLaw.balanced`, `OAI.MetricKMedian.Preparation.FractionalRefinement.Program.Input`, `OAI.MetricKMedian.Preparation.FractionalRefinement.Program.Input.raw`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.Input.start`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.Input.state`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.State.step`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.advance`, `OAI.MetricKMedian.Preparation.RationalSplitting.Program.view`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.Input`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.Input`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.Input.unit`, `OAI.MetricKMedian.Preparation.SupplierStars.flag`, `OAI.MetricKMedian.RoundingProgram.Terminal.BInput`, `OAI.MetricKMedian.ScalarTransfer.c`, `OAI.MetricKMedian.SparseOuterLaw.activation`, `OAI.MetricKMedian.SparsePrepared.Program.Input.outer`, `OAI.MetricKMedian.SparsePrepared.Program.KernelInput.bundles`, `OAI.MetricKMedian.SparseStarActivation.Program.Input.column`, `OAI.MetricKMedian.SparseStarActivation.Program.Input.columns`, `OAI.MetricKMedian.TruncatedLP.rateDen`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Analysis_ScalarTransfer`, `KMedian_Geometry_NearestFillingFormula`, `KMedian_Instance`, `KMedian_Optimization_DualListOperations`, `KMedian_Optimization_FractionalInputProgram`, `KMedian_Optimization_FractionalListChecks`, `KMedian_Optimization_FractionalSelectProgram`, `KMedian_Optimization_GradientDenominator`, `KMedian_Optimization_LPMinimumSelection`, `KMedian_Optimization_OptimizationBitBound`, `KMedian_Optimization_SimplexListProgram`, `KMedian_Optimization_SubgradientDenominator`, `KMedian_Preparation_PreparationStars`, `KMedian_Preparation_PreparedKernelProgram`, `KMedian_Preparation_PreparedLawProgram`, `KMedian_Preparation_RationalSupplierPreparation`, `KMedian_Preparation_RepresentativeProgram`, `KMedian_Preparation_SupplierListOperations`, `KMedian_Preparation_SupplierPreparationProgram`, `KMedian_Process_CountRunHeight`, `KMedian_Process_PhysicalBatchLaw`, `KMedian_Programs_NearestListProgram`, `KMedian_Programs_SplitListProgram`, `KMedian_Programs_StarActivationProgram`, `KMedian_Programs_UnitRepresentativeProgram`, `KMedian_Programs_UnitScanProgram`, `KMedian_Rounding_GridRoundingProgram`, `KMedian_Rounding_IntegerSimplexProjection`, `KMedian_Rounding_SignedTerminalProgram`, `KMedian_Sparse_SparseOuterCounts`, `KMedian_Sparse_SparseOuterLaw`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K000`, `OAIQ035K001`, `OAIQ035K002`, `OAIQ035K003`, `OAIQ035K004`, `OAIQ035K005`, `OAIQ035K006`, `OAIQ035K007`, `OAIQ035K008`, `OAIQ035K009`, `OAIQ035K010` and `OAIQ035K011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K034`, `OAIQ035K035`, `OAIQ035K036` and `OAIQ035K044`; the statement `OAI.MetricKMedian.Preparation.supplier_assignments`; the proofs of `OAI.MetricKMedian.Preparation.supplier_assignments`, `OAI.MetricKMedian.Reduction.CloseCenters.complete_of_choices` and `OAI.MetricKMedian.Reduction.Serving.bad_count`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K001
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K003
import Definitions.Def_OAIQ035K004
import Definitions.Def_OAIQ035K005
import Definitions.Def_OAIQ035K006
import Definitions.Def_OAIQ035K007
import Definitions.Def_OAIQ035K008
import Definitions.Def_OAIQ035K009
import Definitions.Def_OAIQ035K010
import Definitions.Def_OAIQ035K011

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_ScalarTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

noncomputable def c (p : ℝ) (s : Bool) : ℝ := 1-bit s*p

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPMinimumSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

variable {α : Type}
def selectMinimum (d : α → ℚ) (as : List α) (a0 : α) : α :=
  (as.filter (fun a => decide (d a=minimum (as.map d)))).head?.getD a0

 theorem selectMinimum_ofFn {n : ℕ} [NeZero n] (f : Fin n → α) (d : α → ℚ) (a0 : α) :
    selectMinimum d (List.ofFn f) a0=
      f (Preparation.firstNearest univ (fun i => d (f i)) univ_nonempty) := by
  let a := Preparation.firstNearest univ (fun i => d (f i)) univ_nonempty
  have hval : minimum ((List.ofFn f).map d)=d (f a) := by
    apply Eq.trans _ (firstNearest_value univ (fun i => d (f i)) univ_nonempty).symm
    apply minimum_eq_finset
    intro q
    simp only [List.mem_map,List.mem_ofFn,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨x,⟨i,rfl⟩,h⟩
      exact ⟨i,h⟩
    · rintro ⟨i,h⟩
      exact ⟨f i,⟨i,rfl⟩,h⟩
  have hfind : (List.ofFn f).find? (fun x => decide (d x=minimum ((List.ofFn f).map d)))=some (f a) := by
    apply List.find?_ofFn_eq_some.mpr
    refine ⟨by rw [hval]; simp, a,rfl,?_⟩
    intro j hj hp
    have he : d (f j)=d (f a) := by simpa only [decide_eq_true_eq,hval] using hp
    have hh := firstNearest_le univ (fun i => d (f i)) univ_nonempty j (mem_univ j) he
    exact (not_le_of_gt hj) hh
  unfold selectMinimum
  rw [List.head?_filter,hfind]
  rfl

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_NearestFillingFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation
open Finset
variable {n : ℕ}

theorem first_before (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty)
    (i : Fin n) (hi : i∈U) (hne : i≠firstNearest U d hU) : before d (firstNearest U d hU) i := by
  have hd := (firstNearest_spec U d hU).2 i hi
  rcases hd.lt_or_eq with h|h
  · exact Or.inl h
  · exact Or.inr ⟨h,lt_of_le_of_ne (LPBinary.firstNearest_le U d hU i hi h.symm) hne.symm⟩

theorem not_before_first (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty)
    (i : Fin n) (hi : i∈U) : ¬before d i (firstNearest U d hU) := by
  rintro (h|⟨h,hi'⟩)
  · exact (not_lt_of_ge ((firstNearest_spec U d hU).2 i hi)) h
  · exact (not_lt_of_ge (LPBinary.firstNearest_le U d hU i hi h)) hi'

theorem priorMass_first (U : Finset (Fin n)) (y d : Fin n → ℚ) (hU : U.Nonempty) :
    priorMass U y d (firstNearest U d hU)=0 := by
  apply sum_eq_zero
  intro j hj
  exact (not_before_first U d hU j (mem_filter.mp hj).1 (mem_filter.mp hj).2).elim

end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Instance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Instance

theorem nearest_le (I : Instance) (j : Fin I.n) {S : Finset (Fin I.n)}
    {i : Fin I.n} (hi : i ∈ S) : nearest I j S ≤ (I.distance j i:ℝ) := by
  rw [nearest,dite_eq_left (show S.Nonempty from ⟨i,hi⟩)]
  exact min'_le _ _ (mem_image_of_mem _ hi)

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_DualListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

def maximum (xs : Row) : ℚ := xs.foldl max (xs.head?.getD 0)

 theorem maximum_eq_finset (xs : Row) (U : Finset ℚ) (hU : U.Nonempty)
    (hm : ∀ q, q∈xs ↔ q∈U) : maximum xs=U.max' hU := by
  have hne : xs≠[] := by
    intro he
    obtain ⟨q,hq⟩ := hU
    have hx := (hm q).mpr hq
    rw [he] at hx
    cases hx
  have hd : xs.head?.getD 0∈xs := by
    cases xs with
    | nil => contradiction
    | cons a xs => exact List.mem_cons_self
  apply foldl_max_eq
  · exact le_max' U _ ((hm _).mp hd)
  · exact (hm _).mpr (max'_mem U hU)
  · intro q hq
    exact le_max' U q ((hm q).mp hq)

namespace Dual

def candidates (ds : Row) (H : ℚ) : Row := 0::H::ds
def affine (ds ys : Row) (t : ℚ) : ℚ := t-((ds.zip ys).map (fun q => q.2*max 0 (t-q.1))).sum
def value (ds ys : Row) (H : ℚ) : ℚ := maximum ((candidates ds H).map (affine ds ys))
def best (ds ys : Row) (H : ℚ) : ℚ :=
  maximum ((candidates ds H).filter (fun t => decide (affine ds ys t=value ds ys H)))

 theorem affine_ofFn {n : ℕ} (d y : Fin n → ℚ) (t : ℚ) :
    affine (List.ofFn d) (List.ofFn y) t=FractionalDual.affine d y t := by
  simp only [affine,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,List.sum_ofFn,FractionalDual.affine]
  rfl

 theorem mem_candidates {n : ℕ} (d : Fin n → ℚ) (H q : ℚ) :
    q∈candidates (List.ofFn d) H ↔ q∈FractionalDual.thresholds d H := by
  simp only [candidates,List.mem_cons,List.mem_ofFn,FractionalDual.thresholds,mem_insert,mem_image,mem_univ,true_and]

end Dual
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_GradientDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalGrid
open Finset

theorem neg {D : ℤ} {a : ℚ} (ha : At D a) : At D (-a) := by
  obtain ⟨A,rfl⟩ := ha
  exact ⟨-A,by rw [Int.cast_neg]; ring⟩

theorem max {D : ℤ} {a b : ℚ} (ha : At D a) (hb : At D b) : At D (max a b) := by
  rcases le_total a b with h | h
  · simpa only [max_eq_right h] using hb
  · simpa only [max_eq_left h] using ha

theorem sum {ι : Type} (U : Finset ι) (f : ι → ℚ) (D : ℤ)
    (h : ∀ i ∈ U, At D (f i)) : At D (∑ i ∈ U, f i) := by
  classical
  choose A hA using (fun i : U => h i.val i.property)
  refine ⟨∑ i : U, A i,?_⟩
  rw [Int.cast_sum,sum_div]
  simp_rw [← hA]
  exact (sum_coe_sort U f).symm

end MetricKMedian.RationalGrid

namespace MetricKMedian.TruncatedLP
open Finset RationalGrid
variable {ι κ : Type} [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in
theorem truncated_grid (d : κ → ι → ℚ) (D H : ℤ) (hD : D ≠ 0)
    (hd : ∀ j i, At D (d j i)) (j : κ) (i : ι) : At D (truncated d H j i) := by
  unfold truncated
  split_ifs
  · exact hd j i
  · exact RationalGrid.integer D H hD

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_IntegerSimplexProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Simplex
open Finset
variable {n : ℕ} [NeZero n]

theorem project_integer_denominator (x : Fin n → ℚ) (X : Fin n → ℤ) (D k : ℤ)
    (hD : 0 < D) (hx : ∀ i, x i=(X i:ℚ)/(D:ℚ)) :
    ∃ (D' : ℤ) (Y : Fin n → ℤ), 0 < D' ∧ D' ≤ D*(n:ℤ) ∧
      ∀ i, project x (k:ℚ) i=(Y i:ℚ)/(D':ℚ) := by
  obtain ⟨a,ha⟩ := level_attained x (k:ℚ)
  let M : ℤ := (upper x a).card
  let c : ℤ := (∑ i ∈ upper x a, X i)-k*D
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast upper_card_pos x a
  have hDq : (0:ℚ) < D := by exact_mod_cast hD
  have hMq : (0:ℚ) < M := by exact_mod_cast hM
  have hlevel : level x (k:ℚ)=(c:ℚ)/((D*M:ℤ):ℚ) := by
    rw [ha,threshold]
    simp_rw [hx]
    rw [← sum_div]
    change ((∑ i ∈ upper x a, (X i:ℚ))/(D:ℚ)-(k:ℚ))/(M:ℚ)=_
    simp only [c,Int.cast_sub,Int.cast_sum,Int.cast_mul]
    field_simp
  refine ⟨D*M,fun i => max 0 (X i*M-c),mul_pos hD hM,?_,?_⟩
  · have hc : M ≤ (n:ℤ) := by
      dsimp [M]
      exact_mod_cast ((card_le_univ (upper x a)).trans_eq (Fintype.card_fin n))
    exact mul_le_mul_of_nonneg_left hc hD.le
  · intro i
    unfold project
    rw [hx,hlevel,Int.cast_max,Int.cast_zero]
    rw [Int.cast_mul D M,Int.cast_sub (X i*M) c,Int.cast_mul (X i) M]
    have he : (X i:ℚ)/(D:ℚ)-(c:ℚ)/((D:ℚ)*(M:ℚ))=
        ((X i:ℚ)*(M:ℚ)-(c:ℚ))/((D:ℚ)*(M:ℚ)) := by
      field_simp
    rw [he,← max_div_div_right (mul_pos hDq hMq).le,zero_div]

end MetricKMedian.Simplex
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_SubgradientDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ProjectedSubgradient
open Finset
variable {n : ℕ} [NeZero n]

theorem next_denominator (k b R Q : ℤ) (hb : 0 < b) (hR : 0 < R) (hQ : 0 < Q)
    (g : (Fin n → ℚ) → Fin n → ℚ) (v : Vector ℚ n)
    (hv : ∀ i, RationalGrid.At Q (point v i))
    (hg : ∀ i, RationalGrid.At R (g (point v) i)) :
    ∃ Q' : ℤ, 0 < Q' ∧ Q' ≤ Q*(b*R*(n:ℤ)) ∧
      ∀ i, RationalGrid.At Q' (point (next (k:ℚ) (1/(b:ℚ)) g v) i) := by
  choose Y hY using hv
  choose G hG using hg
  let X : Fin n → ℤ := fun i => Y i*(b*R)-G i*Q
  have hQi : Q*b*R > 0 := mul_pos (mul_pos hQ hb) hR
  have hX : ∀ i, point v i-(1/(b:ℚ))*g (point v) i=(X i:ℚ)/((Q*b*R:ℤ):ℚ) := by
    intro i
    rw [hY,hG]
    simp only [X,Int.cast_sub,Int.cast_mul]
    have hq : (Q:ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
    have hbq : (b:ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hrq : (R:ℚ) ≠ 0 := by exact_mod_cast hR.ne'
    field_simp
  obtain ⟨Q',Y',hpos,hbound,hval⟩ := Simplex.project_integer_denominator
    (fun i => point v i-(1/(b:ℚ))*g (point v) i) X (Q*b*R) k hQi hX
  refine ⟨Q',hpos,by nlinarith [hbound],fun i => ⟨Y' i,?_⟩⟩
  rw [next_apply,hval]

theorem trajectory_denominator (k b R : ℤ) (hb : 0 < b) (hR : 0 < R)
    (g : (Fin n → ℚ) → Fin n → ℚ)
    (hg : ∀ y i, RationalGrid.At R (g y i)) (t : ℕ) :
    ∃ Q : ℤ, 0 < Q ∧ Q ≤ (b*R*(n:ℤ))^t ∧
      ∀ i, RationalGrid.At Q (point (trajectory (k:ℚ) (1/(b:ℚ)) g (initial (k:ℚ)) t) i) := by
  induction t with
  | zero =>
    refine ⟨1,by norm_num,by norm_num,?_⟩
    intro i
    simp only [trajectory_zero,initial,point_ofFn_apply]
    split_ifs
    · exact RationalGrid.integer 1 k (by norm_num)
    · exact RationalGrid.zero 1
  | succ t ih =>
    obtain ⟨Q,hQ,hbound,hv⟩ := ih
    obtain ⟨Q',hQ',hbound',hv'⟩ := next_denominator k b R Q hb hR hQ g _ hv (hg _)
    refine ⟨Q',hQ',hbound'.trans ?_,hv'⟩
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right hbound (by positivity)

end MetricKMedian.ProjectedSubgradient
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_OptimizationBitBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset ProjectedSubgradient
variable {n m : ℕ} [NeZero n] [NeZero m]

def rateDen (r H : ℕ) : ℤ := 2*(r:ℤ)*(gradSize (n:=n) (m:=m) H:ℤ)

theorem rateDen_pos (r H : ℕ) (hr : 0 < r) (hH : 0 < H) :
    0 < rateDen (n:=n) (m:=m) r H := by
  unfold rateDen
  have hg := gradSize_pos (n:=n) (m:=m) H hH
  have hri : (0:ℤ) < r := by exact_mod_cast hr
  have hgi : (0:ℤ) < gradSize (n:=n) (m:=m) H := by exact_mod_cast hg
  positivity

omit [NeZero n] [NeZero m] in
theorem rate_eq (r H : ℕ) : rate (n:=n) (m:=m) r H=
    1/(rateDen (n:=n) (m:=m) r H:ℚ) := by
  simp only [rate,rateDen,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_SimplexListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

def upper (xs : Row) (a : ℚ) : Row := xs.filter (fun q => decide (a≤q))
def threshold (xs : Row) (k a : ℚ) : ℚ := ((upper xs a).sum-k)/(upper xs a).length
def thresholds (xs : Row) (k : ℚ) : Row := xs.map (threshold xs k)
def level (xs : Row) (k : ℚ) : ℚ :=
  let ts := thresholds xs k
  ts.foldl max (ts.head?.getD 0)
def project (xs : Row) (k : ℚ) : Row := xs.map (fun q => max 0 (q-level xs k))

 theorem threshold_ofFn {n : ℕ} (x : Fin n → ℚ) (k : ℚ) (a : Fin n) :
    threshold (List.ofFn x) k (x a)=Simplex.threshold x k a := by
  simp only [threshold,upper,sum_filter_ofFn,length_filter_ofFn,decide_eq_true_eq,Simplex.threshold,Simplex.upper]

 theorem thresholds_ofFn {n : ℕ} (x : Fin n → ℚ) (k : ℚ) :
    thresholds (List.ofFn x) k=List.ofFn (Simplex.threshold x k) := by
  simp only [thresholds,List.map_ofFn]
  congr 1
  funext a
  exact threshold_ofFn x k a

 theorem level_ofFn {n : ℕ} [NeZero n] (x : Fin n → ℚ) (k : ℚ) :
    level (List.ofFn x) k=Simplex.level x k := by
  unfold level
  rw [thresholds_ofFn]
  have hmem : (List.ofFn (Simplex.threshold x k)).head?.getD 0∈List.ofFn (Simplex.threshold x k) := by
    have hne : List.ofFn (Simplex.threshold x k)≠[] := by
      intro h
      have hl:=congrArg List.length h
      simp only [List.length_ofFn,List.length_nil] at hl
      exact (NeZero.ne n) hl
    generalize List.ofFn (Simplex.threshold x k)=ts at hne ⊢
    cases ts with
    | nil => contradiction
    | cons a ts => exact List.mem_cons_self
  obtain ⟨a,ha⟩ := Simplex.level_attained x k
  apply foldl_max_eq
  · obtain ⟨b,hb⟩ := List.mem_ofFn.mp hmem
    rw [← hb]
    exact Simplex.threshold_le_level x k b
  · exact List.mem_ofFn.mpr ⟨a,ha.symm⟩
  · intro v hv
    obtain ⟨b,rfl⟩ := List.mem_ofFn.mp hv
    exact Simplex.threshold_le_level x k b

 theorem project_ofFn {n : ℕ} [NeZero n] (x : Fin n → ℚ) (k : ℚ) :
    project (List.ofFn x) k=List.ofFn (Simplex.project x k) := by
  simp only [project,level_ofFn,List.map_ofFn,Function.comp_def]
  rfl

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_NearestListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset

namespace Nearest

theorem prior_ofFn {n : ℕ} (y d : Fin n → ℚ) (i : Fin n) :
    prior (List.ofFn (fun j => (j.val,(y j,d j)))) (i.val,(y i,d i))=Preparation.priorMass univ y d i := by
  rw [prior,sum_map_filter_ofFn]
  simp only [before,decide_eq_true_eq,Preparation.priorMass,Preparation.before,Fin.lt_def]

end Nearest
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalBatchLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.PhysicalBatchLaw
open Finset
variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def balanced (Z : Finset E) (C : E → Finset E) (ω : E → Bool) : Finset E :=
  FiniteLaw.selected C ω ∩ Z

end MetricKMedian.PhysicalBatchLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparationStars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation.SupplierStars
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

def flag : Star I T → ℝ
  | .inl _ => 1
  | .inr _ => 0

omit [DecidableEq T] in
 theorem flagged_weight (y : I → ℝ) (P A : T → Finset I) (c : T → ℝ) (γ : ℝ) :
    (∑ e, flag e*weight y P A c γ e)=∑ i ∈ outside P, y i := by
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [flag,weight,one_mul,zero_mul,sum_const_zero,add_zero,sum_ite_mem,univ_inter]

end MetricKMedian.Preparation.SupplierStars
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseOuterLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

def activation (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (z : State n m) (e : Fin m) (i : Fin n) : ℚ :=
  (if i∈D e then (base q e:ℚ) else 0)+(if i∈z.2.1 e then 1 else 0)

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseOuterCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem activationCount_cast (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (z : State n m) (e : Fin m) (i : Fin n) :
    (activationCount D q z e i:ℚ)=activation D q z e i := by
  simp only [activationCount,activation,Nat.cast_add,Nat.cast_ite,Nat.cast_zero,Nat.cast_one]

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RationalSupplierPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                   
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars
variable {f n : ℕ}

theorem flag_cast (e : Star (Fin f) (Fin n)) : (flagQ e : ℝ)=flag e := by
  cases e <;> simp [flagQ, flag]

theorem scaled_q (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f))
    (c : Fin n → ℚ) (γ g : ℚ) (hg : g ≠ 0) (e : Fin (size f n)) :
    (g : ℝ) * (q y P A c γ g e : ℝ) =
      weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ (index e) := by
  have hh : (g : ℝ) ≠ 0 := by exact_mod_cast hg
  simp [q, Rat.cast_div, mul_div_cancel₀ _ hh, weight_cast]

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (setView indices)

theorem ofFn_star {f n : ℕ} {α : Type} (F : SupplierStars.Star (Fin f) (Fin n) → α) :
    List.ofFn (fun i => F (index i)) =
    List.ofFn (fun i => F (.inl i)) ++
      ((List.ofFn (fun s => List.ofFn (fun t => F (.inr (.inl (s,t)))))).flatten ++
        List.ofFn (fun t => F (.inr (.inr t)))) := by
  conv_lhs => rw [List.ofFn_add]
  simp only [index,Equiv.trans_apply,Equiv.sumCongr_apply,finSum_symm_castLE,
    finSumFinEquiv_symm_apply_natAdd,Sum.map_inl,Sum.map_inr,Equiv.refl_apply]
  conv_lhs => arg 2; rw [List.ofFn_add]
  simp only [finSum_symm_castLE,
    finSumFinEquiv_symm_apply_natAdd,Sum.map_inl,Sum.map_inr,Equiv.refl_apply]
  rw [RoundingList.ofFn_product]

end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_SplitListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Preparation.RationalSplitting.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
def view {f j : ℕ} (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) : Raw :=
  (List.ofFn y,List.ofFn (fun c => List.ofFn (x c)))
end MetricKMedian.Preparation.RationalSplitting.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RepresentativeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalRepresentatives.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram

def advance (x : Input) (s : Cut x) : Cut x :=
  if h : s.1.Nonempty then
    let c := Preparation.firstNearest s.1 x.R h
    (s.1.filter (fun i => x.M*x.R i < x.d i c),insert c s.2)
  else s
def State.step (s : State) : State := ⟨s.input,advance s.input s.cut⟩
def Input.state (x : Input) (t : ℕ) : State := ⟨x,(advance x)^[t] (x.U,∅)⟩
def Input.start (x : Input) := x.state 0

 theorem state_iterate (x : Input) (t : ℕ) : State.step^[t] x.start=x.state t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih]
    change (⟨x,advance x ((advance x)^[t] (x.U,∅))⟩ : State)=_
    simp only [Input.state,Function.iterate_succ_apply']

end MetricKMedian.Preparation.RationalRepresentatives.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_UnitRepresentativeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Preparation.RationalUnitInput.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
structure Input where
  f : ℕ
  j : ℕ
  U : RationalUnitInput f j

end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.FractionalRefinement.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
structure Input where
  f : ℕ
  j : ℕ
  k : ℕ
  a : TruncatedLP.FractionalData f j
  ha : a.Valid k
  hj : 0<j
  dc : Fin j → Fin f → ℚ
  dd : Fin j → Fin j → ℚ
  df : Fin f → Fin f → ℚ
  hdc : ∀ c i, 0≤dc c i
  hdd : ∀ c, dd c c=0
  hds : ∀ c c', dd c c'=dd c' c
abbrev Input.raw (z : Input) : Raw :=
  (List.ofFn (y z.a),(List.ofFn (fun c => List.ofFn (z.dc c)),
    (List.ofFn (fun c => List.ofFn (z.dd c)),List.ofFn (fun a => List.ofFn (z.df a)))))
end MetricKMedian.Preparation.FractionalRefinement.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalListChecks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.LPBinary.Repair
open Binary Binary.PolyProgram Function Finset

def dominated (xs ys : Row) : Bool := (xs.zip ys).all (fun p => decide (0 ≤ p.1 ∧ p.1 ≤ p.2))
def dot (xs ds : Row) : ℚ := ((xs.zip ds).map (fun p => p.1*p.2)).sum
end MetricKMedian.LPBinary.Repair
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalSelectProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Scale

def argmin (xs : Row) (f : ℚ → ℚ) : ℚ := minimum (xs.filter (fun x => decide (f x=minimum (xs.map f))))

theorem argmin_eq (xs : Row) (A : Finset ℚ) (f : ℚ → ℚ) (hm : ∀ q, q ∈ xs ↔ q ∈ A) :
    argmin xs f=rationalArgmin A f := by
  by_cases hA : A.Nonempty
  · let v := (A.image f).min' (hA.image f)
    let B := A.filter (fun t => f t=v)
    have hB : B.Nonempty := by
      obtain ⟨t,ht,he⟩ := mem_image.mp (min'_mem (A.image f) (hA.image f))
      exact ⟨t,mem_filter.mpr ⟨ht,he⟩⟩
    have hv : minimum (xs.map f)=v := by
      apply minimum_eq_finset
      intro q
      simp only [List.mem_map,mem_image]
      exact exists_congr (fun x => and_congr_left (fun _ => hm x))
    unfold argmin
    rw [hv]
    have hh := minimum_eq_finset (xs.filter (fun t => decide (f t=v))) B hB (fun q => by
      simp only [List.mem_filter,decide_eq_true_eq,mem_filter,B,hm])
    rw [hh]
    simp only [rationalArgmin,dite_eq_left hA]
    change B.min' hB=(if h : B.Nonempty then B.min' h else 0)
    rw [dite_eq_left hB]
  · have hz : xs=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro q hq
      exact hA ⟨q,(hm q).mp hq⟩
    simp only [argmin,hz,List.map_nil,List.filter_nil,minimum,List.head?_nil,Option.getD_none,
      List.foldl_nil,rationalArgmin,dite_eq_right hA]

end Scale
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_StarActivationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparseStarActivation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView indices)

def Input.column (x : Input) (e : Fin x.m) : SparseTargetSubset.Program.Input :=
  ⟨x.n,x.D e,x.q e,x.feasible e⟩
def Input.columns (x : Input) := List.ofFn x.column

end MetricKMedian.SparseStarActivation.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedTerminalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open Binary.Automatic Binary.Automatic.Poly
namespace Terminal

abbrev BInput := SparseBernoulli.Program.Input

end Terminal
end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountRunHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseCounts
open Binary
variable {n m : ℕ}

theorem edge_height (G : Table n m) (H : ℕ) (hG : ∀ i h, G i h≤2^H)
    (h : Fin n) (i : Fin m) : HasHeight (edge G h i) H := by
  constructor
  · simpa only [edge,Rat.num_natCast,abs_of_nonneg (Nat.cast_nonneg _ : (0:ℤ)≤((G i h:ℕ):ℤ)),Nat.cast_pow,Nat.cast_ofNat]
      using (Nat.cast_le (α:=ℤ)).mpr (hG i h)
  · simp only [edge,Rat.den_natCast,Nat.cast_one]
    exact one_le_pow₀ (by norm_num)

theorem features_height (G : Table n m) (H : ℕ) (hG : ∀ i h, G i h≤2^H)
    (a : Fin (n*m+(n*m)*(n*m))) : HasHeight (features G a) (H+H) := by
  unfold features edgeCode
  generalize finSumFinEquiv.symm a=z
  cases z with
  | inl i => exact (edge_height _ _ hG _ _).mono (Nat.le_add_right _ _)
  | inr ij => exact (edge_height _ _ hG _ _).mul (edge_height _ _ hG _ _)

end MetricKMedian.SparseCounts
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_GridRoundingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGridRounding.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
theorem ofFn_point {n : ℕ} (p : Vector ℚ n) : List.ofFn (RationalWeightedStep.point p)=p.toList := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'; simp [RationalWeightedStep.point]
 theorem vector_point {n : ℕ} (p : Vector ℚ n) : Vector.ofFn (RationalWeightedStep.point p)=p := by
  ext i hi
  simp only [RationalWeightedStep.point,Vector.getElem_ofFn]
end MetricKMedian.SparseGridRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparedKernelProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

def KernelInput.bundles (x : KernelInput) : SparseBundles.Program.QInput :=
  ⟨x.f,x.n,SparseRescaledInner.piece x.P x.y x.p (total x.D x.q x.Δ x.z),
    SparseRescaledInner.piece_nonnegative x.P x.y x.p _ x.hy x.hp⟩
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparedLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (setView)

def Input.outer (x : Input) : SparseOuterLaw.Program.Input := ⟨x.n,x.m,x.D,x.c,x.q,x.hc,x.hq⟩
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierPreparationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (setView indices)
open SparseIntegerLaw.BinarySparse
variable {τ : ℝ}

theorem ofFn_physical {f n : ℕ} {α : Type} (F : Sum (Fin f) (Fin n × Fin f) → α) :
    List.ofFn (fun e => F (physicalIndex e))=List.ofFn (fun i => F (.inl i)) ++
      (List.ofFn (fun t => List.ofFn (fun i => F (.inr (t,i))))).flatten := by
  conv_lhs => rw [List.ofFn_add]
  simp only [physicalIndex,Equiv.trans_apply,Equiv.sumCongr_apply,finSum_symm_castLE,
    finSumFinEquiv_symm_apply_natAdd,Sum.map_inl,Sum.map_inr,Equiv.refl_apply]
  rw [RoundingList.ofFn_product]

end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_UnitScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Preparation.RationalUnitInput.ScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open Program
structure Input where
  f : ℕ
  j : ℕ
  m : ℕ
  U : RationalUnitInput f j
  metric : PseudoMetricSpace (Fin m)
  R : @Realization f j U (Fin m) metric
  B : ℚ
variable {η τ : ℝ}
def Input.unit (x : Input) : Program.Input := ⟨x.f,x.j,x.U⟩
end MetricKMedian.Preparation.RationalUnitInput.ScanProgram
end

end OAI
end


