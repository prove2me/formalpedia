-- Prove2me | Definitions.Def_OAIQ035K010
-- name    : OAIQ035K010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:53:57.729356+00:00
-- url     : https://prove2.me/theorems/385ec537-0201-4904-876e-d9211e5bc76a
-- title:
--   Definitions bundle OAIQ035K010 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 108 declarations of OpenAI's Lean: 70 definitions, 10 inductive types or structures, 3 instances and 25 theorems. The definitions and types are `OAI.MetricKMedian.LPBinary.Input`, `OAI.MetricKMedian.LPBinary.Input.scale`, `OAI.MetricKMedian.LPBinary.Repair.bounded`, `OAI.MetricKMedian.LPBinary.baseBound`, `OAI.MetricKMedian.LPBinary.exponentBound`, `OAI.MetricKMedian.LPBinary.gradientBound`, `OAI.MetricKMedian.LPBinary.heightBound`, `OAI.MetricKMedian.LPBinary.heightPolynomial`, `OAI.MetricKMedian.LPBinary.stepsBound`, `OAI.MetricKMedian.LPBinary.stepsPolynomial`, `OAI.MetricKMedian.Preparation.BundleGeometry`, `OAI.MetricKMedian.Preparation.Physical`, `OAI.MetricKMedian.Preparation.RationalBundles.mass`, `OAI.MetricKMedian.Preparation.RationalSuppliers.D`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Data`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.Input`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.ScanInput`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.ScanInput.prep`, `OAI.MetricKMedian.Preparation.RationalSuppliers.a`, `OAI.MetricKMedian.Preparation.RationalSuppliers.flagQ`, `OAI.MetricKMedian.Preparation.RationalSuppliers.index`, `OAI.MetricKMedian.Preparation.RationalSuppliers.original`, `OAI.MetricKMedian.Preparation.RationalSuppliers.physicalIndex`, `OAI.MetricKMedian.Preparation.RationalSuppliers.q`, `OAI.MetricKMedian.Preparation.RationalSuppliers.size`, `OAI.MetricKMedian.Preparation.RationalSuppliers.weightQ`, `OAI.MetricKMedian.Preparation.SupplierStars.Star`, `OAI.MetricKMedian.Preparation.SupplierStars.outside`, `OAI.MetricKMedian.Preparation.SupplierStars.targets`, `OAI.MetricKMedian.Preparation.SupplierStars.weight`, `OAI.MetricKMedian.Preparation.before`, `OAI.MetricKMedian.Preparation.failureFactor`, `OAI.MetricKMedian.Preparation.farFactor`, `OAI.MetricKMedian.Preparation.nearFactor`, `OAI.MetricKMedian.Preparation.priorMass`, `OAI.MetricKMedian.Preparation.shortfallFactor`, `OAI.MetricKMedian.SparseBernoulli.tuple`, `OAI.MetricKMedian.SparseBernoulli.without`, `OAI.MetricKMedian.SparseBundles.Program.QInput`, `OAI.MetricKMedian.SparseBundles.Program.QInput.column` and 40 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Geometry_NearestFillingFormula`, `KMedian_Geometry_RationalBundleGeometry`, `KMedian_Optimization_FractionalListChecks`, `KMedian_Optimization_LPBinaryInput`, `KMedian_Optimization_LPBinaryStart`, `KMedian_Optimization_LPListFacts`, `KMedian_Optimization_TruncatedListOperations`, `KMedian_Preparation_CoupledGeometry`, `KMedian_Preparation_PreparationParameters`, `KMedian_Preparation_PreparationStars`, `KMedian_Preparation_PreparedDataOperations`, `KMedian_Preparation_PreparedLawProgram`, `KMedian_Preparation_RationalSupplierPreparation`, `KMedian_Preparation_RationalSupplierScan`, `KMedian_Preparation_RepresentativeBundles`, `KMedian_Preparation_RepresentativeGeometry`, `KMedian_Preparation_SupplierListOperations`, `KMedian_Preparation_SupplierPreparationProgram`, `KMedian_Preparation_SupplierScanProgram`, `KMedian_Process_CountListOperations`, `KMedian_Process_CountRunHeight`, `KMedian_Process_CountRunProgram`, `KMedian_Programs_BundlesProgram`, `KMedian_Programs_NearestListProgram`, `KMedian_Programs_ScaleListProgram`, `KMedian_Programs_StarActivationProgram`, `KMedian_Rounding_GridRoundingProgram`, `KMedian_Sparse_SparseBernoulliFeatures`, `KMedian_Sparse_SparseBernoulliSubsets`, `KMedian_Sparse_SparseCountFeatures`, `KMedian_Sparse_SparseGridRounding`, `KMedian_Sparse_SparseOuterCounts`, `KMedian_Sparse_SparsePreparedLaw`, `KMedian_Sparse_SparseRescaledInner`, `KMedian_Sparse_SparseSignedPreparation`, `KMedian_Sparse_SparseSupplierSupport`, `KMedian_Sparse_SparseTargetSubset`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K021`, `OAIQ035K022`, `OAIQ035K023`, `OAIQ035K024`, `OAIQ035K025`, `OAIQ035K044` and `OAIQ035K062`; the statement `OAI.MetricKMedian.Preparation.shortfall_from_deviation`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPListFacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.LPBinary
open Finset

 theorem sum_filter_ofFn (n : ℕ) (f : Fin n → ℚ) (p : ℚ → Bool) :
    ((List.ofFn f).filter p).sum=∑ i∈univ.filter (fun i => p (f i)), f i := by
  rw [Finset.sum_filter]
  have he : ((List.ofFn f).filter p).sum=((List.ofFn f).map (fun a => if p a then a else 0)).sum := by
    generalize List.ofFn f=xs
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : p a <;> simp [h,ih]
  rw [he,List.map_ofFn,List.sum_ofFn]
  rfl

 theorem length_filter_ofFn (n : ℕ) (f : Fin n → ℚ) (p : ℚ → Bool) :
    ((List.ofFn f).filter p).length=(univ.filter (fun i => p (f i))).card := by
  have he : ((List.ofFn f).filter p).length=((List.ofFn f).map (fun a => if p a then (1:ℕ) else 0)).sum := by
    generalize List.ofFn f=xs
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : p a <;> simp [h,ih,Nat.add_comm]
  rw [he,List.map_ofFn,List.sum_ofFn]
  simp

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

def before (d : Fin n → ℚ) (j i : Fin n) : Prop := d j  <  d i ∨ d j=d i ∧ j < i
instance instDecidableBefore (d : Fin n → ℚ) (j i : Fin n) : Decidable (before d j i) := by unfold before; infer_instance
def priorMass (U : Finset (Fin n)) (y d : Fin n → ℚ) (i : Fin n) : ℚ :=
  ∑ j∈U.filter (fun j => before d j i), y j

theorem priorMass_erase (U : Finset (Fin n)) (y d : Fin n → ℚ) (a i : Fin n)
    (ha : a∈U) (hai : before d a i) : priorMass U y d i=priorMass (U.erase a) y d i+y a := by
  have he : (U.erase a).filter (fun j => before d j i)=(U.filter (fun j => before d j i)).erase a := by
    ext j
    simp only [mem_filter,mem_erase,and_assoc]
  unfold priorMass
  rw [he]
  exact (sum_erase_add _ y (mem_filter.mpr ⟨ha,hai⟩)).symm

theorem priorMass_nonneg (U : Finset (Fin n)) (y d : Fin n → ℚ) (i : Fin n)
    (hy : ∀ j∈U, 0 ≤ y j) : 0 ≤ priorMass U y d i :=
  sum_nonneg (fun j hj => hy j (mem_filter.mp hj).1)

end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RepresentativeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {J I X : Type*} [DecidableEq J] [PseudoMetricSpace X]

omit [DecidableEq J] in

theorem bundle_disjoint_geometry (s t i : X) {δ Ls Lt : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ < 1/2) (hst : 0 < dist s t)
    (hLs : Ls ≤ dist s t) (hLt : Lt ≤ dist s t)
    (hsi : dist s i ≤ δ*Ls) (hti : dist t i ≤ δ*Lt) : False := by
  have hs := hsi.trans (mul_le_mul_of_nonneg_left hLs hδ)
  have ht := hti.trans (mul_le_mul_of_nonneg_left hLt hδ)
  have htri := dist_triangle s i t
  rw [dist_comm i t] at htri
  have hh := mul_lt_mul_of_pos_right hδ1 hst
  linarith only [hs,ht,htri,hh]

omit [DecidableEq J] [PseudoMetricSpace X] in
                                                                   
theorem outside_mass_bound [DecidableEq I] (F : Finset I) (y d : I → ℝ) {r : ℝ}
    (hy : ∀ i ∈ F, 0 ≤ y i) (hd : ∀ i ∈ F, 0 ≤ d i) :
    r*(∑ i ∈ F.filter (fun i => r < d i), y i) ≤ ∑ i ∈ F, y i*d i := by
  calc
    _ = ∑ i ∈ F.filter (fun i => r < d i), y i*r := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ ∑ i ∈ F.filter (fun i => r < d i), y i*d i := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (mem_filter.mp hi).2.le (hy i (mem_filter.mp hi).1)
    _ ≤ ∑ i ∈ F, y i*d i := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i hi _ => mul_nonneg (hy i hi) (hd i hi))

omit [DecidableEq J] [PseudoMetricSpace X] in
 theorem deficit_small {M δ L V c : ℝ} (hM : 0 < M) (hδ : 0 < δ) (hL : 0 < L)
    (hc : δ*L*c ≤ V) (hsep : M*V ≤ L) : c ≤ 1/(M*δ) := by
  have ha : c ≤ V/(δ*L) := (le_div_iff₀ (mul_pos hδ hL)).mpr (by nlinarith only [hc])
  have hb : V ≤ L/M := (le_div_iff₀ hM).mpr (by nlinarith only [hsep])
  calc
    c ≤ V/(δ*L) := ha
    _ ≤ (L/M)/(δ*L) := div_le_div_of_nonneg_right hb (mul_pos hδ hL).le
    _ = 1/(M*δ) := by field_simp

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RepresentativeBundles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {T I X : Type*} [Fintype T] [DecidableEq T] [DecidableEq I]
  [PseudoMetricSpace X]

structure BundleGeometry (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
    (V : T → ℝ) (M δ : ℝ) where
  P : T → Finset I
  A : T → Finset I
  p : T → ℝ
  c : T → ℝ
  L : T → ℝ
  next : T → T
  sub : ∀ t, P t ⊆ F t
  missing : ∀ t, A t=F t \ P t
  mass : ∀ t, ∑ a ∈ P t, y a=p t
  deficit_mass : ∀ t, ∑ a ∈ A t, y a=c t
  unit : ∀ t, p t+c t=1
  nonneg : ∀ t, 0 ≤ c t
  small : ∀ t, c t ≤ 1/(M*δ)
  large : ∀ t, 1-1/(M*δ) ≤ p t
  disjoint : Pairwise (fun t u => Disjoint (P t) (P u))
  next_distance : ∀ t, L t=dist (s t) (s (next t))
  closest : ∀ t u, t ≠ u → L t ≤ dist (s t) (s u)
  radius : ∀ t, next t ≠ t → ∀ a ∈ P t, dist (s t) (i a) ≤ δ*L t
  outside_radius : ∀ t, next t ≠ t → ∀ a ∈ A t, δ*L t < dist (s t) (i a)
  self_singleton : ∀ t, next t=t → ∀ u, u=t
  self_zero : ∀ t, next t=t → c t=0
  zero_full : ∀ t, c t=0 → P t=F t
  charge : ∀ t, δ*L t*c t ≤ V t

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalBundleGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalBundles
open Finset
variable {n m : ℕ}

def mass (y : Fin m → ℚ) (P : Fin n → Finset (Fin m)) (t : Fin n) : ℚ := ∑ a ∈ P t, y a

end MetricKMedian.Preparation.RationalBundles
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPBinaryInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Polynomial Finset

structure Input where
  n : ℕ
  m : ℕ
  k : ℕ
  npos : 0 < n
  mpos : 0 < m
  kpos : 0 < k
  kle : k ≤ n
  distance : Fin m → Fin n → ℚ

namespace Input
instance instNeZeroNatN (I : Input) : NeZero I.n := ⟨I.npos.ne'⟩
instance instNeZeroNatM (I : Input) : NeZero I.m := ⟨I.mpos.ne'⟩
end Input

def gradientBound (r L : ℕ) := L*(L*(4*r*(L+1)))^2
def baseBound (r L : ℕ) := 2*r*gradientBound r L*L
def stepsBound (r L : ℕ) := 8*r^2*gradientBound r L*L^2
def exponentBound (r L : ℕ) := baseBound r L+L*(L*L)+L+1
def heightBound (r L : ℕ) := exponentBound r L*(stepsBound r L+1)

noncomputable def stepsPolynomial (r : ℕ) : Polynomial ℕ := 8*C r^2*(X*(X*(4*C r*(X+1)))^2)*X^2
noncomputable def heightPolynomial (r : ℕ) : Polynomial ℕ :=
  (2*C r*(X*(X*(4*C r*(X+1)))^2)*X+X*(X*X)+X+1)*(stepsPolynomial r+1)
 theorem stepsPolynomial_eval (r L : ℕ) : (stepsPolynomial r).eval L=stepsBound r L := by
  simp only [stepsPolynomial,stepsBound,gradientBound,eval_add,eval_mul,eval_pow,eval_ofNat,eval_C,eval_X,eval_one]
 theorem heightPolynomial_eval (r L : ℕ) : (heightPolynomial r).eval L=heightBound r L := by
  simp only [heightPolynomial,heightBound,exponentBound,baseBound,gradientBound,eval_add,eval_mul,eval_pow,eval_ofNat,eval_C,eval_X,eval_one,stepsPolynomial_eval]
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_TruncatedListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.LPBinary
open Finset
theorem range_ofFn (n : ℕ) : List.range n=List.ofFn (fun i : Fin n => i.val) := by
  apply List.ext_getElem
  · simp
  · intros; simp

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPBinaryStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Function

theorem head_ofFn {α : Type} {n : ℕ} [NeZero n] (f : Fin n → α) (a : α) :
    (List.ofFn f).head?.getD a=f ⟨0,NeZero.pos n⟩ := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rw [List.ofFn_succ]; rfl

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
open Function Finset

theorem sum_map_filter_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (p : α → Bool) (v : α → ℚ) :
    (((List.ofFn f).filter p).map v).sum=∑ i ∈ univ.filter (fun i => p (f i)), v (f i) := by
  rw [Finset.sum_filter]
  have he (xs : List α) : ((xs.filter p).map v).sum=(xs.map (fun a => if p a then v a else 0)).sum := by
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : p a <;> simp [h,ih]
  rw [he,List.map_ofFn,List.sum_ofFn]
  rfl

end MetricKMedian.LPBinary
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
open Function Finset

def bounded (q : ℚ) : Bool := decide (0 ≤ q ∧ q ≤ 1)

theorem all_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (p : α → Bool) :
    (List.ofFn f).all p=true ↔ ∀ i, p (f i)=true := by
  simp only [List.all_eq_true,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff]

end MetricKMedian.LPBinary.Repair
end

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

abbrev Star (I T : Type) := I ⊕ ((T × T) ⊕ T)

def outside (P : T → Finset I) : Finset I := univ.filter (fun i => ∀ t, i ∉ P t)

def targets (A : T → Finset I) : Star I T → Finset T
  | .inl i => univ.filter (fun t => i ∈ A t)
  | .inr (.inl st) => {st.1}
  | .inr (.inr t) => {t}

noncomputable def weight (y : I → ℝ) (P A : T → Finset I) (c : T → ℝ) (γ : ℝ) : Star I T → ℝ
  | .inl i => if i ∈ outside P then y i else 0
  | .inr (.inl st) => ∑ i ∈ A st.1 ∩ P st.2, y i
  | .inr (.inr t) => γ*c t

omit [DecidableEq T] in
 theorem weight_nonneg (y : I → ℝ) (P A : T → Finset I) (c : T → ℝ) (γ : ℝ)
    (hy : ∀ i, 0 ≤ y i) (hc : ∀ t, 0 ≤ c t) (hγ : 0 ≤ γ) :
    ∀ e, 0 ≤ weight y P A c γ e := by
  rintro (i | (st | t))
  · dsimp only [weight]; split_ifs; exact hy i; exact le_rfl
  · exact sum_nonneg (fun i _ => hy i)
  · exact mul_nonneg hγ (hc t)

end MetricKMedian.Preparation.SupplierStars
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_CoupledGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

abbrev Physical (I T : Type) := I ⊕ (T × I)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparationParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation

noncomputable def farFactor (δ p₀ α β γ : ℝ) : ℝ :=
  max (1/p₀) (1+2*δ/(1-β-δ))*((1+α)/(1-α))+(β+1+δ)*γ/δ
noncomputable def shortfallFactor (p₀ γ g : ℝ) : ℝ :=
  Real.sqrt g+Real.sqrt (g/p₀)+(γ+Real.sqrt (g*(1+γ)))/p₀
noncomputable def nearFactor (p₀ Q γ g : ℝ) : ℝ :=
  1/p₀+Q*shortfallFactor p₀ γ g
noncomputable def failureFactor (γ g : ℝ) : ℝ := 4*g*(1+γ)/γ

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBernoulliFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

def without (f : Fin d → Fin (n+1)) (i : Fin n) : Fin d → Fin (n+1) :=
  fun a => if (f a).val=i.val then ⟨n,Nat.lt_succ_self n⟩ else f a

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBernoulliSubsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

def tuple (S : Finset (Fin n)) : Fin d → Fin (n+1) :=
  fun a => if h : a.val<S.card then (S.orderEmbOfFin rfl ⟨a.val,h⟩).castSucc
    else ⟨n,Nat.lt_succ_self n⟩

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseTargetSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseTargetSubset
open Finset
variable {n : ℕ}

def initial (D : Finset (Fin n)) (q : ℚ) : Vector ℚ n :=
  Vector.ofFn (fun i => if i∈D then q else 0)

end MetricKMedian.SparseTargetSubset
end
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
structure Input where
  n : ℕ
  m : ℕ
  D : Fin m → Finset (Fin n)
  q : Fin m → ℚ
  feasible : ∀ e, 0≤q e ∧ q e≤1
end MetricKMedian.SparseStarActivation.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSignedPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPreparation
open Finset
variable {n m : ℕ}

abbrev State (n m : ℕ) := Vector ℚ m × ((Fin m → Finset (Fin n)) × (Fin m → Bool))

def signed (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) : Fin m → ℚ :=
  fun e => c e-((D e).card:ℚ)

end MetricKMedian.SparseSignedPreparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGridRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGridRounding
open Finset
variable {n : ℕ}

def base (q : Fin n → ℚ) (i : Fin n) : ℕ := ⌊q i⌋₊
def fraction (q : Fin n → ℚ) : Vector ℚ n := Vector.ofFn (fun i => q i-(base q i:ℚ))

end MetricKMedian.SparseGridRounding
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
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

def activationCount (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (z : State n m) (e : Fin m) (i : Fin n) : ℕ :=
  (if i∈D e then base q e else 0)+(if i∈z.2.1 e then 1 else 0)

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCountFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCounts
open Finset
variable {n m : ℕ}

abbrev Table (n m : ℕ) := Fin m → (Fin n → ℕ)

def edge (G : Table n m) (h : Fin n) (i : Fin m) : ℚ := (G i h:ℚ)

def edgeCode (G : Table n m) (a : Fin (n*m)) : ℚ :=
  edge G (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2

def features (G : Table n m) (a : Fin (n*m+(n*m)*(n*m))) : ℚ :=
  Sum.elim (edgeCode G) (fun ij : Fin ((n*m)*(n*m)) =>
    edgeCode G (finProdFinEquiv.symm ij).1*edgeCode G (finProdFinEquiv.symm ij).2)
    (finSumFinEquiv.symm a)

@[simp] theorem features_single (G : Table n m) (h : Fin n) (i : Fin m) :
    features G (finSumFinEquiv (Sum.inl (finProdFinEquiv (h,i))))=edge G h i := by
  simp only [features,edgeCode,Equiv.symm_apply_apply,Sum.elim_inl]

@[simp] theorem features_pair (G : Table n m) (h k : Fin n) (i j : Fin m) :
    features G (finSumFinEquiv (Sum.inr (finProdFinEquiv
      (finProdFinEquiv (h,i),finProdFinEquiv (k,j)))))=edge G h i*edge G k j := by
  simp only [features,edgeCode,Equiv.symm_apply_apply,Sum.elim_inr]

def next (G : Table n m) (S : (Fin n → ℕ)) (i : Fin m) : Table n m :=
  Function.update G i S

@[simp] theorem edge_next (G : Table n m) (S : (Fin n → ℕ)) (h : Fin n) (i j : Fin m) :
    edge (next G S i) h j=if j=i then (S h:ℚ) else edge G h j := by
  by_cases hji : j=i <;> simp [edge,next,hji]

end MetricKMedian.SparseCounts
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseRescaledInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseRescaledInner
open Finset
variable {n t : ℕ}

def piece (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) : Fin n → Fin t → ℚ :=
  fun i j => if i∈P j then (K j:ℚ)*y i/p j else 0

theorem piece_nonnegative (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) (hy : ∀ i,0 ≤ y i) (hp : ∀ j,0 < p j) :
    ∀ i j,0 ≤ piece P y p K i j := by
  intro i j
  dsimp only [piece]
  split_ifs
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hy i)) (hp j).le
  · exact le_rfl

end MetricKMedian.SparseRescaledInner
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparsePreparedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m f : ℕ}

def total (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) : Fin n → ℕ :=
  fun j => Δ-min (∑ e,activationCount D q z e j) (Δ/2)

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparedDataOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.SparsePrepared.Program
abbrev QRow := List ℚ
abbrev BTable := List (List Bool)

abbrev BaseRaw := BTable × (QRow × (BTable × (QRow × (QRow × ℕ))))
structure KernelInput where
  n : ℕ
  m : ℕ
  f : ℕ
  D : Fin m → Finset (Fin n)
  q : Fin m → ℚ
  P : Fin n → Finset (Fin f)
  y : Fin f → ℚ
  p : Fin n → ℚ
  Δ : ℕ
  z : SparseSignedPreparation.State n m
  hy : ∀ i,0≤y i
  hp : ∀ j,0<p j

end MetricKMedian.SparsePrepared.Program
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
variable {n m : ℕ}

theorem next_bound (G : Table n m) (S : Fin n → ℕ) (i : Fin m) (U : ℕ)
    (hG : ∀ j h,G j h≤U) (hS : ∀ h,S h≤U) : ∀ j h,next G S i j h≤U := by
  intro j h
  by_cases hj : j=i
  · subst j; simpa only [next,Function.update_self] using hS h
  · simpa only [next,Function.update_of_ne hj] using hG j h

def stepHeight (n m N L H : ℕ) :=
  let d := n*m+(n*m)*(n*m)
  L+((2*(d+1)*(d+1+(H+H)*((d+1)*N+1)))*((d+1)*N+1))*((d+1)*N)

end MetricKMedian.SparseCounts
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseCounts.ListOperation
abbrev Row := List ℕ
abbrev Table := List Row

def indices {α : Type} (xs : List α) : List ℕ := List.range xs.length

def view {n m : ℕ} (G : SparseCounts.Table n m) : Table := List.ofFn (fun i => List.ofFn (G i))
def setView {n : ℕ} (S : Fin n → ℕ) : Row := List.ofFn S
end MetricKMedian.SparseCounts.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseCounts.Program
open Function Polynomial
open ListOperation (Row Table )

def supportBound (L : ℕ) := L*L+(L*L)*(L*L)+1
def heightBound (L : ℕ) := SparseCounts.stepHeight L L L L L*L
def graphSize (L : ℕ) := L*(2*(L*(2*(L+1)+1))+1)
def sizeBound (L : ℕ) :=
  2*(3*L+2)+1+(2*(2*(heightBound L+4)+1+supportBound L*(2*(heightBound L+4)+1))+1+
    supportBound L*(2*graphSize L+1))
noncomputable def SPoly : Polynomial ℕ := X*X+(X*X)*(X*X)+1
noncomputable def HPoly : Polynomial ℕ := (X+(2*SPoly*(SPoly+(X+X)*(SPoly*X+1)))*(SPoly*X+1)*(SPoly*X))*X
noncomputable def APoly : Polynomial ℕ := X*(2*(X*(2*(X+1)+1))+1)
noncomputable def sizePolynomial : Polynomial ℕ :=
  2*(3*X+2)+1+(2*(2*(HPoly+4)+1+SPoly*(2*(HPoly+4)+1))+1+SPoly*(2*APoly+1))
theorem sizePolynomial_eval (L : ℕ) : sizePolynomial.eval L=sizeBound L := by
  simp only [sizePolynomial,sizeBound,heightBound,supportBound,graphSize,HPoly,SPoly,APoly,
    SparseCounts.stepHeight,eval_add,eval_mul,eval_ofNat,eval_X,eval_one]

end MetricKMedian.SparseCounts.Program
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
structure Input where
  n : ℕ
  q : Fin n → ℚ
  nonnegative : ∀ i, 0≤q i
abbrev Input.raw (x : Input) := List.ofFn x.q

def fractionRow (q : List ℚ) : List ℚ := q.map (fun x => x-(⌊x⌋₊:ℚ))
end MetricKMedian.SparseGridRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_BundlesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseBundles.Program
open Function
open SparseCounts.Program

structure QInput where
  n : ℕ
  m : ℕ
  q : Fin n → Fin m → ℚ
  feasible : ∀ h i, 0≤q h i

def QInput.raw (x : QInput) : List Unit × List (List ℚ) :=
  (List.replicate x.n (),List.ofFn fun i => List.ofFn fun h => x.q h i)

def QInput.column (x : QInput) (i : Fin x.m) : SparseGridRounding.Program.Input :=
  ⟨x.n,fun h => x.q h i,fun h => x.feasible h i⟩
def QInput.columns (x : QInput) : List SparseGridRounding.Program.Input := List.ofFn x.column
def emptyColumn : SparseGridRounding.Program.Input := ⟨0,Fin.elim0,fun i => Fin.elim0 i⟩
end MetricKMedian.SparseBundles.Program
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
structure Input where
  n : ℕ
  m : ℕ
  f : ℕ
  D : Fin m → Finset (Fin n)
  c : Fin m → ℚ
  q : Fin m → ℚ
  P : Fin n → Finset (Fin f)
  y : Fin f → ℚ
  p : Fin n → ℚ
  Δ : ℕ
  hy : ∀ i,0≤y i
  hp : ∀ j,0<p j
  hc : ∀ e,0 ≤ c e ∧ c e≤1
  hq : ∀ e,0≤q e
def dummy : KernelInput :=
  ⟨0,0,0,Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,0,(#v[],Fin.elim0,Fin.elim0),(fun i => Fin.elim0 i),(fun i => Fin.elim0 i)⟩
end MetricKMedian.SparsePrepared.Program
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

abbrev size (f n : ℕ) := f+(n*n+n)

def index : Fin (size f n) ≃ Star (Fin f) (Fin n) :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) <|
    finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl _)))

def flagQ : Star (Fin f) (Fin n) → ℚ
  | .inl _ => 1
  | .inr _ => 0

def weightQ (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f)) (c : Fin n → ℚ)
    (γ : ℚ) : Star (Fin f) (Fin n) → ℚ
  | .inl i => if i ∈ outside P then y i else 0
  | .inr (.inl st) => ∑ i ∈ A st.1 ∩ P st.2, y i
  | .inr (.inr t) => γ*c t

theorem weight_cast (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f))
    (c : Fin n → ℚ) (γ : ℚ) (e : Star (Fin f) (Fin n)) :
    (weightQ y P A c γ e : ℝ) = weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ e := by
  rcases e with i | (st | t)
  · dsimp only [weightQ, weight]
    split_ifs <;> simp
  · simp [weightQ, weight, Rat.cast_sum]
  · simp [weightQ, weight]

def D (A : Fin n → Finset (Fin f)) : Fin (size f n) → Finset (Fin n) := targets A ∘ index

def a : Fin (size f n) → ℚ := flagQ ∘ index

def q (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f)) (c : Fin n → ℚ)
    (γ g : ℚ) (e : Fin (size f n)) : ℚ := weightQ y P A c γ (index e) / g

theorem a_bounds (e : Fin (size f n)) : 0 ≤ a e ∧ a e ≤ 1 := by
  dsimp only [a, Function.comp_apply]
  generalize index e = z
  cases z <;> norm_num [flagQ]

theorem q_nonneg (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f))
    (c : Fin n → ℚ) (γ g : ℚ) (hy : ∀ i, 0 ≤ y i) (hc : ∀ t, 0 ≤ c t)
    (hγ : 0 ≤ γ) (hg : 0 ≤ g) (e : Fin (size f n)) : 0 ≤ q y P A c γ g e := by
  apply div_nonneg _ hg
  have hw := weight_nonneg (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) (γ : ℝ)
    (fun i => by exact_mod_cast hy i) (fun t => by exact_mod_cast hc t)
    (by exact_mod_cast hγ) (index e)
  rw [← weight_cast] at hw
  exact_mod_cast hw

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSupplierSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars
variable {f n : ℕ}

def physicalIndex : Fin (f+n*f) ≃ Physical (Fin f) (Fin n) :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv.symm)

def original (a : Fin (f+n*f)) : Fin f := Sum.elim id Prod.snd (physicalIndex a)

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RationalSupplierScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars

structure Data (f n : ℕ) where
  y : Fin f → ℚ
  P : Fin n → Finset (Fin f)
  A : Fin n → Finset (Fin f)
  p : Fin n → ℚ
  c : Fin n → ℚ
  γ : ℚ
  hy : ∀ i, 0 ≤ y i
  hp : ∀ t, 0 < p t
  hP : Pairwise (fun s t => Disjoint (P s) (P t))
  hm : ∀ t, ∑ i ∈ P t, y i=p t
  hc : ∀ t, ∑ i ∈ A t, y i=c t
  hc0 : ∀ t, 0 ≤ c t
  hc1 : ∀ t, c t ≤ 1/8
  hunit : ∀ t, p t+c t=1
  hγ : 0 < γ
  hγ1 : γ ≤ 1

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
open Finset

theorem finSum_symm_castLE {m n : ℕ} (h : m ≤ m+n) (i : Fin m) :
    (finSumFinEquiv.symm (Fin.castLE h i) : Fin m ⊕ Fin n)=.inl i :=
  finSumFinEquiv_symm_apply_castAdd i

end MetricKMedian.Preparation.RationalSuppliers.Program
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
open Finset
variable {τ : ℝ}
structure Input where
  f : ℕ
  n : ℕ
  S : Data f n

theorem index_inl {f n : ℕ} (i : Fin f) : (index (f:=f) (n:=n)).symm (.inl i)=Fin.castAdd (n*n+n) i := by
  apply (index (f:=f) (n:=n)).injective
  simp only [Equiv.apply_symm_apply,index,Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply,Sum.map_inl,Equiv.refl_apply]

end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset
variable {τ : ℝ}
structure ScanInput where
  f : ℕ
  n : ℕ
  j : ℕ
  S : Data f n
  df : Fin f → Fin f → ℚ
  dc : Fin j → Fin f → ℚ
  budget : ℚ
def ScanInput.prep (x : ScanInput) : Input := ⟨x.f,x.n,x.S⟩
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_ScaleListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.LPBinary
open Function Finset
namespace Input

def scale (I : Input) (B : ℚ) : Input := { I with distance := fun j i => I.distance j i/B }
end Input
end MetricKMedian.LPBinary
end

end OAI
end


