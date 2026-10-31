-- Prove2me | Definitions.Def_OAIQ053K005
-- name    : OAIQ053K005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:53:46.571735+00:00
-- url     : https://prove2.me/theorems/e19601cd-7f45-4368-aa56-8ae78e392996
-- title:
--   Definitions bundle OAIQ053K005 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 102 declarations of OpenAI's Lean: 66 definitions, 2 inductive types or structures, 1 instance and 33 theorems. The definitions and types are `OAI.MetricKMedian.IntegerLaw.positiveSet`, `OAI.MetricKMedian.MarginalRounding.fractional`, `OAI.MetricKMedian.PhysicalPotential.mass`, `OAI.MetricKMedian.Preparation.BundleGeometry`, `OAI.MetricKMedian.Preparation.Physical`, `OAI.MetricKMedian.Preparation.RationalBundles.mass`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Data`, `OAI.MetricKMedian.Preparation.RationalSuppliers.flagQ`, `OAI.MetricKMedian.Preparation.RationalSuppliers.original`, `OAI.MetricKMedian.Preparation.RationalSuppliers.physicalIndex`, `OAI.MetricKMedian.Preparation.RationalSuppliers.weightQ`, `OAI.MetricKMedian.Preparation.SupplierStars.Star`, `OAI.MetricKMedian.Preparation.SupplierStars.outside`, `OAI.MetricKMedian.Preparation.SupplierStars.targets`, `OAI.MetricKMedian.Preparation.SupplierStars.weight`, `OAI.MetricKMedian.RationalLastFraction.endpoint`, `OAI.MetricKMedian.RationalLastFraction.pick`, `OAI.MetricKMedian.RationalLastFraction.probability`, `OAI.MetricKMedian.RationalSignedStep.Active`, `OAI.MetricKMedian.RationalSignedStep.endpoint`, `OAI.MetricKMedian.RationalSignedStep.pair`, `OAI.MetricKMedian.RationalSignedStep.pairs`, `OAI.MetricKMedian.RationalSignedStep.probability`, `OAI.MetricKMedian.RationalWeightedStep.down`, `OAI.MetricKMedian.RationalWeightedStep.endpoint`, `OAI.MetricKMedian.RationalWeightedStep.fractional`, `OAI.MetricKMedian.RationalWeightedStep.move`, `OAI.MetricKMedian.RationalWeightedStep.pair`, `OAI.MetricKMedian.RationalWeightedStep.point`, `OAI.MetricKMedian.RationalWeightedStep.probability`, `OAI.MetricKMedian.RationalWeightedStep.realPoint`, `OAI.MetricKMedian.RationalWeightedStep.up`, `OAI.MetricKMedian.SparseBernoulli.tuple`, `OAI.MetricKMedian.SparseBernoulli.without`, `OAI.MetricKMedian.SparseCardinalRounding.selected`, `OAI.MetricKMedian.SparseCounts.ListOperation.Row`, `OAI.MetricKMedian.SparseCounts.ListOperation.Table`, `OAI.MetricKMedian.SparseCounts.ListOperation.indices`, `OAI.MetricKMedian.SparseCounts.Table`, `OAI.MetricKMedian.SparseCounts.edge` and 28 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Compression_AffineElimination`, `KMedian_Compression_ComputedPivot`, `KMedian_Compression_GramDependence`, `KMedian_Geometry_BoundFreeCompression`, `KMedian_Geometry_RationalBundleGeometry`, `KMedian_Preparation_CoupledGeometry`, `KMedian_Preparation_PreparationStars`, `KMedian_Preparation_PreparedDataOperations`, `KMedian_Preparation_RationalSupplierPreparation`, `KMedian_Preparation_RationalSupplierScan`, `KMedian_Preparation_RepresentativeBundles`, `KMedian_Preparation_RepresentativeGeometry`, `KMedian_Process_CountListOperations`, `KMedian_Process_PhysicalPotential`, `KMedian_Rounding_MarginalRounding`, `KMedian_Rounding_RationalLastFraction`, `KMedian_Rounding_RationalSignedStep`, `KMedian_Rounding_RationalTaperAffine`, `KMedian_Rounding_RationalTaperData`, `KMedian_Rounding_RationalTaperZero`, `KMedian_Rounding_RationalWeightedStep`, `KMedian_Rounding_WeightedRounding`, `KMedian_Sparse_SparseBernoulliFeatures`, `KMedian_Sparse_SparseBernoulliSubsets`, `KMedian_Sparse_SparseCardinalRounding`, `KMedian_Sparse_SparseCountFeatures`, `KMedian_Sparse_SparseGridRounding`, `KMedian_Sparse_SparseOuterCounts`, `KMedian_Sparse_SparsePhysicalBatch`, `KMedian_Sparse_SparsePreparedLaw`, `KMedian_Sparse_SparseRescaledInner`, `KMedian_Sparse_SparseSignedPreparation`, `KMedian_Sparse_SparseSupplierSupport`, `KMedian_Sparse_SparseTargetSubset`, `KMedian_Sparse_SparseWeightedPartial`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K016`, `OAIQ053K017`, `OAIQ053K018`, `OAIQ053K019`, `OAIQ053K020`, `OAIQ053K022`, `OAIQ053K023`, `OAIQ053K026` and `OAIQ053K027`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_AffineElimination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
open Finset

namespace IntegerLaw
variable {Ω I : Type} [Fintype Ω] [Fintype I]

theorem positive_entry {z : Ω → ℤ} (hsum : ∑ i, z i=0) (hz : ∃ i, z i ≠ 0) :
    ∃ i, 0 < z i := by
  by_contra hn
  push Not at hn
  have he : ∀ i, z i=0 := by
    intro i
    have hsingle : z i ≤ 0 := hn i
    have hsum' : (∑ j, -z j)=0 := by rw [sum_neg_distrib,hsum,neg_zero]
    have hm : -z i ≤ 0 := by
      rw [← hsum']
      exact single_le_sum (fun j _ => neg_nonneg.mpr (hn j)) (mem_univ i)
    omega
  obtain ⟨i,hi⟩ := hz
  exact hi (he i)

end IntegerLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_ComputedPivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def positiveSet {n : ℕ} (z : Fin n → ℤ) : Finset (Fin n) :=
  univ.filter (fun i => 0 < z i)

theorem positiveSet_nonempty {n : ℕ} (z : Fin n → ℤ)
    (hsum : ∑ i, z i=0) (hne : ∃ i, z i ≠ 0) : (positiveSet z).Nonempty := by
  obtain ⟨i,hi⟩ := positive_entry hsum hne
  exact ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩⟩

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GramDependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix

variable {R C : Type} [Fintype R] [Fintype C] [DecidableEq C]

theorem gram_det_ne_zero (A : Matrix R C ℤ)
    (hi : LinearIndependent ℚ (fun c => fun r => (A r c:ℚ))) :
    (A.transpose*A).det ≠ 0 := by
  intro hz
  obtain ⟨v,hv,hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  have hzero : A*ᵥv=0 := by
    have hh := congrArg (dotProduct v) hker
    rw [← mulVec_mulVec,dotProduct_mulVec,dotProduct_zero,vecMul_transpose,
      dotProduct_self_eq_zero] at hh
    exact hh
  have hlin : Function.Injective ((fun r c => (A r c:ℚ)) *ᵥ ·) :=
    Matrix.mulVec_injective_iff.mpr hi
  have hcast : (fun r c => (A r c:ℚ))*ᵥ(fun c => (v c:ℚ))=0 := by
    ext r
    have hh := congrFun hzero r
    change (∑ c, A r c*v c)=0 at hh
    change (∑ c, (A r c:ℚ)*(v c:ℚ))=0
    exact_mod_cast hh
  have hvQ := hlin (hcast.trans (mulVec_zero _).symm)
  apply hv
  ext c
  have hh := congrFun hvQ c
  change (v c:ℚ)=0 at hh
  change v c=0
  exact_mod_cast hh

theorem gram_span_relation (A : Matrix R C ℤ) (w : R → ℤ)
    (hi : LinearIndependent ℚ (fun c => fun r => (A r c:ℚ)))
    (hc : (fun r => (w r:ℚ)) ∈ Submodule.span ℚ (Set.range (fun c => fun r => (A r c:ℚ)))) :
    let B := A.transpose*A
    let z := B.cramer (A.transpose*ᵥw)
    ∀ r, (A*ᵥz) r=B.det*w r := by
  let AQ : Matrix R C ℚ := fun r c => A r c
  have hc' : (fun r => (w r:ℚ)) ∈ LinearMap.range AQ.mulVecLin := by
    rwa [Matrix.range_mulVecLin]
  obtain ⟨x,hx⟩ := hc'
  change AQ*ᵥx=(fun r => (w r:ℚ)) at hx
  let B := A.transpose*A
  let z := B.cramer (A.transpose*ᵥw)
  have hz := Matrix.mulVec_cramer B (A.transpose*ᵥw)
  have hdet : B.det ≠ 0 := gram_det_ne_zero A hi
  have hB : Function.Injective ((fun c d => (B c d:ℚ))*ᵥ ·) := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    change IsUnit (((Int.castRingHom ℚ).mapMatrix B).det)
    rw [← RingHom.map_det (Int.castRingHom ℚ)]
    apply isUnit_iff_ne_zero.mpr
    change (B.det:ℚ) ≠ 0
    exact_mod_cast hdet
  have hBcast : (fun c d => (B c d:ℚ))=AQ.transpose*AQ := by
    exact Matrix.map_mul (L:=A.transpose) (M:=A) (f:=Int.castRingHom ℚ)
  have hzQ : (AQ.transpose*AQ)*ᵥ(fun c => (z c:ℚ))=(B.det:ℚ) •
      (AQ.transpose*ᵥ(fun r => (w r:ℚ))) := by
    rw [← hBcast]
    ext c
    have hh := congrFun hz c
    simp only [mulVec,dotProduct,Pi.smul_apply,smul_eq_mul] at hh ⊢
    change (∑ d, (B c d:ℚ)*(z d:ℚ))=(B.det:ℚ)*∑ r, (A r c:ℚ)*(w r:ℚ)
    change (∑ d, B c d*z d)=B.det*∑ r, A r c*w r at hh
    exact_mod_cast hh
  have he : (fun c => (z c:ℚ))=(B.det:ℚ) • x := by
    apply hB
    change ((fun c d => (B c d:ℚ))*ᵥ(fun c => (z c:ℚ))) =
      (fun c d => (B c d:ℚ))*ᵥ((B.det:ℚ) • x)
    rw [hBcast,hzQ,mulVec_smul,← mulVec_mulVec,hx]
  change ∀ r, (A*ᵥz) r=B.det*w r
  intro r
  have heq : (AQ*ᵥ(fun c => (z c:ℚ))) r=(B.det:ℚ)*(w r:ℚ) := by
    rw [he,mulVec_smul,hx]
    rfl
  simp only [mulVec,dotProduct,AQ] at heq ⊢
  exact_mod_cast heq

end MetricKMedian.Compression

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_BoundFreeCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

theorem exists_feature_bound {n d : ℕ} (v : Fin n → Fin d → ℤ) :
    ∃ L : ℕ, ∀ i j, |v i j| ≤ (2:ℤ)^L := by
  let L := ∑ i, ∑ j, (v i j).natAbs
  refine ⟨L,?_⟩
  intro i j
  have h1 : (v i j).natAbs ≤ ∑ j, (v i j).natAbs :=
    single_le_sum (f:=fun (j : Fin d) => (v i j).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ j)
  have h2 : (∑ j, (v i j).natAbs) ≤ L :=
    single_le_sum (f:=fun (i : Fin n) => ∑ j, (v i j).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)
  have hn : (v i j).natAbs ≤ L := h1.trans h2
  have hh := hn.trans (Nat.lt_two_pow_self (n:=L)).le
  have hh' : ((v i j).natAbs:ℤ) ≤ (2:ℤ)^L := by exact_mod_cast hh
  simpa only [Int.natCast_natAbs] using hh'

theorem exists_rational_feature_bound {n d : ℕ} (v : Fin n → Fin d → ℚ) :
    ∃ L : ℕ, (∀ i j, |(v i j).num| ≤ (2:ℤ)^L) ∧
      (∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) := by
  obtain ⟨A,hA⟩ := exists_feature_bound (fun i j => (v i j).num)
  obtain ⟨B,hB⟩ := exists_feature_bound (fun i j => ((v i j).den:ℤ))
  refine ⟨max A B,fun i j => (hA i j).trans ?_,fun i j => ?_⟩
  · exact pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
  · exact (le_abs_self _).trans ((hB i j).trans
      (pow_le_pow_right₀ (by norm_num) (le_max_right _ _)))

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RepresentativeGeometry
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
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RepresentativeBundles
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
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalBundleGeometry
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
-- module Solutions.OAIQ053_KM.KMedian_Rounding_MarginalRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.MarginalRounding

variable {I : Type*} [Fintype I]

noncomputable def fractional (p : I → ℝ) : Finset I :=
  Finset.univ.filter (fun i => 0 < p i ∧ p i < 1)

@[simp] theorem mem_fractional (p : I → ℝ) (i : I) :
    i ∈ fractional p ↔ 0 < p i ∧ p i < 1 := by simp [fractional]

theorem nonfractional_integral {p : I → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {i : I} (hi : i ∉ fractional p) : p i=0 ∨ p i=1 := by
  simp only [mem_fractional, not_and_or, not_lt] at hi
  rcases hi with hi | hi
  · exact Or.inl (le_antisymm hi (hp i))
  · exact Or.inr (le_antisymm (hp1 i) hi)

end MetricKMedian.MarginalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_WeightedRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.WeightedRounding

variable {I : Type*} [Fintype I] [DecidableEq I]
open MarginalRounding

noncomputable def sign (i j : I) (r : ℝ) (k : I) : ℝ :=
  (if k=i then 1 else 0)-(if k=j then r else 0)
noncomputable def move (p : I → ℝ) (i j : I) (r t : ℝ) : I → ℝ :=
  fun k => p k+t*sign i j r k
noncomputable def up (p : I → ℝ) (i j : I) (r : ℝ) := min (1-p i) (p j/r)
noncomputable def down (p : I → ℝ) (i j : I) (r : ℝ) := min (p i) ((1-p j)/r)

theorem weighted_sum (β p : I → ℝ) {i j : I} (hj : β j ≠ 0) (t : ℝ) :
    (∑ k, β k*move p i j (β i/β j) t k)=∑ k, β k*p k := by
  simp only [move, sign, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  field_simp
  ring

end MetricKMedian.WeightedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparationStars
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
-- module Solutions.OAIQ053_KM.KMedian_Preparation_CoupledGeometry
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
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalWeightedStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalWeightedStep
open Finset
variable {n : ℕ}

abbrev point (p : Vector ℚ n) (i : Fin n) : ℚ := p[i.val]
def realPoint (p : Vector ℚ n) (i : Fin n) : ℝ := (point p i:ℝ)
def fractional (p : Vector ℚ n) : Finset (Fin n) :=
  univ.filter (fun i => 0 < point p i ∧ point p i < 1)

def pair (p : Vector ℚ n) (h : 1 < (fractional p).card) :
    {a : Fin n × Fin n // a.1 ∈ fractional p ∧ a.2 ∈ fractional p ∧ a.1 ≠ a.2} :=
  let F := fractional p
  have hFc : 1 < F.card := h
  have hF : F.Nonempty := card_pos.mp (by omega)
  let i := F.min' hF
  have hi : i ∈ F := min'_mem _ _
  have hE : (F.erase i).Nonempty := by
    rw [← card_pos,card_erase_of_mem hi]
    omega
  let j := (F.erase i).min' hE
  have hj : j ∈ F.erase i := min'_mem _ _
  ⟨(i,j),hi,(mem_erase.mp hj).2,(mem_erase.mp hj).1.symm⟩

def move (p : Vector ℚ n) (i j : Fin n) (r t : ℚ) : Vector ℚ n :=
  Vector.ofFn (fun k => point p k+t*((if k=i then 1 else 0)-(if k=j then r else 0)))

def up (p : Vector ℚ n) (i j : Fin n) (r : ℚ) : ℚ := min (1-point p i) (point p j/r)
def down (p : Vector ℚ n) (i j : Fin n) (r : ℚ) : ℚ := min (point p i) ((1-point p j)/r)

@[simp] theorem real_move (p : Vector ℚ n) (i j : Fin n) (r t : ℚ) :
    realPoint (move p i j r t)=WeightedRounding.move (realPoint p) i j (r:ℝ) (t:ℝ) := by
  funext k
  simp only [realPoint,point,move,Vector.getElem_ofFn,Fin.eta,WeightedRounding.move,
    WeightedRounding.sign,Rat.cast_add,Rat.cast_mul,Rat.cast_sub]
  split_ifs <;> simp only [Rat.cast_one,Rat.cast_zero]

@[simp] theorem real_up (p : Vector ℚ n) (i j : Fin n) (r : ℚ) :
    (up p i j r:ℝ)=WeightedRounding.up (realPoint p) i j (r:ℝ) := by
  simp only [up,WeightedRounding.up,realPoint,Rat.cast_min,Rat.cast_sub,Rat.cast_one,Rat.cast_div]

@[simp] theorem real_down (p : Vector ℚ n) (i j : Fin n) (r : ℚ) :
    (down p i j r:ℝ)=WeightedRounding.down (realPoint p) i j (r:ℝ) := by
  simp only [down,WeightedRounding.down,realPoint,Rat.cast_min,Rat.cast_sub,Rat.cast_one,Rat.cast_div]

@[simp] theorem real_fractional (p : Vector ℚ n) :
    MarginalRounding.fractional (realPoint p)=fractional p := by
  ext i
  simp only [fractional,mem_filter,mem_univ,true_and,MarginalRounding.mem_fractional,
    realPoint]
  constructor <;> rintro ⟨h0,h1⟩ <;> exact ⟨by exact_mod_cast h0,by exact_mod_cast h1⟩

theorem up_pos (p : Vector ℚ n) (i j : Fin n) (r : ℚ) (hr : 0 < r)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) : 0 < up p i j r := by
  exact lt_min (sub_pos.mpr (mem_filter.mp hi).2.2)
    (div_pos (mem_filter.mp hj).2.1 hr)

theorem down_pos (p : Vector ℚ n) (i j : Fin n) (r : ℚ) (hr : 0 < r)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) : 0 < down p i j r := by
  exact lt_min (mem_filter.mp hi).2.1
    (div_pos (sub_pos.mpr (mem_filter.mp hj).2.2) hr)

def probability (β : Fin n → ℚ) (p : Vector ℚ n) : ℚ :=
  if h : 1 < (fractional p).card then
    let a := pair p h
    let r := β a.val.1/β a.val.2
    down p a.val.1 a.val.2 r/(up p a.val.1 a.val.2 r+down p a.val.1 a.val.2 r)
  else 0

def endpoint (β : Fin n → ℚ) (p : Vector ℚ n) (b : Fin 2) : Vector ℚ n :=
  if h : 1 < (fractional p).card then
    let a := pair p h
    let r := β a.val.1/β a.val.2
    move p a.val.1 a.val.2 r (if b=0 then up p a.val.1 a.val.2 r else -down p a.val.1 a.val.2 r)
  else p

theorem probability_unit (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i) (p : Vector ℚ n) :
    0 ≤ probability β p ∧ probability β p ≤ 1 := by
  unfold probability
  split_ifs with h
  · let a := pair p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := div_pos (hβ _) (hβ _)
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    exact ⟨(div_pos hd (add_pos hu hd)).le,(div_le_one (add_pos hu hd)).mpr (by linarith)⟩
  · exact ⟨le_rfl,by norm_num⟩

end MetricKMedian.RationalWeightedStep
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalSignedStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalSignedStep
open Finset RationalWeightedStep
variable {n : ℕ}

def pairs (u : Fin n → ℚ) (p : Vector ℚ n) : Finset (Fin (n*n)) :=
  univ.filter (fun z => let a := finProdFinEquiv.symm z;
    a.1∈fractional p ∧ a.2∈fractional p ∧ a.1≠a.2 ∧ 0<u a.1*u a.2)

def Active (u : Fin n → ℚ) (p : Vector ℚ n) : Prop := (pairs u p).Nonempty
instance instDecidableActive (u : Fin n → ℚ) (p : Vector ℚ n) : Decidable (Active u p) :=
  inferInstanceAs (Decidable (pairs u p).Nonempty)

def pair (u : Fin n → ℚ) (p : Vector ℚ n) (h : Active u p) :
    {a : Fin n × Fin n // a.1∈fractional p ∧ a.2∈fractional p ∧
      a.1≠a.2 ∧ 0<u a.1*u a.2} :=
  ⟨finProdFinEquiv.symm ((pairs u p).min' h), by
    have hh := min'_mem (pairs u p) h
    exact (mem_filter.mp hh).2⟩

theorem pair_ratio_pos (u : Fin n → ℚ) (p : Vector ℚ n) (h : Active u p) :
    0<u (pair u p h).val.1/u (pair u p h).val.2 := by
  rcases mul_pos_iff.mp (pair u p h).property.2.2.2 with h | h
  · exact div_pos h.1 h.2
  · exact div_pos_of_neg_of_neg h.1 h.2

theorem pair_right_ne (u : Fin n → ℚ) (p : Vector ℚ n) (h : Active u p) :
    u (pair u p h).val.2≠0 := by
  intro hz
  have hh := (pair u p h).property.2.2.2
  rw [hz,mul_zero] at hh
  exact lt_irrefl _ hh

theorem inactive (u : Fin n → ℚ) (p : Vector ℚ n) (h : ¬Active u p) :
    ∀ i∈fractional p, ∀ j∈fractional p, i≠j → ¬0<u i*u j := by
  intro i hi j hj hij hs
  apply h
  refine ⟨finProdFinEquiv (i,j),?_⟩
  simp only [pairs,mem_filter,mem_univ,true_and,Equiv.symm_apply_apply]
  exact ⟨hi,hj,hij,hs⟩

def probability (β : Fin n → ℚ) (p : Vector ℚ n) : ℚ :=
  if h : Active β p then
    let a := pair β p h
    let r := β a.val.1/β a.val.2
    down p a.val.1 a.val.2 r/(up p a.val.1 a.val.2 r+down p a.val.1 a.val.2 r)
  else 0

def endpoint (β : Fin n → ℚ) (p : Vector ℚ n) (b : Fin 2) : Vector ℚ n :=
  if h : Active β p then
    let a := pair β p h
    let r := β a.val.1/β a.val.2
    move p a.val.1 a.val.2 r (if b=0 then up p a.val.1 a.val.2 r else -down p a.val.1 a.val.2 r)
  else p

theorem probability_unit (β : Fin n → ℚ) (p : Vector ℚ n) :
    0 ≤ probability β p ∧ probability β p ≤ 1 := by
  unfold probability
  split_ifs with h
  · let a := pair β p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := pair_ratio_pos β p h
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    exact ⟨(div_pos hd (add_pos hu hd)).le,(div_le_one (add_pos hu hd)).mpr (by linarith)⟩
  · exact ⟨le_rfl,by norm_num⟩

end MetricKMedian.RationalSignedStep
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseWeightedPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedPartial
open Finset RationalWeightedStep
variable {n : ℕ}

def features (p : Vector ℚ n) (a : Fin (n+n*n)) : ℚ :=
  Sum.elim (point p) (fun ij : Fin (n*n) =>
    point p (finProdFinEquiv.symm ij).1*point p (finProdFinEquiv.symm ij).2)
    (finSumFinEquiv.symm a)

@[simp] theorem features_single (p : Vector ℚ n) (i : Fin n) :
    features p (finSumFinEquiv (Sum.inl i))=point p i := by
  simp only [features,Equiv.symm_apply_apply,Sum.elim_inl]

@[simp] theorem features_pair (p : Vector ℚ n) (i j : Fin n) :
    features p (finSumFinEquiv (Sum.inr (finProdFinEquiv (i,j))))=point p i*point p j := by
  simp only [features,Equiv.symm_apply_apply,Sum.elim_inr]

end MetricKMedian.SparseWeightedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

noncomputable def mass {I : Type*} (g : ℝ) (S : Finset I) : ℝ := g * S.card

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBernoulliFeatures
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
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBernoulliSubsets
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
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparsePhysicalBatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparsePhysicalBatch
open Finset
variable {n : ℕ}

def balanced (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n)) (ω : Fin n → Bool) : Finset (Fin n) :=
  (univ.filter (fun e => ω e=true ∧ ∀ f∈C e, ω f=false)) ∩ Z

def unbalanced (Z : Finset (Fin n)) (ω : Fin n → Bool) : Finset (Fin n) :=
  univ.filter (fun e => ω e=true ∧ e∉Z)

end MetricKMedian.SparsePhysicalBatch

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaperAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset

variable {I : Type*} [Fintype I]

def upper (d : I → ℚ) : ℚ := 1+∑ i, (d i)⁻¹

def breakpoints (P : ℚ) (d : I → ℚ) : Finset ℚ :=
  insert 0 (insert (upper d) ((univ.image (fun i => (1-P)/d i)) ∪ (univ.image (fun i => 1/d i))))

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaperZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I] [LinearOrder I]

def extend (own Z : Finset I) (Δ : ℕ) : Finset I :=
  own ∪ (((Z \ own).sort (· ≤ ·)).take (Δ-own.card)).toFinset

def zeroSources (d : I → ℚ) : Finset I := univ.filter (fun i => d i=0)

def zeroSelection (d : I → ℚ) (own : Finset I) (Δ : ℕ) : Finset I :=
  extend own (zeroSources d) Δ

def zeroMarginal (d : I → ℚ) (own : Finset I) (Δ : ℕ) (i : I) : ℚ :=
  if i ∈ zeroSelection d own Δ then 1 else 0

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaperData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I] [LinearOrder I]

def rationalColocatedMass (g : ℚ) (d : I → ℚ) : ℚ :=
  ∑ i, if d i=0 then g else 0

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalLastFraction
attribute [-simp] _root_.OAI.MetricKMedian.SparseWeightedPartial.features_pair _root_.OAI.MetricKMedian.SparseWeightedPartial.features_single
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalLastFraction
open Finset RationalWeightedStep
variable {n : ℕ}

def pick (p : Vector ℚ n) (h : (fractional p).Nonempty) : Fin n := (fractional p).min' h

theorem pick_mem (p : Vector ℚ n) (h : (fractional p).Nonempty) : pick p h ∈ fractional p :=
  min'_mem _ _

def probability (p : Vector ℚ n) : ℚ :=
  if h : (fractional p).Nonempty then point p (pick p h) else 0

def endpoint (p : Vector ℚ n) (b : Fin 2) : Vector ℚ n :=
  if h : (fractional p).Nonempty then
    Vector.ofFn (fun k => if k=pick p h then (if b=0 then 1 else 0) else point p k)
  else p

theorem probability_unit (p : Vector ℚ n) : 0 ≤ probability p ∧ probability p ≤ 1 := by
  unfold probability
  split_ifs with h
  · have hh := (mem_filter.mp (pick_mem p h)).2
    exact ⟨hh.1.le,hh.2.le⟩
  · exact ⟨le_rfl,by norm_num⟩

end MetricKMedian.RationalLastFraction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCardinalRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCardinalRounding
open Finset RationalWeightedStep
variable {n : ℕ}

def selected (q : Vector ℚ n) : Finset (Fin n) := univ.filter (fun i => point q i=1)

end MetricKMedian.SparseCardinalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseTargetSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseTargetSubset
open Finset RationalWeightedStep
variable {n : ℕ}

def initial (D : Finset (Fin n)) (q : ℚ) : Vector ℚ n :=
  Vector.ofFn (fun i => if i∈D then q else 0)

@[simp] theorem point_initial (D : Finset (Fin n)) (q : ℚ) (i : Fin n) :
    point (initial D q) i=(if i∈D then q else 0) := by
  simp only [initial,point,Vector.getElem_ofFn,Fin.eta]

end MetricKMedian.SparseTargetSubset
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPreparation
open Finset
open RationalWeightedStep (point fractional)
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
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGridRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGridRounding
open Finset
open RationalWeightedStep (point)
variable {n : ℕ}

def base (q : Fin n → ℚ) (i : Fin n) : ℕ := ⌊q i⌋₊
def fraction (q : Fin n → ℚ) : Vector ℚ n := Vector.ofFn (fun i => q i-(base q i:ℚ))
def count (q : Fin n → ℚ) (p : Vector ℚ n) (i : Fin n) : ℕ :=
  base q i+if point p i=1 then 1 else 0

theorem fraction_unit (q : Fin n → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∀ i, 0 ≤ point (fraction q) i ∧ point (fraction q) i ≤ 1 := by
  intro i
  simp only [point,fraction,Vector.getElem_ofFn]
  constructor
  · exact sub_nonneg.mpr (Nat.floor_le (hq i))
  · have hh := Nat.lt_floor_add_one (q i)
    dsimp only [base]
    linarith only [hh]

end MetricKMedian.SparseGridRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterCounts
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

def activationCount (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (z : State n m) (e : Fin m) (i : Fin n) : ℕ :=
  (if i∈D e then base q e else 0)+(if i∈z.2.1 e then 1 else 0)

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCountFeatures
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
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseRescaledInner
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

end MetricKMedian.SparseRescaledInner
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparsePreparedLaw
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
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedDataOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.SparsePrepared.Program
abbrev QRow := List ℚ
abbrev BTable := List (List Bool)
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalSupplierPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                   
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars
variable {f n : ℕ}

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

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSupplierSupport
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
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalSupplierScan
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
-- module Solutions.OAIQ053_KM.KMedian_Process_CountListOperations
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
end MetricKMedian.SparseCounts.ListOperation
end

end OAI
end


