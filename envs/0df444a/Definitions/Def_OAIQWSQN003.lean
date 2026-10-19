-- Prove2me | Definitions.Def_OAIQWSQN003
-- name    : OAIQWSQN003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T20:58:25.685015+00:00
-- url     : https://prove2.me/theorems/af50f5f1-65fe-471b-869f-0a9935355a72
-- title:
--   OpenAI separable quotient split: definitions bundle OAIQWSQN003
-- statement:
--   One of the definitions bundles of the split of OpenAI's proof of `OAI.SeparableQuotient.negative_main`. Under the continuum hypothesis, neither the real nor the complex separable quotient assertion holds. The bundle holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/SeparableQuotients` (OpenAI, *Relative independence of the separable quotient problem*, OpenAI Math Release, September 23, 2026, result family 323, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. It also holds the lemmas these definitions use in their bodies, and OpenAI's `@[simp]` lemmas about them. Each module section starts by removing the instances `SubfieldClass.toSubringClass` and `SubringClass.toSubsemiringClass` locally, which speeds up instance search and changes nothing that is proved.
--
--   The definitions of the published statement (`CH`, `HasSeparableQuotient`, `SQ`) come from the published bundle `Def_SeparableQuotientNegative`. It also imports the bundles `OAIQWSQN000`, `OAIQWSQN001` of this split.
--
--   Modules: `BlockEstimates`, `BranchPaths`, `Complexification`, `CoordinateDual`, `CoordinatePredual`, `ExactPairs`, `FiniteLp`, `MarkedEstimates`, `NormCompletion`, `NormingBounds`, `NormingOperations`, `NormingTrees`, `Parameters`, `PartitionBlocks`, `PathConvergence`, `PathLimits`, `PathRigidity`, `PathStabilization`, `PrefixNormers`, `StoppedCharges`, `TailBlocks`, `TreeBounds`, `TreeCharges`, `WindowCharges`, `WindowEstimates`, `WindowThinning`.
-- source:
--   OpenAI, Relative independence of the separable quotient problem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 323; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-independence-of-the-separable-quotient-problem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/SeparableQuotients at commit adc7f12

import Mathlib
import Theorems.Thm_OAI_SeparableQuotient_Singular_StrictlySingular_exists_small_restriction
import Definitions.Def_OAIQWSQN000
import Definitions.Def_OAIQWSQN001

section
-- module Solutions.OAIQW_SeparableQuotient.PrefixNormers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient
open Set Metric
open scoped BigOperators Topology
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace PrefixNormers

attribute [local instance] OAI.SeparableQuotient.prefixDualNormedGroup
attribute [local instance] OAI.SeparableQuotient.prefixDualNormedSpace
variable {f : ℕ → StrongDual 𝕜 X} (H : PrefixNormers f)

include H

omit H in
noncomputable def basisVector (f : ℕ → StrongDual 𝕜 X) (n : ℕ) : closedSpan f :=
  ⟨f n, Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self n))⟩

end PrefixNormers
end SeparableQuotient

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

/- Admissible parameters for the pure s = k + 2 families and mixed s = 2 family, with q = (s + 1) / s. Integer powers avoid rounding noninteger powers. -/
namespace SeparableQuotient.Parameters

open Filter Topology

lemma B_zero (s : ℕ) : B s 0 = 0 := rfl
lemma B_succ (s n : ℕ) : B s (n+1) = B s n + 2*L s n := rfl
lemma t_succ (s n : ℕ) : t s (n+1) =
    t s n+(B s (n+1)+1)*(d (n+1)+1)+1+d (n+1)+(d (n+1))^2 := rfl

lemma d_pos (n : ℕ) : 0 < d n := by simp [d]

lemma t_bound (s n : ℕ) : (B s n+1)*(d n+1)+1+d n ≤ t s n := by
  cases n with
  | zero => simp [t, B, state]
  | succ n => rw [t_succ]; omega

lemma t_square (s n : ℕ) : (d n)^2 ≤ t s n := by
  cases n with
  | zero => simp [t, state]
  | succ n => rw [t_succ]; omega

lemma t_pos (s n : ℕ) : 0 < t s n := by
  have := t_bound s n
  omega

lemma t_strict (s : ℕ) : StrictMono (t s) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [t_succ]
  omega

lemma L_strict {s : ℕ} (hs : 2 ≤ s) : StrictMono (L s) := by
  intro i j hij
  apply Nat.pow_lt_pow_right (by omega : 1 < 2)
  exact Nat.mul_lt_mul_of_pos_left (t_strict s hij) (by positivity)

lemma m_strict {s : ℕ} (_hs : 2 ≤ s) : StrictMono (m s) := by
  intro i j hij
  apply Nat.pow_lt_pow_right (by omega : 1 < 2)
  have htt := (t_strict s).monotone hij.le
  have hmul := Nat.mul_le_mul_left ((s-1)*(s+1)) htt
  dsimp [d]
  omega

lemma length_qprime_power (s n : ℕ) :
    (L s n : ℝ) ^ (1/((s:ℝ)+1)) = (2:ℝ)^(s*t s n) := by
  have hs1 : (s:ℝ)+1 ≠ 0 := by positivity
  simp only [L, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  push_cast
  field_simp

lemma ratio_eq {s : ℕ} (hs : 2 ≤ s) (n : ℕ) :
    (L s n : ℝ) / (m s n : ℝ) = (2:ℝ)^((s+1)*t s n) / (2:ℝ)^(d n) := by
  have hsplit : s*(s+1)*t s n = (s-1)*(s+1)*t s n+(s+1)*t s n := by
    calc
      _ = ((s-1)+1)*(s+1)*t s n := by congr 2; omega
      _ = _ := by ring
  simp only [L, m, Nat.cast_pow, Nat.cast_ofNat]
  rw [hsplit, pow_add, pow_add]
  exact mul_div_mul_left _ _ (by positivity)

lemma depth_integer_bound (s n : ℕ) :
    (1+B s n)^(d n) * (1+B s n+2^(s*t s n)) * 2^(d n) ≤ 2^((s+1)*t s n) := by
  let b := B s n
  let u := t s n
  let e := d n
  have ha : 1+b ≤ 2^(b+1) := by
    have h := @Nat.lt_two_pow_self (b+1)
    omega
  have ha1 : 1 ≤ 2^(b+1) := Nat.one_le_pow _ _ (by omega)
  have hc1 : 1 ≤ 2^(s*u) := Nat.one_le_pow _ _ (by omega)
  have hsum : 1+b+2^(s*u) ≤ 2^(b+1+s*u+1) := by
    have hleft : 1+b ≤ 2^(b+1)*2^(s*u) := ha.trans (by nlinarith)
    have hright : 2^(s*u) ≤ 2^(b+1)*2^(s*u) := by nlinarith
    rw [pow_succ, pow_add]
    omega
  have hp := Nat.pow_le_pow_left ha e
  have hstep : (1+b)^e * (1+b+2^(s*u)) * 2^e ≤
      2^((b+1)*e) * 2^(b+1+s*u+1) * 2^e := by
    have hp' : (1+b)^e ≤ 2^((b+1)*e) := by simpa only [pow_mul] using hp
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hp' hsum)
  calc
    _ ≤ 2^((b+1)*e) * 2^(b+1+s*u+1) * 2^e := hstep
    _ = 2^((b+1)*e+(b+1+s*u+1)+e) := by rw [← pow_add, ← pow_add]
    _ ≤ 2^((s+1)*u) := by
      apply Nat.pow_le_pow_right (by omega : 0 < 2)
      have h := t_bound s n
      change (b+1)*(e+1)+1+e ≤ u at h
      nlinarith

lemma depth_bound {s : ℕ} (hs : 2 ≤ s) (n : ℕ) :
    (1+(B s n:ℝ))^(d n) *
      (1+(B s n:ℝ)+(L s n:ℝ)^(1/((s:ℝ)+1))) ≤ (L s n:ℝ)/(m s n:ℝ) := by
  rw [length_qprime_power, ratio_eq hs]
  apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^(d n))).mpr
  exact_mod_cast depth_integer_bound s n

lemma depth_theta_bound {s : ℕ} (hs : 2 ≤ s) (n : ℕ) :
    (1/8:ℝ)^(d n) ≤ theta s n := by
  rw [theta_eq hs]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) _

lemma theta_tail {s : ℕ} (hs : 2 ≤ s) (J : ℕ) :
    ∑' n, theta s (J+n) ≤ 4*theta s J := by
  have hgeom : HasSum (fun n : ℕ => (1/2:ℝ)^n) 2 := by
    convert hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1) using 1; norm_num
  have htail : HasSum (fun n => theta s (J+n)) (2*theta s J) := by
    have h' : HasSum (fun n => theta s (J+n)) (theta s J*2) :=
      (hgeom.mul_left (theta s J)).congr_fun (by
        intro n
        rw [theta_eq hs, theta_eq hs, d, d]
        rw [show J+n+11 = (J+11)+n by omega, pow_add])
    simpa only [mul_comm] using h'
  rw [htail.tsum_eq]
  have hpos : 0 ≤ theta s J := by rw [theta_eq hs]; positivity
  linarith

lemma d_div_t_tendsto (s : ℕ) :
    Tendsto (fun n => (d n:ℝ)/(t s n:ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by positivity)
    (g := fun n => 1/(d n:ℝ))
  · intro n
    have hd : 0 < (d n:ℝ) := by exact_mod_cast d_pos n
    have ht : 0 < (t s n:ℝ) := by exact_mod_cast t_pos s n
    apply (div_le_div_iff₀ ht hd).mpr
    simpa only [one_mul, ← sq] using (show (d n:ℝ)^2 ≤ (t s n:ℝ) by exact_mod_cast t_square s n)
  · exact (tendsto_add_atTop_iff_nat 11).mpr tendsto_one_div_atTop_nhds_zero_nat

lemma log_ratio_eq {s : ℕ} (hs : 2 ≤ s) (n : ℕ) :
    Real.log ((L s n:ℝ)/(m s n:ℝ)) / Real.log (L s n:ℝ) =
      1/(s:ℝ) - ((d n:ℝ)/(t s n:ℝ))/((s:ℝ)*((s:ℝ)+1)) := by
  have hs0 : (s:ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have hs1 : (s:ℝ)+1 ≠ 0 := by positivity
  have ht : (t s n:ℝ) ≠ 0 := by exact_mod_cast (t_pos s n).ne'
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne'
  rw [ratio_eq hs, Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  simp only [L, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  push_cast
  field_simp

lemma parameter_growth {s : ℕ} (hs : 2 ≤ s) :
    Tendsto (fun n => Real.log ((L s n:ℝ)/(m s n:ℝ)) / Real.log (L s n:ℝ))
      atTop (𝓝 (1/(s:ℝ))) := by
  simp_rw [log_ratio_eq hs]
  convert tendsto_const_nhds.sub ((d_div_t_tendsto s).div_const ((s:ℝ)*((s:ℝ)+1))) using 1
  simp

lemma ratio_tendsto_atTop {s : ℕ} (hs : 2 ≤ s) :
    Tendsto (fun n => (L s n:ℝ)/(m s n:ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n => (2:ℝ)^n)
    (fun n => ?_) (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  rw [ratio_eq hs]
  apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^(d n))).mpr
  rw [← pow_add]
  apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
  have h := t_bound s n
  have hd : n ≤ d n := by simp [d]
  have hsd : 1 ≤ s+1 := by omega
  nlinarith

end SeparableQuotient.Parameters

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NormingOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open scoped Classical

lemma stage_neg {base : Set Array} (f : Family) (hbase : ∀ x ∈ base, -x ∈ base) :
    ∀ n x, x ∈ stage base f n → -x ∈ stage base f n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    intro x hx
    rcases hx with (hx | ⟨e, rfl, he⟩) | ⟨e, rfl, he⟩
    · exact Or.inl (Or.inl (ih x hx))
    · exact Or.inl (Or.inr ⟨e.neg, e.neg_value, fun i => ih _ (he i)⟩)
    · exact Or.inr ⟨e.neg, e.neg_value, he⟩

lemma pure_neg (k : ℕ) (x : Array) (hx : x ∈ Pure k) : -x ∈ Pure k := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  refine Set.mem_iUnion.mpr ⟨n, stage_neg (.pure k) ?_ n x hn⟩
  intro y hy
  rcases hy with rfl | ⟨a, ha, rfl | rfl⟩
  · exact Or.inl neg_zero
  · exact Or.inr ⟨a, ha, Or.inr (by simp)⟩
  · exact Or.inr ⟨a, ha, Or.inl (by simp)⟩

lemma full_neg (x : Array) (hx : x ∈ Full) : -x ∈ Full := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  refine Set.mem_iUnion.mpr ⟨n, stage_neg .mixed ?_ n x hn⟩
  intro y hy
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
  exact Set.mem_iUnion.mpr ⟨k, pure_neg k y hk⟩

end SeparableQuotient.Norming

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.FiniteLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open scoped ENNReal NNReal Classical
open LpFinite

lemma Family.theta_nonneg (f : Family) (j : ℕ) : 0 ≤ f.theta j := by
  rw [Family.theta, Parameters.theta_eq f.s_ge_two]; positivity

end SeparableQuotient.Norming

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NormCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

/- The completion of c₀₀ under a bounded rational norming set. -/
namespace SeparableQuotient.NormConstruction
open scoped Topology ENNReal
open Filter
universe u
variable {Γ : Type u}

namespace NormingSet
variable (K : NormingSet Γ)

lemma finiteMap_injective : Function.Injective K.finiteMap := by
  intro x y h
  ext a
  simpa only [K.finiteMap_coordinate] using
    congrArg (fun z : K.BoundedSpace => z ⟨Finsupp.single a 1, K.coordinate_mem a⟩) h

end NormingSet
end SeparableQuotient.NormConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.CoordinateDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Topology Classical
universe u
variable {Γ : Type u} (K : NormingSet Γ)

lemma includeFinite_injective : Function.Injective K.includeFinite := by
  intro x y h
  exact K.finiteMap_injective (congrArg Subtype.val h)

attribute [local instance] OAI.SeparableQuotient.NormConstruction.NormingSet.dualNormedGroup
attribute [local instance] OAI.SeparableQuotient.NormConstruction.NormingSet.dualNormedSpace
lemma functional_mem_predual (f : K.carrier) : K.functional f ∈ K.predual := by
  rw [K.functional_eq_sum]
  exact Submodule.sum_mem _ (fun a _ =>
    Submodule.smul_mem _ _ (K.coordinate_mem_predual a))

attribute [local instance] OAI.SeparableQuotient.NormConstruction.NormingSet.predualDualNormedGroup
attribute [local instance] OAI.SeparableQuotient.NormConstruction.NormingSet.predualDualNormedSpace
lemma norm_evaluation (x : K.Space) : ‖K.evaluation x‖ = ‖x‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
    intro g
    exact (g.val.le_opNorm x).trans_eq (mul_comm _ _)
  · change ‖x.val‖ ≤ ‖K.evaluation x‖
    apply lp.norm_le_of_forall_le (f := x.val) (norm_nonneg (K.evaluation x))
    intro f
    let g : K.predual := ⟨K.functional f, K.functional_mem_predual f⟩
    calc
      |K.functional f x| = ‖K.evaluation x g‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖K.evaluation x‖ * ‖g‖ := (K.evaluation x).le_opNorm g
      _ ≤ ‖K.evaluation x‖ * 1 :=
        mul_le_mul_of_nonneg_left (K.norm_functional_le f) (norm_nonneg (K.evaluation x))
      _ = _ := mul_one _

def evaluationIsometry : K.Space →ₗᵢ[ℝ] StrongDual ℝ K.predual where
  toLinearMap := K.evaluation.toLinearMap
  norm_map' := K.norm_evaluation

end SeparableQuotient.NormConstruction.NormingSet

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Topology Classical
universe u
variable {Γ : Type u} (K : NormingSet Γ)

attribute [local instance] OAI.SeparableQuotient.NormConstruction.NormingSet.dualNormedGroup'
attribute [local instance] OAI.SeparableQuotient.NormConstruction.NormingSet.dualNormedSpace'
lemma norm_rationalPredual_le (f : Γ →₀ ℚ) (hf : f ∈ K.carrier) :
    ‖K.rationalPredual f‖ ≤ 1 := by
  change ‖(K.rationalPredual f).val‖ ≤ 1
  rw [K.rationalPredual_eq_functional ⟨f, hf⟩]
  exact K.norm_functional_le ⟨f, hf⟩

end SeparableQuotient.NormConstruction.NormingSet

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Classical
universe u
variable {Γ : Type u} (K : NormingSet Γ)

attribute [local instance] OAI.SeparableQuotient.NormConstruction.NormingSet.dualNormedGroup''
attribute [local instance] OAI.SeparableQuotient.NormConstruction.NormingSet.dualNormedSpace''
lemma norm_le_of_evaluateArray (x : K.Space) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ f ∈ K.carrier, |K.evaluateArray x f| ≤ r) : ‖x‖ ≤ r := by
  change ‖x.val‖ ≤ r
  apply lp.norm_le_of_forall_le hr
  intro f
  change ‖K.functional f x‖ ≤ r
  simpa only [K.evaluateArray_eq_functional x f, Real.norm_eq_abs] using h f.val f.property

end SeparableQuotient.NormConstruction.NormingSet

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Classical
universe u
variable {Γ : Type u} (K : NormingSet Γ)

lemma evaluateArray_filter_of_zero (x : K.Space) (A : Set Γ)
    (hx : ∀ a ∉ A, K.coordinate a x = 0) (f : Γ →₀ ℚ) :
    K.evaluateArray x (f.filter (· ∈ A)) = K.evaluateArray x f := by
  rw [K.evaluateArray_eq, K.evaluateArray_eq]
  simp only [Finsupp.support_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ A
  · simp [ha]
  · simp [ha, hx a ha]

end SeparableQuotient.NormConstruction.NormingSet

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.CoordinatePredual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction
open scoped Classical

instance EContinuousAdd : ContinuousAdd E := ETopologicalAdd.toContinuousAdd

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open scoped Classical

/-- Every finite successive family of existing normers has its prescribed
Type I average in the same actual family. -/
lemma pure_typeI_mem (k : ℕ) (e : TypeI (.pure k))
    (h : ∀ i, e.child i ∈ Pure k) : e.value ∈ Pure k := by
  classical
  choose n hn using (fun i => Set.mem_iUnion.mp (h i))
  let N := Finset.univ.sup n
  have hn' : ∀ i, e.child i ∈ stage (pureBase k) (.pure k) N := by
    intro i
    exact stage_mono _ _ (Finset.le_sup (f := n) (Finset.mem_univ i)) (hn i)
  exact Set.mem_iUnion.mpr ⟨N+1, Or.inl (Or.inr ⟨e, rfl, hn'⟩)⟩

lemma mixed_typeI_mem (e : TypeI .mixed)
    (h : ∀ i, e.child i ∈ Full) : e.value ∈ Full := by
  classical
  choose n hn using (fun i => Set.mem_iUnion.mp (h i))
  let N := Finset.univ.sup n
  have hn' : ∀ i, e.child i ∈ stage (⋃ k, Pure k) .mixed N := by
    intro i
    exact stage_mono _ _ (Finset.le_sup (f := n) (Finset.mem_univ i)) (hn i)
  exact Set.mem_iUnion.mpr ⟨N+1, Or.inl (Or.inr ⟨e, rfl, hn'⟩)⟩

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

lemma evaluateArray_projection (A : Crop) (x : E) (f : Array) :
    norming.evaluateArray (projection A x) f =
      norming.evaluateArray x (restrict (A.set .mixed) f) :=
  norming.evaluateArray_projection x (A.set .mixed) (cropStable A) f

lemma evaluateArray_crop_of_zero (A : Set Γ) (x : E)
    (hx : ∀ a ∉ A, coordinate a x = 0) (f : Array) :
    norming.evaluateArray x (restrict A f) = norming.evaluateArray x f :=
  norming.evaluateArray_filter_of_zero x A hx f

/-- The full and pure norms coincide on a single color. -/
lemma norm_le_of_pure (k : ℕ) (x : E) (hx : ∀ a, Colors.color a ≠ k → coordinate a x = 0)
    (r : ℝ) (hr : 0 ≤ r) (h : ∀ f ∈ Pure k, |norming.evaluateArray x f| ≤ r) : ‖x‖ ≤ r := by
  apply norming.norm_le_of_evaluateArray x r hr
  intro f hf
  have hb := absConvexHull_min h (absConvex_abs_le (norming.evaluateArray x) r hr)
    (full_color_hull k f hf)
  change |norming.evaluateArray x (restrict (colorSet k) f)| ≤ r at hb
  rwa [evaluateArray_crop_of_zero (colorSet k) x (fun a ha => hx a ha) f] at hb

lemma exists_full_normer (x : E) (r : ℝ) (hr : 0 ≤ r) (hx : r < ‖x‖) :
    ∃ f ∈ Full, r < norming.evaluateArray x f := by
  by_contra h
  push Not at h
  have hb : ‖x‖ ≤ r := norming.norm_le_of_evaluateArray x r hr (by
    intro f hf
    apply abs_le.mpr
    constructor
    · have hn := h (-f) (full_neg f hf)
      simpa only [map_neg, neg_le] using hn
    · exact h f hf)
  exact (not_lt_of_ge hb) hx

lemma exists_pure_normer (k : ℕ) (x : E)
    (hc : ∀ a, Colors.color a ≠ k → coordinate a x = 0)
    (r : ℝ) (hr : 0 ≤ r) (hx : r < ‖x‖) :
    ∃ f ∈ Pure k, r < norming.evaluateArray x f := by
  by_contra h
  push Not at h
  have hb : ‖x‖ ≤ r := norm_le_of_pure k x hc r hr (by
    intro f hf
    apply abs_le.mpr
    constructor
    · have hn := h (-f) (pure_neg k f hf)
      simpa only [map_neg, neg_le] using hn
    · exact h f hf)
  exact (not_lt_of_ge hb) hx

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open scoped Classical

def Family.normers : Family → Set Array
  | .pure k => Pure k
  | .mixed => Full

lemma Family.normers_subset_full (t : Family) : t.normers ⊆ Full := by
  cases t with
  | pure k => exact pure_subset_full k
  | mixed => exact Set.Subset.rfl

lemma Family.typeI_mem (t : Family) (e : TypeI t)
    (h : ∀ i, e.child i ∈ t.normers) : e.value ∈ t.normers := by
  cases t with
  | pure k => exact pure_typeI_mem k e h
  | mixed => exact mixed_typeI_mem e h

lemma Family.exists_large_ratio (t : Family) (R : ℝ) :
    ∃ j, 1 ≤ j ∧ R < (t.L j : ℝ) / (t.m j : ℝ) := by
  obtain ⟨l, hl⟩ := ((Parameters.ratio_tendsto_atTop t.s_ge_two).eventually
    (Filter.eventually_gt_atTop R)).exists
  exact ⟨l+1, by omega, by simpa [Family.L, Family.m] using hl⟩

end SeparableQuotient.Norming

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open scoped Classical
open PathCoding

lemma TypeI.mem_family {f : Family} (e : TypeI f)
    (h : ∀ i, e.child i ∈ f.norming) : e.value ∈ f.norming := by
  obtain ⟨n, hn⟩ := common_stage e.child h
  exact Set.mem_iUnion.mpr ⟨n+1, Or.inl (Or.inr ⟨e, rfl, hn⟩)⟩

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualEGroup8
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualESpace8
lemma norm_pathFunctional_le {f : Family} (P : InfinitePath f) : ‖pathFunctional P‖ ≤ 1 :=
  (exists_pathFunctional P).choose_spec.1

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualEGroup10
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualESpace10
lemma tail_abs_sum_bound {f : Family} {h : ℕ} (P : Fin h → InfinitePath f) (N : ℕ)
    (hN : ∀ c : Fin h → ℝ,
      ‖∑ i, c i • pathTail (P i) N‖ ≤ (∑ i, |c i| ^ f.q) ^ (1/f.q)) (x : E) :
    (∑ i, |pathTail (P i) N x|) ≤ (h : ℝ) ^ (1/f.q) * ‖x‖ := by
  let c : Fin h → ℝ := fun i => RealCoefficients.signChoice (pathTail (P i) N x)
  have hc (i : Fin h) : |c i| = 1 := RealCoefficients.abs_signChoice _
  have hv (i : Fin h) : c i * pathTail (P i) N x = |pathTail (P i) N x| :=
    RealCoefficients.signChoice_mul _
  have he : (∑ i, c i • pathTail (P i) N) x = ∑ i, |pathTail (P i) N x| := by
    simp only [sum_apply, smul_apply, smul_eq_mul, hv]
  calc
    _ = |(∑ i, c i • pathTail (P i) N) x| := by
      rw [he, abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))]
    _ ≤ ‖∑ i, c i • pathTail (P i) N‖ * ‖x‖ :=
      by simpa only [Real.norm_eq_abs] using (∑ i, c i • pathTail (P i) N).le_opNorm x
    _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa only [hc, Real.one_rpow,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using hN c)
      (norm_nonneg _)

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathStabilization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open PathCoding CoherentClosures Filter
open scoped Classical

lemma PrefixValid.support_subset_closure {P : RawPath} {len : ℕ}
    (h : PrefixValid P len) {n : ℕ} (hn : n < len) :
    P.support n ⊆ P.closure n := by
  intro a ha
  exact (rho_le_iff a (P.endpoint n) (P.le_endpoint ha) _ (h.metadata_pos n hn)).mp
    (h.rho_bound n hn a (P.endpoint n) ha (P.endpoint_mem n) (P.le_endpoint ha))

lemma PrefixValid.piece_support_subset_closure {P : RawPath} {len : ℕ}
    (h : PrefixValid P len) {i n : ℕ} (hi : i ≤ n) (hn : n < len) :
    (P.piece i).support ⊆ P.closure n :=
  (P.piece_support_subset hi).trans (h.support_subset_closure hn)

/-- A retained coordinate in a later piece anchors the compressed code in the
actual ordinal labels. This is the finite-prefix version of path rigidity. -/
lemma PrefixValid.piece_eq_of_code_anchor {P Q : RawPath} {len len' i j n : ℕ}
    (hP : PrefixValid P len) (hQ : PrefixValid Q len')
    (hn : n < len) (hn' : n < len') (hij : i < j) (hjn : j ≤ n)
    (hc : P.code n = Q.code n) (a : Γ)
    (ha : a ∈ (P.piece j).support) (ha' : a ∈ Q.closure n) :
    P.piece i = Q.piece i := by
  have hm := (RawPath.code_eq_at hc n le_rfl).2.1
  have haP := hP.piece_support_subset_closure hjn hn ha
  apply position_alignment (a := a) ?_
    (hP.piece_support_subset_closure (hij.le.trans hjn) hn)
    (hQ.piece_support_subset_closure (hij.le.trans hjn) hn')
    (fun x hx => hP.successive i j hij (hjn.trans_lt hn) x hx a ha)
    (RawPath.code_eq_at hc i (hij.le.trans hjn)).2.2
  unfold RawPath.closure at haP ha' ⊢
  rw [hm] at haP ⊢
  exact shared_initial_segment (P.endpoint n) (Q.endpoint n) a (Q.metadata n) haP ha'

/-- Fixed successor weights and arbitrarily late retained coordinates force
stabilization of the entire *uncropped* data, not just coordinatewise limits. -/
lemma finite_paths_stabilize {f : Family} (P : ℕ → FinitePath f)
    (hlen : ∀ i, ∀ᶠ n in atTop, i < (P n).length)
    (hw : ∀ i, ∃ w, ∀ᶠ n in atTop, (P n).raw.weight i = w)
    (ha : ∀ i, ∃ j > i, ∃ a : Γ,
      ∀ᶠ n in atTop, a ∈ ((P n).raw.piece j).support) :
    ∀ i, ∃ d : Array × ℕ × ℕ, ∀ᶠ n in atTop,
      (P n).raw.piece i = d.1 ∧ (P n).raw.weight i = d.2.1 ∧
        (P n).raw.metadata i = d.2.2 := by
  intro i
  obtain ⟨j, hij, a, ha⟩ := ha i
  obtain ⟨w, hw⟩ := hw (j+1)
  have hg := (hlen (j+1)).and (hw.and ha)
  obtain ⟨n₀, hn₀, hw₀, ha₀⟩ := hg.exists
  refine ⟨⟨(P n₀).raw.piece i, (P n₀).raw.weight i, (P n₀).raw.metadata i⟩, ?_⟩
  filter_upwards [hg] with n hn
  have hc : (P n).raw.code j = (P n₀).raw.code j := by
    apply sigma_injective
    rw [← (P n).valid.rule j hn.1, ← (P n₀).valid.rule j hn₀, hn.2.1, hw₀]
  refine ⟨(P n).valid.piece_eq_of_code_anchor (P n₀).valid
    (by omega) (by omega) hij le_rfl hc a hn.2.2
    ((P n₀).valid.piece_support_subset_closure le_rfl (by omega) ha₀), ?_, ?_⟩
  · exact (RawPath.code_eq_at hc i hij.le).1
  · exact (RawPath.code_eq_at hc i hij.le).2.1

lemma raw_support_eq_of_prefix {P Q : RawPath} {n : ℕ}
    (hp : ∀ i ≤ n, P.piece i = Q.piece i) : P.support n = Q.support n := by
  ext a
  simp only [RawPath.mem_support_iff]
  constructor <;> rintro ⟨i, hi, ha⟩
  · exact ⟨i, hi, (hp i hi) ▸ ha⟩
  · exact ⟨i, hi, (hp i hi).symm ▸ ha⟩

lemma raw_code_eq_of_prefix {P Q : RawPath} {n : ℕ}
    (hp : ∀ i ≤ n, P.piece i = Q.piece i)
    (hw : ∀ i ≤ n, P.weight i = Q.weight i)
    (hm : ∀ i ≤ n, P.metadata i = Q.metadata i) : P.code n = Q.code n := by
  have hs := raw_support_eq_of_prefix hp
  have he : P.endpoint n = Q.endpoint n := by
    unfold RawPath.endpoint
    congr 1
  have hc : P.closure n = Q.closure n := by
    simp only [RawPath.closure, he, hm n le_rfl]
  apply congrArg List.ofFn
  funext i
  simp only [hw i (by omega), hm i (by omega), hp i (by omega), hc]

/-- Assemble the pointwise stabilized raw data into an actual infinite path.
Type-I membership is witnessed by original finite-path pieces, never by an
assumption that a limit belongs to the norming set. -/
lemma infinite_path_of_stabilized {f : Family} (P : ℕ → FinitePath f)
    (hmem : ∀ n i j, ((P n).piece i).child j ∈ f.norming)
    (hlen : ∀ i, ∀ᶠ n in atTop, i < (P n).length)
    (hstable : ∀ i, ∃ d : Array × ℕ × ℕ, ∀ᶠ n in atTop,
      (P n).raw.piece i = d.1 ∧ (P n).raw.weight i = d.2.1 ∧
        (P n).raw.metadata i = d.2.2) :
    ∃ Q : InfinitePath f, ∀ i, ∀ᶠ n in atTop,
      (P n).raw.piece i = Q.raw.piece i ∧
      (P n).raw.weight i = Q.raw.weight i ∧
      (P n).raw.metadata i = Q.raw.metadata i := by
  choose d hd using hstable
  let Q : RawPath := {
    piece := fun i => (d i).1
    weight := fun i => (d i).2.1
    metadata := fun i => (d i).2.2
    nonzero := fun i => by
      obtain ⟨n, hn⟩ := (hd i).exists
      exact hn.1 ▸ (P n).raw.nonzero i }
  have he (i : ℕ) : ∀ᶠ n in atTop,
      (P n).raw.piece i = Q.piece i ∧ (P n).raw.weight i = Q.weight i ∧
        (P n).raw.metadata i = Q.metadata i := hd i
  have heAll (i : ℕ) : ∀ᶠ n in atTop, ∀ j ≤ i,
      (P n).raw.piece j = Q.piece j ∧ (P n).raw.weight j = Q.weight j ∧
        (P n).raw.metadata j = Q.metadata j := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using
      (eventually_all_finset (I := Finset.range (i+1))).mpr (fun j _ => he j)
  have hc (i : ℕ) : ∀ᶠ n in atTop, (P n).raw.code i = Q.code i := by
    filter_upwards [heAll i] with n hn
    exact raw_code_eq_of_prefix (fun j hj => (hn j hj).1)
      (fun j hj => (hn j hj).2.1) (fun j hj => (hn j hj).2.2)
  have hvalid : Q.Admissible := {
    successive := by
      intro i j hij a ha b hb
      obtain ⟨n, hn, hi, hj⟩ := ((hlen j).and ((he i).and (he j))).exists
      exact (P n).valid.successive i j hij hn a (hi.1.symm ▸ ha) b (hj.1.symm ▸ hb)
    metadata_strict := by
      intro i j hij
      obtain ⟨n, hn, hi, hj⟩ := ((hlen j).and ((he i).and (he j))).exists
      simpa only [hi.2.2, hj.2.2] using (P n).valid.metadata_strict i j hij hn
    metadata_pos := by
      intro i
      obtain ⟨n, hn, hi⟩ := ((hlen i).and (he i)).exists
      simpa only [hi.2.2] using (P n).valid.metadata_pos i hn
    weight_pos := by
      intro i
      obtain ⟨n, hn, hi⟩ := ((hlen i).and (he i)).exists
      simpa only [hi.2.1] using (P n).valid.weight_pos i hn
    weight_le_metadata := by
      intro i
      obtain ⟨n, hn, hi⟩ := ((hlen i).and (he i)).exists
      simpa only [hi.2.1, hi.2.2] using (P n).valid.weight_le_metadata i hn
    rho_bound := by
      intro i a b ha hb hab
      obtain ⟨n, hn, hi⟩ := ((hlen i).and (heAll i)).exists
      have hs := raw_support_eq_of_prefix (fun j hj => (hi j hj).1)
      simpa only [(hi i le_rfl).2.2] using (P n).valid.rho_bound i hn a b
        (hs.symm ▸ ha) (hs.symm ▸ hb) hab
    rule := by
      intro i
      obtain ⟨n, hn, hi, hci⟩ := ((hlen (i+1)).and ((he (i+1)).and (hc i))).exists
      simpa only [hi.2.1, hci] using (P n).valid.rule i hn }
  have hpiece (i : ℕ) : ∃ e : TypeI f, e.value = Q.piece i ∧ e.weight = Q.weight i ∧
      ∀ j, e.child j ∈ f.norming := by
    obtain ⟨n, hn, hi⟩ := ((hlen i).and (he i)).exists
    exact ⟨(P n).piece ⟨i, hn⟩, ((P n).value_eq _).trans hi.1,
      ((P n).weight_eq _).trans hi.2.1, hmem n _⟩
  choose e heval heweight hemem using hpiece
  refine ⟨⟨Q, hvalid, e, heval, heweight, ?_, hemem⟩, he⟩
  intro i j hij
  obtain ⟨n, hn, hi, hj⟩ := ((hlen j).and ((he i).and (he j))).exists
  simpa only [hi.1, hj.1] using (P n).mixed_successive
    ⟨i, hij.trans hn⟩ ⟨j, hn⟩ hij

lemma infinite_path_of_fixed_chain {f : Family} (P : ℕ → FinitePath f)
    (hmem : ∀ n i j, ((P n).piece i).child j ∈ f.norming)
    (hlen : ∀ i, ∀ᶠ n in atTop, i < (P n).length)
    (hw : ∀ i, ∃ w, ∀ᶠ n in atTop, (P n).raw.weight i = w)
    (ha : ∀ i, ∃ j > i, ∃ a : Γ,
      ∀ᶠ n in atTop, a ∈ ((P n).raw.piece j).support) :
    ∃ Q : InfinitePath f, ∀ i, ∀ᶠ n in atTop,
      (P n).raw.piece i = Q.raw.piece i ∧
      (P n).raw.weight i = Q.raw.weight i ∧
      (P n).raw.metadata i = Q.raw.metadata i :=
  infinite_path_of_stabilized P hmem hlen (finite_paths_stabilize P hlen hw ha)

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open PathCoding Filter
open scoped Classical

lemma PrefixValid.index_le_weight {P : RawPath} {len : ℕ} (h : PrefixValid P len)
    (i : ℕ) (hi : i < len) : i ≤ P.weight i := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hv := h.weight_strict (show (⟨i, by omega⟩ : Fin len) < ⟨i+1, hi⟩ from by change i < i+1; omega)
    have := ih (by omega)
    change P.weight i < P.weight (i+1) at hv
    omega

/-- A compactness statement sufficient for the four-hits contradiction. Unlike
weak-star compactness alone, it recovers one actual infinite coded path. Every
high window has a finite upper endpoint and a finite possible coordinate set. -/
lemma path_of_recurrent_windows {f : Family} (P : ℕ → FinitePath f)
    (hmem : ∀ n i j, ((P n).piece i).child j ∈ f.norming)
    (hwin : ∀ B : ℕ, ∃ T : ℕ, ∃ s : Finset Γ, ∀ᶠ n in atTop,
      ∃ i < (P n).length, B < (P n).raw.weight i ∧ (P n).raw.weight i ≤ T ∧
        ∃ a ∈ s, a ∈ ((P n).raw.piece i).support) :
    ∃ (φ : ℕ → ℕ) (Q : InfinitePath f), StrictMono φ ∧ ∀ i, ∀ᶠ n in atTop,
      i < (P (φ n)).length ∧ (P (φ n)).raw.piece i = Q.raw.piece i ∧
      (P (φ n)).raw.weight i = Q.raw.weight i ∧
      (P (φ n)).raw.metadata i = Q.raw.metadata i := by
  choose T s hs using hwin
  let ι := ℕ ⊕ (Σ B : ℕ, ℕ × s B)
  let test : ℕ → ι → Prop := fun n t => match t with
    | .inl w => ∃ i < (P n).length, (P n).raw.weight i = w
    | .inr ⟨B, i, a⟩ => a.val ∈ ((P n).raw.piece i).support
  obtain ⟨φ, hφ, htest⟩ := DiscreteDiagonal.exists_stabilizing_subsequence test
  choose b hb using htest
  let W : Set ℕ := {w | b (.inl w)}
  have hWmem (w : ℕ) : ∀ᶠ n in atTop,
      (∃ i < (P (φ n)).length, (P (φ n)).raw.weight i = w) ↔ w ∈ W := hb (.inl w)
  have hwin' (B : ℕ) : ∀ᶠ n in atTop,
      ∃ i < (P (φ n)).length, B < (P (φ n)).raw.weight i ∧
        (P (φ n)).raw.weight i ≤ T B ∧ ∃ a ∈ s B,
          a ∈ ((P (φ n)).raw.piece i).support := (hs B).filter_mono hφ.tendsto_atTop
  have hW : W.Infinite := IncreasingLists.infinite_of_windows
    (fun n => (P (φ n)).length) (fun n i => (P (φ n)).raw.weight i) W hWmem
    (fun B => ⟨T B, (hwin' B).mono fun _ ⟨i, hi, hBi, hiT, _⟩ => ⟨i, hi, hBi, hiT⟩⟩)
  let w := Nat.nth (· ∈ W)
  have hpos (i : ℕ) : ∀ᶠ n in atTop,
      i < (P (φ n)).length ∧ (P (φ n)).raw.weight i = w i :=
    IncreasingLists.positions_stabilize _ _ (fun n => (P (φ n)).valid.weight_strict) W hW hWmem i
  have hanchor (i : ℕ) : ∃ j > i, ∃ a : Γ,
      ∀ᶠ n in atTop, a ∈ ((P (φ n)).raw.piece j).support := by
    let B := w i
    have hpall : ∀ᶠ n in atTop, ∀ j ≤ T B,
        j < (P (φ n)).length ∧ (P (φ n)).raw.weight j = w j := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using
        (eventually_all_finset (I := Finset.range (T B+1))).mpr (fun j _ => hpos j)
    have hc (j : Fin (T B+1)) (a : s B) : ∀ᶠ n in atTop,
        a.val ∈ ((P (φ n)).raw.piece j).support ↔ b (.inr ⟨B, j.val, a⟩) :=
      hb (.inr ⟨B, j.val, a⟩)
    have hcall : ∀ᶠ n in atTop, ∀ j : Fin (T B+1), ∀ a : s B,
        a.val ∈ ((P (φ n)).raw.piece j).support ↔ b (.inr ⟨B, j.val, a⟩) :=
      eventually_all.mpr (fun j => eventually_all.mpr (hc j))
    obtain ⟨n, hn, hp, hcoord⟩ := ((hwin' B).and (hpall.and hcall)).exists
    obtain ⟨j, hj, hBj, hjT, a, has, haj⟩ := hn
    have hjT' : j ≤ T B := ((P (φ n)).valid.index_le_weight j hj).trans hjT
    have hij : i < j := (Nat.nth_lt_nth hW).mp (hBj.trans_eq (hp j hjT').2)
    have hba : b (.inr ⟨B, j, ⟨a, has⟩⟩) := (hcoord ⟨j, by omega⟩ ⟨a, has⟩).mp haj
    refine ⟨j, hij, a, ?_⟩
    exact (hb (.inr ⟨B, j, ⟨a, has⟩⟩)).mono (fun _ h => h.mpr hba)
  obtain ⟨Q, hQ⟩ := infinite_path_of_fixed_chain (P ∘ φ) (fun n => hmem (φ n))
    (fun i => (hpos i).mono fun _ h => h.1)
    (fun i => ⟨w i, (hpos i).mono fun _ h => h.2⟩) hanchor
  exact ⟨φ, Q, hφ, fun i => ((hpos i).and (hQ i)).mono (fun _ h => ⟨h.1.1, h.2⟩)⟩

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open Filter PathCoding
open scoped Classical Topology

lemma FinitePath.at_piece {f : Family} (P : FinitePath f) (i : Fin P.length)
    (a : Γ) (hi : P.raw.piece i a ≠ 0) : P.value a = P.raw.piece i a := by
  change (∑ j : Fin P.length, P.raw.piece j) a = _
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · intro j _ hji
    by_contra hj
    have he : j = i := Fin.ext (by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact (lt_irrefl a) (P.valid.successive j i h i.isLt a
          (Finsupp.mem_support_iff.mpr hj) a (Finsupp.mem_support_iff.mpr hi))
      · exact (lt_irrefl a) (P.valid.successive i j h j.isLt a
          (Finsupp.mem_support_iff.mpr hi) a (Finsupp.mem_support_iff.mpr hj)))
    exact hji he
  · simp

lemma FinitePath.coefficient_le {f : Family} (P : FinitePath f)
    (hm : ∀ i j, (P.piece i).child j ∈ f.norming) (a : Γ) :
    |(P.value a : ℝ)| ≤ 1/(f.m (P.raw.weight (P.hitIndex a)) : ℝ) := by
  rw [P.value_at_hit, ← P.value_eq, ← P.weight_eq]
  exact (P.piece (P.hitIndex a)).coefficient_bound
    (fun j b => full_coefficient_bound _ (f.norming_subset_full (hm _ j)) b) a

/-- Coordinate value of the bounded infinite path functional. -/
def InfinitePath.coordinateValue {f : Family} (P : InfinitePath f) (a : Γ) : ℚ :=
  (P.prefix_coordinate_eventually_constant a).choose

lemma InfinitePath.prefix_coordinateValue {f : Family} (P : InfinitePath f) (a : Γ) :
    ∀ᶠ n in atTop, (P.prefix n).value a = P.coordinateValue a :=
  (P.prefix_coordinate_eventually_constant a).choose_spec

lemma InfinitePath.coordinateValue_at_hit {f : Family} (P : InfinitePath f)
    (a : Γ) (i : ℕ) (hi : P.raw.piece i a ≠ 0) :
    P.coordinateValue a = P.raw.piece i a := by
  obtain ⟨n, hn, hiv⟩ := ((P.prefix_coordinateValue a).and (eventually_ge_atTop i)).exists
  exact hn.symm.trans (P.prefix_at_hit a i n hi hiv)

lemma InfinitePath.coordinateValue_zero {f : Family} (P : InfinitePath f)
    (a : Γ) (hi : ∀ i, P.raw.piece i a = 0) : P.coordinateValue a = 0 := by
  obtain ⟨n, hn⟩ := (P.prefix_coordinateValue a).exists
  rw [← hn]
  change (∑ i : Fin (n+1), P.raw.piece i) a = 0
  simp only [Finsupp.finsetSum_apply, hi, Finset.sum_const_zero]

/-- Stabilization is on exact actual uncropped pieces. Any extra pieces escape
in weight, and their coordinate coefficients tend to zero. -/
lemma stabilized_coordinate_tendsto {f : Family} (P : ℕ → FinitePath f)
    (hm : ∀ n i j, ((P n).piece i).child j ∈ f.norming) (Q : InfinitePath f)
    (hst : ∀ i, ∀ᶠ n in atTop, i < (P n).length ∧
      (P n).raw.piece i = Q.raw.piece i ∧ (P n).raw.weight i = Q.raw.weight i)
    (a : Γ) : Tendsto (fun n => ((P n).value a : ℝ)) atTop (𝓝 (Q.coordinateValue a : ℝ)) := by
  by_cases hh : ∃ i, Q.raw.piece i a ≠ 0
  · obtain ⟨i, hi⟩ := hh
    apply tendsto_const_nhds.congr'
    filter_upwards [hst i] with n hn
    rw [Q.coordinateValue_at_hit a i hi]
    congr 1
    exact ((P n).at_piece ⟨i, hn.1⟩ a (by simpa only [hn.2.1] using hi)).trans
      (congrArg (fun z : Array => z a) hn.2.1) |>.symm
  · push Not at hh
    rw [Q.coordinateValue_zero a hh, Rat.cast_zero]
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp f.reciprocal_summable.tendsto_atTop_zero ε hε
    have heps : 1/(Parameters.m f.s N : ℝ) < ε := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
        0 ≤ 1/(Parameters.m f.s N : ℝ))] using hN N le_rfl
    have hall : ∀ᶠ n in atTop, ∀ i ≤ N+2, i < (P n).length ∧
        (P n).raw.piece i = Q.raw.piece i ∧ (P n).raw.weight i = Q.raw.weight i := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using
        (eventually_all_finset (I := Finset.range (N+2+1))).mpr (fun i _ => hst i)
    filter_upwards [hall] with n hn
    rw [Real.dist_eq, sub_zero]
    by_cases hz : (P n).value a = 0
    · simpa only [hz, Rat.cast_zero, abs_zero] using hε
    · let i := (P n).hitIndex a
      have hi : N+2 < i.val := by
        by_contra hnle
        have hzero : (P n).raw.piece i a = 0 := by
          rw [(hn i (by omega)).2.1, hh]
        exact hz ((P n).value_at_hit a |>.trans hzero)
      have hw : N+2 ≤ (P n).raw.weight i :=
        hi.le.trans ((P n).valid.index_le_weight i i.isLt)
      have hmle : Parameters.m f.s N ≤ f.m ((P n).raw.weight i) :=
        (Parameters.m_strict f.s_ge_two).monotone (by omega)
      exact ((P n).coefficient_le (hm n) a).trans_lt
        ((one_div_le_one_div_of_le (by exact_mod_cast Parameters.m_pos f.s N)
          (by exact_mod_cast hmle)).trans_lt heps)

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualEGroup12
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualESpace12
lemma pathFunctional_finite {f : Family} (Q : InfinitePath f) (x : Γ →₀ ℝ) :
    pathFunctional Q (norming.includeFinite x) = x.sum (fun a t => t * (Q.coordinateValue a : ℝ)) := by
  apply tendsto_nhds_unique (pathPartial_tendsto Q _)
  apply tendsto_const_nhds.congr'
  filter_upwards [(eventually_all_finset x.support).mpr (fun a _ => Q.prefix_coordinateValue a)] with n hn
  rw [pathPartial, norming.functional_includeFinite]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [hn a ha]

lemma finitePath_mem_full {f : Family} (P : FinitePath f)
    (hm : ∀ i j, (P.piece i).child j ∈ f.norming) : P.value ∈ Full := by
  have h := TypeII.mem_family (P.oneTerm Crop.all) (fun _ i j => hm i j)
  apply f.norming_subset_full
  simpa only [FinitePath.oneTerm_value, Crop.all_set, restrict_univ] using h

def finitePathFunctional {f : Family} (P : FinitePath f)
    (hm : ∀ i j, (P.piece i).child j ∈ f.norming) : StrongDual ℝ E :=
  norming.functional ⟨P.value, finitePath_mem_full P hm⟩

lemma norm_finitePathFunctional_le {f : Family} (P : FinitePath f)
    (hm : ∀ i j, (P.piece i).child j ∈ f.norming) : ‖finitePathFunctional P hm‖ ≤ 1 :=
  norming.norm_functional_le _

lemma stabilized_path_tendsto {f : Family} (P : ℕ → FinitePath f)
    (hm : ∀ n i j, ((P n).piece i).child j ∈ f.norming) (Q : InfinitePath f)
    (hst : ∀ i, ∀ᶠ n in atTop, i < (P n).length ∧
      (P n).raw.piece i = Q.raw.piece i ∧ (P n).raw.weight i = Q.raw.weight i)
    (x : E) : Tendsto (fun n => finitePathFunctional (P n) (hm n) x) atTop (𝓝 (pathFunctional Q x)) := by
  let g : ℕ → StrongDual ℝ E := fun n => finitePathFunctional (P n) (hm n) - pathFunctional Q
  have hb (n : ℕ) : ‖g n‖ ≤ 2 := (norm_sub_le _ _).trans
    (by linarith [norm_finitePathFunctional_le (P n) (hm n), norm_pathFunctional_le Q])
  have hz (y : E) (hy : y ∈ Set.range norming.includeFinite) :
      Tendsto (fun n => g n y) atTop (𝓝 0) := by
    obtain ⟨v, rfl⟩ := hy
    have ht : Tendsto (fun n => finitePathFunctional (P n) (hm n) (norming.includeFinite v))
        atTop (𝓝 (pathFunctional Q (norming.includeFinite v))) := by
      simp only [finitePathFunctional, norming.functional_includeFinite, pathFunctional_finite]
      exact tendsto_finsetSum _ (fun a _ => tendsto_const_nhds.mul (stabilized_coordinate_tendsto P hm Q hst a))
    simpa only [g, sub_apply, sub_self] using ht.sub_const (pathFunctional Q (norming.includeFinite v))
  have ht := DenseZero.tendsto_zero_of_dense g 2 hb _ norming.denseRange_includeFinite hz x
  have he : (fun n => g n x + pathFunctional Q x) = (fun n => finitePathFunctional (P n) (hm n) x) := by
    funext n
    simp only [g, sub_apply, sub_add_cancel]
  simpa only [he, zero_add] using ht.add_const (pathFunctional Q x)

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open PathCoding
open scoped Classical

/-- Legal crop selecting an interval of original weights, without recoding. -/
def FinitePath.weightCrop {f : Family} (P : FinitePath f) (J T : ℕ) : Crop where
  ordinal := {a | (∀ i : Fin P.length, P.raw.weight i < J → ∀ b ∈ (P.raw.piece i).support, b < a) ∧
    (∀ i : Fin P.length, T < P.raw.weight i → ∀ b ∈ (P.raw.piece i).support, a < b)}
  ordinal_convex := ⟨by
    intro a ha b hb z hz
    exact ⟨fun i hi x hx => (ha.1 i hi x hx).trans_le hz.1,
      fun i hi x hx => hz.2.trans_lt (hb.2 i hi x hx)⟩⟩
  colors := Set.univ
  colors_convex := Set.ordConnected_univ

lemma FinitePath.weightCrop_set {f : Family} (P : FinitePath f) (J T : ℕ) :
    (P.weightCrop J T).set f = (P.weightCrop J T).ordinal := by
  cases f <;> simp only [Crop.set, weightCrop, Set.preimage_univ, Set.inter_univ]

lemma FinitePath.weightCrop_piece {f : Family} (P : FinitePath f) (J T : ℕ) (i : Fin P.length) :
    restrict ((P.weightCrop J T).set f) (P.raw.piece i) =
      if J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T then P.raw.piece i else 0 := by
  rw [P.weightCrop_set]
  ext a
  rw [restrict_apply]
  by_cases hi : J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T
  · rw [ite_eq_left hi]
    by_cases hia : P.raw.piece i a = 0
    · simp only [hia, ite_self]
    · have ha : a ∈ (P.weightCrop J T).ordinal := by
        refine ⟨fun j hj b hb => ?_, fun j hj b hb => ?_⟩
        · have hji : j < i := P.valid.weight_strict.lt_iff_lt.mp (hj.trans_le hi.1)
          exact P.valid.successive j i hji i.isLt b hb a (Finsupp.mem_support_iff.mpr hia)
        · have hij : i < j := P.valid.weight_strict.lt_iff_lt.mp (hi.2.trans_lt hj)
          exact P.valid.successive i j hij j.isLt a (Finsupp.mem_support_iff.mpr hia) b hb
      rw [ite_eq_left ha]
  · rw [ite_eq_right hi]
    by_cases hia : P.raw.piece i a = 0
    · simp only [hia, ite_self, Finsupp.zero_apply]
    · have ha : a ∉ (P.weightCrop J T).ordinal := by
        intro ha
        rcases lt_or_ge (P.raw.weight i) J with h | h
        · exact (lt_irrefl a) (ha.1 i h a (Finsupp.mem_support_iff.mpr hia))
        · have ht : T < P.raw.weight i := lt_of_not_ge (fun hh => hi ⟨h, hh⟩)
          exact (lt_irrefl a) (ha.2 i ht a (Finsupp.mem_support_iff.mpr hia))
      simp only [ite_eq_right ha, Finsupp.zero_apply]

def FinitePath.windowWeights {f : Family} (P : FinitePath f) (J T : ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun i : Fin P.length => J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T)).image
    (fun i : Fin P.length => P.raw.weight i)

lemma FinitePath.weightCrop_active {f : Family} (P : FinitePath f) (J T : ℕ) :
    P.active (P.weightCrop J T) = P.windowWeights J T := by
  unfold active windowWeights
  apply congrArg (Finset.image (fun i : Fin P.length => P.raw.weight i))
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, P.weightCrop_piece]
  split_ifs with hi
  · exact iff_of_true (P.raw.nonzero i) hi
  · exact iff_of_false (by simp) hi

lemma FinitePath.mem_windowWeights {f : Family} (P : FinitePath f) (J T w : ℕ) :
    w ∈ P.windowWeights J T ↔ J ≤ w ∧ w ≤ T ∧ ∃ i : Fin P.length, P.raw.weight i = w := by
  simp only [windowWeights, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hi.1, hi.2, i, rfl⟩
  · rintro ⟨hJ, hT, i, rfl⟩
    exact ⟨i, ⟨hJ, hT⟩, rfl⟩

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualEGroup13
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualESpace13
def croppedPathFunctional {f : Family} (P : FinitePath f) (A : Crop) : StrongDual ℝ E :=
  (norming.rationalPredual (restrict (A.set f) P.value)).val

lemma rational_cropped_path_bound {f : Family} {h : ℕ} (P : Fin h → FinitePath f)
    (A : Fin h → Crop) (hm : ∀ b i j, ((P b).piece i).child j ∈ f.norming)
    (hdis : Pairwise (fun i j => Disjoint ((P i).active (A i)) ((P j).active (A j))))
    (c : Fin h → ℚ) (hc : ∑ i, |(c i : ℝ)| ^ f.q ≤ 1) :
    ‖∑ i, (c i : ℝ) • croppedPathFunctional (P i) (A i)‖ ≤ 1 := by
  let e : TypeII f := ⟨h, P, A, c, hc, hdis⟩
  have he : e.value ∈ Full := f.norming_subset_full (e.mem_family hm)
  have heq : norming.functional ⟨e.value, he⟩ =
      ∑ i, (c i : ℝ) • croppedPathFunctional (P i) (A i) := by
    ext x
    rw [← norming.evaluateArray_eq_functional]
    simp only [e, TypeII.value, map_sum, map_rat_smul, Rat.smul_def,
      sum_apply, smul_apply, smul_eq_mul, croppedPathFunctional, NormingSet.evaluateArray]
    rfl
  rw [← heq]
  exact norming.norm_functional_le _

lemma real_cropped_path_bound {f : Family} {h : ℕ} (P : Fin h → FinitePath f)
    (A : Fin h → Crop) (hm : ∀ b i j, ((P b).piece i).child j ∈ f.norming)
    (hdis : Pairwise (fun i j => Disjoint ((P i).active (A i)) ((P j).active (A j))))
    (c : Fin h → ℝ) :
    ‖∑ i, c i • croppedPathFunctional (P i) (A i)‖ ≤ (∑ i, |c i| ^ f.q) ^ (1/f.q) := by
  have hq : 0 < f.q := lt_trans zero_lt_one (Parameters.q_bounds f.s_ge_two).1
  apply RealCoefficients.bound_from_unit f.q hq
  exact RealCoefficients.rational_to_real f.q hq _ (rational_cropped_path_bound P A hm hdis)

lemma cropped_abs_sum_bound {f : Family} {h : ℕ} (P : Fin h → FinitePath f)
    (A : Fin h → Crop) (hm : ∀ b i j, ((P b).piece i).child j ∈ f.norming)
    (hdis : Pairwise (fun i j => Disjoint ((P i).active (A i)) ((P j).active (A j)))) (x : E) :
    (∑ i, |croppedPathFunctional (P i) (A i) x|) ≤ (h : ℝ) ^ (1/f.q) * ‖x‖ := by
  let c : Fin h → ℝ := fun i => RealCoefficients.signChoice (croppedPathFunctional (P i) (A i) x)
  have hc (i : Fin h) : |c i| = 1 := RealCoefficients.abs_signChoice _
  have hv (i : Fin h) : c i * croppedPathFunctional (P i) (A i) x =
      |croppedPathFunctional (P i) (A i) x| := RealCoefficients.signChoice_mul _
  have he : (∑ i, c i • croppedPathFunctional (P i) (A i)) x =
      ∑ i, |croppedPathFunctional (P i) (A i) x| := by
    simp only [sum_apply, smul_apply, smul_eq_mul, hv]
  calc
    _ = |(∑ i, c i • croppedPathFunctional (P i) (A i)) x| := by
      rw [he, abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))]
    _ ≤ ‖∑ i, c i • croppedPathFunctional (P i) (A i)‖ * ‖x‖ :=
      by simpa only [Real.norm_eq_abs] using (∑ i, c i • croppedPathFunctional (P i) (A i)).le_opNorm x
    _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa only [hc, Real.one_rpow,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      using (real_cropped_path_bound P A hm hdis c)) (norm_nonneg _)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open PathCoding CoherentClosures
open scoped Classical

/-- Actual pieces, original weights, and original metadata below a threshold.
This is deliberately not the compressed history, nor a cropped code. -/
def FinitePath.lowHistory {f : Family} (P : FinitePath f) (J : ℕ) : Set (Array × ℕ × ℕ) :=
  {d | d.2.1 < J ∧ ∃ i : Fin P.length,
    d = (P.raw.piece i, P.raw.weight i, P.raw.metadata i)}

lemma PrefixValid.metadata_mono {P : RawPath} {len : ℕ} (hP : PrefixValid P len)
    {i j : ℕ} (hij : i ≤ j) (hj : j < len) : P.metadata i ≤ P.metadata j := by
  rcases hij.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (hP.metadata_strict i j h hj).le

lemma FinitePath.code_of_shared_weight {f : Family} (P Q : FinitePath f)
    (i : Fin P.length) (j : Fin Q.length) (hi : 0 < i.val) (hj : 0 < j.val)
    (hw : P.raw.weight i = Q.raw.weight j) :
    i.val = j.val ∧ P.raw.code (i.val-1) = Q.raw.code (i.val-1) := by
  have hc : P.raw.code (i.val-1) = Q.raw.code (j.val-1) := by
    apply sigma_injective
    rw [← P.valid.rule (i.val-1) (by omega), ← Q.valid.rule (j.val-1) (by omega)]
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i.val),
      Nat.sub_add_cancel (by omega : 1 ≤ j.val)] using hw
  have heq := RawPath.code_eq_length hc
  have hij : i.val = j.val := by omega
  exact ⟨hij, by simpa only [hij] using hc⟩

lemma closure_downward_rho (β a b : Γ) (p : ℕ) (hp : 1 ≤ p)
    (hab : a ≤ b) (hb : b ∈ F β p) (hr : rho a b ≤ p) : a ∈ F β p := by
  have ha := (rho_le_iff a b hab p hp).mp hr
  rw [F_coherent β b p hb] at ha
  exact (Finset.mem_filter.mp ha).1

/-- Two agreeing compressed histories whose later pieces meet one finite
coordinate set with sufficiently small rho have identical actual earlier
pieces. The anchors may be different coordinates and different pieces. -/
lemma PrefixValid.low_piece_eq_of_anchors {P Q : RawPath} {len len' n i j k : ℕ}
    (hP : PrefixValid P len) (hQ : PrefixValid Q len')
    (hn : n < len) (hn' : n < len') (hc : P.code n = Q.code n)
    (hij : i < j) (hik : i < k) (hjn : j ≤ n) (hkn : k ≤ n)
    (a b : Γ) (ha : a ∈ (P.piece j).support) (hb : b ∈ (Q.piece k).support)
    (hr : rho (min a b) (max a b) ≤ P.metadata n) : P.piece i = Q.piece i := by
  have hm := (RawPath.code_eq_at hc n le_rfl).2.1
  rcases le_total a b with hab | hba
  · have haQ : a ∈ Q.closure n := by
      have hbQ := hQ.piece_support_subset_closure hkn hn' hb
      unfold RawPath.closure at hbQ ⊢
      apply closure_downward_rho _ a b _ (hQ.metadata_pos n hn') hab hbQ
      simpa only [min_eq_left hab, max_eq_right hab, hm] using hr
    exact hP.piece_eq_of_code_anchor hQ hn hn' hij hjn hc a ha haQ
  · have hbP : b ∈ P.closure n := by
      have haP := hP.piece_support_subset_closure hjn hn ha
      unfold RawPath.closure at haP ⊢
      apply closure_downward_rho _ b a _ (hP.metadata_pos n hn) hba haP
      simpa only [min_eq_right hba, max_eq_left hba] using hr
    exact (hQ.piece_eq_of_code_anchor hP hn' hn hik hkn hc.symm b hb hbP).symm

lemma FinitePath.lowHistory_eq_of_code_anchors {f : Family} (P Q : FinitePath f)
    (J n : ℕ) (hn : n < P.length) (hn' : n < Q.length) (hc : P.raw.code n = Q.raw.code n)
    (j : Fin P.length) (k : Fin Q.length) (hjn : j.val ≤ n) (hkn : k.val ≤ n)
    (hj : J ≤ P.raw.weight j) (hk : J ≤ Q.raw.weight k)
    (a b : Γ) (ha : a ∈ (P.raw.piece j).support) (hb : b ∈ (Q.raw.piece k).support)
    (hr : rho (min a b) (max a b) ≤ P.raw.metadata n) : P.lowHistory J = Q.lowHistory J := by
  have hleft (i : Fin P.length) (hi : P.raw.weight i < J) :
      ∃ i' : Fin Q.length, P.raw.piece i = Q.raw.piece i' ∧
        P.raw.weight i = Q.raw.weight i' ∧ P.raw.metadata i = Q.raw.metadata i' := by
    have hij : i < j := P.valid.weight_strict.lt_iff_lt.mp (hi.trans_le hj)
    have hin : i.val ≤ n := (show i.val ≤ j.val from hij.le).trans hjn
    let i' : Fin Q.length := ⟨i.val, hin.trans_lt hn'⟩
    have he := RawPath.code_eq_at hc i hin
    have hik : i' < k := Q.valid.weight_strict.lt_iff_lt.mp
      (by change Q.raw.weight i < Q.raw.weight k; rw [← he.1]; exact hi.trans_le hk)
    exact ⟨i', P.valid.low_piece_eq_of_anchors Q.valid hn hn' hc hij hik hjn hkn a b ha hb hr,
      he.1, he.2.1⟩
  have hright (i : Fin Q.length) (hi : Q.raw.weight i < J) :
      ∃ i' : Fin P.length, Q.raw.piece i = P.raw.piece i' ∧
        Q.raw.weight i = P.raw.weight i' ∧ Q.raw.metadata i = P.raw.metadata i' := by
    have hik : i < k := Q.valid.weight_strict.lt_iff_lt.mp (hi.trans_le hk)
    have hin : i.val ≤ n := (show i.val ≤ k.val from hik.le).trans hkn
    let i' : Fin P.length := ⟨i.val, hin.trans_lt hn⟩
    have he := RawPath.code_eq_at hc i hin
    have hij : i' < j := P.valid.weight_strict.lt_iff_lt.mp
      (by change P.raw.weight i < P.raw.weight j; rw [he.1]; exact hi.trans_le hj)
    exact ⟨i', (P.valid.low_piece_eq_of_anchors Q.valid hn hn' hc hij hik hjn hkn a b ha hb hr).symm,
      he.1.symm, he.2.1.symm⟩
  ext d
  constructor
  · rintro ⟨hd, i, rfl⟩
    obtain ⟨i', hp, hw, hm⟩ := hleft i hd
    exact ⟨hd, i', by rw [hp, hw, hm]⟩
  · rintro ⟨hd, i, rfl⟩
    obtain ⟨i', hp, hw, hm⟩ := hright i hd
    exact ⟨hd, i', by rw [hp, hw, hm]⟩

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open PathCoding CoherentClosures
open scoped Classical

lemma FinitePath.lowHistory_eq_of_shared_later_weight {f : Family} (P Q : FinitePath f)
    (Jv Tv Jt Tt Jk Tk : ℕ) (hvt : Tv < Jt) (htk : Tt < Jk)
    (j : Fin P.length) (k : Fin Q.length) (t : Fin P.length)
    (hj : Jv ≤ P.raw.weight j ∧ P.raw.weight j ≤ Tv)
    (hk : Jv ≤ Q.raw.weight k ∧ Q.raw.weight k ≤ Tv)
    (ht : Jt ≤ P.raw.weight t ∧ P.raw.weight t ≤ Tt)
    (a b : Γ) (ha : a ∈ (P.raw.piece j).support) (hb : b ∈ (Q.raw.piece k).support)
    (hr : rho (min a b) (max a b) ≤ Jt)
    (hw : ∃ w, w ∈ P.windowWeights Jk Tk ∧ w ∈ Q.windowWeights Jk Tk) :
    P.lowHistory Jv = Q.lowHistory Jv := by
  obtain ⟨w, hwP, hwQ⟩ := hw
  obtain ⟨hwJ, _, i, hei⟩ := (P.mem_windowWeights Jk Tk w).mp hwP
  obtain ⟨_, _, i', hei'⟩ := (Q.mem_windowWeights Jk Tk w).mp hwQ
  have htw : P.raw.weight t < P.raw.weight i := by omega
  have hti : t < i := P.valid.weight_strict.lt_iff_lt.mp htw
  have htJ : Jt ≤ Tt := ht.1.trans ht.2
  have hji : j < i := P.valid.weight_strict.lt_iff_lt.mp (by omega)
  have hki' : k < i' := Q.valid.weight_strict.lt_iff_lt.mp (by omega)
  have hi : 0 < i.val := (Nat.zero_le t.val).trans_lt hti
  have hi' : 0 < i'.val := (Nat.zero_le k.val).trans_lt hki'
  obtain ⟨he, hc⟩ := P.code_of_shared_weight Q i i' hi hi' (hei.trans hei'.symm)
  have hn : i.val - 1 < P.length := by omega
  have hn' : i.val - 1 < Q.length := by have := i'.isLt; omega
  have htn : t.val ≤ i.val - 1 := by omega
  have hmn : Jt ≤ P.raw.metadata (i.val-1) := ht.1.trans
    ((P.valid.weight_le_metadata t t.isLt).trans (P.valid.metadata_mono htn hn))
  exact P.lowHistory_eq_of_code_anchors Q Jv (i.val-1) hn hn' hc j k
    (by omega) (by omega) hj.1 hk.1 a b ha hb (hr.trans hmn)

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open PathCoding
open scoped Classical

def FinitePath.lowHistoryFinset {f : Family} (P : FinitePath f) (J : ℕ) : Finset (Array × ℕ × ℕ) :=
  (Finset.univ.filter (fun i : Fin P.length => P.raw.weight i < J)).image
    (fun i : Fin P.length => (P.raw.piece i, P.raw.weight i, P.raw.metadata i))

lemma FinitePath.mem_lowHistoryFinset {f : Family} (P : FinitePath f) (J : ℕ)
    (d : Array × ℕ × ℕ) : d ∈ P.lowHistoryFinset J ↔ d ∈ P.lowHistory J := by
  simp only [lowHistoryFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    lowHistory, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hi, i, rfl⟩
  · rintro ⟨hd, i, rfl⟩
    exact ⟨i, hd, rfl⟩

end SeparableQuotient.Norming

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.WindowEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.SeriesTails
open Filter
open scoped Topology Classical

lemma tendsto_tail (a : ℕ → ℝ) : Tendsto (tail a) atTop (𝓝 0) :=
  tendsto_sum_nat_add a

lemma tail_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (N : ℕ) : 0 ≤ tail a N :=
  tsum_nonneg (fun _ => ha _)

lemma sum_le_tail {ι : Type*} (a : ℕ → ℝ) (ha : Summable a) (hn : ∀ n, 0 ≤ a n)
    (s : Finset ι) (w : ι → ℕ) (hi : Set.InjOn w s) (N : ℕ) (hN : ∀ i ∈ s, N ≤ w i) :
    ∑ i ∈ s, a (w i) ≤ tail a N := by
  have hinj : Set.InjOn (fun i => w i - N) s := by
    intro i hi' j hj' hij
    apply hi hi' hj'
    have h1 := hN i hi'
    have h2 := hN j hj'
    change w i - N = w j - N at hij
    omega
  calc
    ∑ i ∈ s, a (w i) = ∑ i ∈ s, a ((w i-N)+N) := by
      exact Finset.sum_congr rfl (fun i hi => by rw [Nat.sub_add_cancel (hN i hi)])
    _ = ∑ k ∈ s.image (fun i => w i-N), a (k+N) := by
      symm
      apply Finset.sum_image
      exact hinj
    _ ≤ tail a N := ((summable_nat_add_iff N).mpr ha).sum_le_tsum _ (fun _ _ => hn _)

end SeparableQuotient.SeriesTails

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

lemma evaluateArray_finite (x : Γ →₀ ℝ) (g : Array) :
    norming.evaluateArray (norming.includeFinite x) g = ∑ a ∈ x.support, (g a : ℝ) * x a := by
  rw [norming.evaluateArray_eq]
  simp only [norming.coordinate_includeFinite]
  have h1 : ∑ a ∈ g.support, (g a : ℝ) * x a =
      ∑ a ∈ g.support ∪ x.support, (g a : ℝ) * x a := by
    apply Finset.sum_subset Finset.subset_union_left
    intro a _ ha
    simp [Finsupp.notMem_support_iff.mp ha]
  have h2 : ∑ a ∈ x.support, (g a : ℝ) * x a =
      ∑ a ∈ g.support ∪ x.support, (g a : ℝ) * x a := by
    apply Finset.sum_subset Finset.subset_union_right
    intro a _ ha
    simp [Finsupp.notMem_support_iff.mp ha]
  exact h1.trans h2.symm

lemma vectorL1_nonneg (x : Γ →₀ ℝ) : 0 ≤ vectorL1 x :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma typeI_eval_le_l1 {f : Family} (e : TypeI f)
    (hm : ∀ j, e.child j ∈ f.norming) (x : Γ →₀ ℝ) :
    |norming.evaluateArray (norming.includeFinite x) e.value| ≤
      vectorL1 x * (1 / (f.m e.weight : ℝ)) := by
  rw [evaluateArray_finite]
  calc
    |∑ a ∈ x.support, (e.value a : ℝ) * x a| ≤ ∑ a ∈ x.support, |(e.value a : ℝ) * x a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ x.support, |x a| * (1 / (f.m e.weight : ℝ)) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (e.coefficient_bound
        (fun j a => full_coefficient_bound _ (f.norming_subset_full (hm j)) a) a) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; rfl

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open scoped Classical

lemma Family.theta_summable (f : Family) : Summable f.theta := by
  apply (summable_nat_add_iff 1).mp
  simpa only [Family.theta, Nat.add_sub_cancel] using (Parameters.hasSum_theta f.s_ge_two).summable

lemma Family.m_inv_summable (f : Family) : Summable (fun j => 1 / (f.m j : ℝ)) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [Family.m, Nat.add_sub_cancel] using f.reciprocal_summable

end SeparableQuotient.Norming

namespace SeparableQuotient.SeriesTails
open scoped Classical

lemma sum_outside_window_bound {ι : Type*} (s : Finset ι) (w : ι → ℕ) (v : ι → ℝ)
    (hi : Set.InjOn w s) (B J T : ℕ) (hBJ : B ≤ J) (hJT : J ≤ T)
    (a b : ℕ → ℝ) (ha : Summable a) (hb : Summable b)
    (han : ∀ n, 0 ≤ a n) (hbn : ∀ n, 0 ≤ b n)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hz : ∀ i ∈ s, w i < B → v i = 0)
    (hl : ∀ i ∈ s, B ≤ w i → w i < J → |v i| ≤ A * a (w i))
    (hh : ∀ i ∈ s, T < w i → |v i| ≤ C * b (w i)) :
    |(∑ i ∈ s, v i) - ∑ i ∈ s, if J ≤ w i ∧ w i ≤ T then v i else 0| ≤
      A * tail a B + C * tail b (T+1) := by
  let lo := s.filter (fun i => B ≤ w i ∧ w i < J)
  let hi' := s.filter (fun i => T < w i)
  have heq : (∑ i ∈ s, v i) - (∑ i ∈ s, if J ≤ w i ∧ w i ≤ T then v i else 0) =
      (∑ i ∈ lo, v i) + ∑ i ∈ hi', v i := by
    rw [← Finset.sum_sub_distrib]
    simp only [lo, hi', Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i his
    by_cases h1 : w i < B
    · have h2 : ¬ (J ≤ w i ∧ w i ≤ T) := by omega
      have h3 : ¬ (B ≤ w i ∧ w i < J) := by omega
      have h4 : ¬ T < w i := by omega
      simp only [hz i his h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, sub_self, add_zero]
    · by_cases h2 : w i < J
      · have h3 : ¬ (J ≤ w i ∧ w i ≤ T) := by omega
        have h4 : B ≤ w i ∧ w i < J := by omega
        have h5 : ¬ T < w i := by omega
        simp only [ite_eq_right h3, ite_eq_left h4, ite_eq_right h5, sub_zero, add_zero]
      · by_cases h3 : w i ≤ T
        · have h4 : J ≤ w i ∧ w i ≤ T := by omega
          have h5 : ¬ (B ≤ w i ∧ w i < J) := by omega
          have h6 : ¬ T < w i := by omega
          simp only [ite_eq_left h4, ite_eq_right h5, ite_eq_right h6, sub_self, add_zero]
        · have h4 : ¬ (J ≤ w i ∧ w i ≤ T) := by omega
          have h5 : ¬ (B ≤ w i ∧ w i < J) := by omega
          have h6 : T < w i := by omega
          simp only [ite_eq_right h4, ite_eq_right h5, ite_eq_left h6, sub_zero, zero_add]
  have hlo : |∑ i ∈ lo, v i| ≤ A * tail a B := by
    calc
      _ ≤ ∑ i ∈ lo, |v i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ lo, A * a (w i) := Finset.sum_le_sum (fun i his =>
        hl i (Finset.mem_filter.mp his).1 (Finset.mem_filter.mp his).2.1 (Finset.mem_filter.mp his).2.2)
      _ = A * ∑ i ∈ lo, a (w i) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_tail a ha han lo w
        (hi.mono (Finset.filter_subset _ _)) B (fun i his => (Finset.mem_filter.mp his).2.1)) hA
  have hhi : |∑ i ∈ hi', v i| ≤ C * tail b (T+1) := by
    calc
      _ ≤ ∑ i ∈ hi', |v i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ hi', C * b (w i) := Finset.sum_le_sum (fun i his =>
        hh i (Finset.mem_filter.mp his).1 (Finset.mem_filter.mp his).2)
      _ = C * ∑ i ∈ hi', b (w i) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_tail b hb hbn hi' w
        (hi.mono (Finset.filter_subset _ _)) (T+1) (fun i his => (Finset.mem_filter.mp his).2)) hC
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hlo hhi)

end SeparableQuotient.SeriesTails

namespace SeparableQuotient.CoverRecurrence
open Filter
open scoped Classical Topology

/-- Uniformly finite covers of all initial segments give a single sequence of
covering objects which eventually hits every member of an infinite fixed set.
No compactness of the covering objects themselves is assumed. -/
lemma recurrent_of_covers {Λ : Type*} (Hit : Λ → ℕ → Prop) (D : ℕ)
    (hcover : ∀ n, ∃ R : Finset Λ, R.card ≤ D ∧ ∀ i ≤ n, ∃ P ∈ R, Hit P i) :
    ∃ (P : ℕ → Λ) (W : Set ℕ), W.Infinite ∧ ∀ i ∈ W, ∀ᶠ n in atTop, Hit (P n) i := by
  choose R hR hhit using hcover
  have hfunc (n : ℕ) : ∃ P : Fin (D+1) → Λ, ∀ i ≤ n, ∃ b, Hit (P b) i := by
    obtain ⟨p₀, hp₀, _⟩ := hhit n 0 (Nat.zero_le _)
    let e : Fin (R n).card ≃ R n := (R n).equivFin.symm
    let P : Fin (D+1) → Λ := fun b => if hb : b.val < (R n).card then (e ⟨b, hb⟩).val else p₀
    refine ⟨P, fun i hi => ?_⟩
    obtain ⟨p, hp, hh⟩ := hhit n i hi
    let j := e.symm ⟨p, hp⟩
    let b : Fin (D+1) := ⟨j.val, j.isLt.trans_le ((hR n).trans (Nat.le_succ D))⟩
    refine ⟨b, ?_⟩
    have hb : b.val < (R n).card := j.isLt
    change Hit (P b) i
    rw [show P b = p from by
      dsimp only [P]
      rw [dite_eq_left hb]
      change (e (e.symm ⟨p, hp⟩)).val = p
      rw [e.apply_symm_apply]]
    exact hh
  choose P hP using hfunc
  let c : ℕ → ℕ → Fin (D+1) := fun n i => if hi : i ≤ n then (hP n i hi).choose else 0
  have hc (n i : ℕ) (hi : i ≤ n) : Hit (P n (c n i)) i := by
    simpa only [c, dite_eq_left hi] using (hP n i hi).choose_spec
  obtain ⟨l, _, φ, hφ, hl⟩ := isCompact_univ.tendsto_subseq
    (x := c) (fun _ => Set.mem_univ _)
  obtain ⟨b, hb⟩ := Finite.exists_infinite_fiber l
  refine ⟨fun n => P (φ n) b, {i | l i = b}, Set.infinite_coe_iff.mp hb, fun i hi => ?_⟩
  have he : ∀ᶠ n in atTop, c (φ n) i = l i := by
    simpa only [nhds_discrete, tendsto_pure, Function.comp_apply] using (tendsto_pi_nhds.mp hl i)
  filter_upwards [he, eventually_ge_atTop i] with n hn hin
  have hh := hc (φ n) i (hin.trans (hφ.id_le n))
  rwa [hn, hi] at hh

end SeparableQuotient.CoverRecurrence

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PartitionBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

lemma mem_ordinalHull {s : Finset Γ} (hs : s.Nonempty) {a : Γ} (ha : a ∈ s) :
    a ∈ ordinalHull s hs := ⟨s.min'_le _ ha, s.le_max' _ ha⟩

lemma ordinalHull_successive {s t : Finset Γ} (hs : s.Nonempty) (ht : t.Nonempty)
    (h : ∀ a ∈ s, ∀ b ∈ t, a < b) :
    ∀ a ∈ ordinalHull s hs, ∀ b ∈ ordinalHull t ht, a < b := by
  intro a ha b hb
  exact ha.2.trans_lt ((h _ (s.max'_mem hs) _ (t.min'_mem ht)).trans_le hb.1)

lemma abs_eval_supported_interval (g : Array) (hg : g ∈ Full)
    (I : Set Γ) (hI : Set.OrdConnected I) (hs : (g.support : Set Γ) ⊆ I) (x : E) :
    |norming.evaluateArray x g| ≤ ‖intervalProjection I hI x‖ := by
  have hr : restrict I g = g := by
    ext a
    by_cases ha : a ∈ I
    · simp [ha]
    · have hz : g a = 0 := by
        by_contra hne
        exact ha (hs (Finsupp.mem_support_iff.mpr hne))
      simp [ha, hz]
  have he : norming.evaluateArray (intervalProjection I hI x) g = norming.evaluateArray x g := by
    rw [intervalProjection, evaluateArray_projection, Crop.ordinalSet_set, hr]
  rw [← he, norming.evaluateArray_eq_functional _ ⟨g, hg⟩]
  exact norming.functional_bound _ _

lemma typeI_eval_le_of_partition {f : Family} (x : E) (N : ℕ) (A : ℝ)
    (hA : 0 ≤ A) (hx : PartitionBound x N A f.r) (e : TypeI f)
    (he : ∀ i, e.child i ∈ f.norming) (hL : f.L e.weight ≤ N) :
    |norming.evaluateArray x e.value| ≤ A * f.theta e.weight := by
  have hs (i : Fin e.length) : (e.child i).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (e.child_nonzero i)
  let I : Fin e.length → Set Γ := fun i => ordinalHull (e.child i).support (hs i)
  have hI (i : Fin e.length) : Set.OrdConnected (I i) := ordinalHull_connected _ _
  have hIs : ∀ i j, i < j → ∀ a ∈ I i, ∀ b ∈ I j, a < b := by
    intro i j hij
    exact ordinalHull_successive (hs i) (hs j) (fun a ha b hb => (e.successive i j hij a ha b hb).1)
  have hp := hx e.length e.length_pos (e.length_le.trans hL) I hI hIs
  have hb : |∑ i : Fin e.length, norming.evaluateArray x (e.child i)| ≤ A * (e.length : ℝ)^(1/f.r) := by
    apply le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum (fun i _ => ?_)) hp)
    exact abs_eval_supported_interval _ (f.norming_subset_full (he i)) (I i) (hI i)
      (fun a ha => mem_ordinalHull (hs i) ha) x
  have hm : 0 < (f.m e.weight : ℝ) := by exact_mod_cast f.m_pos e.weight
  have heq : norming.evaluateArray x e.value = (1 / (f.m e.weight : ℝ)) *
      ∑ i : Fin e.length, norming.evaluateArray x (e.child i) := by
    simp only [TypeI.value, map_smul, map_sum, Rat.smul_def, Rat.cast_div, Rat.cast_one,
      Rat.cast_natCast]
  rw [heq, abs_mul, abs_of_pos (one_div_pos.mpr hm), Family.theta_formula]
  calc
    _ ≤ (1 / (f.m e.weight : ℝ)) * (A * (e.length : ℝ)^(1/f.r)) :=
      mul_le_mul_of_nonneg_left hb (one_div_nonneg.mpr hm.le)
    _ ≤ (1 / (f.m e.weight : ℝ)) * (A * (f.L e.weight : ℝ)^(1/f.r)) := by
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hm.le)
      apply mul_le_mul_of_nonneg_left _ hA
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast e.length_le)
        (one_div_nonneg.mpr f.r_pos.le)
    _ = _ := by ring

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

structure UnitBlocks (f : Family) (S : Submodule ℝ (Γ →₀ ℝ)) (k : ℕ) where
  vector : Fin k → Γ →₀ ℝ
  mem : ∀ i, vector i ∈ S
  unit : ∀ i, ‖norming.includeFinite (vector i)‖ = 1
  successive : ∀ i j, i < j → ∀ a ∈ (vector i).support, ∀ b ∈ (vector j).support,
    a < b ∧ (f = .mixed → Colors.color a < Colors.color b)
  pure_color : ∀ c, f = .pure c → ∀ i a, a ∈ (vector i).support → Colors.color a = c

lemma UnitBlocks.nonzero {f S k} (v : UnitBlocks f S k) (i : Fin k) : v.vector i ≠ 0 := by
  intro h
  have := v.unit i
  simp [h] at this

noncomputable def UnitBlocks.select {f S k} (v : UnitBlocks f S k) (t : Finset (Fin k)) :
    UnitBlocks f S t.card where
  vector i := v.vector (t.orderEmbOfFin rfl i)
  mem i := v.mem (t.orderEmbOfFin rfl i)
  unit i := v.unit (t.orderEmbOfFin rfl i)
  successive i j hij := v.successive (t.orderEmbOfFin rfl i) (t.orderEmbOfFin rfl j) ((t.orderEmbOfFin rfl).strictMono hij)
  pure_color c hc i := v.pure_color c hc (t.orderEmbOfFin rfl i)

lemma UnitBlocks.select_sum {f S k} (v : UnitBlocks f S k) (t : Finset (Fin k)) :
    ∑ i, (v.select t).vector i = ∑ i ∈ t, v.vector i := by
  change ∑ i, v.vector (t.orderEmbOfFin rfl i) = _
  conv_rhs => rw [← t.map_orderEmbOfFin_univ rfl]
  rw [Finset.sum_map]
  rfl

noncomputable def BlockSequence.unitBlocks {f : Family} (z : BlockSequence f) (a k : ℕ) :
    UnitBlocks f (z.tailSpan a) k where
  vector i := (‖norming.includeFinite (z.vector (i+a))‖⁻¹) • z.vector (i+a)
  mem i := Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  unit i := by
    rw [map_smul, norm_smul, norm_inv, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (fun h => z.nonzero (i+a) (norming.includeFinite_injective (by simpa using h)))
  successive i j hij α hα β hβ := by
    apply z.successive (i+a) (j+a) (by omega) α _ β _
    · exact Finsupp.support_smul hα
    · exact Finsupp.support_smul hβ
  pure_color c hc i α hα := z.pure_color c hc (i+a) α (Finsupp.support_smul hα)

noncomputable def blockSumSup (f : Family) (S : Submodule ℝ (Γ →₀ ℝ)) (k : ℕ) : ℝ :=
  sSup (Set.range (fun v : UnitBlocks f S k => ‖norming.includeFinite (∑ i, v.vector i)‖))

lemma UnitBlocks.norm_sum_le_length {f S k} (v : UnitBlocks f S k) :
    ‖norming.includeFinite (∑ i, v.vector i)‖ ≤ k := by
  rw [map_sum]
  exact (norm_sum_le _ _).trans (by simp [v.unit])

lemma blockSumSup_bdd (f S k) : BddAbove
    (Set.range (fun v : UnitBlocks f S k => ‖norming.includeFinite (∑ i, v.vector i)‖)) :=
  ⟨k, by rintro _ ⟨v, rfl⟩; exact v.norm_sum_le_length⟩

lemma UnitBlocks.norm_sum_le_sup {f S k} (v : UnitBlocks f S k) :
    ‖norming.includeFinite (∑ i, v.vector i)‖ ≤ blockSumSup f S k :=
  le_csSup (blockSumSup_bdd f S k) ⟨v, rfl⟩

lemma UnitBlocks.norm_subsum_le_sup {f S k} (v : UnitBlocks f S k) (t : Finset (Fin k)) :
    ‖norming.includeFinite (∑ i ∈ t, v.vector i)‖ ≤ blockSumSup f S t.card := by
  rw [← v.select_sum t]
  exact (v.select t).norm_sum_le_sup

lemma blockSumSup_nonneg {f S k} (hne : Nonempty (UnitBlocks f S k)) :
    0 ≤ blockSumSup f S k := by
  obtain ⟨v⟩ := hne
  exact (norm_nonneg _).trans v.norm_sum_le_sup

lemma unitBlocks_near_sup {f S k} (hne : Nonempty (UnitBlocks f S k)) (ha : 0 < blockSumSup f S k) :
    ∃ v : UnitBlocks f S k, blockSumSup f S k / 2 < ‖norming.includeFinite (∑ i, v.vector i)‖ := by
  obtain ⟨b, ⟨v, rfl⟩, hv⟩ := exists_lt_of_lt_csSup (s := Set.range
    (fun v : UnitBlocks f S k => ‖norming.includeFinite (∑ i, v.vector i)‖))
    (Set.range_nonempty_iff_nonempty.mpr hne)
    (by linarith : blockSumSup f S k / 2 < blockSumSup f S k)
  exact ⟨v, hv⟩

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

lemma support_mem_vectorCrop (f : Family) (x : Γ →₀ ℝ) (hx : x ≠ 0) (a : Γ)
    (ha : a ∈ x.support) : a ∈ (vectorCrop x hx).set f := by
  have ho := mem_ordinalHull (Finsupp.support_nonempty_iff.mpr hx) ha
  have hc : Colors.color a ∈ (vectorCrop x hx).colors := by
    exact ⟨Finset.min'_le _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩),
      Finset.le_max' _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)⟩
  cases f with
  | pure _ => exact ho
  | mixed => exact ⟨ho, hc⟩

lemma vectorCrop_successive {f : Family} {x y : Γ →₀ ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ∀ a ∈ x.support, ∀ b ∈ y.support,
      a < b ∧ (f = .mixed → Colors.color a < Colors.color b)) :
    ∀ a ∈ (vectorCrop x hx).set f, ∀ b ∈ (vectorCrop y hy).set f,
      a < b ∧ (f = .mixed → Colors.color a < Colors.color b) := by
  intro a ha b hb
  have haO : a ∈ (vectorCrop x hx).ordinal := by cases f <;> simp_all [Crop.set]
  have hbO : b ∈ (vectorCrop y hy).ordinal := by cases f <;> simp_all [Crop.set]
  refine ⟨ordinalHull_successive _ _ (fun c hc d hd => (h c hc d hd).1) a haO b hbO, ?_⟩
  intro hf
  subst f
  obtain ⟨c, hc, hcx⟩ := Finset.mem_image.mp ((x.support.image Colors.color).max'_mem
    ((Finsupp.support_nonempty_iff.mpr hx).image _))
  obtain ⟨d, hd, hdy⟩ := Finset.mem_image.mp ((y.support.image Colors.color).min'_mem
    ((Finsupp.support_nonempty_iff.mpr hy).image _))
  have hcd := (h c hc d hd).2 rfl
  rw [hcx, hdy] at hcd
  exact ha.2.2.trans_lt (hcd.trans_le hb.2.1)

lemma family_norming_crop (f : Family) (A : Crop) (g : Array) (hg : g ∈ f.norming) :
    restrict (A.set f) g ∈ f.norming := by
  cases f with
  | pure k => exact pure_crop k A g hg
  | mixed => exact full_crop A g hg

lemma exists_unit_vector_normer {f : Family} (x : Γ →₀ ℝ) (hx : ‖norming.includeFinite x‖ = 1)
    (hcolor : ∀ k, f = .pure k → ∀ a ∈ x.support, Colors.color a = k) :
    ∃ (g : Array), g ∈ f.norming ∧ g ≠ 0 ∧
      (∀ a ∈ g.support, a ∈ (vectorCrop x (by intro h; simp [h] at hx)).set f) ∧
      1/2 < norming.evaluateArray (norming.includeFinite x) g := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hn : ∃ g ∈ f.norming, 1/2 < norming.evaluateArray (norming.includeFinite x) g := by
    cases f with
    | pure k =>
      apply exists_pure_normer k _ _ _ (by norm_num) (by rw [hx]; norm_num)
      intro a ha
      rw [norming.coordinate_includeFinite]
      exact Finsupp.notMem_support_iff.mp (fun h => ha (hcolor k rfl a h))
    | mixed => exact exists_full_normer _ _ (by norm_num) (by rw [hx]; norm_num)
  obtain ⟨g, hg, hgv⟩ := hn
  let A := vectorCrop x hx0
  have heq : norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) g) =
      norming.evaluateArray (norming.includeFinite x) g := by
    apply evaluateArray_crop_of_zero
    intro a ha
    rw [norming.coordinate_includeFinite]
    exact Finsupp.notMem_support_iff.mp (fun h => ha (support_mem_vectorCrop f x hx0 a h))
  refine ⟨restrict (A.set f) g, family_norming_crop f A g hg, ?_, ?_, by rwa [heq]⟩
  · intro hz
    rw [hz, map_zero] at heq
    linarith
  · intro a ha
    by_contra hn
    change a ∉ A.set f at hn
    exact Finsupp.mem_support_iff.mp ha (by simp [restrict, hn])

lemma evaluateArray_finite_disjoint (x : Γ →₀ ℝ) (g : Array)
    (h : Disjoint x.support g.support) : norming.evaluateArray (norming.includeFinite x) g = 0 := by
  rw [evaluateArray_finite]
  apply Finset.sum_eq_zero
  intro a ha
  have hg : g a = 0 := Finsupp.notMem_support_iff.mp (fun hg => Finset.disjoint_left.mp h ha hg)
  simp [hg]

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BlockEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

lemma UnitBlocks.full_card_sum_le {f S k} (v : UnitBlocks f S k) (d : ℕ)
    (I : Fin d → Set Γ)
    (hIs : ∀ i j, i < j → ∀ a ∈ I i, ∀ b ∈ I j, a < b) :
    ∑ b : Fin d, (Finset.univ.filter (fun i => ((v.vector i).support : Set Γ) ⊆ I b)).card ≤ k := by
  let F := fun b : Fin d => Finset.univ.filter (fun i => ((v.vector i).support : Set Γ) ⊆ I b)
  have hd : ((Finset.univ : Finset (Fin d)) : Set (Fin d)).PairwiseDisjoint F := by
    intro b _ c _ hbc
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hb := (Finset.mem_filter.mp hi).2
    have hc := (Finset.mem_filter.mp hj).2
    obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr (v.nonzero i)
    rcases lt_or_gt_of_ne hbc with hbc | hcb
    · exact (lt_irrefl a) (hIs b c hbc a (hb ha) a (hc ha))
    · exact (lt_irrefl a) (hIs c b hcb a (hc ha) a (hb ha))
  change ∑ b, (F b).card ≤ k
  rw [← Finset.card_biUnion hd]
  simpa using (Finset.card_le_univ (Finset.univ.biUnion F))

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

lemma UnitBlocks.subsum_record {f S k} (v : UnitBlocks f S k) (t : Finset (Fin k))
    (e : ℝ) (he : 0 < e) (_hk : 1 ≤ k)
    (hrec : ∀ l : ℕ, 1 ≤ l → l ≤ k →
      blockSumSup f S l ≤ blockSumSup f S k * ((l : ℝ)/(k : ℝ))^e) :
    ‖norming.includeFinite (∑ i ∈ t, v.vector i)‖ ≤ blockSumSup f S k * ((t.card : ℝ)/(k : ℝ))^e := by
  by_cases ht : t.Nonempty
  · exact v.norm_subsum_le_sup t |>.trans (hrec t.card ht.card_pos (by simpa using t.card_le_univ))
  · rw [Finset.not_nonempty_iff_eq_empty.mp ht]
    simp [Real.zero_rpow he.ne']

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.TailBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

lemma BlockSequence.support_mem_tail {f : Family} (z : BlockSequence f) (a : ℕ)
    {x : Γ →₀ ℝ} (hx : x ∈ z.tailSpan a) {α : Γ} (hα : α ∈ x.support) :
    ∃ n, a ≤ n ∧ α ∈ (z.vector n).support := by
  have hprop : ∀ (u : Γ →₀ ℝ), u ∈ z.tailSpan a →
      ∀ α ∈ u.support, ∃ n, a ≤ n ∧ α ∈ (z.vector n).support := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, rfl⟩ := hy
      intro α hα
      exact ⟨n+a, by omega, hα⟩
    | zero => simp
    | add u v _ _ hu hv =>
      intro α hα
      rcases Finset.mem_union.mp (Finsupp.support_add hα) with h | h
      · exact hu α h
      · exact hv α h
    | smul c u _ hu =>
      intro α hα
      exact hu α (Finsupp.support_smul hα)
  exact hprop x hx α hα

lemma BlockSequence.prefixSupport_mono {f : Family} (z : BlockSequence f) : Monotone z.prefixSupport := by
  intro a b hab
  exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono hab)

lemma BlockSequence.support_subset_prefix {f : Family} (z : BlockSequence f) (a : ℕ)
    {x : Γ →₀ ℝ} (hx : x ∈ z.tailSpan a) : ∃ b, a ≤ b ∧ x.support ⊆ z.prefixSupport b := by
  have hprop : ∀ (u : Γ →₀ ℝ), u ∈ z.tailSpan a →
      ∃ b, a ≤ b ∧ u.support ⊆ z.prefixSupport b := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, rfl⟩ := hy
      refine ⟨n+a+1, by omega, ?_⟩
      intro α hα
      exact Finset.mem_biUnion.mpr ⟨n+a, Finset.mem_range.mpr (by omega), hα⟩
    | zero => exact ⟨a, le_rfl, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨b, hb, hbu⟩ := hu
      obtain ⟨c, hc, hcv⟩ := hv
      refine ⟨max b c, hb.trans (le_max_left _ _), ?_⟩
      intro α hα
      rcases Finset.mem_union.mp (Finsupp.support_add hα) with h | h
      · exact z.prefixSupport_mono (le_max_left _ _) (hbu h)
      · exact z.prefixSupport_mono (le_max_right _ _) (hcv h)
    | smul c u _ hu =>
      obtain ⟨b, hb, hbu⟩ := hu
      exact ⟨b, hb, fun _ h => hbu (Finsupp.support_smul h)⟩
  exact hprop x hx

lemma BlockSequence.prefix_tail_successive {f : Family} (z : BlockSequence f) (b : ℕ)
    {x y : Γ →₀ ℝ} (hx : x.support ⊆ z.prefixSupport b) (hy : y ∈ z.tailSpan b) :
    ∀ α ∈ x.support, ∀ β ∈ y.support,
      α < β ∧ (f = .mixed → Colors.color α < Colors.color β) := by
  intro α hα β hβ
  obtain ⟨i, hi, hiα⟩ := Finset.mem_biUnion.mp (hx hα)
  obtain ⟨j, hj, hjβ⟩ := z.support_mem_tail b hy hβ
  exact z.successive i j (lt_of_lt_of_le (Finset.mem_range.mp hi) hj) α hiα β hjβ

lemma BlockSequence.tailSpan_mono {f : Family} (z : BlockSequence f) {a b : ℕ} (hab : a ≤ b) :
    z.tailSpan b ≤ z.tailSpan a := by
  apply Submodule.span_le.mpr
  rintro u ⟨n, rfl⟩
  apply Submodule.subset_span
  refine ⟨n+(b-a), ?_⟩
  change z.vector (n+(b-a)+a) = z.vector (n+b)
  rw [show n+(b-a)+a = n+b by omega]

lemma BlockSequence.tail_pure_color {f : Family} (z : BlockSequence f) (a : ℕ)
    {x : Γ →₀ ℝ} (hx : x ∈ z.tailSpan a) (c : ℕ) (hc : f = .pure c) :
    ∀ α ∈ x.support, Colors.color α = c := by
  intro α hα
  obtain ⟨n, _, hn⟩ := z.support_mem_tail a hx hα
  exact z.pure_color c hc n α hn

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

lemma BlockSequence.le_prefixRho {f : Family} (z : BlockSequence f) (a : ℕ) {α β : Γ}
    (hα : α ∈ z.prefixSupport a) (hβ : β ∈ z.prefixSupport a) :
    rho (min α β) (max α β) ≤ z.prefixRho a :=
  Finset.le_sup (b := (α, β)) (f := fun p => rho (min p.1 p.2) (max p.1 p.2)) (Finset.mem_product.mpr ⟨hα, hβ⟩)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.SeriesTails
open Filter
open scoped Topology Classical

lemma tail_antitone (a : ℕ → ℝ) (ha : Summable a) (hn : ∀ n, 0 ≤ a n) : Antitone (tail a) := by
  intro N M hNM
  have hs := ((summable_nat_add_iff N).mpr ha).sum_add_tsum_nat_add (M-N)
  have hid : (∑' k, a (k+(M-N)+N)) = tail a M := by
    apply tsum_congr
    intro k
    rw [show k+(M-N)+N = k+M by omega]
  rw [hid] at hs
  have hpos : 0 ≤ ∑ k ∈ Finset.range (M-N), a (k+N) := Finset.sum_nonneg (fun _ _ => hn _)
  change tail a M ≤ ∑' k, a (k+N)
  linarith

end SeparableQuotient.SeriesTails

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

lemma vectorL1_eq_sum {x : Γ →₀ ℝ} {s : Finset Γ} (hs : x.support ⊆ s) :
    vectorL1 x = ∑ a ∈ s, |x a| := by
  apply Finset.sum_subset hs
  intro a _ ha
  rw [Finsupp.notMem_support_iff.mp ha, abs_zero]

lemma vectorL1_sub_le (x y : Γ →₀ ℝ) : vectorL1 (x-y) ≤ vectorL1 x + vectorL1 y := by
  rw [vectorL1_eq_sum Finsupp.support_sub,
    vectorL1_eq_sum (Finset.subset_union_left : x.support ⊆ x.support ∪ y.support),
    vectorL1_eq_sum (Finset.subset_union_right : y.support ⊆ x.support ∪ y.support), ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => abs_sub _ _)

lemma PartitionBound.mono {x : E} {N M : ℕ} {A r : ℝ} (h : PartitionBound x N A r) (hMN : M ≤ N) :
    PartitionBound x M A r := fun d hd hdM => h d hd (hdM.trans hMN)

lemma PartitionBound.sub {x y : E} {N : ℕ} {A B r : ℝ}
    (hx : PartitionBound x N A r) (hy : PartitionBound y N B r) :
    PartitionBound (x-y) N (A+B) r := by
  intro d hd hdN I hI hIs
  calc
    _ ≤ ∑ b, (‖intervalProjection (I b) (hI b) x‖ + ‖intervalProjection (I b) (hI b) y‖) := by
      apply Finset.sum_le_sum
      intro b _
      rw [map_sub]
      exact norm_sub_le _ _
    _ = (∑ b, ‖intervalProjection (I b) (hI b) x‖) + (∑ b, ‖intervalProjection (I b) (hI b) y‖) := Finset.sum_add_distrib
    _ ≤ A * (d : ℝ)^(1/r) + B * (d : ℝ)^(1/r) := add_le_add (hx d hd hdN I hI hIs) (hy d hd hdN I hI hIs)
    _ = _ := by ring

noncomputable def BlockSequence.subsequence {f : Family} (z : BlockSequence f) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    BlockSequence f where
  vector n := z.vector (φ n)
  nonzero n := z.nonzero (φ n)
  successive i j hij := z.successive (φ i) (φ j) (hφ hij)
  pure_color c hc n := z.pure_color c hc (φ n)

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.WindowThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

lemma FamilyL_mono (f : Family) : Monotone f.L := by
  intro i j hij
  exact (Parameters.L_strict f.s_ge_two).monotone (Nat.sub_le_sub_right hij 1)

lemma tail_sub_mul_le {f : Family} (x y : Γ →₀ ℝ) (T U : ℕ) (hTU : T ≤ U) :
    vectorL1 (x-y) * tail (fun j => 1/(f.m j : ℝ)) (U+1) ≤
    vectorL1 x * tail (fun j => 1/(f.m j : ℝ)) (T+1) +
    vectorL1 y * tail (fun j => 1/(f.m j : ℝ)) (U+1) := by
  have hn : ∀ j, 0 ≤ 1/(f.m j : ℝ) := fun _ => by positivity
  calc
    _ ≤ (vectorL1 x+vectorL1 y) * tail (fun j => 1/(f.m j : ℝ)) (U+1) :=
      mul_le_mul_of_nonneg_right (vectorL1_sub_le x y) (tail_nonneg _ hn _)
    _ = vectorL1 x * tail (fun j => 1/(f.m j : ℝ)) (U+1) +
      vectorL1 y * tail (fun j => 1/(f.m j : ℝ)) (U+1) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
      (tail_antitone _ f.m_inv_summable hn (Nat.add_le_add_right hTU 1)) (vectorL1_nonneg x)) le_rfl

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.AdaptiveThinning
open scoped Classical

variable (R : ℕ → ℕ → Set ℕ → Prop)
variable (hR : ∀ n i (N : Set ℕ), N.Infinite → ∃ W ⊆ N, W.Infinite ∧ R n i W)

noncomputable def initial : State R 0 :=
  let s := choice R hR 0 Set.univ Set.infinite_univ
  ⟨s.index, s.rest, s.infinite, s.later, s.good⟩

noncomputable def next {n : ℕ} (s : State R n) : State R (n+1) :=
  let t := choice R hR (n+1) s.rest s.infinite
  ⟨t.index, t.rest, t.infinite, t.later, t.good⟩

lemma next_mem {n : ℕ} (s : State R n) : (next R hR s).index ∈ s.rest :=
  (choice R hR (n+1) s.rest s.infinite).mem

lemma next_subset {n : ℕ} (s : State R n) : (next R hR s).rest ⊆ s.rest :=
  (choice R hR (n+1) s.rest s.infinite).subset

noncomputable def state : (n : ℕ) → State R n
  | 0 => initial R hR
  | n+1 => next R hR (state n)

lemma index_strict : StrictMono (fun n => (state R hR n).index) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (state R hR n).later _ (next_mem R hR (state R hR n))

lemma rest_antitone : Antitone (fun n => (state R hR n).rest) := by
  apply antitone_nat_of_succ_le
  intro n
  exact next_subset R hR (state R hR n)

lemma later_mem {n m : ℕ} (hnm : n < m) : (state R hR m).index ∈ (state R hR n).rest := by
  have hm : 0 < m := Nat.zero_lt_of_lt hnm
  have hh : m = (m-1)+1 := by omega
  rw [hh]
  exact rest_antitone R hR (show n ≤ m-1 by omega) (next_mem R hR (state R hR (m-1)))

include hR in
/-- Repeated infinite thinning where the new relation can depend on the already
selected index and its position. No uniform-threshold or countability assumption
on the predicate R is required. -/
theorem exists_adaptive : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ W : ℕ → Set ℕ,
    (∀ n, R n (φ n) (W n)) ∧ (∀ n m, n < m → φ m ∈ W n) := by
  exact ⟨fun n => (state R hR n).index, index_strict R hR,
    fun n => (state R hR n).rest, fun n => (state R hR n).good,
    fun _ _ h => later_mem R hR h⟩

end SeparableQuotient.AdaptiveThinning

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.WindowCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

/-- A crop meets but does not contain an actual finite block support. -/
def PartialBlock {f : Family} (z : BlockSequence f) (A : Crop) (i : ℕ) : Prop :=
  (∃ a ∈ (z.vector i).support, a ∈ A.set f) ∧ ¬ (↑(z.vector i).support : Set Γ) ⊆ A.set f

lemma BlockSequence.partial_crop_le_four {f : Family} (z : BlockSequence f) (A : Crop) (s : Finset ℕ) :
    (s.filter (PartialBlock z A)).card ≤ 4 := by
  cases f with
  | pure k =>
    have ho := IntervalIncidence.partial_intersections_le_two s (fun i => (z.vector i).support)
      (fun i j hij a ha b hb => (z.successive i j hij a ha b hb).1) A.ordinal A.ordinal_convex
    have he : s.filter (PartialBlock z A) =
        s.filter (fun i => (∃ a ∈ (z.vector i).support, a ∈ A.ordinal) ∧ ¬ (↑(z.vector i).support : Set Γ) ⊆ A.ordinal) := by
      ext i
      simp [PartialBlock, Crop.set]
    rw [he]
    omega
  | mixed =>
    have ho := IntervalIncidence.partial_intersections_le_two s (fun i => (z.vector i).support)
      (fun i j hij a ha b hb => (z.successive i j hij a ha b hb).1) A.ordinal A.ordinal_convex
    let F (i : ℕ) : Finset ℕ := (z.vector i).support.image Colors.color
    have hF : ∀ i j, i < j → ∀ a ∈ F i, ∀ b ∈ F j, a < b := by
      intro i j hij a ha b hb
      obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hb
      exact (z.successive i j hij α hα β hβ).2 rfl
    have hc := IntervalIncidence.partial_intersections_le_two s F hF A.colors A.colors_convex
    let O := s.filter (fun i => (∃ a ∈ (z.vector i).support, a ∈ A.ordinal) ∧
      ¬ (↑(z.vector i).support : Set Γ) ⊆ A.ordinal)
    let C := s.filter (fun i => (∃ a ∈ F i, a ∈ A.colors) ∧ ¬ (↑(F i) : Set ℕ) ⊆ A.colors)
    have hsub : s.filter (PartialBlock z A) ⊆ O ∪ C := by
      intro i hi
      obtain ⟨hi, ⟨a, ha, hao, hac⟩, hnot⟩ := Finset.mem_filter.mp hi
      by_cases hO : (↑(z.vector i).support : Set Γ) ⊆ A.ordinal
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨hi, ⟨Colors.color a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, hac⟩, ?_⟩
        intro hC
        apply hnot
        intro b hb
        exact ⟨hO hb, hC (Finset.mem_image.mpr ⟨b, hb, rfl⟩)⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, ⟨a, ha, hao⟩, hO⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by dsimp [O,C]; omega))

lemma evaluateArray_crop_finite_fixed {f : Family} (x : Γ →₀ ℝ) (A : Crop)
    (hx : (↑x.support : Set Γ) ⊆ A.set f) (g : Array) :
    norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) g) =
      norming.evaluateArray (norming.includeFinite x) g := by
  apply evaluateArray_crop_of_zero
  intro a ha
  rw [norming.coordinate_includeFinite]
  exact Finsupp.notMem_support_iff.mp (fun hh => ha (hx hh))

lemma evaluateArray_crop_nonzero_support {f : Family} (x : Γ →₀ ℝ) (A : Crop) (g : Array)
    (h : norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) g) ≠ 0) :
    ∃ a ∈ x.support, a ∈ A.set f := by
  by_contra hn
  push Not at hn
  apply h
  rw [evaluateArray_finite]
  apply Finset.sum_eq_zero
  intro a ha
  simp [restrict_apply, hn a ha]

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

/-- The weighted absolute column estimate, obtained using the actual rational
Type II normers and density of rational coefficients, not an assumed dual ball. -/
lemma cropped_weighted_abs_sum_bound {f : Family} {h : ℕ} (P : Fin h → FinitePath f)
    (A : Fin h → Crop) (hm : ∀ b i j, ((P b).piece i).child j ∈ f.norming)
    (hdis : Pairwise (fun i j => Disjoint ((P i).active (A i)) ((P j).active (A j))))
    (c : Fin h → ℝ) (x : E) :
    (∑ i, |c i| * |croppedPathFunctional (P i) (A i) x|) ≤
      (∑ i, |c i|^f.q)^(1/f.q) * ‖x‖ := by
  let d : Fin h → ℝ := fun i => |c i| * RealCoefficients.signChoice (croppedPathFunctional (P i) (A i) x)
  have hd (i : Fin h) : |d i| = |c i| := by simp only [d, abs_mul, abs_abs, RealCoefficients.abs_signChoice, mul_one]
  have he : (∑ i, d i • croppedPathFunctional (P i) (A i)) x =
      ∑ i, |c i| * |croppedPathFunctional (P i) (A i) x| := by
    simp only [sum_apply, smul_apply, smul_eq_mul, d, mul_assoc, RealCoefficients.signChoice_mul]
  calc
    _ = |(∑ i, d i • croppedPathFunctional (P i) (A i)) x| := by
      rw [he, abs_of_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))]
    _ ≤ ‖∑ i, d i • croppedPathFunctional (P i) (A i)‖ * ‖x‖ :=
      by simpa only [Real.norm_eq_abs] using (∑ i, d i • croppedPathFunctional (P i) (A i)).le_opNorm x
    _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa only [hd] using real_cropped_path_bound P A hm hdis d) (norm_nonneg _)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

lemma firstNonzero_mem {s : Finset ℕ} {t : ℕ → ℝ} {i : ℕ} (hi : i ∈ s) (ht : t i ≠ 0) :
    firstNonzero s t ∈ s ∧ t (firstNonzero s t) ≠ 0 := by
  have h : (s.filter (fun i => t i ≠ 0)).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, ht⟩⟩
  rw [firstNonzero, dite_eq_left h]
  exact Finset.mem_filter.mp (Finset.min'_mem _ h)

lemma firstNonzero_le {s : Finset ℕ} {t : ℕ → ℝ} {i : ℕ} (hi : i ∈ s) (ht : t i ≠ 0) :
    firstNonzero s t ≤ i := by
  have h : (s.filter (fun i => t i ≠ 0)).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, ht⟩⟩
  rw [firstNonzero, dite_eq_left h]
  exact Finset.min'_le _ i (Finset.mem_filter.mpr ⟨hi, ht⟩)

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.MarkedEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.FiniteVectors
open scoped Classical ENNReal
universe u
variable {ι : Type u} [Fintype ι]

lemma norm_mono_exponent {p r : ℝ≥0∞} (hp : 0 < p.toReal) (hpr : p.toReal ≤ r.toReal)
    (v : ι → ℝ) : ‖vec r v‖ ≤ ‖vec p v‖ := by
  apply norm_le (hp.trans_le hpr) _ _ (lp.norm_nonneg' (vec p v))
  exact sum_rpow_larger v p.toReal r.toReal _ hp hpr (lp.norm_nonneg' (vec p v)) (le_of_eq (norm_rpow hp v).symm)

lemma norm_const {p : ℝ≥0∞} (hp : 0 < p.toReal) (c : ℝ) :
    ‖vec p (fun _ : ι => c)‖ = |c| * (Fintype.card ι : ℝ)^(1/p.toReal) := by
  apply (Real.rpow_left_inj (lp.norm_nonneg' (vec p (fun _ : ι => c))) (by positivity) hp.ne').mp
  rw [norm_rpow hp, Real.mul_rpow (abs_nonneg _) (by positivity),
    ← Real.rpow_mul (Nat.cast_nonneg _), one_div_mul_cancel hp.ne', Real.rpow_one]
  simp [mul_comm]

end SeparableQuotient.FiniteVectors

namespace SeparableQuotient.FiniteVectors
open scoped Classical ENNReal
universe u v
variable {ι : Type u} [Fintype ι] {β : Type v} [Fintype β]

lemma norm_eq_rpow {p : ℝ≥0∞} (hp : 0 < p.toReal) (v : ι → ℝ) :
    ‖vec p v‖ = (∑ i, |v i|^p.toReal)^(1/p.toReal) := by
  rw [← norm_rpow hp, ← Real.rpow_mul (lp.norm_nonneg' _), mul_one_div_cancel hp.ne', Real.rpow_one]

lemma sum_abs_le_norm (p : ℝ) (hp : 1 < p) (v : ι → ℝ) :
    ∑ i, |v i| ≤ ‖vec (ENNReal.ofReal p) v‖ * (Fintype.card ι : ℝ)^(1-1/p) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have he : 0 < 1-1/p := sub_pos.mpr ((div_lt_one hp0).mpr hp)
  have hc : Real.HolderConjugate p (1/(1-1/p)) := {
    inv_add_inv_eq_inv := by simp [one_div]
    left_pos := hp0
    right_pos := by positivity }
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ (f := fun i => |v i|)
    (g := fun _ => (1 : ℝ)) hc (fun i _ => abs_nonneg _) (fun _ _ => zero_le_one)
  simpa only [mul_one, Real.one_rpow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    one_div_one_div, norm_eq_rpow (by simpa only [ENNReal.toReal_ofReal hp0.le] using hp0 : 0 < (ENNReal.ofReal p).toReal),
    ENNReal.toReal_ofReal hp0.le] using h

/-- Eight marked entries per row imply the precise uniform marked charge,
using only the actual column Hölder bound. -/
lemma marked_norm_bound (q : ℝ) (hq : 1 < q) (r : ℝ≥0∞) (hqr : q ≤ r.toReal)
    (a : β → ℝ) (ha : ∑ b, |a b|^q ≤ 1) (marks : β → Finset ι)
    (hmarks : ∀ b, (marks b).card ≤ 8) (M : ι → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hcolumn : ∀ i, M i ≤ 2 * (∑ b, if i ∈ marks b then |a b|^q else 0)^(1/q)) :
    ‖vec r M‖ ≤ 16 ∧ ∑ i, M i ≤ 16*(Fintype.card ι : ℝ)^(1-1/q) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  let H (i : ι) : ℝ := ∑ b, if i ∈ marks b then |a b|^q else 0
  have hH (i : ι) : 0 ≤ H i := by apply Finset.sum_nonneg; intro b _; split_ifs <;> positivity
  have hHsum : ∑ i, H i ≤ 8 := by
    dsimp only [H]
    rw [Finset.sum_comm]
    calc
      _ = ∑ b, ((marks b).card : ℝ) * |a b|^q := by
        apply Finset.sum_congr rfl
        intro b _
        simp
      _ ≤ ∑ b, 8 * |a b|^q := Finset.sum_le_sum (fun b _ =>
        mul_le_mul_of_nonneg_right (by exact_mod_cast hmarks b) (Real.rpow_nonneg (abs_nonneg _) _))
      _ = 8 * ∑ b, |a b|^q := (Finset.mul_sum ..).symm
      _ ≤ 8 := by linarith
  have hpow (i : ι) : |M i|^q ≤ 2^q * H i := by
    rw [abs_of_nonneg (hM i)]
    calc
      _ ≤ (2*H i^(1/q))^q := Real.rpow_le_rpow (hM i) (hcolumn i) hq0.le
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (hH i) _),
          ← Real.rpow_mul (hH i), one_div_mul_cancel hq0.ne', Real.rpow_one]
  have hbound : ‖vec (ENNReal.ofReal q) M‖ ≤ 2*(8 : ℝ)^(1/q) := by
    apply norm_le (by simpa only [ENNReal.toReal_ofReal hq0.le] using hq0 : 0 < (ENNReal.ofReal q).toReal) _ _ (by positivity)
    rw [ENNReal.toReal_ofReal hq0.le, Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8), one_div_mul_cancel hq0.ne', Real.rpow_one]
    exact (Finset.sum_le_sum (fun i _ => hpow i)).trans (by rw [← Finset.mul_sum]; gcongr)
  have h16 : ‖vec (ENNReal.ofReal q) M‖ ≤ 16 := by
    apply hbound.trans
    have he : 1/q ≤ 1 := (div_le_one hq0).mpr hq.le
    have hh : (8 : ℝ)^(1/q) ≤ 8 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 8) he
    linarith
  refine ⟨(norm_mono_exponent (by simpa only [ENNReal.toReal_ofReal hq0.le] using hq0 : 0 < (ENNReal.ofReal q).toReal)
    (by simpa only [ENNReal.toReal_ofReal hq0.le] using hqr) M).trans h16, ?_⟩
  simpa only [abs_of_nonneg (hM _)] using (sum_abs_le_norm q hq M).trans
    (mul_le_mul_of_nonneg_right h16 (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end SeparableQuotient.FiniteVectors

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NormingTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

noncomputable def TypeI.childRange {f : Family} (e : TypeI f) (h : Fin e.length) : Set Γ :=
  ordinalHull (e.child h).support (Finsupp.support_nonempty_iff.mpr (e.child_nonzero h))

lemma TypeI.childRange_connected {f : Family} (e : TypeI f) (h : Fin e.length) :
    Set.OrdConnected (TypeI.childRange e h) := ordinalHull_connected _ _

lemma TypeI.mem_childRange {f : Family} (e : TypeI f) (h : Fin e.length) {a : Γ}
    (ha : a ∈ (e.child h).support) : a ∈ TypeI.childRange e h := mem_ordinalHull _ ha

lemma TypeI.childRange_successive {f : Family} (e : TypeI f) (h k : Fin e.length) (hhk : h < k) :
    ∀ a ∈ TypeI.childRange e h, ∀ b ∈ TypeI.childRange e k, a < b :=
  ordinalHull_successive _ _ (fun a ha b hb => (e.successive h k hhk a ha b hb).1)

noncomputable def TypeI.hitChildren {f : Family} (e : TypeI f) (x : Γ →₀ ℝ) : Finset (Fin e.length) :=
  Finset.univ.filter (fun h => ∃ a ∈ x.support, a ∈ TypeI.childRange e h)

lemma TypeI.cropped_child_zero {f : Family} (e : TypeI f) (A : Crop) (x : Γ →₀ ℝ)
    (h : Fin e.length) (hh : h ∉ TypeI.hitChildren e x) :
    norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) (e.child h)) = 0 := by
  rw [norming.evaluateArray_eq]
  apply Finset.sum_eq_zero
  intro a ha
  have haR := TypeI.mem_childRange e h (restrict_support_subset _ _ ha)
  have hxa : x a = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hx
    exact hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, hx, haR⟩)
  simp only [norming.coordinate_includeFinite,hxa,mul_zero]

lemma TypeI.cropped_child_bound {f : Family} (e : TypeI f) (A : Crop)
    (he : ∀ h, e.child h ∈ f.norming) (x : E) (h : Fin e.length) :
    |norming.evaluateArray x (restrict (A.set f) (e.child h))| ≤
      ‖intervalProjection (TypeI.childRange e h) (TypeI.childRange_connected e h) x‖ :=
  abs_eval_supported_interval _ (f.norming_subset_full (family_norming_crop f A _ (he h)))
    _ _ (fun _ ha => TypeI.mem_childRange e h (restrict_support_subset _ _ ha)) x

lemma TypeI.cropped_child_sum_bound {f : Family} (e : TypeI f) (A : Crop)
    (he : ∀ h, e.child h ∈ f.norming) (x : Γ →₀ ℝ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hx : PartitionBound (norming.includeFinite x) N C f.r)
    (hL : e.length ≤ N) :
    ∑ h, |norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) (e.child h))| ≤
      C * ((TypeI.hitChildren e x).card : ℝ)^(1/f.r) := by
  let S := TypeI.hitChildren e x
  have heq : (∑ h, |norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) (e.child h))|) =
      ∑ h ∈ S, |norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) (e.child h))| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro h _ hh
    simp only [TypeI.cropped_child_zero e A x h hh,abs_zero]
  rw [heq]
  by_cases hS : S.Nonempty
  · let idx := S.orderEmbOfFin rfl
    have hN : S.card ≤ N := (Finset.card_le_univ S).trans (by simpa only [Fintype.card_fin] using hL)
    have hp := hx S.card (by exact hS.card_pos) hN
      (fun i => TypeI.childRange e (idx i)) (fun i => TypeI.childRange_connected e (idx i))
      (fun i j hij => TypeI.childRange_successive e _ _ (idx.strictMono hij))
    calc
      _ ≤ ∑ h ∈ S, ‖intervalProjection (TypeI.childRange e h) (TypeI.childRange_connected e h) (norming.includeFinite x)‖ :=
        Finset.sum_le_sum (fun h _ => TypeI.cropped_child_bound e A he _ h)
      _ = ∑ i : Fin S.card, ‖intervalProjection (TypeI.childRange e (idx i)) (TypeI.childRange_connected e (idx i)) (norming.includeFinite x)‖ := by
        conv_lhs => rw [← S.map_orderEmbOfFin_univ rfl]
        rw [Finset.sum_map]
        rfl
      _ ≤ _ := hp
  · have hSE : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hSE,Finset.sum_empty]
    exact mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma TypeI.hitChildren_noncrossing {f : Family} (e : TypeI f) (z : BlockSequence f)
    (i j : ℕ) (hij : i < j) (h k : Fin e.length)
    (hh : h ∈ TypeI.hitChildren e (z.vector i)) (hk : k ∈ TypeI.hitChildren e (z.vector j)) : h ≤ k := by
  apply le_of_not_gt
  intro hkh
  obtain ⟨a, ha, haR⟩ := (Finset.mem_filter.mp hh).2
  obtain ⟨b, hb, hbR⟩ := (Finset.mem_filter.mp hk).2
  have hab := (z.successive i j hij a ha b hb).1
  have hba := TypeI.childRange_successive e k h hkh b hbR a haR
  exact (lt_asymm hab hba)

lemma TypeI.boundary_incidence {f : Family} (e : TypeI f) (z : BlockSequence f) (s : Finset ℕ) :
    ∑ i ∈ s.filter (fun i => 2 ≤ (TypeI.hitChildren e (z.vector i)).card),
      (TypeI.hitChildren e (z.vector i)).card ≤ 2 * e.length := by
  have hh := IntervalIncidence.noncrossing_boundary_incidence s (Finset.univ : Finset (Fin e.length))
      (fun i h => h ∈ TypeI.hitChildren e (z.vector i))
      (fun i _ j _ hij h _ k _ hi hk => TypeI.hitChildren_noncrossing e z i j hij h k hi hk)
  simpa only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.card_univ,Fintype.card_fin] using hh

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.FiniteVectors
open scoped Classical ENNReal
universe u v
variable {ι : Type u} [Fintype ι] {κ : Type v}

lemma vec_sum (p : ℝ≥0∞) (s : Finset κ) (v : κ → ι → ℝ) :
    vec p (fun i => ∑ k ∈ s, v k i) = ∑ k ∈ s, vec p (v k) := by
  apply lp.ext
  funext i
  simp only [vec_apply,lp.coeFn_sum,Finset.sum_apply]

lemma norm_sum_disjoint_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal)
    (s : Finset κ) (v : κ → ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hd : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → ∀ i, v k i = 0 ∨ v l i = 0)
    (hb : ∀ k ∈ s, ‖vec p (v k)‖ ≤ K) :
    ‖vec p (fun i => ∑ k ∈ s, v k i)‖ ≤ K * (s.card : ℝ)^(1/p.toReal) := by
  rw [vec_sum]
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (by positivity) hp).mp
  rw [LpFinite.norm_sum_rpow hp s (fun k => vec p (v k)) hd,
    Real.mul_rpow hK (by positivity), ← Real.rpow_mul (Nat.cast_nonneg _),
    one_div_mul_cancel hp.ne',Real.rpow_one]
  calc
    _ ≤ ∑ _k ∈ s, K^p.toReal := Finset.sum_le_sum (fun k hk =>
      Real.rpow_le_rpow (norm_nonneg _) (hb k hk) hp.le)
    _ = _ := by simp [mul_comm]

lemma norm_degree_le {p : ℝ≥0∞} (hp : 0 < p.toReal) (d : ι → ℝ) (A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i ≤ C)
    (v : ι → ℝ) (hv : ∀ i, |v i| ≤ A*(d i)^(1/p.toReal)) :
    ‖vec p v‖ ≤ A*C^(1/p.toReal) := by
  apply norm_le hp _ _ (by positivity)
  calc
    _ ≤ ∑ i, (A*(d i)^(1/p.toReal))^p.toReal :=
      Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow (abs_nonneg _) (hv i) hp.le)
    _ = A^p.toReal * ∑ i, d i := by
      simp_rw [Real.mul_rpow hA (Real.rpow_nonneg (hd _) _), ← Real.rpow_mul (hd _),
        one_div_mul_cancel hp.ne',Real.rpow_one]
      rw [Finset.mul_sum]
    _ ≤ A^p.toReal*C := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hA _)
    _ = _ := by
      rw [Real.mul_rpow hA (Real.rpow_nonneg hC _), ← Real.rpow_mul hC,
        one_div_mul_cancel hp.ne',Real.rpow_one]

lemma sum_abs_le_holder {p : ℝ≥0∞} (hp : 1 < p.toReal) (v : ι → ℝ) :
    ∑ i, |v i| ≤ (Fintype.card ι : ℝ)^(1-1/p.toReal) * ‖vec p v‖ := by
  have hcon := Real.HolderConjugate.conjExponent hp
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ (f := fun i => |v i|)
    (g := fun _ => (1 : ℝ)) hcon (fun i _ => abs_nonneg _) (fun _ _ => zero_le_one)
  have hroot : (∑ i, |v i|^p.toReal)^(1/p.toReal) = ‖vec p v‖ := by
    rw [← norm_rpow (zero_lt_one.trans hp), ← Real.rpow_mul (lp.norm_nonneg' _),
      mul_one_div_cancel (zero_lt_one.trans hp).ne',Real.rpow_one]
  have hq : 1/Real.conjExponent p.toReal = 1-1/p.toReal := by
    dsimp [Real.conjExponent]
    field_simp
  simpa only [mul_one,Real.one_rpow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hroot,hq,mul_comm] using hh

end SeparableQuotient.FiniteVectors

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

abbrev TypeII.Group {f : Family} (e : TypeII f) := Σ b : Fin e.length, Fin (e.path b).length

noncomputable def TypeII.groupValue {f : Family} (e : TypeII f) (g : TypeII.Group e) : Array :=
  restrict ((e.crop g.1).set f) (((e.path g.1).piece g.2).value)

def TypeII.groupWeight {f : Family} (e : TypeII f) (g : TypeII.Group e) : ℕ :=
  ((e.path g.1).piece g.2).weight

noncomputable def TypeII.activeGroups {f : Family} (e : TypeII f) : Finset (TypeII.Group e) :=
  Finset.univ.filter (fun g => TypeII.groupValue e g ≠ 0)

lemma TypeII.groupWeight_active {f : Family} (e : TypeII f) {g : TypeII.Group e}
    (hg : g ∈ TypeII.activeGroups e) : TypeII.groupWeight e g ∈ (e.path g.1).active (e.crop g.1) := by
  apply Finset.mem_image.mpr
  refine ⟨g.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · simpa only [TypeII.groupValue,(e.path g.1).value_eq g.2] using (Finset.mem_filter.mp hg).2
  · exact ((e.path g.1).weight_eq g.2).symm

lemma TypeII.groupWeight_injOn {f : Family} (e : TypeII f) :
    Set.InjOn (TypeII.groupWeight e) (TypeII.activeGroups e) := by
  intro g hg h hh hw
  obtain ⟨b,i⟩ := g
  obtain ⟨c,j⟩ := h
  have hbc : b = c := by
    by_contra hbc
    exact Finset.disjoint_left.mp (e.disjoint_active hbc)
      (TypeII.groupWeight_active e hg) (hw.symm ▸ TypeII.groupWeight_active e hh)
  subst c
  have hij : i = j := by
    apply (e.path b).valid.weight_strict.injective
    exact ((e.path b).weight_eq i).symm.trans (hw.trans ((e.path b).weight_eq j))
  subst j
  rfl

lemma TypeII.value_group_sum {f : Family} (e : TypeII f) :
    e.value = ∑ g ∈ TypeII.activeGroups e, e.coefficient g.1 • TypeII.groupValue e g := by
  have heq : e.value = ∑ g : TypeII.Group e, e.coefficient g.1 • TypeII.groupValue e g := by
    rw [Fintype.sum_sigma]
    change (∑ b, e.coefficient b • restrict ((e.crop b).set f) (e.path b).value) = _
    apply Finset.sum_congr rfl
    intro b _
    simp only [FinitePath.value,restrict_sum,Finset.smul_sum,TypeII.groupValue,(e.path b).value_eq]
  rw [heq]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro g _ hg
  have hz : TypeII.groupValue e g = 0 := by simpa only [TypeII.activeGroups,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hg
  simp only [hz,smul_zero]

lemma TypeII.eval_group_sum {f : Family} (e : TypeII f) (x : E) :
    norming.evaluateArray x e.value = ∑ g ∈ TypeII.activeGroups e,
      (e.coefficient g.1 : ℝ) * norming.evaluateArray x (TypeII.groupValue e g) := by
  rw [TypeII.value_group_sum]
  simp only [map_sum,map_smul,Rat.smul_def]

lemma typeI_cropped_eval_le_l1 {f : Family} (e : TypeI f) (A : Crop)
    (hm : ∀ j, e.child j ∈ f.norming) (x : Γ →₀ ℝ) :
    |norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) e.value)| ≤
      vectorL1 x * (1 / (f.m e.weight : ℝ)) := by
  rw [evaluateArray_finite]
  calc
    _ ≤ ∑ a ∈ x.support, |((restrict (A.set f) e.value) a : ℝ) * x a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ x.support, (1 / (f.m e.weight : ℝ)) * |x a| := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      by_cases ha : a ∈ A.set f
      · simpa only [restrict_apply,ite_eq_left ha] using e.coefficient_bound
          (fun j b => full_coefficient_bound _ (f.norming_subset_full (hm j)) b) a
      · simp only [restrict_apply,ite_eq_right ha,Rat.cast_zero,abs_zero]
        positivity
    _ = _ := by rw [← Finset.mul_sum]; dsimp [vectorL1]; ring

lemma TypeII.high_weight_bound {f : Family} (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (x : Γ →₀ ℝ) (T : ℕ) :
    ∑ g ∈ (TypeII.activeGroups e).filter (fun g => T < TypeII.groupWeight e g),
      |(e.coefficient g.1 : ℝ)| * |norming.evaluateArray (norming.includeFinite x) (TypeII.groupValue e g)| ≤
      vectorL1 x * tail (fun j => 1/(f.m j : ℝ)) (T+1) := by
  let S := (TypeII.activeGroups e).filter (fun g => T < TypeII.groupWeight e g)
  have hsum : ∑ g ∈ S, 1/(f.m (TypeII.groupWeight e g) : ℝ) ≤ tail (fun j => 1/(f.m j : ℝ)) (T+1) :=
    sum_le_tail _ f.m_inv_summable (fun _ => by positivity) S (TypeII.groupWeight e)
      ((TypeII.groupWeight_injOn e).mono (Finset.filter_subset _ _)) (T+1)
      (fun g hg => by have h := (Finset.mem_filter.mp hg).2; omega)
  calc
    _ ≤ ∑ g ∈ S, vectorL1 x * (1/(f.m (TypeII.groupWeight e g) : ℝ)) := by
      apply Finset.sum_le_sum
      intro g _
      apply le_trans (mul_le_mul_of_nonneg_right (e.coefficient_le_one g.1) (abs_nonneg _))
      simpa only [one_mul,TypeII.groupValue,TypeII.groupWeight] using
        typeI_cropped_eval_le_l1 ((e.path g.1).piece g.2) (e.crop g.1) (hm g.1 g.2) x
    _ = vectorL1 x * ∑ g ∈ S, 1/(f.m (TypeII.groupWeight e g) : ℝ) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (vectorL1_nonneg x)

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.TreeCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology

lemma TypeI.eval_crop_sum {f : Family} (e : TypeI f) (A : Crop) (x : E) :
    norming.evaluateArray x (restrict (A.set f) e.value) =
      (1/(f.m e.weight : ℝ)) * ∑ h, norming.evaluateArray x (restrict (A.set f) (e.child h)) := by
  simp only [TypeI.value,restrict_smul,restrict_sum,map_smul,map_sum,Rat.smul_def,
    Rat.cast_div,Rat.cast_one,Rat.cast_natCast]

noncomputable def TypeI.boundaryDegree {f : Family} (e : TypeI f) (z : BlockSequence f) (i : ℕ) : ℝ :=
  if 2 ≤ (TypeI.hitChildren e (z.vector i)).card then (TypeI.hitChildren e (z.vector i)).card else 0

lemma TypeI.boundaryDegree_nonneg {f : Family} (e : TypeI f) (z : BlockSequence f) (i : ℕ) :
    0 ≤ TypeI.boundaryDegree e z i := by unfold TypeI.boundaryDegree; split_ifs <;> positivity

lemma TypeI.boundaryDegree_sum {f : Family} (e : TypeI f) (z : BlockSequence f) (s : Finset ℕ) :
    (∑ i : s, TypeI.boundaryDegree e z i) ≤ 2 * (e.length : ℝ) := by
  have he : (∑ i : s, TypeI.boundaryDegree e z i) =
      ((∑ i ∈ s.filter (fun i => 2 ≤ (TypeI.hitChildren e (z.vector i)).card),
        (TypeI.hitChildren e (z.vector i)).card : ℕ) : ℝ) := by
    simp only [TypeI.boundaryDegree,Finset.sum_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]
    exact (Finset.sum_coe_sort s (fun i : ℕ => if 2 ≤ (TypeI.hitChildren e (z.vector i)).card then ((TypeI.hitChildren e (z.vector i)).card : ℝ) else 0))
  rw [he]
  exact_mod_cast TypeI.boundary_incidence e z s

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology

lemma Family.sum_theta_le {κ : Type*} (f : Family) (S : Finset κ) (j : κ → ℕ)
    (hp : ∀ g ∈ S, 1 ≤ j g) (hinj : Set.InjOn j S) :
    ∑ g ∈ S, f.theta (j g) ≤ 1/8 := by
  have hi : Set.InjOn (fun g => j g - 1) S := by
    intro g hg h hh he
    apply hinj hg hh
    have := hp g hg
    have := hp h hh
    dsimp only at he
    omega
  calc
    _ = ∑ n ∈ S.image (fun g => j g - 1), Parameters.theta f.s n := by
      rw [Finset.sum_image hi]
      rfl
    _ ≤ ∑' n, Parameters.theta f.s n :=
      (Parameters.hasSum_theta f.s_ge_two).summable.sum_le_tsum _
        (fun n _ => by rw [Parameters.theta_eq f.s_ge_two]; positivity)
    _ ≤ 1/8 := (Parameters.theta_sum_small f.s_ge_two).le

lemma TypeII.group_theta_sum {f : Family} (e : TypeII f) :
    ∑ g ∈ TypeII.activeGroups e, f.theta (TypeII.groupWeight e g) ≤ 1/8 :=
  Family.sum_theta_le f _ _ (fun g _ => ((e.path g.1).piece g.2).weight_pos) (TypeII.groupWeight_injOn e)

lemma TypeII.sum_vector_norm {f : Family} (e : TypeII f) (s : Finset ℕ)
    (v : TypeII.Group e → s → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hv : ∀ g ∈ TypeII.activeGroups e, ‖vec f.exponent (v g)‖ ≤ K*f.theta (TypeII.groupWeight e g)) :
    ‖vec f.exponent (fun i => ∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| * v g i)‖ ≤ K/8 := by
  have hr : ∀ g, ‖vec f.exponent (fun i => |(e.coefficient g.1 : ℝ)| * v g i)‖ ≤ ‖vec f.exponent (v g)‖ := by
    intro g
    change ‖|(e.coefficient g.1 : ℝ)| • vec f.exponent (v g)‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_abs]
    exact (mul_le_mul_of_nonneg_right (e.coefficient_le_one g.1) (norm_nonneg _)).trans_eq (one_mul _)
  calc
    _ ≤ ∑ g ∈ TypeII.activeGroups e, ‖vec f.exponent (fun i => |(e.coefficient g.1 : ℝ)| * v g i)‖ := by
      rw [vec_sum]
      exact norm_sum_le _ _
    _ ≤ ∑ g ∈ TypeII.activeGroups e, K*f.theta (TypeII.groupWeight e g) :=
      Finset.sum_le_sum (fun g hg => (hr g).trans (hv g hg))
    _ = K * ∑ g ∈ TypeII.activeGroups e, f.theta (TypeII.groupWeight e g) := (Finset.mul_sum ..).symm
    _ ≤ K*(1/8) := mul_le_mul_of_nonneg_left (TypeII.group_theta_sum e) hK
    _ = K/8 := by ring

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology

lemma TypeII.sum_group_mask {f : Family} (e : TypeII f) (x : E) (p : ℕ → Prop) [DecidablePred p] :
    (∑ g ∈ TypeII.activeGroups e, if p (TypeII.groupWeight e g) then
      (e.coefficient g.1 : ℝ) * norming.evaluateArray x (TypeII.groupValue e g) else 0) =
    ∑ g : TypeII.Group e, if p (TypeII.groupWeight e g) then
      (e.coefficient g.1 : ℝ) * norming.evaluateArray x (TypeII.groupValue e g) else 0 := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro g _ hg
  have hz : TypeII.groupValue e g = 0 := by
    simpa only [TypeII.activeGroups,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hg
  simp [hz]

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NormingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.FiniteVectors
open scoped Classical BigOperators ENNReal
universe u
variable {ι : Type u} [Fintype ι]

lemma norm_mask_le_explicit {p : ℝ≥0∞} [DecidableEq ι] (hp : p ≠ 0) (v : ι → ℝ) (s : Finset ι) :
    ‖vec p (fun i => if i ∈ s then v i else 0)‖ ≤ ‖vec p v‖ := by
  apply lp.norm_mono hp
  intro i
  by_cases hi : i ∈ s <;> simp [vec_apply,hi]

lemma norm_le_four {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ 0) (v a b c d : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i)
    (h : ∀ i, |v i| ≤ a i+b i+c i+d i) :
    ‖vec p v‖ ≤ ‖vec p a‖+‖vec p b‖+‖vec p c‖+‖vec p d‖ := by
  calc
    _ ≤ ‖vec p (fun i => a i+b i+c i+d i)‖ := by
      apply lp.norm_mono hp
      intro i
      simpa only [vec_apply,Real.norm_eq_abs,abs_of_nonneg (add_nonneg (add_nonneg (add_nonneg (ha i) (hb i)) (hc i)) (hd i))] using h i
    _ = ‖vec p a+vec p b+vec p c+vec p d‖ := rfl
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)

lemma single_support_bounds {p : ℝ≥0∞} (hp : 0 < p.toReal) (v : ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hv : ∀ i, |v i| ≤ K) (hs : ∀ i j, v i ≠ 0 → v j ≠ 0 → i = j) :
    ‖vec p v‖ ≤ K ∧ (∑ i, |v i|) ≤ K := by
  by_cases he : ∃ i, v i ≠ 0
  · obtain ⟨i,hi⟩ := he
    have hz (j : ι) (hji : j ≠ i) : v j = 0 := by
      by_contra hj
      exact hji (hs j i hj hi)
    constructor
    · apply norm_le hp v K hK
      rw [Finset.sum_eq_single i]
      · exact Real.rpow_le_rpow (abs_nonneg _) (hv i) hp.le
      · intro j _ hji
        simp only [hz j hji,abs_zero,Real.zero_rpow hp.ne']
      · simp
    · rw [Finset.sum_eq_single i]
      · exact hv i
      · intro j _ hji
        simp [hz j hji]
      · simp
  · have hz : ∀ i, v i = 0 := by simpa only [not_exists,not_not] using he
    constructor
    · apply norm_le hp v K hK
      simp only [hz,abs_zero,Real.zero_rpow hp.ne',Finset.sum_const_zero]
      exact Real.rpow_nonneg hK _
    · simpa only [hz,abs_zero,Finset.sum_const_zero] using hK
end SeparableQuotient.FiniteVectors

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology

lemma Family.base_zero (f : Family) : (0 : Array) ∈ f.base := by
  cases f with
  | pure k => exact pureBase_zero k
  | mixed => exact Set.mem_iUnion.mpr ⟨0,pure_zero 0⟩

lemma Family.base_crop (f : Family) (A : Crop) (g : Array) (hg : g ∈ f.base) :
    restrict (A.set f) g ∈ f.base := by
  cases f with
  | pure k => exact pureBase_crop k A g hg
  | mixed =>
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hg
    apply Set.mem_iUnion.mpr
    refine ⟨k,?_⟩
    rw [pure_mixed_crop k A g hk]
    split_ifs
    · exact pure_crop k A g hk
    · exact pure_zero k

lemma Family.stage_crop (f : Family) (n : ℕ) (A : Crop) (g : Array) (hg : g ∈ stage f.base f n) :
    restrict (A.set f) g ∈ stage f.base f n :=
  Norming.stage_crop f (Family.base_zero f) (Family.base_crop f) n A g hg

lemma evaluateArray_nonzero_witness (x : Γ →₀ ℝ) (g : Array)
    (h : norming.evaluateArray (norming.includeFinite x) g ≠ 0) :
    ∃ α ∈ x.support, g α ≠ 0 := by
  rw [evaluateArray_finite] at h
  obtain ⟨α,hα,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨α,hα, fun hg => hne (by simp [hg])⟩

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.StoppedCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

lemma TypeI.total_incidence {f : Family} (e : TypeI f) (z : BlockSequence f) (s : Finset ℕ) :
    (∑ i : s, ((TypeI.hitChildren e (z.vector i)).card : ℝ)) ≤ 2*e.length+s.card := by
  have hh (i : s) : ((TypeI.hitChildren e (z.vector i)).card : ℝ) ≤ TypeI.boundaryDegree e z i + 1 := by
    unfold TypeI.boundaryDegree
    split_ifs with h
    · linarith
    · have : (TypeI.hitChildren e (z.vector i)).card ≤ 1 := by omega
      simpa only [zero_add] using (show ((TypeI.hitChildren e (z.vector i)).card : ℝ) ≤ 1 by exact_mod_cast this)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  rw [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one] at hs
  linarith [TypeI.boundaryDegree_sum e z s]

lemma Family.sum_theta_tail_le {κ : Type*} (f : Family) (S : Finset κ) (j : κ → ℕ) (J : ℕ)
    (hJ : 1 ≤ J) (hp : ∀ g ∈ S, J ≤ j g) (hinj : Set.InjOn j S) :
    ∑ g ∈ S, f.theta (j g) ≤ 4*f.theta J := by
  have hi : Set.InjOn (fun g => j g-J) S := by
    intro g hg h hh he
    apply hinj hg hh
    have := hp g hg
    have := hp h hh
    dsimp only at he
    omega
  have he (g : κ) (hg : g ∈ S) : j g-1 = (J-1)+(j g-J) := by have := hp g hg; omega
  have hs : Summable (fun n => Parameters.theta f.s ((J-1)+n)) :=
    ((Parameters.hasSum_theta f.s_ge_two).summable.comp_injective (fun n m h => by omega))
  calc
    _ = ∑ n ∈ S.image (fun g => j g-J), Parameters.theta f.s ((J-1)+n) := by
      rw [Finset.sum_image hi]
      exact Finset.sum_congr rfl (fun g hg => congrArg (Parameters.theta f.s) (he g hg))
    _ ≤ ∑' n, Parameters.theta f.s ((J-1)+n) := hs.sum_le_tsum _
      (fun n _ => by rw [Parameters.theta_eq f.s_ge_two]; positivity)
    _ ≤ _ := Parameters.theta_tail f.s_ge_two (J-1)

lemma Parameters.B_sum (s n : ℕ) : Parameters.B s n = 2*∑ j ∈ Finset.range n, Parameters.L s j := by
  induction n with
  | zero => simp only [Parameters.B_zero,Finset.range_zero,Finset.sum_empty,mul_zero]
  | succ n ih => rw [Parameters.B_succ,ih,Finset.sum_range_succ]; ring

lemma Family.sum_low_lengths {κ : Type*} (f : Family) (S : Finset κ) (j : κ → ℕ) (J : ℕ)
    (hp : ∀ g ∈ S, 1 ≤ j g) (hlt : ∀ g ∈ S, j g < J) (hinj : Set.InjOn j S) :
    2*(∑ g ∈ S, f.L (j g)) ≤ Parameters.B f.s (J-1) := by
  have hi : Set.InjOn (fun g => j g-1) S := by
    intro g hg h hh he
    apply hinj hg hh
    have := hp g hg
    have := hp h hh
    dsimp only at he
    omega
  have hsub : S.image (fun g => j g-1) ⊆ Finset.range (J-1) := by
    intro n hn
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hn
    have := hp g hg
    have := hlt g hg
    simp only [Finset.mem_range]
    omega
  rw [Parameters.B_sum]
  apply Nat.mul_le_mul_left
  rw [show (∑ g ∈ S, f.L (j g)) = ∑ n ∈ S.image (fun g => j g-1), Parameters.L f.s n by rw [Finset.sum_image hi]; rfl]
  exact Finset.sum_le_sum_of_subset hsub

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

noncomputable def TypeII.earlyGroups {f : Family} (e : TypeII f) (J : ℕ) : Finset (TypeII.Group e) :=
  (TypeII.activeGroups e).filter (fun g => TypeII.groupWeight e g < J)

abbrev TypeII.ChildVectors {f : Family} (e : TypeII f) (s : Finset ℕ) :=
  (g : TypeII.Group e) → Fin ((e.path g.1).piece g.2).length → s → ℝ

noncomputable def TypeII.recombineEarly {f : Family} (e : TypeII f) (J : ℕ) (s : Finset ℕ)
    (v : TypeII.ChildVectors e s) (i : s) : ℝ :=
  ∑ g ∈ TypeII.earlyGroups e J, |(e.coefficient g.1 : ℝ)| *
    ((1/(f.m (TypeII.groupWeight e g) : ℝ)) * ∑ h, v g h i)

lemma TypeII.early_lengths_bound {f : Family} (e : TypeII f) (J : ℕ) :
    2*(∑ g ∈ TypeII.earlyGroups e J, ((e.path g.1).piece g.2).length) ≤ Parameters.B f.s (J-1) := by
  apply le_trans (Nat.mul_le_mul_left 2 (Finset.sum_le_sum (fun g _ => ((e.path g.1).piece g.2).length_le)))
  exact Family.sum_low_lengths f _ (TypeII.groupWeight e) J (fun g _ => ((e.path g.1).piece g.2).weight_pos)
    (fun _ hg => (Finset.mem_filter.mp hg).2) ((TypeII.groupWeight_injOn e).mono (Finset.filter_subset _ _))

lemma TypeII.early_theta_bound {f : Family} (e : TypeII f) (J : ℕ) :
    ∑ g ∈ TypeII.earlyGroups e J, f.theta (TypeII.groupWeight e g) ≤ 1/8 :=
  Family.sum_theta_le f _ _ (fun g _ => ((e.path g.1).piece g.2).weight_pos)
    ((TypeII.groupWeight_injOn e).mono (Finset.filter_subset _ _))

lemma TypeII.recombineEarly_nonneg {f : Family} (e : TypeII f) (J : ℕ) (s : Finset ℕ)
    (v : TypeII.ChildVectors e s) (hv : ∀ g h i, 0 ≤ v g h i) (i : s) :
    0 ≤ TypeII.recombineEarly e J s v i := by
  unfold TypeII.recombineEarly
  exact Finset.sum_nonneg (fun g _ => mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (Finset.sum_nonneg (fun h _ => hv g h i))))

lemma TypeII.recombineEarly_l1 {f : Family} (e : TypeII f) (J : ℕ) (s : Finset ℕ)
    (v : TypeII.ChildVectors e s) (K : ℝ) (hK : 0 ≤ K)
    (hv : ∀ g h i, 0 ≤ v g h i) (hs : ∀ g h, (∑ i : s, v g h i) ≤ K) :
    (∑ i : s, TypeII.recombineEarly e J s v i) ≤ (Parameters.B f.s (J-1) : ℝ)*K := by
  have hc (g : TypeII.Group e) : |(e.coefficient g.1 : ℝ)| * (1/(f.m (TypeII.groupWeight e g) : ℝ)) ≤ 1 := by
    have hm : (1 : ℝ) ≤ f.m (TypeII.groupWeight e g) := by exact_mod_cast f.m_pos _
    exact (mul_le_mul (e.coefficient_le_one g.1) (one_div_le_one_div_of_le (by norm_num) hm) (by positivity) (by norm_num)).trans_eq (by norm_num)
  have hd : (∑ g ∈ TypeII.earlyGroups e J, (((e.path g.1).piece g.2).length : ℝ)) ≤ Parameters.B f.s (J-1) := by
    have hh := TypeII.early_lengths_bound e J
    exact_mod_cast (show (∑ g ∈ TypeII.earlyGroups e J, ((e.path g.1).piece g.2).length) ≤ Parameters.B f.s (J-1) by omega)
  calc
    _ = ∑ g ∈ TypeII.earlyGroups e J, (|(e.coefficient g.1 : ℝ)| * (1/(f.m (TypeII.groupWeight e g) : ℝ))) *
        ∑ h, ∑ i : s, v g h i := by
      unfold TypeII.recombineEarly
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      simp only [← Finset.mul_sum,← mul_assoc]
      congr 1
      exact Finset.sum_comm
    _ ≤ ∑ g ∈ TypeII.earlyGroups e J, ∑ h, ∑ i : s, v g h i := by
      exact Finset.sum_le_sum (fun g _ => (mul_le_mul_of_nonneg_right (hc g)
        (Finset.sum_nonneg (fun h _ => Finset.sum_nonneg (fun i _ => hv g h i)))).trans_eq (one_mul _))
    _ ≤ ∑ g ∈ TypeII.earlyGroups e J, (((e.path g.1).piece g.2).length : ℝ)*K := by
      apply Finset.sum_le_sum
      intro g _
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun h _ => hs g h)
    _ = (∑ g ∈ TypeII.earlyGroups e J, (((e.path g.1).piece g.2).length : ℝ))*K := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hd hK

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

noncomputable def TypeII.lateGroups {f : Family} (e : TypeII f) (J : ℕ) : Finset (TypeII.Group e) :=
  (TypeII.activeGroups e).filter (fun g => J ≤ TypeII.groupWeight e g)

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.TreeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

lemma TypeII.recombineEarly_add {f : Family} (e : TypeII f) (J : ℕ) (s : Finset ℕ)
    (v u : TypeII.ChildVectors e s) (i : s) :
    TypeII.recombineEarly e J s (fun g h i => v g h i + u g h i) i =
      TypeII.recombineEarly e J s v i + TypeII.recombineEarly e J s u i := by
  simp only [TypeII.recombineEarly,Finset.sum_add_distrib,mul_add]

lemma TypeII.recombineEarly_mono {f : Family} (e : TypeII f) (J : ℕ) (s : Finset ℕ)
    (v u : TypeII.ChildVectors e s) (h : ∀ g h i, v g h i ≤ u g h i) (i : s) :
    TypeII.recombineEarly e J s v i ≤ TypeII.recombineEarly e J s u i := by
  apply Finset.sum_le_sum
  intro g _
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun k _ => h g k i)

lemma Family.norming_crop (f : Family) (A : Crop) (g : Array) (hg : g ∈ f.norming) :
    restrict (A.set f) g ∈ f.norming := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hg
  exact Set.mem_iUnion.mpr ⟨n,Family.stage_crop f n A g hn⟩

lemma Family.norming_cases (f : Family) (g : Array) (hg : g ∈ f.norming) :
    g ∈ f.base ∨ ∃ e : TypeII f, e.value = g ∧ ∀ b i j, ((e.path b).piece i).child j ∈ f.norming := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hg
  induction n with
  | zero => exact Or.inl hn
  | succ n ih =>
    rcases hn with (hn | ⟨e,rfl,he⟩) | ⟨e,rfl,he⟩
    · exact ih hn
    · refine Or.inr ⟨e.toTypeII,e.toTypeII_value,fun _ _ h => ?_⟩
      exact Set.mem_iUnion.mpr ⟨n,he h⟩
    · exact Or.inr ⟨e,rfl,fun b i j => Set.mem_iUnion.mpr ⟨n,he b i j⟩⟩

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

lemma Family.qprime_formula (f : Family) : 1-1/f.q = 1/((f.s : ℝ)+1) := by
  have hs : (0 : ℝ) < f.s := by exact_mod_cast (show 0 < f.s by have := f.s_ge_two; omega)
  unfold Norming.Family.q Parameters.q
  field_simp
  ring

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.ExactPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

lemma exists_finite_vector_normer {f : Family} (x : Γ →₀ ℝ) (hx0 : x ≠ 0)
    (hx : 1 ≤ ‖norming.includeFinite x‖)
    (hcolor : ∀ k, f = .pure k → ∀ a ∈ x.support, Colors.color a = k) :
    ∃ (g : Array), g ∈ f.norming ∧ g ≠ 0 ∧
      (∀ a ∈ g.support, a ∈ (vectorCrop x hx0).set f) ∧
      1/2 < norming.evaluateArray (norming.includeFinite x) g := by
  have hn : ∃ g ∈ f.norming, 1/2 < norming.evaluateArray (norming.includeFinite x) g := by
    cases f with
    | pure k =>
      apply exists_pure_normer k _ _ _ (by norm_num) (by linarith)
      intro a ha
      rw [norming.coordinate_includeFinite]
      exact Finsupp.notMem_support_iff.mp (fun h => ha (hcolor k rfl a h))
    | mixed => exact exists_full_normer _ _ (by norm_num) (by linarith)
  obtain ⟨g,hg,hgv⟩ := hn
  let A := vectorCrop x hx0
  have heq : norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) g) =
      norming.evaluateArray (norming.includeFinite x) g := by
    apply evaluateArray_crop_of_zero
    intro a ha
    rw [norming.coordinate_includeFinite]
    exact Finsupp.notMem_support_iff.mp (fun h => ha (support_mem_vectorCrop f x hx0 a h))
  refine ⟨restrict (A.set f) g,family_norming_crop f A g hg,?_,?_,by rwa [heq]⟩
  · intro hz
    rw [hz,map_zero] at heq
    linarith
  · intro a ha
    by_contra hn
    change a ∉ A.set f at hn
    exact Finsupp.mem_support_iff.mp ha (by simp [restrict,hn])

lemma vectorCrop_mono {f : Family} {x y : Γ →₀ ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x.support ⊆ y.support) : (vectorCrop x hx).set f ⊆ (vectorCrop y hy).set f := by
  have ho : (vectorCrop x hx).ordinal ⊆ (vectorCrop y hy).ordinal := by
    intro a ha
    exact ⟨(Finset.min'_le _ _ (hxy (Finset.min'_mem _ _))).trans ha.1,
      ha.2.trans (Finset.le_max' _ _ (hxy (Finset.max'_mem _ _)))⟩
  have hc : (vectorCrop x hx).colors ⊆ (vectorCrop y hy).colors := by
    intro a ha
    have hsub : x.support.image Colors.color ⊆ y.support.image Colors.color := Finset.image_subset_image hxy
    exact ⟨(Finset.min'_le _ _ (hsub (Finset.min'_mem _ _))).trans ha.1,
      ha.2.trans (Finset.le_max' _ _ (hsub (Finset.max'_mem _ _)))⟩
  intro a ha
  cases f with
  | pure k => exact ho ha
  | mixed => exact ⟨ho ha.1,hc ha.2⟩

lemma BlockSequence.support_subset_sum {f : Family} (z : BlockSequence f) (k : ℕ) (i : Fin k) :
    (z.vector i).support ⊆ (∑ j : Fin k, z.vector j).support := by
  intro α hα
  apply Finsupp.mem_support_iff.mpr
  rw [Finsupp.finsetSum_apply,Finset.sum_eq_single i]
  · exact Finsupp.mem_support_iff.mp hα
  · intro j _ hji
    apply Finsupp.notMem_support_iff.mp
    intro hj
    have hne : (j : ℕ) ≠ i := fun h => hji (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (lt_irrefl α) (z.successive j i hlt α hj α hα).1
    · exact (lt_irrefl α) (z.successive i j hlt α hα α hj).1
  · simp

lemma BlockSequence.sum_nonzero {f : Family} (z : BlockSequence f) (k : ℕ) (hk : 0 < k) :
    (∑ j : Fin k, z.vector j) ≠ 0 := by
  intro hz
  obtain ⟨α,hα⟩ := Finsupp.support_nonempty_iff.mpr (z.nonzero 0)
  have hh := z.support_subset_sum k ⟨0,hk⟩ hα
  simp only [hz,Finsupp.support_zero,Finset.notMem_empty] at hh

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BranchPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

lemma RawPath.code_congr_prefix {P Q : RawPath} {n : ℕ}
    (hp : ∀ i ≤ n, P.piece i = Q.piece i)
    (hw : ∀ i ≤ n, P.weight i = Q.weight i)
    (hm : ∀ i ≤ n, P.metadata i = Q.metadata i) : P.code n = Q.code n := by
  have hs : P.support n = Q.support n := by
    unfold RawPath.support
    exact Finset.biUnion_congr rfl (fun i hi => congrArg Finsupp.support (hp i (by simpa using hi)))
  have he : P.endpoint n = Q.endpoint n := by simp only [RawPath.endpoint,hs]
  have hc : P.closure n = Q.closure n := by rw [RawPath.closure,RawPath.closure,he,hm n le_rfl]
  unfold RawPath.code
  congr 1
  funext i
  rw [hp i (by omega),hw i (by omega),hm i (by omega),hc]

namespace TreeNode
variable {f : Family} (z : BlockSequence f)

def rawAlong (D : ℕ → TreeNode z) (v : ℕ → ℕ) : RawPath where
  piece := fun n => (D (v n)).pair.piece.value
  weight := fun n => (D (v n)).weight
  metadata := fun n => (D (v n)).metadata
  nonzero := fun n => (D (v n)).pair.piece.value_ne_zero

def nodeCode (D : ℕ → TreeNode z) (n : ℕ) : Code :=
  (rawAlong z D (fun i => (BinaryNodes.ancestors n).getD i 0)).code
    ((BinaryNodes.ancestors n).length-1)

def listSupport (l : List (TreeNode z)) : Finset Γ :=
  l.toFinset.biUnion (fun d => d.pair.piece.value.support)

lemma mem_listSupport (l : List (TreeNode z)) (α : Γ) :
    α ∈ listSupport z l ↔ ∃ d ∈ l, α ∈ d.pair.piece.value.support := by
  simp [listSupport]

def nextStart (l : List (TreeNode z)) : ℕ := l.toFinset.sup (fun d => d.finish)

end TreeNode
end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.Complexification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

/- Complexification by real-linear maps from ℂ with the operator norm and real coordinates f(1), f(i). -/
namespace SeparableQuotient
open scoped Classical
universe u
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace Complexify
@[ext] lemma ext {f g : Complexify X} (h : ∀ z, f z = g z) : f = g := ContinuousLinearMap.ext h

instance instNormedAddCommGroup : NormedAddCommGroup (Complexify X) := inferInstanceAs (NormedAddCommGroup (ℂ →L[ℝ] X))
instance instNormedSpaceReal : NormedSpace ℝ (Complexify X) := inferInstanceAs (NormedSpace ℝ (ℂ →L[ℝ] X))
instance instCompleteSpace [CompleteSpace X] : CompleteSpace (Complexify X) := inferInstanceAs (CompleteSpace (ℂ →L[ℝ] X))

@[simp] lemma add_apply (f g : Complexify X) (z : ℂ) : (f+g) z = f z + g z := rfl
@[simp] lemma zero_apply (z : ℂ) : (0 : Complexify X) z = 0 := rfl
@[simp] lemma apply_zero (f : Complexify X) : f 0 = 0 := (toCLM X f).map_zero
@[simp] lemma apply_add (f : Complexify X) (z w : ℂ) : f (z+w) = f z + f w := (toCLM X f).map_add _ _
@[simp] lemma apply_smul (f : Complexify X) (r : ℝ) (z : ℂ) : f (r • z) = r • f z := (toCLM X f).map_smul _ _

def cmul (c : ℂ) (f : Complexify X) : Complexify X := (toCLM X f).comp ((ContinuousLinearMap.mul ℝ ℂ) c)
instance instSMulComplex : SMul ℂ (Complexify X) := ⟨cmul X⟩
@[simp] lemma smul_apply (c : ℂ) (f : Complexify X) (z : ℂ) :
    (c • f : Complexify X) z = f (c*z) := rfl

instance instModuleComplex : Module ℂ (Complexify X) where
  one_smul f := by ext z; simp
  mul_smul c d f := by ext z; simp [mul_assoc,mul_left_comm]
  smul_zero c := by ext z; rfl
  smul_add c f g := by ext z; rfl
  add_smul c d f := by ext z; simp [add_mul]
  zero_smul f := by ext z; simp

instance instNormedSpaceComplex : NormedSpace ℂ (Complexify X) where
  norm_smul_le c f := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    change ‖f (c*z)‖ ≤ (‖c‖*‖f‖)*‖z‖
    calc
      _ ≤ ‖f‖*‖c*z‖ := (toCLM X f).le_opNorm _
      _ = _ := by rw [norm_mul]; ring

instance instIsScalarTowerRealComplex : IsScalarTower ℝ ℂ (Complexify X) where
  smul_assoc r c f := by
    ext z
    change f ((r • c)*z) = r • f (c*z)
    rw [smul_mul_assoc,apply_smul]

instance instSMulCommClassRealComplex : SMulCommClass ℝ ℂ (Complexify X) where
  smul_comm r c f := by
    ext z
    change r • f (c*z) = (r • f : ℂ →L[ℝ] X) (c*z)
    rfl

def pairMap : Complexify X →L[ℝ] X × X :=
  (ContinuousLinearMap.apply ℝ X (1 : ℂ)).prod (ContinuousLinearMap.apply ℝ X Complex.I)

def ofPair (p : X × X) : Complexify X :=
  Complex.reCLM.smulRight p.1 + Complex.imCLM.smulRight p.2

lemma pairMap_ofPair (p : X × X) : pairMap X (ofPair X p) = p := by
  apply Prod.ext
  · change ((Complex.reCLM.smulRight p.1 + Complex.imCLM.smulRight p.2) (1 : ℂ)) = p.1
    simp
  · change ((Complex.reCLM.smulRight p.1 + Complex.imCLM.smulRight p.2) Complex.I) = p.2
    simp

lemma ofPair_pairMap (f : Complexify X) : ofPair X (pairMap X f) = f := by
  ext z
  change z.re • f 1 + z.im • f Complex.I = f z
  rw [← apply_smul,← apply_smul,← apply_add]
  congr 1
  apply Complex.ext <;> simp

def pairEquiv [CompleteSpace X] : Complexify X ≃L[ℝ] (X × X) :=
  (LinearEquiv.ofBijective (pairMap X).toLinearMap
    ⟨Function.HasLeftInverse.injective ⟨ofPair X,ofPair_pairMap X⟩,
      Function.HasRightInverse.surjective ⟨ofPair X,pairMap_ofPair X⟩⟩).toContinuousLinearEquivOfContinuous
    (pairMap X).continuous

end Complexify
end SeparableQuotient

end

end OAI
end


