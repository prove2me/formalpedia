-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_PositiveScheduling
-- name    : OAI_Analysis_SphereIsometry_PositiveScheduling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:10:06.959559+00:00
-- url     : https://prove2.me/theorems/5f3017f8-ba64-4464-b61d-6fb2e43a6694
-- title:
--   Strictly positive weight schedules hitting every rational prefix mean
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Let $v_0,v_1,\dots$ be a sequence in a normed space.
--
--   1. **Rational prefixes.** Rational probability vectors on an initial segment $\{0,\dots,m\}$, enumerated by a countable encoding. A zero extension is used beyond the prefix.
--   2. **Stage weights.** At stage $n$, the decoded rational prefix (or the point mass at $0$) is mixed with the uniform vector:
--   $$
--   w_n(i)=\Bigl(1-\tfrac1{n+2}\Bigr)q_n(i)+\tfrac1{n+2}\cdot\tfrac1{n+1}>0\quad(i\le n).
--   $$
--   3. **Stage means.** $\mu_n=\sum_{i\le n}w_n(i)\,v_i\in\mathrm{conv}\{v_0,\dots,v_n\}$. Every rational prefix mean is a limit of late stage means, so for bounded sequences the closure of $\{\mu_n\}$ contains the whole convex hull of $\{v_i\}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/PositiveScheduling.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/PositiveScheduling.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TingleySphereIsometry mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.SeparationQuotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Encodable.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
import Definitions.Def_TingleySphereIsometry
import Definitions.Def_OAI_Analysis_SphereIsometry_Basic
import Definitions.Def_OAI_Analysis_SphereIsometry_UnitRepresentatives
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraRealLimit
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraNormed
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraSphere
import Definitions.Def_OAI_Analysis_SphereIsometry_DefectSequence
import Definitions.Def_OAI_Analysis_SphereIsometry_SphereCompletion
import Definitions.Def_OAI_Analysis_SphereIsometry_DefectAttainment
import Definitions.Def_OAI_Analysis_SphereIsometry_RadialContact
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMap
import Definitions.Def_OAI_Analysis_SphereIsometry_Supports
import Definitions.Def_OAI_Analysis_SphereIsometry_PositiveConvexFace
import Definitions.Def_OAI_Analysis_SphereIsometry_ExtremalPropagation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! A fixed positive coefficient schedule, dense for every bounded sequence. -/

noncomputable section

open scoped BigOperators
open Set Finset

namespace Tingley

/-- A rational probability vector on an initial, nonempty list of indices. -/
abbrev RationalPrefix :=
  Σ m : ℕ, {q : Fin (m + 1) → ℚ // (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1}

/-- Extend a finite vector by zero, using the actual natural-number indices. -/
def prefixZeroExtend {A : Type*} [Zero A] {k : ℕ} (f : Fin k → A) (i : ℕ) : A :=
  if h : i < k then f ⟨i, h⟩ else 0

@[simp] theorem prefixZeroExtend_apply {A : Type*} [Zero A] {k : ℕ}
    (f : Fin k → A) (i : Fin k) : prefixZeroExtend f i.val = f i := by
  simp [prefixZeroExtend, i.isLt]

theorem sum_prefixZeroExtend {A : Type*} [AddCommMonoid A] {k n : ℕ}
    (f : Fin k → A) (hkn : k ≤ n) :
    (∑ i : Fin n, prefixZeroExtend f i.val) = ∑ i, f i := by
  rw [Fin.sum_univ_eq_sum_range, Finset.sum_fin_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono hkn)
  intro i _ hi
  simp only [Finset.mem_range] at hi
  simp [hi]

/-- A failed or premature code is replaced by the point mass at the first index. -/
def baseStageWeights (n : ℕ) : Fin (n + 1) → ℚ :=
  match Encodable.decode (α := RationalPrefix) (Nat.unpair n).1 with
  | none => fun i => if i = 0 then 1 else 0
  | some q => if q.1 ≤ n then fun i => prefixZeroExtend q.2.val i.val
      else fun i => if i = 0 then 1 else 0

theorem baseStageWeights_nonneg (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ baseStageWeights n i := by
  cases hdecode : Encodable.decode (α := RationalPrefix) (Nat.unpair n).1 with
  | none =>
    simp only [baseStageWeights, hdecode]
    split_ifs <;> norm_num
  | some q =>
    by_cases h : q.1 ≤ n
    · simp only [baseStageWeights, hdecode, ite_eq_left h]
      unfold prefixZeroExtend
      split_ifs
      · exact q.2.property.1 _
      · exact le_rfl
    · simp only [baseStageWeights, hdecode, ite_eq_right h]
      split_ifs <;> norm_num

theorem baseStageWeights_sum (n : ℕ) : ∑ i, baseStageWeights n i = 1 := by
  cases hdecode : Encodable.decode (α := RationalPrefix) (Nat.unpair n).1 with
  | none => simp [baseStageWeights, hdecode]
  | some q =>
    by_cases h : q.1 ≤ n
    · simp only [baseStageWeights, hdecode, ite_eq_left h]
      rw [sum_prefixZeroExtend q.2.val (Nat.add_le_add_right h 1)]
      exact q.2.property.2
    · simp [baseStageWeights, hdecode, h]

theorem baseStageWeights_pair (q : RationalPrefix) (r : ℕ) (hr : q.1 ≤ r) :
    baseStageWeights (Nat.pair (Encodable.encode q) r) =
      fun i => prefixZeroExtend q.2.val i.val := by
  have hq : q.1 ≤ Nat.pair (Encodable.encode q) r := hr.trans (Nat.right_le_pair _ _)
  simp [baseStageWeights, hq]

def stageMixing (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem stageMixing_pos (n : ℕ) : 0 < stageMixing n := by
  unfold stageMixing
  positivity

theorem stageMixing_lt_one (n : ℕ) : stageMixing n < 1 := by
  unfold stageMixing
  rw [div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
  linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]

/-- Mix with the uniform vector on *all* available indices. -/
def positiveStageWeights (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  (1 - stageMixing n) * (baseStageWeights n i : ℝ) +
    stageMixing n / ((n : ℝ) + 1)

theorem positiveStageWeights_pos (n : ℕ) (i : Fin (n + 1)) :
    0 < positiveStageWeights n i := by
  have hb : (0 : ℝ) ≤ (baseStageWeights n i : ℝ) := by
    exact_mod_cast baseStageWeights_nonneg n i
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr (stageMixing_lt_one n).le) hb)
    (div_pos (stageMixing_pos n) (by positivity))

theorem positiveStageWeights_sum (n : ℕ) : ∑ i, positiveStageWeights n i = 1 := by
  have hb : (∑ i, (baseStageWeights n i : ℝ)) = 1 := by
    exact_mod_cast baseStageWeights_sum n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [positiveStageWeights, Finset.sum_add_distrib, ← Finset.mul_sum,
    hb, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one]
  field_simp [hn]
  ring

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def stageMean (v : ℕ → X) (n : ℕ) : X :=
  ∑ i : Fin (n + 1), positiveStageWeights n i • v i.val

def rationalPrefixMean (v : ℕ → X) (q : RationalPrefix) : X :=
  ∑ i : Fin (q.1 + 1), (q.2.val i : ℝ) • v i.val

theorem norm_probability_sum_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (z : ι → X) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (B : ℝ) (hz : ∀ i, ‖z i‖ ≤ B) :
    ‖∑ i, w i • z i‖ ≤ B := by
  calc
    ‖∑ i, w i • z i‖ ≤ ∑ i, ‖w i • z i‖ := norm_sum_le _ _
    _ = ∑ i, w i * ‖z i‖ := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg, hw]
    _ ≤ ∑ i, w i * B := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hz i) (hw i)
    _ = B := by rw [← Finset.sum_mul, hsum, one_mul]

 theorem sum_padded_mean (v : ℕ → X) (q : RationalPrefix) {n : ℕ}
    (hq : q.1 ≤ n) :
    (∑ i : Fin (n+1), (prefixZeroExtend (A := ℚ) q.2.val i.val : ℝ) • v i.val) =
      rationalPrefixMean v q := by
  have he (i : ℕ) : (prefixZeroExtend (A := ℚ) q.2.val i : ℝ) • v i =
      prefixZeroExtend (fun j : Fin (q.1+1) => (q.2.val j : ℝ) • v j.val) i := by
    unfold prefixZeroExtend
    split <;> simp
  simp_rw [he]
  exact sum_prefixZeroExtend _ (Nat.add_le_add_right hq 1)

 theorem norm_stageMean_sub_rational_le (v : ℕ → X)
    (B : ℝ) (hv : ∀ i, ‖v i‖ ≤ B) (q : RationalPrefix) (r : ℕ) (hr : q.1 ≤ r) :
    ‖stageMean v (Nat.pair (Encodable.encode q) r) - rationalPrefixMean v q‖ ≤
      2 * B / ((Nat.pair (Encodable.encode q) r : ℝ) + 2) := by
  let n := Nat.pair (Encodable.encode q) r
  let U : X := ∑ i : Fin (n+1), (1 / ((n : ℝ)+1)) • v i.val
  have hq : q.1 ≤ n := hr.trans (Nat.right_le_pair _ _)
  have hQ : ‖rationalPrefixMean v q‖ ≤ B := by
    refine norm_probability_sum_le (fun i => (q.2.val i : ℝ))
      (fun i => v i.val) ?_ ?_ B ?_
    · intro i
      exact_mod_cast q.2.property.1 i
    · exact_mod_cast q.2.property.2
    · intro i; exact hv i.val
  have hU : ‖U‖ ≤ B := by
    refine norm_probability_sum_le (fun _ : Fin (n+1) => 1 / ((n : ℝ)+1))
      (fun i => v i.val) ?_ ?_ B ?_
    · intro i; positivity
    · simp [Finset.sum_const, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
        ne_of_gt (show (0 : ℝ) < (n : ℝ)+1 by positivity)]
    · intro i; exact hv i.val
  have hbase := baseStageWeights_pair q r hr
  have he : stageMean v n =
      (1-stageMixing n) • rationalPrefixMean v q + stageMixing n • U := by
    unfold stageMean positiveStageWeights
    rw [hbase]
    simp_rw [add_smul, mul_smul, div_eq_mul_inv, mul_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
    rw [sum_padded_mean v q hq]
    simp [U, div_eq_mul_inv]
  have hd : stageMean v n - rationalPrefixMean v q =
      stageMixing n • (U-rationalPrefixMean v q) := by
    rw [he, sub_smul, one_smul, smul_sub]
    abel
  calc
    ‖stageMean v n-rationalPrefixMean v q‖ =
        stageMixing n * ‖U-rationalPrefixMean v q‖ := by
          rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (stageMixing_pos n)]
    _ ≤ stageMixing n * (B+B) :=
      mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hU hQ))
        (stageMixing_pos n).le
    _ = 2*B/((n:ℝ)+2) := by unfold stageMixing; ring

theorem exists_late_stageMean_close_rational
    (v : ℕ → X) (B : ℝ) (hB : 0 ≤ B) (hv : ∀ i, ‖v i‖ ≤ B)
    (q : RationalPrefix) (δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    ∃ n, N ≤ n ∧ ‖stageMean v n-rationalPrefixMean v q‖ < δ := by
  obtain ⟨K, hK⟩ := exists_nat_gt (2*B/δ)
  let r := max K (max N q.1)
  let n := Nat.pair (Encodable.encode q) r
  have hrK : K ≤ r := le_max_left _ _
  have hrN : N ≤ r := (le_max_left _ _).trans (le_max_right _ _)
  have hrq : q.1 ≤ r := (le_max_right _ _).trans (le_max_right _ _)
  have hrn : r ≤ n := Nat.right_le_pair _ _
  refine ⟨n, hrN.trans hrn, (norm_stageMean_sub_rational_le v B hv q r hrq).trans_lt ?_⟩
  have hKn : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrK.trans hrn
  apply (div_lt_iff₀ (show (0 : ℝ) < (n : ℝ)+2 by positivity)).2
  have hk' : 2*B < (K:ℝ)*δ := (div_lt_iff₀ hδ).1 hK
  nlinarith

/-- Rational simplex approximation by flooring the tail and assigning the residual to index zero. -/
theorem exists_rational_simplex_l1_close
    (m : ℕ) (α : Fin (m+1) → ℝ) (hα : ∀ i, 0 ≤ α i)
    (hsum : ∑ i, α i = 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ q : Fin (m+1) → ℚ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
      (∑ i, |(q i : ℝ)-α i|) < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2*((m:ℝ)+1)/δ)
  have hNpos : (0 : ℝ) < (N:ℝ) :=
    lt_trans (by positivity : (0:ℝ) < 2*((m:ℝ)+1)/δ) hN
  have hN0 : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  let b : Fin m → ℚ := fun i => (⌊(N:ℝ)*α i.succ⌋₊ : ℚ) / (N:ℚ)
  have hb0 (i : Fin m) : 0 ≤ b i := by dsimp [b]; positivity
  have hbcast (i : Fin m) : (b i : ℝ) =
      (⌊(N:ℝ)*α i.succ⌋₊ : ℝ)/(N:ℝ) := by simp [b]
  have hble (i : Fin m) : (b i : ℝ) ≤ α i.succ := by
    rw [hbcast, div_le_iff₀ hNpos]
    simpa [mul_comm] using Nat.floor_le (mul_nonneg hNpos.le (hα i.succ))
  have hberr (i : Fin m) : α i.succ-(b i : ℝ) < 1/(N:ℝ) := by
    rw [hbcast]
    have hf := Nat.lt_floor_add_one ((N:ℝ)*α i.succ)
    apply (lt_div_iff₀ hNpos).2
    rw [sub_mul, div_mul_cancel₀ _ hN0]
    nlinarith
  have hsumα : α 0 + ∑ i : Fin m, α i.succ = 1 := by
    simpa only [Fin.sum_univ_succ] using hsum
  have htail : (∑ i : Fin m, (b i : ℝ)) ≤ ∑ i : Fin m, α i.succ :=
    Finset.sum_le_sum fun i _ => hble i
  have hres : (0 : ℝ) ≤ 1-∑ i : Fin m, (b i : ℝ) := by
    have := hα 0
    linarith
  let q : Fin (m+1) → ℚ := Fin.cons (1-∑ i, b i) b
  refine ⟨q, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => hb0 j) i
    change (0:ℚ) ≤ 1-∑ i, b i
    exact_mod_cast hres
  · simp [q, Fin.sum_univ_succ]
  · have herrsum : (∑ i : Fin m, (α i.succ-(b i : ℝ))) ≤ (m:ℝ)/(N:ℝ) := by
      calc
        _ ≤ ∑ _i : Fin m, 1/(N:ℝ) := Finset.sum_le_sum fun i _ => (hberr i).le
        _ = _ := by simp [nsmul_eq_mul, div_eq_mul_inv]
    have hfirst : (1-∑ i : Fin m, (b i : ℝ))-α 0 =
        ∑ i : Fin m, (α i.succ-(b i : ℝ)) := by
      rw [Finset.sum_sub_distrib]
      linarith
    have hfirst0 : 0 ≤ (1-∑ i : Fin m, (b i : ℝ))-α 0 := by
      rw [hfirst]
      exact Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hble i)
    have hnorm : (∑ i, |(q i : ℝ)-α i|) =
        2 * ∑ i : Fin m, (α i.succ-(b i : ℝ)) := by
      rw [Fin.sum_univ_succ]
      simp only [q, Fin.cons_zero, Fin.cons_succ, Rat.cast_sub, Rat.cast_one,
        Rat.cast_sum, abs_of_nonneg hfirst0]
      rw [hfirst]
      have htailabs : (∑ i : Fin m, |(b i : ℝ)-α i.succ|) =
          ∑ i : Fin m, (α i.succ-(b i : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_of_nonpos (sub_nonpos.mpr (hble i))]
        ring
      rw [htailabs]
      ring
    rw [hnorm]
    have hsmall : 2*(m:ℝ)/(N:ℝ) < δ := by
      apply (div_lt_iff₀ hNpos).2
      have := (div_lt_iff₀ hδ).1 hN
      nlinarith
    calc
      _ ≤ 2*((m:ℝ)/(N:ℝ)) := mul_le_mul_of_nonneg_left herrsum (by norm_num)
      _ = 2*(m:ℝ)/(N:ℝ) := by ring
      _ < δ := hsmall

theorem stageMean_mem_convexHull (v : ℕ → X) (n : ℕ) :
    stageMean v n ∈ convexHull ℝ (Set.range v) := by
  exact mem_convexHull_of_exists_fintype (positiveStageWeights n)
    (fun i => v i.val) (fun i => (positiveStageWeights_pos n i).le)
    (positiveStageWeights_sum n) (fun i => ⟨i.val, rfl⟩) rfl

theorem rationalPrefixMean_mem_closure (v : ℕ → X) (B : ℝ)
    (hB : 0 ≤ B) (hv : ∀ i, ‖v i‖ ≤ B) (q : RationalPrefix) :
    rationalPrefixMean v q ∈ closure (Set.range (stageMean v)) := by
  apply Metric.mem_closure_iff.2
  intro δ hδ
  obtain ⟨n, _, hn⟩ := exists_late_stageMean_close_rational v B hB hv q δ hδ 0
  exact ⟨stageMean v n, ⟨n, rfl⟩, by simpa [dist_eq_norm, norm_sub_rev] using hn⟩

theorem prefixMean_mem_closure (v : ℕ → X) (B : ℝ)
    (hB : 0 ≤ B) (hv : ∀ i, ‖v i‖ ≤ B) (m : ℕ)
    (α : Fin (m+1) → ℝ) (hα : ∀ i, 0 ≤ α i) (hsum : ∑ i, α i = 1) :
    (∑ i : Fin (m+1), α i • v i.val) ∈ closure (Set.range (stageMean v)) := by
  apply closure_minimal (fun _ hx => hx) isClosed_closure
  apply Metric.mem_closure_iff.2
  intro δ hδ
  have hBp : 0 < B+1 := by linarith
  obtain ⟨q, hq0, hq1, hqerr⟩ :=
    exists_rational_simplex_l1_close m α hα hsum (δ/(B+1)) (div_pos hδ hBp)
  let Q : RationalPrefix := ⟨m, q, hq0, hq1⟩
  refine ⟨rationalPrefixMean v Q, rationalPrefixMean_mem_closure v B hB hv Q, ?_⟩
  have hbary : ‖(∑ i : Fin (m+1), α i • v i.val)-rationalPrefixMean v Q‖ ≤
      (∑ i, |(q i : ℝ)-α i|)*(B+1) := by
    unfold rationalPrefixMean
    change ‖(∑ i : Fin (m+1), α i • v i.val)-∑ i, (q i : ℝ) • v i.val‖ ≤ _
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i : Fin (m+1), ‖α i • v i.val-(q i:ℝ) • v i.val‖ := norm_sum_le _ _
      _ = ∑ i : Fin (m+1), |(q i:ℝ)-α i| *‖v i.val‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← sub_smul, norm_smul, Real.norm_eq_abs, abs_sub_comm]
      _ ≤ ∑ i : Fin (m+1), |(q i:ℝ)-α i| *(B+1) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left ((hv i.val).trans (by linarith)) (abs_nonneg _)
      _ = _ := by rw [Finset.sum_mul]
  rw [dist_eq_norm]
  exact hbary.trans_lt ((lt_div_iff₀ hBp).1 hqerr)

/-- Every finite convex combination of a sequence fits in one initial prefix. -/
theorem convexHull_range_subset_of_prefixes (v : ℕ → X) (E : Set X)
    (hprefix : ∀ n, convexHull ℝ (Set.range (fun i : Fin (n+1) => v i.val)) ⊆ E) :
    convexHull ℝ (Set.range v) ⊆ E := by
  let H (n : ℕ) := convexHull ℝ (Set.range (fun i : Fin (n+1) => v i.val))
  have hmono : Monotone H := by
    intro n m hnm
    apply convexHull_mono
    rintro x ⟨i, rfl⟩
    exact ⟨⟨i.val, lt_of_lt_of_le i.isLt (Nat.add_le_add_right hnm 1)⟩, rfl⟩
  have hdir : Directed (· ⊆ ·) H := fun n m =>
    ⟨max n m, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩
  have hconv : Convex ℝ (⋃ n, H n) := hdir.convex_iUnion (fun _ => convex_convexHull _ _)
  have hbase : Set.range v ⊆ ⋃ n, H n := by
    rintro x ⟨n, rfl⟩
    exact Set.mem_iUnion.2 ⟨n, subset_convexHull ℝ _ ⟨Fin.last n, rfl⟩⟩
  intro x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (convexHull_min hbase hconv hx)
  exact hprefix n hn

theorem closure_range_stageMean_eq (v : ℕ → X) (B : ℝ)
    (hB : 0 ≤ B) (hv : ∀ i, ‖v i‖ ≤ B) :
    closure (Set.range (stageMean v)) = closure (convexHull ℝ (Set.range v)) := by
  apply Set.Subset.antisymm
  · apply closure_mono
    rintro x ⟨n, rfl⟩
    exact stageMean_mem_convexHull v n
  · apply closure_minimal _ isClosed_closure
    apply convexHull_range_subset_of_prefixes v
    intro m x hx
    rw [convexHull_range_eq_exists_affineCombination] at hx
    obtain ⟨s, w, hw0, hw1, hcomb⟩ := hx
    let α : Fin (m+1) → ℝ := fun i => if i ∈ s then w i else 0
    have hα0 : ∀ i, 0 ≤ α i := by
      intro i
      dsimp [α]
      split_ifs with hi
      · exact hw0 i hi
      · exact le_rfl
    have hα1 : ∑ i, α i = 1 := by simpa [α] using hw1
    have he : (∑ i, α i • v i.val) = x := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1] at hcomb
      simpa [α, ite_smul] using hcomb
    rw [← he]
    exact prefixMean_mem_closure v B hB hv m α hα0 hα1

end Tingley

end

end OAI


