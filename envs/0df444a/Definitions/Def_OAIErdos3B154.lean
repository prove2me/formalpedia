-- Prove2me | Definitions.Def_OAIErdos3B154
-- name    : OAIErdos3B154
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T00:46:50.49698+00:00
-- url     : https://prove2.me/theorems/82f66867-b061-4690-b26e-055c6de6f5ab
-- title:
--   OpenAI Erdős-3 split, definitions bundle 155 of 177
-- statement:
--   Definitions bundle 155 of 177 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B153`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 155 available.
--
--   Modules: `OAI.Erdos3.IntervalGlobalReductionStatement`, `OAI.Erdos3.NativeIntegerQuadrupleWitness`, `OAI.Erdos3.NativeMultilinearIntervalFamily`, `OAI.Erdos3.NativeMultilinearIntervalFamily.delta`, `OAI.Erdos3.NativeMultilinearIntervalFamily.intervalSet`, `OAI.Erdos3.NativeMultilinearIntervalFamily.intervalSet_nonempty`, `OAI.Erdos3.NativeMultilinearIntervalFamily.lowerProduct`, `OAI.Erdos3.NativeMultilinearIntervalFamily.lowerProductExpansion`, `OAI.Erdos3.NativeMultilinearIntervalFamily.mixed_correlation`, `OAI.Erdos3.NativeMultilinearIntervalFamily.product_factorization`, `OAI.Erdos3.NativeMultilinearIntervalFamily.rankProduct`, `OAI.Erdos3.NativeMultilinearIntervalFamily.rankProduct_norm`, `OAI.Erdos3.NativeMultilinearIntervalFamily.reduce_mixed`, `OAI.Erdos3.NativeMultilinearIntervalFamily.reduce_with_budget`, `OAI.Erdos3.NativeMultilinearIntervalFamily.residual`, `OAI.Erdos3.NativeMultilinearIntervalFamily.sample`, `OAI.Erdos3.NativeMultilinearIntervalFamily.sample_update`, `OAI.Erdos3.NativeReducedIntervalFamily`, `OAI.Erdos3.NativeReducedIntervalFamily.exists_fixed_global_term`, `OAI.Erdos3.NativeReducedIntervalFamily.globalExpansion`, `OAI.Erdos3.NativeReducedIntervalFamily.interval_length_ratio`, `OAI.Erdos3.NativeReducedIntervalFamily.localExpansion`, `OAI.Erdos3.NativeReducedIntervalFamily.localLower`, `OAI.Erdos3.NativeReducedIntervalFamily.localLower_norm`, `OAI.Erdos3.NativeReducedIntervalFamily.rank_correlation`, `OAI.Erdos3.NativeReducedIntervalFamily.scalar_norm`, `OAI.Erdos3.NativeRetainedMultilinearIntervalFamily.noConfusion`, `OAI.Erdos3.exists_absorbed_interval_family`, `OAI.Erdos3.exists_interval_global_reduction`, `OAI.Erdos3.exists_native_multilinear_interval_family`, `OAI.Erdos3.exists_native_rank_relation`, `OAI.Erdos3.exists_native_reduced_interval_family`, `OAI.Erdos3.exists_native_retained_multilinear_interval_family`, `OAI.Erdos3.exists_native_weighted_rank_intervals`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B157

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeRetainedIntegerMultilinearQuadruples
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.NativeCrossWitnesses

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

end Erdos3.NativeCrossWitnesses

end

section

namespace Erdos3

open scoped BigOperators

structure NativeIntegerQuadrupleWitness {s N : ℕ} [NeZero N] {p : ℝ}
    {f₀ f₁ : ZMod N → ℂ} {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
    (U : NativeCrossWitnesses s N p f₀ f₁ m H) (M : ZMod N → ℤ → ℂ)
    (q : ℝ) (t : ZMod N × ZMod N × ZMod N) where
  first_mem : t.2.1 ∈ H
  second_mem : t.2.1 - t.1 ∈ H
  third_mem : t.2.2 ∈ H
  fourth_mem : t.2.2 - t.1 ∈ H
  integer_relation :
    -(t.2.1.val : ℤ) + (t.2.1 - t.1).val + t.2.2.val - (t.2.2 - t.1).val = 0
  cyclic_correlation : Real.exp (-q) ≤ additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2
  branch : Bool
  start : ℕ
  length : ℕ
  length_pos : 0 < length
  endpoint_le : start + length ≤ N
  length_short : 2 * ((length : ℤ) - 1) < N
  correlation : Real.exp (-q) ≤ ‖𝔼 n ∈ Finset.Ico (start : ℤ) (start + length),
    fourPointProduct
      (U.integerProduct M ⟨t.2.1, first_mem⟩)
      (U.integerProduct M ⟨t.2.1 - t.1, second_mem⟩)
      (U.integerProduct M ⟨t.2.2, third_mem⟩)
      (U.integerProduct M ⟨t.2.2 - t.1, fourth_mem⟩)
      (cyclicBranchOffset t.1 branch) n‖
  length_ratio : Real.exp (-q) ≤ (length : ℝ) / N

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeCorrelationStructure

end NativeCorrelationStructure

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeAbsorbedIntervals
namespace OAI

section

namespace Erdos3

structure NativeMultilinearIntervalFamily {s r N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℂ} (W : NativeCorrelationStructure s r N p f) (q : ℝ) where
  mixed : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) q
  mixed_dim : mixed.dim ≤ 2 ^ (s + 1) * W.mixed.dim
  mixed_symmetric : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
    mixed.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
      mixed.eval k x
  coordinate : Fin mixed.outputDim
  rankCoordinate : Fin W.family.outputDim
  weight : ZMod N → ℂ
  weight_norm : ∀ x, ‖weight x‖ ≤ 1
  shifts : Finset (ZMod N)
  shifts_subset : shifts ⊆ W.shifts
  shifts_nonempty : shifts.Nonempty
  shifts_short : CyclicShortShiftSet shifts
  shifts_density : Real.exp (-q) * Fintype.card (ZMod N) ≤ (shifts.card : ℝ)
  lower : NativeCrossWitnesses (s - 1) N q (fun x => f x * star (weight x)) f
    (fun h x => W.multilinearFactor mixed coordinate rankCoordinate h x.val) shifts
  quadruples : Finset (ZMod N × ZMod N × ZMod N)
  quadruples_nonempty : quadruples.Nonempty
  quadruples_density : Real.exp (-q) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (quadruples.card : ℝ)
  interval : ∀ t : quadruples, NativeIntegerQuadrupleWitness lower
    (W.multilinearFactor mixed coordinate rankCoordinate) q t

end Erdos3

end

section

namespace Erdos3.NativeMultilinearIntervalFamily

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)

noncomputable def intervalSet (t : B.quadruples) : Finset ℤ :=
  Finset.Ico ((B.interval t).start : ℤ) ((B.interval t).start + (B.interval t).length)

def delta (t : B.quadruples) : ℤ := cyclicBranchOffset t.val.1 (B.interval t).branch

def sample (t : B.quadruples) (n : ℤ) : Fin 5 → ℤ :=
  ![(t.val.2.1.val : ℤ), (t.val.2.1 - t.val.1).val, t.val.2.2.val, n, B.delta t]

noncomputable def rankProduct (t : B.quadruples) (n : ℤ) : ℂ :=
  fourPointProduct (W.family.eval B.rankCoordinate t.val.2.1)
    (W.family.eval B.rankCoordinate (t.val.2.1 - t.val.1))
    (W.family.eval B.rankCoordinate t.val.2.2)
    (W.family.eval B.rankCoordinate (t.val.2.2 - t.val.1)) (B.delta t) n

noncomputable def lowerProduct (t : B.quadruples) (n : ℤ) : ℂ :=
  fourPointProduct
    (B.lower.integerLower ⟨t.val.2.1, (B.interval t).first_mem⟩)
    (B.lower.integerLower ⟨t.val.2.1 - t.val.1, (B.interval t).second_mem⟩)
    (B.lower.integerLower ⟨t.val.2.2, (B.interval t).third_mem⟩)
    (B.lower.integerLower ⟨t.val.2.2 - t.val.1, (B.interval t).fourth_mem⟩) (B.delta t) n

noncomputable def residual (t : B.quadruples) (n : ℤ) : ℂ :=
  B.rankProduct t n * B.lowerProduct t n

theorem product_factorization (t : B.quadruples) (n : ℤ) :
    fourPointProduct
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.1, (B.interval t).first_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.1 - t.val.1, (B.interval t).second_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.2, (B.interval t).third_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.2 - t.val.1, (B.interval t).fourth_mem⟩) (B.delta t) n =
    B.residual t n * translatedMixedProduct B.mixed (fun _ => B.coordinate)
      t.val.2.1.val (t.val.2.1 - t.val.1).val t.val.2.2.val (t.val.2.2 - t.val.1).val
      (B.delta t) n := by
  have h := B.lower.integerProduct_fourPoint_factorization
    (fun h n => B.mixed.eval B.coordinate (fun j => correlationInput (h.val : ℤ) n j.1))
    (W.family.eval B.rankCoordinate)
    ⟨t.val.2.1, (B.interval t).first_mem⟩
    ⟨t.val.2.1 - t.val.1, (B.interval t).second_mem⟩
    ⟨t.val.2.2, (B.interval t).third_mem⟩
    ⟨t.val.2.2 - t.val.1, (B.interval t).fourth_mem⟩ (B.delta t) n
  calc
    _ = translatedMixedProduct B.mixed (fun _ => B.coordinate)
        t.val.2.1.val (t.val.2.1 - t.val.1).val t.val.2.2.val (t.val.2.2 - t.val.1).val
        (B.delta t) n * B.rankProduct t n * B.lowerProduct t n := h
    _ = _ := by rw [residual]; ring

theorem mixed_correlation (t : B.quadruples) :
    Real.exp (-q) ≤ ‖𝔼 n ∈ B.intervalSet t,
      B.residual t n * translatedMixedProduct B.mixed (fun _ => B.coordinate)
        t.val.2.1.val (t.val.2.1 - t.val.1).val t.val.2.2.val (t.val.2.2 - t.val.1).val
        (B.delta t) n‖ := by
  have hc := (B.interval t).correlation
  change Real.exp (-q) ≤ ‖𝔼 n ∈ B.intervalSet t,
    fourPointProduct
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.1, (B.interval t).first_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.1 - t.val.1, (B.interval t).second_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.2, (B.interval t).third_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.2 - t.val.1, (B.interval t).fourth_mem⟩) (B.delta t) n‖ at hc
  simpa only [B.product_factorization] using hc

end Erdos3.NativeMultilinearIntervalFamily

end

section

namespace Erdos3

theorem exists_native_multilinear_interval_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      Nonempty (NativeMultilinearIntervalFamily W ((p + C) ^ C)) := by
  obtain ⟨C, hC, hquad⟩ := exists_integer_multilinear_quadruples s
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  obtain ⟨V, hdim, hsymm, k, i, weight, H, hweight, hsub, hH, hshort,
    hHsize, U, Q, hQ, hQsize, hinterval⟩ := hquad W hf
  classical
  have hdata (t : Q) := hinterval t.val t.property
  choose h₁ h₂ h₃ h₄ hrel hcyclic branch c len hlen hN hlenShort hcor hvol using hdata
  exact ⟨{
    mixed := V
    mixed_dim := hdim
    mixed_symmetric := hsymm
    coordinate := k
    rankCoordinate := i
    weight := weight
    weight_norm := hweight
    shifts := H
    shifts_subset := hsub
    shifts_nonempty := hH
    shifts_short := hshort
    shifts_density := hHsize
    lower := U
    quadruples := Q
    quadruples_nonempty := hQ
    quadruples_density := hQsize
    interval := fun t => {
      first_mem := h₁ t
      second_mem := h₂ t
      third_mem := h₃ t
      fourth_mem := h₄ t
      integer_relation := hrel t
      cyclic_correlation := hcyclic t
      branch := branch t
      start := c t
      length := len t
      length_pos := hlen t
      endpoint_le := hN t
      length_short := hlenShort t
      correlation := hcor t
      length_ratio := hvol t } }⟩

end Erdos3

end

section

namespace Erdos3

structure NativeRetainedMultilinearIntervalFamily {s r N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℂ} (W : NativeCorrelationStructure s r N p f) (q : ℝ)
    extends NativeMultilinearIntervalFamily W q where
  equivalence : NativeIntegerVectorEquivalence s q W.mixed.eval
    (fun k x => mixed.eval k (fun j => x j.1))

theorem exists_native_retained_multilinear_interval_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      Nonempty (NativeRetainedMultilinearIntervalFamily W ((p + C) ^ C)) := by
  obtain ⟨C, hC, hquad⟩ := exists_integer_multilinear_quadruples_with_equivalence s
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  obtain ⟨V, hdim, hsymm, E, k, i, weight, H, hweight, hsub, hH, hshort,
    hHsize, U, Q, hQ, hQsize, hinterval⟩ := hquad W hf
  classical
  have hdata (t : Q) := hinterval t.val t.property
  choose h₁ h₂ h₃ h₄ hrel hcyclic branch c len hlen hN hlenShort hcor hvol using hdata
  exact ⟨{
    mixed := V
    mixed_dim := hdim
    mixed_symmetric := hsymm
    equivalence := E
    coordinate := k
    rankCoordinate := i
    weight := weight
    weight_norm := hweight
    shifts := H
    shifts_subset := hsub
    shifts_nonempty := hH
    shifts_short := hshort
    shifts_density := hHsize
    lower := U
    quadruples := Q
    quadruples_nonempty := hQ
    quadruples_density := hQsize
    interval := fun t => {
      first_mem := h₁ t
      second_mem := h₂ t
      third_mem := h₃ t
      fourth_mem := h₄ t
      integer_relation := hrel t
      cyclic_correlation := hcyclic t
      branch := branch t
      start := c t
      length := len t
      length_pos := hlen t
      endpoint_le := hN t
      length_short := hlenShort t
      correlation := hcor t
      length_ratio := hvol t } }⟩

end Erdos3

end

section

namespace Erdos3.NativeMultilinearIntervalFamily

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)

theorem intervalSet_nonempty (t : B.quadruples) : (B.intervalSet t).Nonempty := by
  refine ⟨((B.interval t).start : ℤ), Finset.mem_Ico.mpr ⟨le_rfl, ?_⟩⟩
  exact lt_add_of_pos_right _ (Nat.cast_pos.mpr (B.interval t).length_pos)

theorem sample_update (t : B.quadruples) (n : ℤ) :
    B.sample t n = Function.update (B.sample t 0) (3 : Fin 5) n := by
  funext k
  fin_cases k <;> rfl

end Erdos3.NativeMultilinearIntervalFamily

end

section

namespace Erdos3.NativeMultilinearIntervalFamily

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

noncomputable def lowerProductExpansion {s r N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} {W : NativeCorrelationStructure s r N p f}
    (B : NativeMultilinearIntervalFamily W q) (t : B.quadruples) :
    NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) (mixedErrorBudget (q + 2))
      (fun x => B.lowerProduct t (x ())) := by
  have hq : 0 ≤ q := (Nat.cast_nonneg B.mixed.dim).trans B.mixed.complexity.1.1
  let h : Fin 4 → B.shifts :=
    ![⟨t.val.2.1, (B.interval t).first_mem⟩,
      ⟨t.val.2.1 - t.val.1, (B.interval t).second_mem⟩,
      ⟨t.val.2.2, (B.interval t).third_mem⟩,
      ⟨t.val.2.2 - t.val.1, (B.interval t).fourth_mem⟩]
  let v (i : Fin 4) := B.lower.integerLower (h i)
  let E (i : Fin 4) : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) (q + 2)
      (fun x => v i (x ())) :=
    NativeIntegerExpansion.ofTest (B.lower (h i)).test
      ((B.lower (h i)).complexity.mono (by linarith)) (fun _ => rfl)
  exact NativeIntegerExpansion.fourPoint v E (by linarith) (B.delta t)

end Erdos3.NativeMultilinearIntervalFamily

end

section

namespace Erdos3.NativeMultilinearIntervalFamily

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p q P : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)

theorem reduce_mixed (D : NativeMixedReductionData B.mixed P) :
    ∃ (a : D.ReductionCode (fun _ => B.coordinate)) (R : Finset B.quadruples), R.Nonempty ∧
      Real.exp (-(q + 5 * P)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (R.card : ℝ) ∧
      ∀ t ∈ R, ∃ c : D.LowerCode a.translations (t.val.2.1 - t.val.1).val
          (t.val.2.2 - t.val.1).val (B.delta t),
        Real.exp (-(q + 7 * P)) ≤ ‖𝔼 n ∈ B.intervalSet t,
          B.residual t n * D.globalError (fun _ => B.coordinate) a (B.sample t n) *
            D.translationLower a.translations (t.val.2.1 - t.val.1).val
              (t.val.2.2 - t.val.1).val (B.delta t) c n‖ := by
  classical
  have hnonempty : (Finset.univ : Finset B.quadruples).Nonempty := by
    obtain ⟨t, ht⟩ := B.quadruples_nonempty
    exact ⟨⟨t, ht⟩, Finset.mem_univ _⟩
  obtain ⟨a, R, _, hR, hsize, hcor⟩ := D.reduce_family Finset.univ hnonempty
    B.intervalSet (fun _ n => n)
    (fun t => (t.val.2.1.val : ℤ)) (fun t => ((t.val.2.1 - t.val.1).val : ℤ))
    (fun t => (t.val.2.2.val : ℤ)) (fun t => ((t.val.2.2 - t.val.1).val : ℤ))
    B.delta (fun _ => B.coordinate) B.residual q
    (fun t _ => (B.interval t).integer_relation) (fun t _ => B.mixed_correlation t)
  refine ⟨a, R, hR, ?_, hcor⟩
  calc
    Real.exp (-(q + 5 * P)) * (Fintype.card (ZMod N) : ℝ) ^ 3 =
        Real.exp (-(5 * P)) * (Real.exp (-q) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-(5 * P)) * (B.quadruples.card : ℝ) :=
      mul_le_mul_of_nonneg_left B.quadruples_density (Real.exp_nonneg _)
    _ ≤ (R.card : ℝ) := by simpa only [Finset.card_univ, Fintype.card_coe] using hsize

end Erdos3.NativeMultilinearIntervalFamily

end

section

namespace Erdos3

open scoped BigOperators

structure NativeReducedIntervalFamily {s r N : ℕ} [NeZero N] {p q P : ℝ}
    {f : ZMod N → ℂ} {W : NativeCorrelationStructure s r N p f}
    (B : NativeMultilinearIntervalFamily W q) (D : NativeMixedReductionData B.mixed P)
    (K : ℝ) where
  base_budget : q ≤ K
  correlation_budget : q + 7 * P ≤ K
  global_budget : mixedErrorBudget P ≤ K
  lower_budget : mixedErrorPairBudget P ≤ K
  code : D.ReductionCode (fun _ => B.coordinate)
  retained : Finset B.quadruples
  retained_nonempty : retained.Nonempty
  density : Real.exp (-K) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (retained.card : ℝ)
  lowerChoice : ∀ t : retained,
    D.LowerCode code.translations (t.val.val.2.1 - t.val.val.1).val
      (t.val.val.2.2 - t.val.val.1).val (B.delta t.val)
  correlation : ∀ t : retained, Real.exp (-K) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
    B.residual t.val n * D.globalError (fun _ => B.coordinate) code (B.sample t.val n) *
      D.translationLower code.translations (t.val.val.2.1 - t.val.val.1).val
        (t.val.val.2.2 - t.val.val.1).val (B.delta t.val) (lowerChoice t) n‖

end Erdos3

end

section

namespace Erdos3.NativeMultilinearIntervalFamily

theorem reduce_with_budget {s r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
    {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)
    (D : NativeMixedReductionData B.mixed P) (hq : q ≤ K) (hc : q + 7 * P ≤ K)
    (hg : mixedErrorBudget P ≤ K) (hl : mixedErrorPairBudget P ≤ K) :
    Nonempty (NativeReducedIntervalFamily B D K) := by
  obtain ⟨a, R, hR, hsize, hcor⟩ := B.reduce_mixed D
  have hp : 0 ≤ P := le_trans (by norm_num) D.budget_two
  have hsize' : Real.exp (-K) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (R.card : ℝ) := by
    apply le_trans _ hsize
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Real.exp_le_exp.mpr
    linarith only [hp, hc]
  classical
  exact ⟨{
    base_budget := hq
    correlation_budget := hc
    global_budget := hg
    lower_budget := hl
    code := a
    retained := R
    retained_nonempty := hR
    density := hsize'
    lowerChoice := fun t => Classical.choose (hcor t.val t.property)
    correlation := fun t => (Real.exp_le_exp.mpr (neg_le_neg hc)).trans
      (Classical.choose_spec (hcor t.val t.property)) }⟩

end Erdos3.NativeMultilinearIntervalFamily

end

section

namespace Erdos3.NativeReducedIntervalFamily

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
  {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K)

noncomputable def localLower (t : R.retained) (n : ℤ) : ℂ :=
  B.lowerProduct t.val n *
    D.translationLower R.code.translations (t.val.val.2.1 - t.val.val.1).val
      (t.val.val.2.2 - t.val.val.1).val (B.delta t.val) (R.lowerChoice t) n

noncomputable def globalExpansion :
    NativeIntegerExpansion (fun _ : Fin 5 => 1) s K
      (D.globalError (fun _ => B.coordinate) R.code) :=
  (D.globalErrorExpansion (fun _ => B.coordinate) R.code).mono R.global_budget

noncomputable def localExpansion (t : R.retained) :
    NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) (intervalErrorBudget K)
      (fun x => R.localLower t (x ())) := by
  have hq : 0 ≤ q := (Nat.cast_nonneg B.mixed.dim).trans B.mixed.complexity.1.1
  have hK : 0 ≤ K := hq.trans R.base_budget
  have hbase := intervalErrorBaseBudget_bounds hK
  have hfirst : mixedErrorBudget (q + 2) ≤ intervalErrorBaseBudget K :=
    (mixedErrorBudget_mono (by linarith) (by linarith [R.base_budget])).trans hbase.2.2
  have hsecond : mixedErrorPairBudget P ≤ intervalErrorBaseBudget K :=
    R.lower_budget.trans hbase.2.1
  exact ((B.lowerProductExpansion t.val).mono hfirst).mul
    ((D.translationLowerExpansion R.code.translations (t.val.val.2.1 - t.val.val.1).val
      (t.val.val.2.2 - t.val.val.1).val (B.delta t.val) (R.lowerChoice t)).mono hsecond) hbase.1

theorem rank_correlation (t : R.retained) :
    Real.exp (-K) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
      B.rankProduct t.val n * D.globalError (fun _ => B.coordinate) R.code (B.sample t.val n) *
        R.localLower t n‖ := by
  simpa only [localLower, NativeMultilinearIntervalFamily.residual,
    mul_assoc, mul_left_comm, mul_comm] using R.correlation t

theorem interval_length_ratio (t : R.retained) :
    Real.exp (-K) ≤ ((B.interval t.val).length : ℝ) / N :=
  (Real.exp_le_exp.mpr (neg_le_neg R.base_budget)).trans (B.interval t.val).length_ratio

end Erdos3.NativeReducedIntervalFamily

end

section

namespace Erdos3

theorem exists_native_reduced_interval_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ (q : ℝ) (B : NativeMultilinearIntervalFamily W q) (P : ℝ)
        (D : NativeMixedReductionData B.mixed P),
        Nonempty (NativeReducedIntervalFamily B D ((p + C) ^ C)) := by
  obtain ⟨a, _, hfamily⟩ := exists_native_multilinear_interval_family s
  obtain ⟨b, _, hreduce⟩ := exists_mixed_quadruple_budget s
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Y + (Y + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb : 0 ≤ (q + b) ^ b := by positivity
  have hcost : q + (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Y, q, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨B⟩ := hfamily W hf
  obtain ⟨P, ⟨D⟩, hP, hl, hg⟩ := hreduce B.mixed
  refine ⟨q, B, P, D, B.reduce_with_budget D ?_ ?_ ?_ ?_⟩
  · linarith only [hb, hcost]
  · linarith only [hP, hcost]
  · exact hg.trans (by linarith only [hq, hcost])
  · exact hl.trans (by linarith only [hq, hcost])

end Erdos3

end

section

namespace Erdos3.NativeReducedIntervalFamily

open scoped BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_fixed_global_term {s r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
    {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
    {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K) :
    ∃ (j : Fin R.globalExpansion.count) (S : Finset R.retained), S.Nonempty ∧
      Real.exp (-(2 * K)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (S.card : ℝ) ∧
      ∀ t ∈ S, Real.exp (-(2 * K)) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
        B.rankProduct t.val n * (R.globalExpansion.test j).eval (B.sample t.val n) *
          R.localLower t n‖ := by
  classical
  let rel (t : R.retained) (_ : Unit) (j : Fin R.globalExpansion.count) : Prop :=
    Real.exp (-(2 * K)) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
      B.rankProduct t.val n * (R.globalExpansion.test j).eval (B.sample t.val n) * R.localLower t n‖
  have hnonempty : (Finset.univ : Finset R.retained).Nonempty := by
    obtain ⟨t, ht⟩ := R.retained_nonempty
    exact ⟨⟨t, ht⟩, Finset.mem_univ _⟩
  have hchoice : ∀ t ∈ (Finset.univ : Finset R.retained), ∀ b, ∃ j, rel t b j := by
    intro t _ _
    have hc : Real.exp (-K) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
        (B.rankProduct t.val n * R.localLower t n) *
          D.globalError (fun _ => B.coordinate) R.code (B.sample t.val n)‖ := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using R.rank_correlation t
    obtain ⟨j, hj⟩ := R.globalExpansion.select_sample_product_correlation
      (B.intervalSet t.val) (B.sample t.val) (fun n => B.rankProduct t.val n * R.localLower t n) hc
    refine ⟨j, ?_⟩
    rw [show K + K = 2 * K by ring] at hj
    simpa only [rel, mul_assoc, mul_left_comm, mul_comm] using hj
  have hcount : (Fintype.card (Fin R.globalExpansion.count) : ℝ) ≤ Real.exp K := by
    simpa only [Fintype.card_fin] using R.globalExpansion.count_bound
  obtain ⟨j, S, _, hS, hsize, hfixed⟩ :=
    exists_large_fixed_choices Finset.univ hnonempty rel hchoice hcount
  refine ⟨j (), S, hS, ?_, fun t ht => hfixed t ht ()⟩
  calc
    Real.exp (-(2 * K)) * (Fintype.card (ZMod N) : ℝ) ^ 3 =
        Real.exp (-K) * (Real.exp (-K) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-K) * (R.retained.card : ℝ) :=
      mul_le_mul_of_nonneg_left R.density (Real.exp_nonneg _)
    _ ≤ (S.card : ℝ) := by
      simpa only [Fintype.card_unit, Nat.cast_one, mul_one, Finset.card_univ, Fintype.card_coe] using hsize

end Erdos3.NativeReducedIntervalFamily

end

section

namespace Erdos3

namespace NativeMultilinearIntervalFamily

theorem rankProduct_norm {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
    {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)
    (t : B.quadruples) (n : ℤ) : ‖B.rankProduct t n‖ ≤ 1 := by
  simp only [rankProduct, fourPointProduct, norm_mul, norm_star]
  calc
    _ ≤ (1 : ℝ) * 1 * 1 * 1 := by
      gcongr <;> exact W.family.norm_eval _ _ _
    _ = 1 := by norm_num

end NativeMultilinearIntervalFamily

namespace NativeReducedIntervalFamily

variable {s r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
  {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K)

theorem localLower_norm (t : R.retained) (n : ℤ) :
    ‖R.localLower t n‖ ≤ Real.exp (2 * intervalErrorBudget K) :=
  (R.localExpansion t).norm_eval_le (fun _ => n)

theorem scalar_norm (t : R.retained) (n : ℤ) :
    ‖B.rankProduct t.val n * R.localLower t n‖ ≤ Real.exp (2 * intervalErrorBudget K) := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul (B.rankProduct_norm t.val n) (R.localLower_norm t n)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

end NativeReducedIntervalFamily

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def IntervalGlobalReductionStatement (s c : ℕ) : Prop :=
  ∀ {r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
    {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
    {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K),
    ∃ (weight : ℤ → ℂ) (Q : Finset R.retained), (∀ n, ‖weight n‖ ≤ 1) ∧ Q.Nonempty ∧
      Real.exp (-(2 * K + intervalSplitTermBudget c K)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤
        (Q.card : ℝ) ∧
      ∀ t ∈ Q, ∃ v : ℤ → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) (intervalSplitLocalBudget c K)
          (fun x => v (x ()))) ∧
        Real.exp (-intervalSplitTermBudget c K) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
          B.rankProduct t.val n * weight n * v n‖

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_interval_global_reduction (s : ℕ) :
    ∃ c : ℕ, 2 ≤ c ∧ IntervalGlobalReductionStatement s c := by
  obtain ⟨c, hc, hreduce⟩ := exists_coordinate_error_reduction (Fin 5) s
  refine ⟨c, hc, ?_⟩
  intro r N _ p q P K f W B D R
  have hq : 0 ≤ q := (Nat.cast_nonneg B.mixed.dim).trans B.mixed.complexity.1.1
  have hK : 0 ≤ K := hq.trans R.base_budget
  have hinput := intervalSplitInput_bounds hK
  have hinput0 : 0 ≤ intervalSplitInput K := le_trans (by norm_num) hinput.1
  obtain ⟨j, S, hS, hSsize, hcorr⟩ := R.exists_fixed_global_term
  let T := R.globalExpansion.test j
  let F (t : R.retained) (n : ℤ) := B.rankProduct t.val n * R.localLower t n
  have hT : T.ComplexityLE (intervalSplitInput K) :=
    (R.globalExpansion.complexity j).mono hinput.2.1
  have hF : ∀ t ∈ S, ∀ n ∈ B.intervalSet t.val, ‖F t n‖ ≤ Real.exp (intervalSplitInput K) := by
    intro t _ n _
    exact (R.scalar_norm t n).trans (Real.exp_le_exp.mpr hinput.2.2.2)
  have hcorr' : ∀ t ∈ S, Real.exp (-intervalSplitInput K) ≤
      ‖𝔼 n ∈ B.intervalSet t.val, F t n * T.eval
        (Function.update (B.sample t.val 0) (3 : Fin 5) n)‖ := by
    intro t ht
    have h := (Real.exp_le_exp.mpr (neg_le_neg hinput.2.2.1)).trans (hcorr t ht)
    simpa only [F, T, ← B.sample_update, mul_assoc, mul_left_comm, mul_comm] using h
  obtain ⟨weight, Q, hw, _, hQ, hQsize, hcor⟩ := hreduce (3 : Fin 5) T hinput.1 hT S hS
    (fun t => B.intervalSet t.val) (fun t => B.sample t.val 0) (fun _ n => n) F
    (fun t _ => B.intervalSet_nonempty t.val) hF hcorr'
  refine ⟨weight, Q, hw, hQ, ?_, ?_⟩
  · calc
      Real.exp (-(2 * K + intervalSplitTermBudget c K)) * (Fintype.card (ZMod N) : ℝ) ^ 3 =
          Real.exp (-intervalSplitTermBudget c K) *
            (Real.exp (-(2 * K)) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-intervalSplitTermBudget c K) * (S.card : ℝ) :=
        mul_le_mul_of_nonneg_left hSsize (Real.exp_nonneg _)
      _ ≤ (Q.card : ℝ) := hQsize
  · intro t ht
    obtain ⟨v, _, ⟨E⟩, hcv⟩ := hcor t ht
    let w (n : ℤ) := R.localLower t n * v n
    have hL : 0 ≤ intervalErrorBudget K := intervalErrorBudget_nonneg hK
    have hJ : 0 ≤ intervalSplitTermBudget c K := by
      unfold intervalSplitTermBudget
      positivity
    have hL' : intervalErrorBudget K ≤ intervalErrorBudget K + intervalSplitTermBudget c K + 2 := by
      linarith only [hJ]
    have hJ' : intervalSplitTermBudget c K ≤ intervalErrorBudget K + intervalSplitTermBudget c K + 2 := by
      linarith only [hL]
    have htwo : 2 ≤ intervalErrorBudget K + intervalSplitTermBudget c K + 2 := by
      linarith only [hL, hJ]
    refine ⟨w, ⟨?_⟩, ?_⟩
    · exact ((R.localExpansion t).mono hL').mul (E.mono hJ') htwo
    · simpa only [F, w, intervalSplitTermBudget, mul_assoc, mul_left_comm, mul_comm] using hcv

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_absorbed_interval_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
      {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
      {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K),
      ∃ (weight : ℤ → ℂ) (Q : Finset R.retained), (∀ n, ‖weight n‖ ≤ 1) ∧ Q.Nonempty ∧
        Real.exp (-((K + C) ^ C)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, ∃ v : ℤ → ℂ,
          Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((K + C) ^ C)
            (fun x => v (x ()))) ∧
          Real.exp (-((K + C) ^ C)) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
            B.rankProduct t.val n * weight n * v n‖ := by
  obtain ⟨c, _, hreduce⟩ := exists_interval_global_reduction s
  obtain ⟨C, hC, hbudget⟩ := exists_interval_split_budget c
  refine ⟨C, hC, ?_⟩
  intro r N _ p q P K f W B D R
  have hq : 0 ≤ q := (Nat.cast_nonneg B.mixed.dim).trans B.mixed.complexity.1.1
  have hK : 0 ≤ K := hq.trans R.base_budget
  obtain ⟨weight, Q, hw, hQ, hsize, hcor⟩ := hreduce R
  have hF : intervalSplitTermBudget c K ≤ (K + C) ^ C := by
    linarith only [hK, (hbudget K hK).1]
  refine ⟨weight, Q, hw, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg (hbudget K hK).1)) (by positivity)).trans hsize
  · intro t ht
    obtain ⟨v, ⟨E⟩, hc⟩ := hcor t ht
    exact ⟨v, ⟨E.mono (hbudget K hK).2⟩, (Real.exp_le_exp.mpr (neg_le_neg hF)).trans hc⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankRelationExistence
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

namespace NativeWeightedRankIntervals

end NativeWeightedRankIntervals

namespace NativeAnchoredRankFibers

variable {s r N : ℕ} [NeZero N] {b p : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim} {H : Finset (ZMod N)}
  {F : NativeWeightedRankIntervals W out H p} (A : NativeAnchoredRankFibers F)

end NativeAnchoredRankFibers

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeRankInterval

end NativeRankInterval

end Erdos3

end

section

namespace Erdos3

theorem exists_native_weighted_rank_intervals (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
      {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
      {D : NativeMixedReductionData B.mixed P} (_R : NativeReducedIntervalFamily B D K),
      Nonempty (NativeWeightedRankIntervals W.family B.rankCoordinate B.shifts
        (K + (K + C) ^ C + 2)) := by
  obtain ⟨C, hC, hexists⟩ := exists_absorbed_interval_family s
  refine ⟨C, hC, ?_⟩
  intro r N _ p q P K f W B D R
  have hq : 0 ≤ q := (Nat.cast_nonneg B.mixed.dim).trans B.mixed.complexity.1.1
  have hK : 0 ≤ K := hq.trans R.base_budget
  have hpow : 0 ≤ (K + C) ^ C := by positivity
  have hKP : K ≤ K + (K + C) ^ C + 2 := by linarith only [hpow]
  have hPP : (K + C) ^ C ≤ K + (K + C) ^ C + 2 := by linarith only [hK]
  obtain ⟨weight, Q, hw, hQ, hsize, hcor⟩ := hexists R
  classical
  obtain ⟨t₀, ht₀⟩ := hQ
  let : Nonempty Q := ⟨⟨t₀, ht₀⟩⟩
  have hdata (t : Q) := hcor t.val t.property
  choose v hE hv using hdata
  let e := (Fintype.equivFin Q).symm
  let old (i : Fin (Fintype.card Q)) : B.quadruples := (e i).val.val
  refine ⟨{
    budget_two := by linarith only [hK, hpow]
    count := Fintype.card Q
    count_pos := Fintype.card_pos
    index := fun i => (old i).val
    index_injective := ?_
    density := ?_
    first_mem := fun i => (B.interval (old i)).first_mem
    second_mem := fun i => (B.interval (old i)).second_mem
    third_mem := fun i => (B.interval (old i)).third_mem
    fourth_mem := fun i => (B.interval (old i)).fourth_mem
    integer_relation := fun i => (B.interval (old i)).integer_relation
    branch := fun i => (B.interval (old i)).branch
    start := fun i => (B.interval (old i)).start
    length := fun i => (B.interval (old i)).length
    length_pos := fun i => (B.interval (old i)).length_pos
    endpoint_le := fun i => (B.interval (old i)).endpoint_le
    length_short := fun i => (B.interval (old i)).length_short
    length_ratio := fun i => (Real.exp_le_exp.mpr (neg_le_neg hKP)).trans
      (R.interval_length_ratio (e i).val)
    weight := weight
    weight_norm := hw
    lower := fun i => v (e i)
    expansion := fun i => (Classical.choice (hE (e i))).mono hPP
    correlation := fun i => (Real.exp_le_exp.mpr (neg_le_neg hPP)).trans (hv (e i)) }⟩
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hij
  · simpa only [Fintype.card_coe] using
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hPP)) (by positivity)).trans hsize

end Erdos3

end

section

namespace Erdos3

namespace NativeAnchoredRankFibers

variable {s r N : ℕ} [NeZero N] {b p : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim} {H : Finset (ZMod N)}
  {F : NativeWeightedRankIntervals W out H p} (A : NativeAnchoredRankFibers F)

end NativeAnchoredRankFibers

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}

end NativeRankInterval

end Erdos3

end

section

namespace Erdos3

namespace NativeRankRelation

end NativeRankRelation

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q)

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q)

end Erdos3.NativeRankInterval

end

section

namespace Erdos3

namespace NativeWeightedRankIntervals

end NativeWeightedRankIntervals

end Erdos3

end

section

namespace Erdos3

theorem exists_native_rank_relation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)),
        H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
        Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
        Nonempty (NativeRankRelation W.family out H ((p + C) ^ C) ((p + C) ^ C)) := by
  obtain ⟨a, _, hreduce⟩ := exists_native_reduced_interval_family s
  obtain ⟨c, _, habsorb⟩ := exists_native_weighted_rank_intervals s
  obtain ⟨C, hC, hbudget⟩ := exists_rank_relation_budget a c
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  obtain ⟨q, B, P, D, ⟨R⟩⟩ := hreduce W hf
  obtain ⟨F⟩ := habsorb R
  obtain ⟨T⟩ := F.remove_weight
  have hK : 0 ≤ (p + a) ^ a := by positivity
  have hq : q ≤ (p + C) ^ C := by
    have hpow : 0 ≤ ((p + a) ^ a + c) ^ c := by positivity
    linarith only [R.base_budget, (hbudget p hp).1, hK, hpow]
  refine ⟨B.rankCoordinate, B.shifts, B.shifts_subset, B.shifts_nonempty,
    B.shifts_short, ?_, ⟨T.mono (hbudget p hp).1 (hbudget p hp).2⟩⟩
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hq))
    (Nat.cast_nonneg _)).trans B.shifts_density

end Erdos3

end

end OAI

end


