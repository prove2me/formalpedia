-- Prove2me | Definitions.Def_OAIErdos3B1323
-- name    : OAIErdos3B1323
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T18:57:05.583982+00:00
-- url     : https://prove2.me/theorems/43f31532-84d8-438f-9060-01bb698f5185
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1324 of 1341
-- statement:
--   Definitions bundle 1324 of 1341 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1322`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1324 available.
--
--   Modules: `OAI.Erdos3.NativePairPartition`, `OAI.Erdos3.NativePairPartition.partition_sum_norm`, `OAI.Erdos3.exists_antisymmetric_pair_precise_partition`, `OAI.Erdos3.exists_common_anchor_approximation`, `OAI.Erdos3.exists_cyclicNativeInverse_add_two`, `OAI.Erdos3.exists_cyclicNativeInverse_positive`, `OAI.Erdos3.exists_cyclicNativeInverse_two`, `OAI.Erdos3.exists_global_pair_comparison`, `OAI.Erdos3.exists_native_integer_box_inverse`, `OAI.Erdos3.exists_native_inverse_on_cyclic_encoding`, `OAI.Erdos3.exists_native_partner_of_cube_mixture`, `OAI.Erdos3.exists_native_partner_of_physical_cube_mixture`, `OAI.Erdos3.exists_native_partner_of_physical_cube_mixture_all_degrees`, `OAI.Erdos3.exists_precise_global_pair_comparison`, `OAI.Erdos3.exists_quadratic_global_exchange`, `OAI.Erdos3.exists_quadratic_original_integration`, `OAI.Erdos3.exists_quadratic_primitive_correlation_large_modulus`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1324

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelatingVerticalPair
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

section Data

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}

structure NativePairPartition
    (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
      V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
      (fun _ : Fin 2 => (N : ℝ)) r) (b ε : ℝ) where
  I : Type
  [finite : Fintype I]
  card_bound : (Fintype.card (Fin 2 → I) : ℝ) ≤ Real.exp b
  weight : I → ZMod N → ℝ
  positive : ∀ j, PositiveCyclicNiltest.{0} 1 N b (weight j)
  total : ∀ x, ∑ j, weight j x = 1
  anchor : (Fin 2 → I) → (Fin 2 → ZMod N)
  equivalence : ∀ j, NativeIntegerVectorEquivalence 1 b
    (R.pairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 0)
    (R.pairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 1)
  approximation : ∀ (k : Fin 2) (out : Fin W.outputDim),
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval out (correlationInput ((x k).val : ℤ) ((x k.rev).val : ℤ)) -
        ∑ j, ((∏ l, weight (j l) (x l) : ℝ) : ℂ) * R.pairAnchoredVector
          (fun l => ((anchor j l).val : ℤ)) k out (fun l => ((x l).val : ℤ))‖) ≤ ε

attribute [local instance] NativePairPartition.finite

end Data

theorem exists_antisymmetric_pair_precise_partition :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t e : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      R.HasPairLocalApproximation b → R.HasPairFrozenReduction c →
      0 ≤ t → 0 ≤ e → b ≤ t → c ≤ t → Real.exp ((t + e + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativePairPartition R ((t + e + C) ^ C) (Real.exp (-e))) := by
  obtain ⟨A, _, hpartition⟩ := exists_antisymmetric_pair_local_partition 2
  let X : Polynomial ℕ := Polynomial.X
  let T := X + 100
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C A) ^ A + 2 * T)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t e W N _ i j V R hlocal hred ht he hbt hct hN
  let u := t + e + 100
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hsum : (u + A) ^ A + 2 * u ≤ (t + e + C) ^ C := by
    simpa [T, X, u, Polynomial.eval₂_pow] using hbudget (t + e) (add_nonneg ht he)
  have hcost : (u + A) ^ A ≤ (t + e + C) ^ C := by linarith
  have hscale : 2 * u ≤ (t + e + C) ^ C := by
    have : 0 ≤ (u + A) ^ A := by positivity
    linarith
  let ρ := Real.exp (-(2 * u))
  have hρ : 0 < ρ := Real.exp_pos _
  have hprec : 1 / ρ ≤ Real.exp ((u + 2) ^ 2) := by
    dsimp [ρ]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg u]
  obtain ⟨P, hP, hPb, n, hn, hcard, weight, hpositive, htotal, anchor, hequiv, herr⟩ :=
    hpartition R hlocal hred hu (hbt.trans (by dsimp [u]; linarith))
      (hct.trans (by dsimp [u]; linarith)) hρ hprec
  let : NeZero P := ⟨hP.ne'⟩
  have hrecip : 1 / (N : ℝ) ≤ ρ := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos (2 * u))
      ((Real.exp_le_exp.mpr hscale).trans hN)
    simpa only [ρ, one_div, Real.exp_neg] using hh
  have herror : Real.exp (u + 40) * (ρ + 1 / N) ≤ Real.exp (-e) := by
    calc
      _ ≤ Real.exp (u + 40) * (2 * ρ) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _)
      _ = 2 * Real.exp (40 - u) := by
        dsimp [ρ]
        rw [← mul_assoc, mul_comm (Real.exp (u + 40)) 2, mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ 2 * (Real.exp (-e) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply (Real.exp_le_exp.mpr (show 40 - u ≤ -e - 1 by dsimp [u]; linarith)).trans
        exact exp_sub_one_le_half_exp (-e)
      _ = _ := by ring
  exact ⟨{
    I := Fin n × ZMod P
    card_bound := hcard.trans (Real.exp_le_exp.mpr hcost)
    weight := weight
    positive := fun j => (hpositive j).mono le_rfl hcost
    total := htotal
    anchor := anchor
    equivalence := fun j => (hequiv j).mono hcost
    approximation := fun k out => (herr k out).trans herror }⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff NativePairPartition.finite

section Data

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  {R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r}

namespace NativePolynomialOrbitFactors

end NativePolynomialOrbitFactors

end Data

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff NativePairPartition.finite

theorem exists_common_anchor_approximation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u b ε : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      0 ≤ r → 0 ≤ u → 0 ≤ b → R.HasOuterValueControl u →
      (P : NativePairPartition R b ε) →
      ∀ (y : Fin 2 → ℤ), (∀ k, |(y k : ℝ)| ≤ (N : ℝ)) → ∀ l : Fin 2,
      ∃ F : Fin 2 → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ k out a, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
          ((p + q + r + u + b + C) ^ C) (F k out a))) ∧
        (∀ k out a (x : Fin 2 → ZMod N),
          ‖F k out a (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ k out (x : Fin 2 → ZMod N),
          ∑ a, F k out a (fun z => ((x z).val : ℤ)) *
            R.pairAnchoredVector y l a (fun z => ((x z).val : ℤ)) =
          ∑ cell, ((∏ z, P.weight (cell z) (x z) : ℝ) : ℂ) *
            R.pairAnchoredVector (fun z => ((P.anchor cell z).val : ℤ)) k out
              (fun z => ((x z).val : ℤ))) ∧
        (∀ k out,
          (𝔼 x : Fin 2 → ZMod N,
            ‖W.eval out (correlationInput ((x k).val : ℤ) ((x k.rev).val : ℤ)) -
              ∑ a, F k out a (fun z => ((x z).val : ℤ)) *
                R.pairAnchoredVector y l a (fun z => ((x z).val : ℤ))‖) ≤ ε) := by
  obtain ⟨A, _, hanchor⟩ := exists_antisymmetric_anchor_equivalence
  obtain ⟨B, _, hcommon⟩ := exists_weighted_common_factor
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r u b ε W N _ i j V R hr hu hb houter P y hy l
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + u + b
  let t := v + (v + A) ^ A + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 2 ≤ t := by
    have ha : 0 ≤ (v + A) ^ A := by positivity
    dsimp [t]
    linarith
  have hbt : b ≤ t := by
    have ha : 0 ≤ (v + A) ^ A := by positivity
    dsimp [t, v]
    linarith
  have hat : (p + q + r + u + A) ^ A ≤ t := by
    calc
      _ ≤ (v + A) ^ A := by
        apply pow_le_pow_left₀ (by positivity)
        dsimp [v]
        linarith
      _ ≤ t := by dsimp [t]; linarith
  have hcost : (t + B) ^ B ≤ (p + q + r + u + b + C) ^ C := by
    simpa [X, T, t, v, Polynomial.eval₂_pow] using hbudget v hv
  let coords (cell : Fin 2 → P.I) (k : Fin 2 × Fin W.outputDim) :=
    R.pairAnchoredVector (fun z => ((P.anchor cell z).val : ℤ)) k.1 k.2
  have hbox (x : Fin 2 → ZMod N) (z : Fin 2) : |(((x z).val : ℤ) : ℝ)| ≤ (N : ℝ) := by
    simp only [Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x z).val))]
    exact Nat.cast_le.mpr (x z).val_lt.le
  have hcross (cell : Fin 2 → P.I) (k : Fin 2 × Fin W.outputDim) (a : Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 t
        (fun x => coords cell k x * star (R.pairAnchoredVector y l a x))) :=
    ((hanchor R hr hu houter (fun z => ((P.anchor cell z).val : ℤ)) y
      (hbox (P.anchor cell)) hy k.1 l).mono hat).expansion k.2 a
  obtain ⟨F, hF, _, hnorm, hrepr⟩ := hcommon ht
    (by simpa using ht : (Fintype.card (Fin 2) : ℝ) ≤ t)
    (P.card_bound.trans (Real.exp_le_exp.mpr hbt))
    (fun cell z => P.weight (cell z)) coords (R.pairAnchoredVector y l)
    (fun cell z => (P.positive (cell z)).mono le_rfl hbt)
    (sum_productPartitionWeight (fun (_ : Fin 2) a x => P.weight a x) (fun _ => P.total))
    (fun cell k x => R.pairAnchoredVector_norm _ _ _ _)
    (fun a x => R.pairAnchoredVector_norm _ _ _ _)
    (fun x => R.pairFrozenVector_unit l (R.slowValue y) (R.rationalValue y) _)
    hcross
  refine ⟨fun k out => F (k, out), ?_, ?_, ?_, ?_⟩
  · intro k out a
    exact ⟨(Classical.choice (hF (k, out) a)).mono hcost⟩
  · intro k out a x
    exact hnorm (k, out) a x
  · intro k out x
    exact hrepr (k, out) x
  · intro k out
    simpa only [hrepr] using P.approximation k out

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

variable
  [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [T2Space (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiagonalRowTransfer
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff NativePairPartition.finite

theorem NativePairPartition.partition_sum_norm {p q r b ε : ℝ}
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
    {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
    {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
      Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
    {R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
      V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
      (fun _ : Fin 2 => (N : ℝ)) r}
    (P : NativePairPartition R b ε) (k : Fin 2) (out : Fin W.outputDim)
    (x : Fin 2 → ZMod N) :
    ‖∑ cell, ((∏ z, P.weight (cell z) (x z) : ℝ) : ℂ) *
      R.pairAnchoredVector (fun z => ((P.anchor cell z).val : ℤ)) k out
        (fun z => ((x z).val : ℤ))‖ ≤ 1 := by
  classical
  exact norm_positive_partition_sum_le_one
    (fun cell : Fin 2 → P.I => ∏ z, P.weight (cell z) (x z))
    (fun cell => R.pairAnchoredVector (fun z => ((P.anchor cell z).val : ℤ)) k out
      (fun z => ((x z).val : ℤ)))
    (fun cell => Finset.prod_nonneg (fun z _ => ((P.positive (cell z)).unit_interval (x z)).1))
    (sum_productPartitionWeight (fun (_ : Fin 2) a x => P.weight a x) (fun _ => P.total) x)
    (fun cell => R.pairAnchoredVector_norm _ _ _ _)

theorem exists_global_pair_comparison :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u b ε : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      0 ≤ r → 0 ≤ u → 0 ≤ b → R.HasOuterValueControl u →
      NativePairPartition R b ε →
      ∃ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ out₀ out₁, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
          ((p + q + r + u + b + C) ^ C) (G out₀ out₁))) ∧
        (∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ a b, (𝔼 x : Fin 2 → ZMod N,
          ‖W.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
            G a b (fun z => ((x z).val : ℤ))‖) ≤ 2 * ε) := by
  obtain ⟨A, _, hcommon⟩ := exists_common_anchor_approximation
  obtain ⟨B, _, hanchor⟩ := exists_antisymmetric_anchor_equivalence
  obtain ⟨D, _, hproducts⟩ := exists_native_common_factor_products
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p q r u b ε W N _ i j V R hr hu hb houter P
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + u + b
  let t := v + (v + A) ^ A + (v + B) ^ B + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hA : 0 ≤ (v + A) ^ A := by positivity
  have hB : 0 ≤ (v + B) ^ B := by positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t, v]; linarith
  have hAt : (p + q + r + u + b + A) ^ A ≤ t := by change (v + A) ^ A ≤ t; dsimp [t]; linarith
  have hBt : (p + q + r + u + B) ^ B ≤ t := by
    calc
      _ ≤ (v + B) ^ B := by
        apply pow_le_pow_left₀ (by positivity)
        dsimp [v]
        linarith
      _ ≤ t := by dsimp [t]; linarith
  have hcost : (t + D) ^ D ≤ (p + q + r + u + b + C) ^ C := by
    simpa [X, T, t, v, Polynomial.eval₂_pow] using hbudget v hv
  have hzero (k : Fin 2) : |((0 : Fin 2 → ℤ) k : ℝ)| ≤ (N : ℝ) := by simp
  obtain ⟨F, hF, _, hrepr, herr⟩ := hcommon R hr hu hb houter P 0 hzero 0
  let U := R.pairAnchoredVector 0 0
  let Q (k : Fin 2) (out : Fin W.outputDim) (x : Fin 2 → ℤ) := ∑ a, F k out a x * U a x
  let G (a b : Fin W.outputDim) (x : Fin 2 → ℤ) := Q 1 b x * star (Q 0 a x)
  have hU := (hanchor R hr hu houter 0 0 hzero hzero 0 0).mono hBt
  have hG (out₀ out₁ : Fin W.outputDim) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
      ((p + q + r + u + b + C) ^ C) (G out₀ out₁)) := by
    obtain ⟨E⟩ := hproducts ht
      (by simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpt))
      (fun k : Fin 2 × Fin W.outputDim => F k.1 k.2) U
      (fun k a => ⟨(Classical.choice (hF k.1 k.2 a)).mono hAt⟩)
      hU.expansion (1, out₁) (0, out₀)
    exact ⟨E.mono hcost⟩
  have hQcap (k : Fin 2) (out : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      ‖Q k out (fun z => ((x z).val : ℤ))‖ ≤ 1 := by
    have heq := hrepr k out x
    change Q k out (fun z => ((x z).val : ℤ)) = _ at heq
    rw [heq]
    exact P.partition_sum_norm k out x
  refine ⟨G, hG, ?_, ?_⟩
  · intro a b x
    dsimp only [G]
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hQcap 1 b x)).trans (hQcap 0 a x)
  · intro a b
    have hpoint (x : Fin 2 → ZMod N) :
        ‖W.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
          G a b (fun z => ((x z).val : ℤ))‖ ≤
        ‖W.eval b (correlationInput ((x 1).val : ℤ) ((x 0).val : ℤ)) -
          Q 1 b (fun z => ((x z).val : ℤ))‖ +
        ‖W.eval a (correlationInput ((x 0).val : ℤ) ((x 1).val : ℤ)) -
          Q 0 a (fun z => ((x z).val : ℤ))‖ := by
      dsimp only [NativeMultidegreeNilcharacter.antisymmetricKernel, G]
      rw [mul_comm (star _) (W.eval b _)]
      exact norm_mul_star_sub_mul_star_le_of_le_one (W.norm_eval a _) (hQcap 1 b x)
    have hmean := Finset.expect_le_expect (s := Finset.univ) (fun x _ => hpoint x)
    rw [Finset.expect_add_distrib] at hmean
    have hfirst := herr 1 b
    have hsecond := herr 0 a
    change (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval b (correlationInput ((x 1).val : ℤ) ((x 0).val : ℤ)) -
        Q 1 b (fun z => ((x z).val : ℤ))‖) ≤ ε at hfirst
    change (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (correlationInput ((x 0).val : ℤ) ((x 1).val : ℤ)) -
        Q 0 a (fun z => ((x z).val : ℤ))‖) ≤ ε at hsecond
    linarith

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_precise_global_pair_comparison :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r e : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (_R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      0 ≤ r → 0 ≤ e → Real.exp ((p + q + r + e + C) ^ C) ≤ (N : ℝ) →
      ∃ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
          ((p + q + r + e + C) ^ C) (G a b))) ∧
        (∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ a b, (𝔼 x : Fin 2 → ZMod N,
          ‖W.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
            G a b (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hlocal⟩ := exists_antisymmetric_pair_local_approximation
  obtain ⟨B, _, hfrozen⟩ := exists_antisymmetric_pair_frozen_reduction
  obtain ⟨D, _, hpartition⟩ := exists_antisymmetric_pair_precise_partition
  obtain ⟨E, _, hglobal⟩ := exists_global_pair_comparison
  let X : Polynomial ℕ := Polynomial.X
  let L := (X + Polynomial.C A) ^ A
  let K := (X + Polynomial.C B) ^ B
  let T := L + K + X + 2
  let Z := (T + (X + 1) + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Z + (X + K + Z + Polynomial.C E) ^ E)
  refine ⟨C, hC, ?_⟩
  intro p q r e W N _ i j V R hr he hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + e
  let b := (v + A) ^ A
  let c := (v + B) ^ B
  let t := b + c + v + 2
  let z := (t + (e + 1) + D) ^ D
  let zmax := (t + (v + 1) + D) ^ D
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hev : e ≤ v := by dsimp [v]; linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzmax : 0 ≤ zmax := by dsimp [zmax]; positivity
  have hbt : b ≤ t := by dsimp [t]; linarith
  have hct : c ≤ t := by dsimp [t]; linarith
  have hzz : z ≤ zmax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have hsum : zmax + (v + c + zmax + E) ^ E ≤ (p + q + r + e + C) ^ C := by
    simpa [X, L, K, T, Z, b, c, t, zmax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hzC : zmax ≤ (p + q + r + e + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hGC : (v + c + zmax + E) ^ E ≤ (p + q + r + e + C) ^ C :=
    (le_add_of_nonneg_left hzmax).trans hsum
  have hloc : R.HasPairLocalApproximation b :=
    R.hasPairLocalApproximation_mono (hlocal R hr) (by
      apply pow_le_pow_left₀ (by positivity)
      dsimp [v]
      linarith)
  have hred : R.HasPairFrozenReduction c :=
    R.hasPairFrozenReduction_mono (hfrozen R hr) (by
      apply pow_le_pow_left₀ (by positivity)
      dsimp [v]
      linarith)
  obtain ⟨P⟩ := hpartition R hloc hred ht (by linarith : 0 ≤ e + 1) hbt hct
    ((Real.exp_le_exp.mpr (hzz.trans hzC)).trans hN)
  obtain ⟨u, hu, huc, houter, _⟩ := hred
  obtain ⟨G, hG, hcap, herr⟩ := hglobal R hr hu hz houter P
  have hcost : (p + q + r + u + z + E) ^ E ≤ (p + q + r + e + C) ^ C := by
    apply le_trans _ hGC
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  refine ⟨G, ?_, hcap, ?_⟩
  · intro a b
    exact ⟨(Classical.choice (hG a b)).mono hcost⟩
  · intro a b
    apply (herr a b).trans
    have hh := exp_sub_one_le_half_exp (-e)
    have hid : -(e + 1) = -e - 1 := by ring
    rw [hid]
    linarith

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_global_exchange :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ G : Fin M.outputDim → Fin M.outputDim → (Fin 2 → ℤ) → ℂ,
                (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
                  ((p + e + C) ^ C) (G a b))) ∧
                (∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
                (∀ a b, (𝔼 x : Fin 2 → ZMod N,
                  ‖M.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
                    G a b (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hpair⟩ := exists_quadratic_pair_orbit_factors
  obtain ⟨B, _, hcomparison⟩ := exists_precise_global_pair_comparison
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (3 * T + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let t := (p + e + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hbase : (p + A) ^ A ≤ t := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hsum : t + (3 * t + (p + e) + B) ^ B ≤ (p + e + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + e) (add_nonneg hp he)
  have htC : t ≤ (p + e + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (3 * t + (p + e) + B) ^ B ≤ (p + e + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hsum
  have hbaseC : (p + A) ^ A ≤ (p + C) ^ C := by
    have hh : (p + A) ^ A + (3 * (p + A) ^ A + p + B) ^ B ≤ (p + C) ^ C := by
      simpa [X, T, Polynomial.eval₂_pow] using hbudget p hp
    exact (le_add_of_nonneg_right (by positivity)).trans hh
  obtain ⟨q, r, hq, hqt, hr, hrt, H, hH, hdense, M, i, hderiv, i', j', V, ⟨R⟩⟩ :=
    hpair hp ((Real.exp_le_exp.mpr (hbase.trans htC)).trans hN) f hf hGowers
  have hcost : (q + r + (p + A) ^ A + e + B) ^ B ≤ (p + e + C) ^ C := by
    apply le_trans _ hBC
    apply pow_le_pow_left₀ (by positivity)
    have hq' := hqt.trans hbase
    have hr' := hrt.trans hbase
    linarith
  obtain ⟨G, hG, hcap, herr⟩ := hcomparison R
    (by positivity : 0 ≤ (p + A) ^ A) he ((Real.exp_le_exp.mpr hcost).trans hN)
  refine ⟨q, hq, hqt.trans hbaseC, H, hH, hdense, M, i, hderiv, G, ?_, hcap, herr⟩
  intro a b
  exact ⟨(Classical.choice (hG a b)).mono hcost⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_quadratic_original_integration :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ K : (Fin M.quadraticRoot.outputDim × Fin M.quadraticRoot.outputDim) →
                  Fin M.outputDim → Fin M.quadraticRoot.outputDim → (Fin 2 → ℤ) → ℂ,
                (∀ a j c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
                  ((p + e + C) ^ C) (K a j c))) ∧
                (∀ a j c, (𝔼 x : Fin 2 → ZMod N,
                  ‖M.quadraticRoot.cyclicDiagonalDerivative a x *
                      (M.eval j (fun k => ((x k).val : ℤ)) *
                        M.quadraticRoot.eval c (fun _ => ((x 0).val : ℤ))) -
                    K a j c (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hglobal⟩ := exists_quadratic_global_exchange
  obtain ⟨B, _, hroot⟩ := NativeMultidegreeNilcharacter.exists_rootCyclicCorrection_expansion
  obtain ⟨D, _, horiginal⟩ := NativeMultidegreeNilcharacter.exists_originalDiagonalCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let T := (X + 12 * U + 40 + Polynomial.C A) ^ A
  let S := (U + T + X + 4 * U + 40 + Polynomial.C B) ^ B
  let R := (U + S + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + T + X + 4 * U + 40 + S + R)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let v := p + e
  let u := (p + A) ^ A
  let umax := (v + A) ^ A
  let t := (p + (e + 12 * u + 40) + A) ^ A
  let tmax := (v + 12 * umax + 40 + A) ^ A
  let b := e + 4 * u + 40
  let smax := (umax + tmax + v + 4 * umax + 40 + B) ^ B
  let rmax := (umax + smax + D) ^ D
  let δ : ℝ≥0 := ⟨Real.exp (-b), (Real.exp_pos _).le⟩
  have hδval : (δ : ℝ) = Real.exp (-b) := rfl
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have humax : 0 ≤ umax := by dsimp [umax]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htmax : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hsmax : 0 ≤ smax := by dsimp [smax]; positivity
  have hrmax : 0 ≤ rmax := by dsimp [rmax]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hinv : (δ : ℝ)⁻¹ ≤ Real.exp b := by rw [hδval, ← Real.exp_neg, neg_neg]
  have hsum : umax + tmax + v + 4 * umax + 40 + smax + rmax ≤ (p + e + C) ^ C := by
    simpa [X, U, T, S, R, umax, tmax, smax, rmax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hum : u ≤ umax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have htm : t ≤ tmax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have htC : tmax ≤ (p + e + C) ^ C := by linarith
  have hsC : smax ≤ (p + e + C) ^ C := by linarith
  have hrC : rmax ≤ (p + e + C) ^ C := by linarith
  have hbC : b ≤ (p + e + C) ^ C := by dsimp [b, v] at *; linarith
  have huC : u ≤ (p + C) ^ C := by
    have hh : u + (p + 12 * u + 40 + A) ^ A + p + 4 * u + 40 +
        (u + (p + 12 * u + 40 + A) ^ A + p + 4 * u + 40 + B) ^ B +
        (u + (u + (p + 12 * u + 40 + A) ^ A + p + 4 * u + 40 + B) ^ B + D) ^ D ≤ (p + C) ^ C := by
      simpa [X, U, T, S, R, u, Polynomial.eval₂_pow] using hbudget p hp
    have h1 : 0 ≤ (p + 12 * u + 40 + A) ^ A := by positivity
    have h2 : 0 ≤ (u + (p + 12 * u + 40 + A) ^ A + p + 4 * u + 40 + B) ^ B := by positivity
    have h3 : 0 ≤ (u + (u + (p + 12 * u + 40 + A) ^ A + p + 4 * u + 40 + B) ^ B + D) ^ D := by positivity
    linarith
  obtain ⟨q, hq, hqu, H, hH, hdense, M, i, hderiv, G, hG, hcap, herr⟩ :=
    hglobal hp (by positivity : 0 ≤ e + 12 * u + 40)
      ((Real.exp_le_exp.mpr (htm.trans htC)).trans hN) f hf hGowers
  have hqmax := hqu.trans hum
  have hs : (q + t + b + B) ^ B ≤ smax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [b, v]
    linarith
  have hF (a c) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 smax
      (M.rootCyclicCorrection N δ G a c)) :=
    ⟨(Classical.choice (hroot M N δ hδ ht hb hinv G hG a c)).mono hs⟩
  have hfinal : (q + smax + D) ^ D ≤ (p + e + C) ^ C := by
    apply le_trans _ hrC
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have herror := quadratic_original_error_bound (Nat.cast_nonneg M.outputDim) hu
    (M.output_bound.trans (Real.exp_le_exp.mpr hqu)) ((Real.exp_le_exp.mpr hbC).trans hN)
  have hrootError := M.rootCyclicCorrection_mean_error δ hδ G hcap herr
  refine ⟨q, hq, hqu.trans huC, H, hH, hdense, M, i, hderiv,
    M.originalDiagonalCorrection (M.rootCyclicCorrection N δ G), ?_, ?_⟩
  · intro a j c
    exact ⟨(Classical.choice (horiginal M hsmax (M.rootCyclicCorrection N δ G) hF a j c)).mono hfinal⟩
  · intro a j c
    apply (M.originalDiagonalCorrection_mean_error (M.rootCyclicCorrection N δ G) hrootError a j c).trans
    have hdim : M.quadraticRoot.outputDim = M.outputDim ^ 2 := rfl
    simp only [hdim, Nat.cast_pow, hδval]
    dsimp [b] at *
    simpa only [← pow_mul, Nat.reduceMul] using herror

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

end NativeMultidegreeNilcharacter
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HigherResidualRowDifferences
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_quadratic_primitive_correlation_large_modulus :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ g ∈ nativeCyclicFunctions 2 N ((p + C) ^ C),
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n, f n * star (g n)‖ := by
  obtain ⟨A, _, hintegrate⟩ := exists_quadratic_original_integration
  obtain ⟨B, _, hfourier⟩ := exists_fourier_of_stepOne_cross_correlation
  obtain ⟨D, _, hprimitive⟩ :=
    NativeMultidegreeNilcharacter.exists_quadratic_primitive_niltest_budget
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let R := 3 * (U + 1)
  let E := 2 * U + 3 * R + 4
  let T := (X + E + Polynomial.C A) ^ A
  let V := 2 * U + 2 + 3 * R + T
  let F := (V + Polynomial.C B) ^ B
  let G := (R + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + R + E + T + V + F + G)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let r := 3 * (u + 1)
  let e := 2 * u + 3 * r + 4
  let t := (p + e + A) ^ A
  let v := 2 * u + 2 + 3 * r + t
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hsum : u + r + e + t + v + (v + B) ^ B + (r + D) ^ D ≤ (p + C) ^ C := by
    simpa [X, U, R, E, T, V, F, G, u, r, e, t, v, Polynomial.eval₂_pow] using hbudget p hp
  have hF : 0 ≤ (v + B) ^ B := by positivity
  have hG : 0 ≤ (r + D) ^ D := by positivity
  have htC : t ≤ (p + C) ^ C := by linarith
  have hFC : (v + B) ^ B ≤ (p + C) ^ C := by linarith
  have hGC : (r + D) ^ D ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, H, _hH, hdense, M, i, hderiv, K, hK, herr⟩ :=
    hintegrate hp he ((Real.exp_le_exp.mpr htC).trans hN) f hf hGowers
  let W := M.quadraticRoot
  have hroot : tensorPowerBudget 2 q ≤ r := by
    norm_num only [tensorPowerBudget, Nat.cast_ofNat, show (2 : ℝ) + 1 = 3 by norm_num]
    dsimp only [r]
    linarith
  have hroot0 : 0 ≤ tensorPowerBudget 2 q := by
    unfold tensorPowerBudget
    positivity
  have hdim : (W.outputDim : ℝ) ≤ Real.exp r :=
    W.output_bound.trans (Real.exp_le_exp.mpr hroot)
  have hdim3 : (W.outputDim : ℝ) ^ 3 ≤ Real.exp (3 * r) := by
    calc
      _ ≤ Real.exp r ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hdim 3
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  let J := (Fin W.outputDim × Fin W.outputDim) × Fin W.outputDim
  let z (ac : J) := 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
    multiplicativeDerivative f h n * W.cyclicDiagonalDerivative ac.1 ![h, n] *
      star (K ac.1 i ac.2 ![(h.val : ℤ), (n.val : ℤ)])‖
  have hcard : (Fintype.card J : ℝ) ≤ Real.exp (3 * r) := by
    have hcount : (Fintype.card J : ℝ) = (W.outputDim : ℝ) ^ 3 := by
      simp only [J, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      ring
    rw [hcount]
    exact hdim3
  have hmass : Real.exp (-(2 * u)) ≤ 𝔼 h : ZMod N,
      ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
        star (M.evalCyclic N i (correlationInput h n))‖ := by
    have hh := dense_set_mean_lower_bound H
      (fun h : ZMod N => ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
        star (M.evalCyclic N i (correlationInput h n))‖)
      (fun _ => norm_nonneg _) (Real.exp_nonneg (-q))
      (by simpa only [ZMod.card] using hdense) hderiv
    have heq : Real.exp (-q) * Real.exp (-q) = Real.exp (-(2 * q)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq] at hh
    exact (Real.exp_le_exp.mpr (by dsimp [u]; linarith)).trans hh
  have htransfer := M.original_diagonal_row_correlation_bound i f hf
    (fun a c => K a i c) (fun a c => herr a i c)
  change _ ≤ (∑ ac : J, z ac) + (W.outputDim : ℝ) ^ 3 * Real.exp (-e) at htransfer
  let δ := Real.exp (-(2 * u + 2))
  have hδ : 0 < δ := Real.exp_pos _
  have herror : (W.outputDim : ℝ) ^ 3 * Real.exp (-e) ≤ δ := by
    calc
      _ ≤ Real.exp (3 * r) * Real.exp (-e) :=
        mul_le_mul_of_nonneg_right hdim3 (Real.exp_nonneg _)
      _ = Real.exp (-(2 * u + 4)) := by rw [← Real.exp_add]; congr 1; dsimp [e]; ring
      _ ≤ δ := Real.exp_le_exp.mpr (by linarith)
  have htwo : 2 * δ ≤ Real.exp (-(2 * u)) := by
    calc
      _ ≤ Real.exp 2 * δ := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hδ.le
      _ = _ := by dsimp [δ]; rw [← Real.exp_add]; congr 1; ring
  have hmass' : δ ≤ ∑ ac : J, z ac := by linarith
  obtain ⟨ac, hac⟩ := exists_large_nonnegative_weighted_term (fun _ : J => (1 : ℝ)) z
    (fun _ => by norm_num) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hδ (Real.exp_pos _) (by simpa using hcard) (by simpa only [one_mul] using hmass')
  have hac' : Real.exp (-(2 * u + 2 + 3 * r)) ≤ z ac := by
    have heq : δ / Real.exp (3 * r) = Real.exp (-(2 * u + 2 + 3 * r)) := by
      dsimp [δ]
      rw [← Real.exp_sub]
      congr 1
      ring
    rwa [heq] at hac
  let expansion := Classical.choice (hK ac.1 i ac.2)
  obtain ⟨j, hj⟩ := expansion.select_mean_row_correlation
    (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
    (fun h n : ZMod N => multiplicativeDerivative f h n *
      W.cyclicDiagonalDerivative ac.1 ![h, n]) (Real.exp_pos _) hac'
  let f₀ (n : ZMod N) := f n * W.eval ac.1.1 (fun _ => (n.val : ℤ))
  let f₁ (n : ZMod N) := f n * W.eval ac.1.2 (fun _ => (n.val : ℤ))
  have hf₀ (n : ZMod N) : ‖f₀ n‖ ≤ 1 := by
    dsimp only [f₀]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (W.norm_eval _ _)
  have hf₁ (n : ZMod N) : ‖f₁ n‖ ≤ 1 := by
    dsimp only [f₁]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (W.norm_eval _ _)
  have hid (h n : ZMod N) :
      multiplicativeDerivative f h n * W.cyclicDiagonalDerivative ac.1 ![h, n] =
        f₀ n * star (f₁ (n + h)) := by
    simp only [multiplicativeDerivative, NativeMultidegreeNilcharacter.cyclicDiagonalDerivative,
      Matrix.cons_val_zero, Matrix.cons_val_one, f₀, f₁, star_mul]
    rw [add_comm h n]
    ring
  have htest : Real.exp (-v) ≤ 𝔼 h : ZMod N,
      ‖𝔼 n : ZMod N, f₀ n * star (f₁ (n + h)) *
        star ((expansion.test j).eval ![(h.val : ℤ), (n.val : ℤ)])‖ := by
    have heq : Real.exp (-(2 * u + 2 + 3 * r)) / Real.exp t = Real.exp (-v) := by
      rw [← Real.exp_sub]
      congr 1
      dsimp [v]
      ring
    change Real.exp (-(2 * u + 2 + 3 * r)) / Real.exp t ≤ _ at hj
    simpa only [heq, hid] using hj
  obtain ⟨χ, hχ⟩ := hfourier (expansion.model j) hv (expansion.test j)
    ((expansion.complexity j).mono (by dsimp [v]; linarith)) f₀ f₁ hf₀ hf₁ htest
  let g (n : ZMod N) := star (W.eval ac.1.2 (fun _ => (n.val : ℤ))) * χ n
  have hg : g ∈ nativeCyclicFunctions 2 N ((p + C) ^ C) := by
    obtain ⟨model⟩ := hprimitive hroot0 W ac.1.2 χ
    have hcost : (tensorPowerBudget 2 q + D) ^ D ≤ (p + C) ^ C :=
      (pow_le_pow_left₀ (by positivity) (add_le_add hroot le_rfl) D).trans hGC
    exact ⟨{ model with complexity := model.complexity.mono hcost }⟩
  refine ⟨g, hg, (Real.exp_le_exp.mpr (neg_le_neg hFC)).trans ?_⟩
  have heq : finiteFourierCoeff f₁ χ = 𝔼 n, f n * star (g n) := by
    unfold finiteFourierCoeff
    apply Finset.expect_congr rfl
    intro n _
    simp only [f₁, g, star_mul, star_star]
    ring
  rwa [heq] at hχ

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_cyclicNativeInverse_two : ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse 2 C := by
  obtain ⟨A, _, hlarge⟩ := exists_quadratic_primitive_correlation_large_modulus
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + 8 * X + 211)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hGowers
  have hp0 : 0 ≤ p := by linarith
  let u := (p + A) ^ A
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + 8 * p + 211 ≤ (p + C) ^ C := by
    simpa [X, u, Polynomial.eval₂_pow] using hbudget p hp0
  have huC : u ≤ (p + C) ^ C := by linarith
  by_cases hN : Real.exp u ≤ (N : ℝ)
  · obtain ⟨g, ⟨model⟩, hcorr⟩ := hlarge hp0 hN f hf hGowers
    exact ⟨g, ⟨{ model with complexity := model.complexity.mono huC }⟩,
      (Real.exp_le_exp.mpr (neg_le_neg huC)).trans hcorr⟩
  · obtain ⟨g, ⟨model⟩, hcorr⟩ :=
      exists_quadratic_small_modulus_correlation (not_le.mp hN).le f hf hGowers
    have h211 : (211 : ℝ) ≤ (p + C) ^ C := by linarith
    have hc : 8 * p + u ≤ (p + C) ^ C := by linarith
    exact ⟨g, ⟨{ model with complexity := model.complexity.mono h211 }⟩,
      (Real.exp_le_exp.mpr (neg_le_neg hc)).trans hcorr⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AxisCompression
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

section

universe u

namespace Erdos3

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_cyclicNativeInverse_add_two (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse (d + 2) C := by
  induction d with
  | zero => exact exists_cyclicNativeInverse_two
  | succ d ih =>
      obtain ⟨I, _, hI⟩ := ih
      exact exists_cyclicNativeInverse_step d hI

end Erdos3

end

section

namespace Erdos3

theorem exists_cyclicNativeInverse_positive (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse s C := by
  cases s with
  | zero => omega
  | succ s =>
      cases s with
      | zero => exact ⟨2, le_rfl, cyclicNativeInverse_one⟩
      | succ s => exact exists_cyclicNativeInverse_add_two s

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_inverse_on_cyclic_encoding (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ] {N : ℕ} [NeZero N]
      (Q : Finset (σ → ℤ)), Q.Nonempty → ∀ (φ : (σ → ℤ) →+ ℤ),
      ReflectsPairSums ((Int.castAddHom (ZMod N)).comp φ) (Q : Set (σ → ℤ)) →
      (∀ x ∈ Q, 0 ≤ φ x ∧ φ x < (N : ℤ)) →
      ∀ {p q : ℝ}, 2 ≤ p → 0 ≤ q → Real.exp (-q) ≤ (Q.card : ℝ) / (N : ℝ) →
      ∀ f : (σ → ℤ) → ℂ, (∀ x ∈ Q, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ finiteSupportGowersNorm (s + 1) Q f →
      ∃ V : NativeSampleCorrelation (fun _ : σ => 1) s ((p + q + C) ^ C) Q id f,
        V.test.normBound ≤ 1 := by
  obtain ⟨C, hC, hinverse⟩ := exists_cyclicNativeInverse_positive s hs
  refine ⟨C, hC, ?_⟩
  intro σ _ _ N _ Q hQ φ hφ hrep p q hp hq hden f hf hGowers
  let ψ : (σ → ℤ) →+ ZMod N := (Int.castAddHom (ZMod N)).comp φ
  let F := imageExtension ψ Q f
  have hF : ∀ y, ‖F y‖ ≤ 1 := imageExtension_norm_le_one ψ Q f hφ.injOn hf
  have hG : Real.exp (-(p + q)) ≤ gowersNorm (s + 1) F :=
    exp_le_gowers_imageExtension s ψ Q hφ f (by simpa only [ZMod.card] using hden) hGowers
  obtain ⟨g, ⟨M⟩, hcorr⟩ := hinverse (by linarith : 2 ≤ p + q) F hF hG
  let T := M.test.linearPullbackHom (fun _ : Unit => φ)
  have heval (x : σ → ℤ) (hx : x ∈ Q) : T.eval x = g (ψ x) := by
    change (M.test.linearPullbackHom (fun _ : Unit => φ)).eval x = g (ψ x)
    rw [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom, M.eval]
    change M.test.eval (fun _ => φ x) = M.test.eval (fun _ => (((φ x : ZMod N).val) : ℤ))
    simp only [ZMod.val_intCast, Int.emod_eq_of_lt (hrep x hx).1 (hrep x hx).2]
  refine ⟨{
    L := M.L
    dim := M.dim
    model := M.model
    test := T
    complexity := M.complexity
    correlation := ?_ }, ?_⟩
  · have hmean : (𝔼 x ∈ Q, f x * star (T.eval x)) =
        (𝔼 x ∈ Q, f x * star (g (ψ x))) := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [heval x hx]
    change Real.exp (-((p + q + C) ^ C)) ≤ ‖𝔼 x ∈ Q, f x * star (T.eval x)‖
    rw [hmean]
    exact hcorr.trans (norm_expect_imageExtension_mul_le ψ Q hQ hφ.injOn f (fun y => star (g y)))
  · exact M.norm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3.PositiveShiftBasis

universe u

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

universe u

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u

namespace PositiveShiftBasis

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

end PositiveShiftBasis
end Erdos3

end

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

open scoped BigOperators TensorProduct

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerBoxInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_integer_box_inverse (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)]
      {p : ℝ}, 2 ≤ p → ∀ f : (Fin n → ℤ) → ℂ,
      (∀ x ∈ integerBox T, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ integerBoxGowersNorm T (s + 1) f →
      ∃ V : NativeSampleCorrelation (fun _ : Fin n => 1) s ((p + n + C) ^ C) (integerBox T) id f,
        V.test.normBound ≤ 1 := by
  obtain ⟨A, _, htransfer⟩ := exists_native_inverse_on_cyclic_encoding s hs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((4 * X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro n T _ p hp f hf hGowers
  have hp0 : 0 ≤ p := by linarith
  have hcost : (p + 4 * (n : ℝ) + A) ^ A ≤ (p + n + C) ^ C := by
    apply (pow_le_pow_left₀ (by positivity)
      (show p + 4 * (n : ℝ) + A ≤ 4 * (p + n) + A by linarith) A).trans
    simpa [X, Polynomial.eval₂_pow] using hbudget (p + n) (by positivity)
  obtain ⟨V, hV⟩ := htransfer (integerBox T) (integerBox_nonempty T) (boxIntegerCode T)
    (boxCyclicCode_reflectsPairSums T) (fun x hx => boxIntegerCode_bounds T x hx)
    hp (by positivity : (0 : ℝ) ≤ 4 * n) (boxCode_density_lower T) f hf hGowers
  exact ⟨V.mono hcost, hV⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CubeMixtureNativeDetection
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_partner_of_cube_mixture (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {n : ℕ} (N : Fin n → ℕ) [∀ i, NeZero (N i)]
      {I : Type*} [Fintype I] (p : ℝ), 0 ≤ p → (n : ℝ) ≤ p →
      ∀ (f : (Fin n → ℤ) → ℂ) (c : I → ℂ)
        (twist : I → (Fin (s + 1) → Bool) → (Fin n → ℤ) → ℂ),
      (∀ x ∈ integerBox N, ‖f x‖ ≤ 1) →
      (∀ i ω x, x ∈ integerBox N → ‖twist i ω x‖ ≤ 1) →
      (∑ i, ‖c i‖) ≤ Real.exp p →
      ∀ z : ℂ, Real.exp (-p) ≤ z.re →
      ‖z - ∑ i, c i * normalizedSupportedCubeSum (s + 1) (integerBox N)
        (fun ω x => f x * twist i ω x)‖ ≤ Real.exp (-p) / 2 →
      ∀ ω : Fin (s + 1) → Bool,
      ∃ (i : I) (V : NativeSampleCorrelation (fun _ : Fin n => 1) s ((p + 2) ^ C)
        (integerBox N) id (fun x => f x * twist i ω x)),
        V.test.normBound ≤ 1 ∧
        Real.exp (-((p + 2) ^ C)) ≤
          ‖𝔼 x ∈ integerBox N, f x * star (star (twist i ω x) * V.test.eval x)‖ := by
  obtain ⟨A, _, hinverse⟩ := exists_native_integer_box_inverse s hs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((3 * X + 2 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro n N _ I _ p hp hn f c twist hf htwist hc z hz herr ω
  let F := fun i ω x => f x * twist i ω x
  have hF (i) (ω) (x) (hx : x ∈ integerBox N) : ‖F i ω x‖ ≤ 1 := by
    dsimp only [F]
    rw [norm_mul]
    exact (mul_le_mul (hf x hx) (htwist i ω x hx) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hlarge : Real.exp (-p) / 2 ≤
      ‖∑ i, c i * normalizedSupportedCubeSum (s + 1) (integerBox N) (F i)‖ := by
    have h := norm_sub_norm_le z (∑ i, c i * normalizedSupportedCubeSum (s + 1) (integerBox N) (F i))
    have hreal := Complex.re_le_norm z
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term c
    (fun i => normalizedSupportedCubeSum (s + 1) (integerBox N) (F i))
    (half_pos (Real.exp_pos _)) (Real.exp_pos p) hc hlarge
  have hG : Real.exp (-(2 * p + 2)) ≤ integerBoxGowersNorm N (s + 1) (F i ω) := by
    have he : Real.exp (-(2 * p)) / 2 = (Real.exp (-p) / 2) / Real.exp p := by
      rw [div_right_comm, ← Real.exp_sub]
      congr 2
      ring
    have hsmall : Real.exp (-(2 * p + 2)) ≤ Real.exp (-(2 * p)) / 2 :=
      (Real.exp_le_exp.mpr (by linarith : -(2 * p + 2) ≤ -(2 * p) - 1)).trans
        (exp_sub_one_le_half_exp (-(2 * p)))
    rw [he] at hsmall
    exact (hsmall.trans hi).trans
      (normalizedSupportedCubeSum_le_vertex (boxReduction_reflectsPairSums N) s (F i) (hF i) ω)
  obtain ⟨V, hV⟩ := hinverse N (by linarith : 2 ≤ 2 * p + 2) (F i ω) (hF i ω) hG
  have hcost : (2 * p + 2 + n + A) ^ A ≤ (p + 2) ^ C := by
    apply (pow_le_pow_left₀ (by positivity)
      (show 2 * p + 2 + (n : ℝ) + A ≤ 3 * p + 2 + A by linarith) A).trans
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨i, V.mono hcost, hV, ?_⟩
  simpa only [star_mul, star_star, F, id_eq, mul_assoc, mul_left_comm, mul_comm] using
    (V.mono hcost).correlation

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalCubeNativeDetection
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_partner_of_physical_cube_mixture (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {n : ℕ} (N : Fin n → ℕ) [∀ i, NeZero (N i)]
      {I : Type*} [Fintype I] (p : ℝ), 0 ≤ p → (n : ℝ) ≤ p →
      ∀ (f : (Fin n → ℤ) → ℂ) (c : I → ℂ)
        (twist : I → Finset (Fin (s + 1)) → (Fin n → ℤ) → ℂ),
      (∀ x ∈ integerBox N, ‖f x‖ ≤ 1) →
      (∀ i ω x, x ∈ integerBox N → ‖twist i ω x‖ ≤ 1) →
      (∑ i, ‖c i‖) ≤ Real.exp p →
      ∀ z : ℂ, Real.exp (-p) ≤ z.re →
      ‖z - ∑ i, c i * (𝔼 cube : SupportedCube (s + 1) (integerBox N : Set ((Fin n) → ℤ)),
        let u := (physicalCubeParametersEquiv (Fin n) (s + 1)).symm cube.val
        ∏ ω, conjugationPower ω.card (f (physicalCubeVertexValue u ω)) *
          twist i ω (physicalCubeVertexValue u ω))‖ ≤ Real.exp (-p) / 2 →
      ∃ (i : I) (V : NativeSampleCorrelation (fun _ : Fin n => 1) s ((p + 2) ^ C)
        (integerBox N) id (fun x => f x * twist i ∅ x)),
        V.test.normBound ≤ 1 ∧
        Real.exp (-((p + 2) ^ C)) ≤
          ‖𝔼 x ∈ integerBox N, f x * star (star (twist i ∅ x) * V.test.eval x)‖ := by
  obtain ⟨C, hC, hdetect⟩ := exists_native_partner_of_cube_mixture s hs
  refine ⟨C, hC, ?_⟩
  intro n N _ I _ p hp hn f c twist hf htwist hc z hz herr
  simp_rw [physical_twisted_cube_mean] at herr
  have ht : ∀ i ω x, x ∈ integerBox N →
      ‖conjugationPower (booleanWeight ω) (twist i (vertexFinsetEquiv (s + 1) ω) x)‖ ≤ 1 := by
    intro i ω x hx
    rw [conjugationPower_norm]
    exact htwist i _ x hx
  have h := hdetect N p hp hn f c
    (fun i ω x => conjugationPower (booleanWeight ω) (twist i (vertexFinsetEquiv (s + 1) ω) x))
    hf ht hc z hz herr (fun _ => false)
  have hweight : booleanWeight (fun _ : Fin (s + 1) => false) = 0 := by
    simp [booleanWeight]
  have hsite : vertexFinsetEquiv (s + 1) (fun _ => false) = ∅ := by
    ext i
    simp [vertexFinsetEquiv]
  rw [hweight, hsite] at h
  exact h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CubeMixtureAllDegrees
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_partner_of_physical_cube_mixture_all_degrees (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {n : ℕ} (N : Fin n → ℕ) [∀ i, NeZero (N i)]
      {I : Type*} [Fintype I] (p : ℝ), 0 ≤ p → (n : ℝ) ≤ p →
      ∀ (f : (Fin n → ℤ) → ℂ) (c : I → ℂ)
        (twist : I → Finset (Fin (s + 1)) → (Fin n → ℤ) → ℂ),
      (∀ x ∈ integerBox N, ‖f x‖ ≤ 1) →
      (∀ i ω x, x ∈ integerBox N → ‖twist i ω x‖ ≤ 1) →
      (∑ i, ‖c i‖) ≤ Real.exp p →
      ∀ z : ℂ, Real.exp (-p) ≤ z.re →
      ‖z - ∑ i, c i * (𝔼 cube : SupportedCube (s + 1) (integerBox N : Set ((Fin n) → ℤ)),
        let u := (physicalCubeParametersEquiv (Fin n) (s + 1)).symm cube.val
        ∏ ω, conjugationPower ω.card (f (physicalCubeVertexValue u ω)) *
          twist i ω (physicalCubeVertexValue u ω))‖ ≤ Real.exp (-p) / 2 →
      ∃ (i : I) (V : NativeSampleCorrelation (fun _ : Fin n => 1) s ((p + 2) ^ C)
        (integerBox N) id (fun x => f x * twist i ∅ x)),
        V.test.normBound ≤ 1 ∧
        Real.exp (-((p + 2) ^ C)) ≤
          ‖𝔼 x ∈ integerBox N, f x * star (star (twist i ∅ x) * V.test.eval x)‖ := by
  by_cases hs : s = 0
  · subst s
    refine ⟨2, le_rfl, ?_⟩
    intro n N _ I _ p hp hn f c twist hf ht hc z hz herr
    obtain ⟨i, hi⟩ := exists_site_twist_of_degree_zero_cube_mixture (X := Fin n)
      (I := I) N p f c twist hf ht hc z hz herr
    have hcost : 2 * p + 2 ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
    have hlow : 2 ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
    let V : NativeSampleCorrelation (fun _ : Fin n => 1) 0 ((p + 2) ^ 2)
        (integerBox N) id (fun x => f x * twist i ∅ x) :=
      NativeSampleCorrelation.ofMean hlow ((Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hi)
    refine ⟨i, V, ?_, ?_⟩
    · simp only [V, NativeSampleCorrelation.ofMean, RationalFilteredNilmanifold.Niltest.const,
        nnnorm_one, le_refl]
    · simpa only [star_mul, star_star, id_eq, mul_assoc, mul_left_comm, mul_comm] using V.correlation
  · exact exists_native_partner_of_physical_cube_mixture s (Nat.one_le_iff_ne_zero.mpr hs)

end Erdos3

end

end OAI

end


