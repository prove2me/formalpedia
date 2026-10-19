-- Prove2me | Definitions.Def_OAIE3v2B012
-- name    : OAIE3v2B012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:58:17.673103+00:00
-- url     : https://prove2.me/theorems/a02feb99-2237-48f1-a46a-344d85ec5291
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 13 of 311
-- statement:
--   Definitions bundle 13 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/CrootSisaskSampleBudget.lean`, `Dynamics/SpectralLogBudget.lean`, `Estimates/CyclicCutNeighborhood.lean`, `Estimates/ImageCosetReconstruction.lean`, `Estimates/LinearCutoff.lean`, `Estimates/LocalBoostedAlmostPeriods.lean`, `Estimates/LocalShiftFiber.lean`, `Estimates/LocalizedSiftingAlmostPeriods.lean`, `Estimates/MonotoneRegularPoint.lean`, `Fourier/ExponentialBohrVolume.lean`, `Fourier/FiniteFourierSmoothing.lean`, `Fourier/TranslatedBohrDifference.lean`, `Geometry/ChordBoxCutoff.lean`, `Geometry/CoordinateTreeOutside.lean`, `Geometry/CoordinateTreeRelabel.lean`, `Lattices/CircleResiduePartition.lean`, `Lattices/ResidueSliceCountingCost.lean`, `Probability/DifferenceEventProbability.lean`, `Probability/MassConvolution.lean`, `Sampling/FiniteSamplingMoment.lean`, `Sampling/LocalSamplingBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CrootSisaskSampleBudget
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

def samplingMomentCost (m k : ℕ) : ℝ :=
  2 * ((8 * (m : ℝ)) ^ m * (k : ℝ) ^ (m - 1) * k * 2 ^ (2 * m))

theorem samplingMomentCost_error {m k : ℕ} (hm : 0 < m) {epsilon : ℝ}
    (hsize : 256 * (m : ℝ) ≤ epsilon ^ 2 * k) :
    2 ^ (2 * m) * samplingMomentCost m k ≤ (k : ℝ) ^ (2 * m) * epsilon ^ (2 * m) := by
  have hkpow : (k : ℝ) ^ (m - 1) * k = (k : ℝ) ^ m := pow_sub_one_mul hm.ne' _
  have hcoeff : (2 : ℝ) ^ (2 * m) * 2 ^ (2 * m) * (8 * (m : ℝ)) ^ m =
      (128 * (m : ℝ)) ^ m := by
    rw [pow_mul, ← mul_pow, ← mul_pow]
    congr 1
    ring
  have hidentity : (2 : ℝ) ^ (2 * m) * samplingMomentCost m k =
      2 * (128 * (m : ℝ)) ^ m * (k : ℝ) ^ m := by
    unfold samplingMomentCost
    calc
      _ = 2 * ((2 : ℝ) ^ (2 * m) * 2 ^ (2 * m) * (8 * (m : ℝ)) ^ m) *
          ((k : ℝ) ^ (m - 1) * k) := by ring
      _ = _ := by rw [hcoeff, hkpow]
  have htwo : (2 : ℝ) ≤ 2 ^ m := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show 1 ≤ m by omega)
  have hbase : 2 * (128 * (m : ℝ)) ≤ epsilon ^ 2 * k := by linarith
  have hpower := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * (128 * (m : ℝ))) hbase m
  have hnum : 2 * (128 * (m : ℝ)) ^ m ≤ epsilon ^ (2 * m) * (k : ℝ) ^ m := by
    calc
      _ ≤ 2 ^ m * (128 * (m : ℝ)) ^ m := mul_le_mul_of_nonneg_right htwo (by positivity)
      _ ≤ (epsilon ^ 2 * k) ^ m := by simpa only [mul_pow] using hpower
      _ = _ := by rw [mul_pow, ← pow_mul]
  rw [hidentity]
  calc
    _ ≤ (epsilon ^ (2 * m) * (k : ℝ) ^ m) * (k : ℝ) ^ m :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = _ := by rw [pow_mul]; ring

noncomputable def crootSisaskSampleSize (m : ℕ) (epsilon : ℝ) : ℕ :=
  ⌈256 * (m : ℝ) / epsilon ^ 2⌉₊

theorem crootSisaskSampleSize_pos {m : ℕ} (hm : 0 < m) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < crootSisaskSampleSize m epsilon := by
  apply Nat.ceil_pos.mpr
  positivity

theorem crootSisaskSampleSize_bound (m : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    256 * (m : ℝ) ≤ epsilon ^ 2 * crootSisaskSampleSize m epsilon := by
  have h := Nat.le_ceil (256 * (m : ℝ) / epsilon ^ 2)
  have h' := (div_le_iff₀ (sq_pos_of_pos hepsilon)).mp h
  simpa only [crootSisaskSampleSize, mul_comm] using h'

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FiniteSamplingMoment
namespace OAI

section

namespace Erdos3.CyclicMZ

open _root_.Finset Fintype Nat

variable {ι : Type*} {A : Finset ι} {m n : ℕ}

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

lemma step_six {f : ι → ℝ} {a b : Fin n → ι} :
    ∑ k ∈ piAntidiag univ m,
        (multinomial univ fun a ↦ 2 * k a : ℝ) *
          ∏ i, (f (a i) - f (b i)) ^ (2 * k i) ≤
      m ^ m * (∑ i, (f (a i) - f (b i)) ^ 2) ^ m := by
  rw [sum_pow_eq_sum_piAntidiag, mul_sum]
  refine sum_le_sum fun k hk ↦ ?_
  rw [mem_piAntidiag] at hk
  simp only [← mul_assoc, pow_mul]
  gcongr
  norm_cast
  refine multinomial_two_mul_le_mul_multinomial.trans ?_
  rw [hk.1]

lemma step_seven {f : ι → ℝ} {a b : Fin n → ι} :
    m ^ m * (∑ i, (f (a i) - f (b i)) ^ 2 : ℝ) ^ m ≤
      m ^ m * 2 ^ m * (∑ i, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m := by
  rw [← mul_pow, ← mul_pow, ← mul_pow, mul_assoc, mul_sum _ _ (2 : ℝ)]
  gcongr with i
  exact add_sq_le.trans_eq (by simp)

lemma step_eight {f : ι → ℝ} {a b : Fin n → ι} :
    m ^ m * 2 ^ m * (∑ i, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m ≤
      m ^ m * 2 ^ (m + (m - 1)) *
        ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) := by
  rw [pow_add, ← mul_assoc _ _ (2 ^ _), mul_assoc _ (2 ^ (m - 1)), sum_add_distrib]
  gcongr
  refine add_pow_le ?_ ?_ m <;> positivity

lemma end_step {f : ι → ℝ} (hm : 1 ≤ m) (hA : A.Nonempty) :
    (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ piAntidiag univ m,
      ↑(multinomial univ fun i ↦ 2 * k i) *
        ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n ≤
      (4 * m) ^ m * ∑ a ∈ A ^^ n, (∑ i, f (a i) ^ 2) ^ m := by
  let B := A ^^ n
  calc
    (∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ piAntidiag univ m,
      (multinomial univ fun i ↦ 2 * k i : ℝ) *
        ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n ≤
      (∑ a ∈ B, ∑ b ∈ B, m ^ m * 2 ^ (m + (m - 1)) *
        ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) : ℝ) / #A ^ n := by
        gcongr
        exact step_six.trans <| step_seven.trans step_eight
    _ = _ := by
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      rw [← mul_add, ← two_mul, ← mul_assoc 2, ← mul_assoc 2, mul_right_comm 2,
        ← _root_.pow_succ', add_assoc, Nat.sub_add_cancel hm, pow_add, ← mul_pow, ← mul_pow,
        card_piFinset, prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow,
        mul_div_cancel_left₀]
      · norm_num
        dsimp [B]
      · positivity

namespace Real

attribute [-instance] decidableForallFin

end Real

end Erdos3.CyclicMZ

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalShiftFiber
namespace OAI

section

namespace Erdos3

open _root_.Finset Fintype
open scoped BigOperators Pointwise

namespace CyclicCrootSisask

variable {N k m : ℕ} [NeZero N]

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

noncomputable def setAverageTranslate
    (A : Finset (ZMod N)) (f : ZMod N → ℝ) (x : ZMod N) : ℝ :=
  (∑ a ∈ A, f (x - a)) / A.card

noncomputable def centeredTranslate
    (A : Finset (ZMod N)) (f : ZMod N → ℝ) (x a : ZMod N) : ℝ :=
  f (x - a) - setAverageTranslate A f x

noncomputable def sampleDeviation
    (A : Finset (ZMod N)) (f : ZMod N → ℝ)
    (a : Fin k → ZMod N) (x : ZMod N) : ℝ :=
  ∑ i, centeredTranslate A f x (a i)

omit [NeZero N] in
lemma sum_centeredTranslate_eq_zero
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ) (x : ZMod N) :
    ∑ a ∈ A, centeredTranslate A f x a = 0 := by
  have hcard : (A.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hA
  unfold centeredTranslate setAverageTranslate
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

omit [NeZero N] in

lemma abs_setAverageTranslate_le
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ)
    {M : ℝ} (_ : 0 ≤ M) (hf : ∀ x, |f x| ≤ M) (x : ZMod N) :
    |setAverageTranslate A f x| ≤ M := by
  have hcard : (0 : ℝ) < A.card := by
    exact_mod_cast Finset.card_pos.mpr hA
  have hsum : ∑ a ∈ A, |f (x - a)| ≤ ∑ _a ∈ A, M := by
    exact Finset.sum_le_sum fun a _ ↦ hf (x - a)
  unfold setAverageTranslate
  calc
    |(∑ a ∈ A, f (x - a)) / (A.card : ℝ)| =
        |∑ a ∈ A, f (x - a)| / (A.card : ℝ) := by
      rw [abs_div, abs_of_pos hcard]
    _ ≤ (∑ a ∈ A, |f (x - a)|) / (A.card : ℝ) := by
      gcongr
      exact abs_sum_le_sum_abs _ _
    _ ≤ (∑ _a ∈ A, M) / (A.card : ℝ) := by gcongr
    _ = M := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp

noncomputable def goodSamples
    (A : Finset (ZMod N)) (f : ZMod N → ℝ) (k m : ℕ) (C : ℝ) :
    Finset (Fin k → ZMod N) :=
  (A ^^ k).filter fun a ↦
    (∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m)) ≤ C

lemma mem_goodSamples
    {A : Finset (ZMod N)} {f : ZMod N → ℝ} {C : ℝ}
    {a : Fin k → ZMod N} :
    a ∈ goodSamples A f k m C ↔
      a ∈ A ^^ k ∧
        (∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m)) ≤ C := by
  simp [goodSamples]

omit [NeZero N] in
lemma sampleDeviation_sub_const_identity
    (A : Finset (ZMod N)) (f : ZMod N → ℝ)
    (a : Fin k → ZMod N) (t x : ZMod N) :
    sampleDeviation A f (a - fun _ ↦ t) x -
        sampleDeviation A f a (x + t) =
      (k : ℝ) *
        (setAverageTranslate A f (x + t) - setAverageTranslate A f x) := by
  unfold sampleDeviation centeredTranslate
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul]
  have harg (i : Fin k) : x - (a i - t) = x + t - a i := by abel
  simp_rw [harg]
  simp only [Finset.card_univ, Fintype.card_fin]
  ring

theorem goodSamples_give_almost_period
    {A : Finset (ZMod N)} {f : ZMod N → ℝ} {C : ℝ}
    {a : Fin k → ZMod N} {t : ZMod N}
    (ha : a ∈ goodSamples A f k m C)
    (hat : (a - fun _ ↦ t) ∈ goodSamples A f k m C) :
    (k : ℝ) ^ (2 * m) *
        ∑ x : ZMod N,
          |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m) ≤
      2 ^ (2 * m) * C := by
  have haMoment := (mem_goodSamples (N := N) (k := k) (m := m)).1 ha |>.2
  have hatMoment := (mem_goodSamples (N := N) (k := k) (m := m)).1 hat |>.2
  have hshift :
      (∑ x : ZMod N, |sampleDeviation A f a (x + t)| ^ (2 * m)) =
        ∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m) := by
    exact Fintype.sum_equiv (Equiv.addRight t) _ _ fun _ ↦ rfl
  by_cases hm : m = 0
  · subst m
    simpa using haMoment
  have hpne : 2 * m ≠ 0 := mul_ne_zero two_ne_zero hm
  calc
    (k : ℝ) ^ (2 * m) *
        ∑ x : ZMod N,
          |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m) =
      ∑ x : ZMod N,
        ((k : ℝ) ^ (2 * m) *
          |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m)) := by
      rw [Finset.mul_sum]
    _ = ∑ x : ZMod N,
        |sampleDeviation A f (a - fun _ ↦ t) x -
          sampleDeviation A f a (x + t)| ^ (2 * m) := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [← mul_pow]
      have hkabs : |(k : ℝ)| = k := abs_of_nonneg (Nat.cast_nonneg k)
      rw [← hkabs, ← abs_mul, ← sampleDeviation_sub_const_identity]
    _ ≤ ∑ x : ZMod N, 2 ^ (2 * m - 1) *
        (|sampleDeviation A f (a - fun _ ↦ t) x| ^ (2 * m) +
          |sampleDeviation A f a (x + t)| ^ (2 * m)) := by
      refine Finset.sum_le_sum fun x _ ↦ ?_
      calc
        |sampleDeviation A f (a - fun _ ↦ t) x -
            sampleDeviation A f a (x + t)| ^ (2 * m) ≤
          (|sampleDeviation A f (a - fun _ ↦ t) x| +
            |sampleDeviation A f a (x + t)|) ^ (2 * m) := by
          exact pow_le_pow_left₀ (abs_nonneg _)
            (abs_sub _ _)
            _
        _ ≤ _ := add_pow_le (abs_nonneg _) (abs_nonneg _) _
    _ = 2 ^ (2 * m - 1) *
        ((∑ x : ZMod N,
            |sampleDeviation A f (a - fun _ ↦ t) x| ^ (2 * m)) +
          ∑ x : ZMod N, |sampleDeviation A f a (x + t)| ^ (2 * m)) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 ^ (2 * m - 1) * (C + C) := by
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add hatMoment (by rwa [hshift])
      · positivity
    _ = 2 ^ (2 * m) * C := by
      conv_rhs => rw [show 2 * m = (2 * m - 1) + 1 by omega, pow_add, pow_one]
      ring

end CyclicCrootSisask
end Erdos3

end

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators Pointwise

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

theorem exists_local_shift_fiber {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A S : Finset G} (hA : A.Nonempty) (hS : S.Nonempty) {k : ℕ}
    (L : Finset (Fin k → G)) (hL : L.Nonempty) (hLA : L ⊆ A ^^ k) :
    ∃ (x : Fin k → G) (T : Finset G), T ⊆ S ∧ T.Nonempty ∧
      ((L.card : ℝ) * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card ∧
      ∀ t ∈ T, (x - fun _ => t) ∈ L := by
  classical
  let P := L ×ˢ S
  let X := (A + S) ^^ k
  let φ : ((Fin k → G) × G) → (Fin k → G) := fun z => z.1 + fun _ => z.2
  have hX : X.Nonempty := (hA.add hS).piFinset_const
  have hmap : ∀ z ∈ P, φ z ∈ X := by
    rintro ⟨a, t⟩ hat
    obtain ⟨ha, ht⟩ := Finset.mem_product.mp hat
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.add_mem_add (Fintype.mem_piFinset.mp (hLA ha) i) ht
  have hXcard : (X.card : ℝ) = ((A + S).card : ℝ) ^ k := by
    simp [X]
  have hXne : (X.card : ℝ) ≠ 0 := by exact_mod_cast hX.card_ne_zero
  have hpigeon : ∃ x ∈ X, ((L.card : ℝ) * S.card) / X.card ≤
      ∑ z ∈ P with φ z = x, (1 : ℝ) := by
    apply Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hmap hX
    simp only [nsmul_eq_mul, sum_const, P, card_product, Nat.cast_mul]
    rw [mul_comm (X.card : ℝ), div_mul_cancel₀ _ hXne, mul_one]
  obtain ⟨x, _hx, hx⟩ := hpigeon
  let Q := P.filter (fun z => φ z = x)
  let T := Q.image Prod.snd
  have hQcard : (Q.card : ℝ) = ∑ z ∈ P with φ z = x, (1 : ℝ) := by simp [Q]
  have hinj : _root_.Set.InjOn Prod.snd (Q : _root_.Set ((Fin k → G) × G)) := by
    rintro ⟨a, s⟩ has ⟨b, t⟩ hbt hst
    have hab : a + (fun _ => s) = b + fun _ => t :=
      (Finset.mem_filter.mp has).2.trans (Finset.mem_filter.mp hbt).2.symm
    cases hst
    apply Prod.ext
    · funext i
      exact add_right_cancel (congrFun hab i)
    · rfl
  have hTcard : T.card = Q.card := Finset.card_image_iff.mpr hinj
  have hQpos : (0 : ℝ) < Q.card := by
    have hratio : 0 < ((L.card : ℝ) * S.card) / X.card := by
      apply div_pos
      · exact mul_pos (by exact_mod_cast hL.card_pos) (by exact_mod_cast hS.card_pos)
      · exact_mod_cast hX.card_pos
    exact hratio.trans_le (by simpa only [← hQcard] using hx)
  have hT : T.Nonempty := by
    rw [← Finset.card_pos, hTcard]
    exact_mod_cast hQpos
  refine ⟨x, T, ?_, hT, ?_, ?_⟩
  · intro t ht
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).2
  · rw [← hXcard, hTcard, hQcard]
    exact hx
  · intro t ht
    obtain ⟨⟨a, s⟩, has, hst⟩ := Finset.mem_image.mp ht
    have hax := (Finset.mem_filter.mp has).2
    have ha := (Finset.mem_product.mp (Finset.mem_filter.mp has).1).1
    have heq : (x - fun _ => t) = a := by
      funext i
      have h := congrFun hax i
      change a i + s = x i at h
      change s = t at hst
      simp only [Pi.sub_apply]
      rw [← h, hst, add_sub_cancel_right]
    rw [heq]
    exact ha

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalBoostedAlmostPeriods
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem setAverageTranslate_sub (A : Finset (ZMod N)) (f g : ZMod N → ℝ) (x : ZMod N) :
    setAverageTranslate A (fun y => f y - g y) x =
      setAverageTranslate A f x - setAverageTranslate A g x := by
  simp only [setAverageTranslate, Finset.sum_sub_distrib, sub_div]

omit [NeZero N] in
theorem setAverageTranslate_rightTranslate (A : Finset (ZMod N)) (f : ZMod N → ℝ) (x t : ZMod N) :
    setAverageTranslate A (fun y => f (y + t)) x = setAverageTranslate A f (x + t) := by
  unfold setAverageTranslate
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change f (x - a + t) = f (x + t - a)
  rw [show x - a + t = x + t - a by abel]

omit [NeZero N] in
theorem setAverageTranslate_abs_pow_le {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (x : ZMod N) (n : ℕ) :
    |setAverageTranslate A f x| ^ n ≤ (∑ a ∈ A, |f (x - a)| ^ n) / A.card := by
  have hc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  cases n with
  | zero => simp [hc.ne']
  | succ n =>
    have habs : |setAverageTranslate A f x| ≤ (∑ a ∈ A, |f (x - a)|) / A.card := by
      rw [setAverageTranslate, abs_div, abs_of_pos hc]
      exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hc.le
    have hj := pow_sum_div_card_le_sum_pow (s := A) (fun a _ => abs_nonneg (f (x - a))) n
    calc
      _ ≤ ((∑ a ∈ A, |f (x - a)|) / A.card) ^ (n + 1) :=
        pow_le_pow_left₀ (abs_nonneg _) habs _
      _ = (∑ a ∈ A, |f (x - a)|) ^ (n + 1) / (A.card : ℝ) ^ n / A.card := by
        rw [div_pow, pow_succ (A.card : ℝ) n, div_mul_eq_div_div]
      _ ≤ _ := div_le_div_of_nonneg_right hj hc.le

theorem setAverageTranslate_abs_pow_le_total {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (x : ZMod N) (n : ℕ) :
    |setAverageTranslate A f x| ^ n ≤ (∑ y, |f y| ^ n) / A.card := by
  apply (setAverageTranslate_abs_pow_le hA f x n).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ y, |f (x - y)| ^ n := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ A) (fun _ _ _ => by positivity)
    _ = _ := Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun _ => rfl)

theorem convolution_period_moment_bound {L : Finset (ZMod N)} (hL : L.Nonempty)
    (u : ZMod N → ℝ) (t x : ZMod N) (n : ℕ) {E : ℝ}
    (hperiod : ∑ y, |u (y + t) - u y| ^ n ≤ E) :
    |setAverageTranslate L u (x + t) - setAverageTranslate L u x| ^ n ≤ E / L.card := by
  have h := setAverageTranslate_abs_pow_le_total hL (fun y => u (y + t) - u y) x n
  rw [setAverageTranslate_sub, setAverageTranslate_rightTranslate] at h
  exact h.trans (div_le_div_of_nonneg_right hperiod (Nat.cast_nonneg _))

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators

variable {N k m : ℕ} [NeZero N]

theorem goodSamples_relative_moment_bound {A : Finset (ZMod N)} {f : ZMod N → ℝ}
    (hm : 0 < m) (hk : 0 < k) {epsilon : ℝ}
    (hsize : 256 * (m : ℝ) ≤ epsilon ^ 2 * k)
    {a : Fin k → ZMod N} {t : ZMod N}
    (ha : a ∈ goodSamples A f k m (samplingMomentCost m k * ∑ x, |f x| ^ (2 * m)))
    (hat : (a - fun _ => t) ∈
      goodSamples A f k m (samplingMomentCost m k * ∑ x, |f x| ^ (2 * m))) :
    ∑ x, |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m) ≤
      epsilon ^ (2 * m) * ∑ x, |f x| ^ (2 * m) := by
  have hraw := goodSamples_give_almost_period ha hat
  have hbudget := samplingMomentCost_error hm hsize
  have hS : (0 : ℝ) ≤ ∑ x, |f x| ^ (2 * m) := Finset.sum_nonneg (fun _ _ => by positivity)
  have hupper := mul_le_mul_of_nonneg_right hbudget hS
  have hfinal : (k : ℝ) ^ (2 * m) *
      (∑ x, |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m)) ≤
        (k : ℝ) ^ (2 * m) * (epsilon ^ (2 * m) * ∑ x, |f x| ^ (2 * m)) := by
    apply hraw.trans
    simpa only [mul_assoc] using hupper
  exact le_of_mul_le_mul_left hfinal (pow_pos (by exact_mod_cast hk) _)

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

variable {N : ℕ}

noncomputable def convolutionMomentOrder (M L : Finset (ZMod N)) : ℕ :=
  ⌈1 + Real.log (max 1 ((M.card : ℝ) / L.card))⌉₊

theorem convolutionMomentOrder_pos (M L : Finset (ZMod N)) :
    0 < convolutionMomentOrder M L := by
  apply Nat.ceil_pos.mpr
  have h := Real.log_nonneg (le_max_left 1 ((M.card : ℝ) / L.card))
  linarith

theorem cardinal_ratio_le_exp_momentOrder (M L : Finset (ZMod N)) :
    (M.card : ℝ) / L.card ≤ Real.exp (2 * (convolutionMomentOrder M L : ℝ)) := by
  let R : ℝ := max 1 ((M.card : ℝ) / L.card)
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hceil : 1 + Real.log R ≤ (convolutionMomentOrder M L : ℝ) := Nat.le_ceil _
  have hm : (0 : ℝ) ≤ convolutionMomentOrder M L := Nat.cast_nonneg _
  calc
    _ ≤ R := le_max_right _ _
    _ = Real.exp (Real.log R) := (Real.exp_log hR).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem convolution_moment_to_pointwise (M L : Finset (ZMod N)) {delta z : ℝ}
    (hdelta : 0 < delta)
    (hz : |z| ^ (2 * convolutionMomentOrder M L) ≤
      (delta / Real.exp 1) ^ (2 * convolutionMomentOrder M L) * ((M.card : ℝ) / L.card)) :
    |z| ≤ delta := by
  let m := convolutionMomentOrder M L
  have hm : 0 < m := convolutionMomentOrder_pos M L
  have hexp : Real.exp (2 * (m : ℝ)) = Real.exp 1 ^ (2 * m) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 (2 * m)
  apply le_of_pow_le_pow_left₀ (show 2 * m ≠ 0 by omega) hdelta.le
  calc
    _ ≤ (delta / Real.exp 1) ^ (2 * m) * ((M.card : ℝ) / L.card) := hz
    _ ≤ (delta / Real.exp 1) ^ (2 * m) * Real.exp (2 * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left (cardinal_ratio_le_exp_momentOrder M L) (by positivity)
    _ = delta ^ (2 * m) := by
      rw [hexp, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (Real.exp_ne_zero _))]

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators

variable {N : ℕ}

noncomputable def iteratedSetAverage (A : Finset (ZMod N)) (u : ZMod N → ℝ) :
    ℕ → ZMod N → ℝ
  | 0 => u
  | n + 1 => setAverageTranslate A (iteratedSetAverage A u n)

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LocalSamplingBudget
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

theorem crootSisaskSampleSize_le (m : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (crootSisaskSampleSize m epsilon : ℝ) ≤ 256 * (m : ℝ) / epsilon ^ 2 + 1 := by
  apply (Nat.ceil_lt_add_one (show 0 ≤ 256 * (m : ℝ) / epsilon ^ 2 by positivity)).le

variable {N : ℕ}

theorem convolutionMomentOrder_le (M L : Finset (ZMod N)) :
    (convolutionMomentOrder M L : ℝ) ≤ 2 + Real.log (max 1 ((M.card : ℝ) / L.card)) := by
  have hlog := Real.log_nonneg (le_max_left 1 ((M.card : ℝ) / L.card))
  have h := Nat.ceil_lt_add_one (show 0 ≤ 1 + Real.log (max 1 ((M.card : ℝ) / L.card)) by linarith)
  change (⌈1 + Real.log (max 1 ((M.card : ℝ) / L.card))⌉₊ : ℝ) ≤ _
  linarith

theorem convolutionMomentOrder_le_of_ratio (M L : Finset (ZMod N)) {p : ℝ} (hp : 0 ≤ p)
    (hratio : (M.card : ℝ) / L.card ≤ Real.exp p) :
    (convolutionMomentOrder M L : ℝ) ≤ p + 2 := by
  have hmax : max 1 ((M.card : ℝ) / L.card) ≤ Real.exp p :=
    max_le (Real.one_le_exp_iff.mpr hp) hratio
  have hpos : (0 : ℝ) < max 1 ((M.card : ℝ) / L.card) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlog := Real.log_le_log hpos hmax
  rw [Real.log_exp] at hlog
  exact (convolutionMomentOrder_le M L).trans (by linarith)

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SpectralLogBudget
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

noncomputable def spectralIterations (epsilon p : ℝ) : ℕ :=
  ⌈(p + Real.log (16 / epsilon)) / Real.log 2⌉₊ + 1

theorem half_pow_spectralIterations_mul_exp_le {epsilon p : ℝ} (hepsilon : 0 < epsilon) :
    (1 / 2 : ℝ) ^ spectralIterations epsilon p * Real.exp p ≤ epsilon / 16 := by
  let q := spectralIterations epsilon p
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : (p + Real.log (16 / epsilon)) / Real.log 2 ≤ (q : ℝ) := by
    apply (Nat.le_ceil _).trans
    dsimp [q, spectralIterations]
    exact_mod_cast Nat.le_succ _
  have hmul := (div_le_iff₀ htwo).mp hq
  have hpow : (1 / 2 : ℝ) ^ q = Real.exp (-((q : ℝ) * Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp [one_div, inv_pow]
  calc
    (1 / 2 : ℝ) ^ q * Real.exp p = Real.exp (-((q : ℝ) * Real.log 2) + p) := by
      rw [hpow, ← Real.exp_add]
    _ ≤ Real.exp (-Real.log (16 / epsilon)) := Real.exp_le_exp.mpr (by linarith)
    _ = epsilon / 16 := by
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 16 / epsilon)]
      field_simp

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def finiteSetAverage (A : Finset G) (f : G → ℂ) (x : G) : ℂ :=
  𝔼 a ∈ A, f (x - a)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

def finiteIndicator (I : Finset H) (x : H) : ℂ := if x ∈ I then 1 else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageCosetReconstruction
namespace OAI

section

namespace Erdos3

variable {H G A : Type*} [Group H] [Group G]

def CosetImage (φ : H →* G) (Λ : Subgroup G) :=
  Set.range (fun x : H => (QuotientGroup.mk (φ x) : G ⧸ Λ))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def linearCutoff (a : ℝ) (h : ℝ≥0) (t : ℝ) : ℝ :=
  max 0 (min 1 ((a + (h : ℝ) - t) / h))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MassConvolution
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [DecidableEq G]

noncomputable def realUniformMass (A : Finset G) (x : G) : ℝ :=
  if x ∈ A then (A.card : ℝ)⁻¹ else 0

theorem uniformMass_translation_le_shell [Fintype G] [AddCommGroup G]
    (A I O : Finset G) (t : G)
    (hinner : ∀ x ∈ I, x ∈ A ∧ x - t ∈ A)
    (houter : ∀ x, x ∈ A ∨ x - t ∈ A → x ∈ O) :
    ∑ x, |realUniformMass A (x - t) - realUniformMass A x| ≤
      ((O.card : ℝ) - I.card) / A.card := by
  have hpoint (x : G) :
      |realUniformMass A (x - t) - realUniformMass A x| ≤
        (if x ∈ O then (A.card : ℝ)⁻¹ else 0) -
          (if x ∈ I then (A.card : ℝ)⁻¹ else 0) := by
    by_cases hi : x ∈ I
    · obtain ⟨ha, ht⟩ := hinner x hi
      have ho := houter x (Or.inl ha)
      simp [realUniformMass, hi, ho, ha, ht]
    · by_cases ha : x ∈ A <;> by_cases ht : x - t ∈ A
      · have ho := houter x (Or.inl ha)
        simp [realUniformMass, hi, ho, ha, ht]
      · have ho := houter x (Or.inl ha)
        simp [realUniformMass, hi, ho, ha, ht]
      · have ho := houter x (Or.inr ht)
        simp [realUniformMass, hi, ho, ha, ht]
      · simp only [realUniformMass, ha, ht, hi, ite_false, sub_zero, abs_zero]
        split_ifs <;> positivity
  calc
    _ ≤ ∑ x, ((if x ∈ O then (A.card : ℝ)⁻¹ else 0) -
        (if x ∈ I then (A.card : ℝ)⁻¹ else 0)) := Finset.sum_le_sum (fun x _ => hpoint x)
    _ = _ := by simp [Finset.sum_sub_distrib, div_eq_mul_inv, sub_mul]

end Erdos3

end

section

open _root_.Finset
open scoped BigOperators

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def massConvolution (f g : G → ℝ) (x : G) : ℝ :=
  ∑ y : G, f y * g (x - y)

omit [AddCommGroup G] [Fintype G] in
@[simp]
theorem realUniformMass_apply_mem {A : Finset G} {x : G} (hx : x ∈ A) :
    realUniformMass A x = (#A : ℝ)⁻¹ := by
  simp [realUniformMass, hx]

omit [AddCommGroup G] [Fintype G] in
@[simp]
theorem realUniformMass_apply_not_mem {A : Finset G} {x : G} (hx : x ∉ A) :
    realUniformMass A x = 0 := by
  simp [realUniformMass, hx]

def convolutionPower (f : G → ℝ) : ℕ → G → ℝ
  | 0 => realUniformMass {0}
  | n + 1 => massConvolution (convolutionPower f n) f

@[simp] theorem convolutionPower_zero (f : G → ℝ) :
    convolutionPower f 0 = realUniformMass {0} := rfl

end

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MonotoneRegularPoint
namespace OAI

section

namespace Erdos3

open _root_.Finset
open scoped BigOperators

theorem exists_regular_point_of_monotone
    (f : ℝ → ℝ) (hf : Monotone f)
    (hgrowth : f (5 / 4) - f (1 / 4) < 5) :
    ∃ x ∈ Set.Icc (1 / 2 : ℝ) 1,
      ∀ y ∈ Set.Icc (1 / 4 : ℝ) (5 / 4),
        |f y - f x| ≤ 60 * |y - x| := by
  classical
  by_contra! hregular
  let Bad : Set (ℝ × ℝ) := {p |
    1 / 4 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 5 / 4 ∧
      60 * (p.2 - p.1) < f p.2 - f p.1}
  let center : (ℝ × ℝ) → ℝ := fun p ↦ (p.1 + p.2) / 2
  let radius : (ℝ × ℝ) → ℝ := fun p ↦ (p.2 - p.1) / 2
  have hradius_pos {p : ℝ × ℝ} (hp : p ∈ Bad) : 0 < radius p := by
    dsimp [Bad] at hp
    dsimp [radius]
    linarith
  have hradius_le (p : ℝ × ℝ) (hp : p ∈ Bad) : radius p ≤ 1 / 2 := by
    dsimp [Bad] at hp
    dsimp [radius]
    linarith
  obtain ⟨u, huBad, huDisjoint, huCover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
      Bad center radius (1 / 2) hradius_le 5 (by norm_num)
  have hcentralCover : Set.Icc (1 / 2 : ℝ) 1 ⊆
      ⋃ b : ↥u, Metric.ball (center b.1) (6 * radius b.1) := by
    intro x hx
    obtain ⟨y, hybuf, hxy⟩ := hregular x hx
    let p : ℝ × ℝ := (min x y, max x y)
    have hpbuf : p ∈ Bad := by
      dsimp [Bad, p]
      have hxbuf : x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4) := by
        constructor <;> linarith [hx.1, hx.2]
      rcases le_total x y with hle | hle
      · simp only [min_eq_left hle, max_eq_right hle]
        have habs : |f y - f x| = f y - f x :=
          abs_of_nonneg (sub_nonneg.mpr (hf hle))
        have hdist : |y - x| = y - x := abs_of_nonneg (sub_nonneg.mpr hle)
        rw [habs, hdist] at hxy
        exact ⟨hxbuf.1, lt_of_not_ge (fun heq ↦ by
          have : y = x := le_antisymm heq hle
          subst y
          norm_num at hxy), hybuf.2, hxy⟩
      · simp only [min_eq_right hle, max_eq_left hle]
        have habs : |f y - f x| = f x - f y := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (sub_nonneg.mpr (hf hle))
        have hdist : |y - x| = x - y := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (sub_nonneg.mpr hle)
        rw [habs, hdist] at hxy
        exact ⟨hybuf.1, lt_of_not_ge (fun heq ↦ by
          have : x = y := le_antisymm heq hle
          subst y
          norm_num at hxy), hxbuf.2, hxy⟩
    obtain ⟨b, hbu, hsub⟩ := huCover p hpbuf
    have hxp : x ∈ Metric.closedBall (center p) (radius p) := by
      rw [Real.closedBall_eq_Icc]
      dsimp [center, radius, p]
      constructor <;> rcases le_total x y with hle | hle <;>
        simp [hle] <;> linarith
    have hxb : x ∈ Metric.closedBall (center b) (5 * radius b) := hsub hxp
    rw [Metric.mem_closedBall] at hxb
    rw [Set.mem_iUnion]
    refine ⟨⟨b, hbu⟩, ?_⟩
    rw [Metric.mem_ball]
    have hbr : 0 < radius b := hradius_pos (huBad hbu)
    linarith
  obtain ⟨v, hvCover⟩ := isCompact_Icc.elim_finite_subcover
    (fun b : ↥u ↦ Metric.ball (center b.1) (6 * radius b.1))
    (fun _ ↦ Metric.isOpen_ball) hcentralCover
  have hv_nonempty : v.Nonempty := by
    by_contra hv
    rw [Finset.not_nonempty_iff_eq_empty] at hv
    simpa [hv] using hvCover (show (1 / 2 : ℝ) ∈ Set.Icc (1 / 2) 1 by norm_num)
  have hvolume : (1 / 2 : ℝ) ≤ 6 * ∑ b ∈ v, (b.1.2 - b.1.1) := by
    have hm : MeasureTheory.volume (Set.Icc (1 / 2 : ℝ) 1) ≤
        MeasureTheory.volume (⋃ b ∈ v,
          Metric.ball (center b.1) (6 * radius b.1)) :=
      MeasureTheory.measure_mono hvCover
    have hright : 0 ≤ 6 * ∑ b ∈ v, (b.1.2 - b.1.1) := by
      apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intro b hb
      have := hradius_pos (huBad b.2)
      dsimp [radius] at this
      linarith
    rw [← ENNReal.ofReal_le_ofReal_iff hright]
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) =
        MeasureTheory.volume (Set.Icc (1 / 2 : ℝ) 1) := by
      rw [Real.volume_Icc]
      norm_num
    rw [hhalf]
    calc
      MeasureTheory.volume (Set.Icc (1 / 2 : ℝ) 1) ≤
          MeasureTheory.volume (⋃ b ∈ v,
            Metric.ball (center b.1) (6 * radius b.1)) := hm
      _ ≤ ∑ b ∈ v, MeasureTheory.volume
          (Metric.ball (center b.1) (6 * radius b.1)) :=
        MeasureTheory.measure_biUnion_finset_le v _
      _ = ENNReal.ofReal (6 * ∑ b ∈ v, (b.1.2 - b.1.1)) := by
        simp only [Real.volume_ball]
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          simp only [radius]
          calc
            ∑ b ∈ v, 2 * (6 * ((b.1.2 - b.1.1) / 2)) =
                ∑ b ∈ v, 6 * (b.1.2 - b.1.1) := by
              apply Finset.sum_congr rfl
              intro b hb
              ring
            _ = 6 * ∑ b ∈ v, (b.1.2 - b.1.1) := by
              rw [Finset.mul_sum]
        · intro b hb
          have := hradius_pos (huBad b.2)
          dsimp [radius] at this
          positivity
      _ = ENNReal.ofReal (6 * ∑ b ∈ v, (b.1.2 - b.1.1)) := rfl
  let e : ↥u ↪ (ℝ × ℝ) := ⟨Subtype.val, Subtype.val_injective⟩
  let F : Finset (ℝ × ℝ) := v.map e
  have hball (p : ℝ × ℝ) :
      Metric.closedBall (center p) (radius p) = Set.Icc p.1 p.2 := by
    rw [Real.closedBall_eq_Icc]
    dsimp [center, radius]
    congr <;> ring
  have hF_bounds : ∀ ⦃z⦄, z ∈ F →
      (1 / 4 : ℝ) ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ 5 / 4 := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hz
    have hbad := huBad b.2
    dsimp [Bad] at hbad
    exact ⟨hbad.1, hbad.2.1.le, hbad.2.2.1⟩
  have hF_disjoint : (SetLike.coe F).PairwiseDisjoint
      (fun z ↦ Set.Icc z.1 z.2) := by
    intro z hz w hw hzw
    obtain ⟨bz, hbz, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨bw, hbw, rfl⟩ := Finset.mem_map.mp hw
    have hne : (bz : ℝ × ℝ) ≠ bw := by
      simpa [e] using hzw
    have hd := huDisjoint bz.2 bw.2 hne
    change Disjoint (Metric.closedBall (center bz) (radius bz))
      (Metric.closedBall (center bw) (radius bw)) at hd
    rw [hball, hball] at hd
    simpa [e] using hd
  have hsum_le : ∑ z ∈ F, (f z.2 - f z.1) ≤ f (5 / 4) - f (1 / 4) := by
    have htel := F.sum_intervalGapsWithin_add_sum_eq_sub rfl
      (a := (1 / 4 : ℝ)) (b := (5 / 4 : ℝ)) f
    calc
      ∑ z ∈ F, (f z.2 - f z.1) ≤ _ := by
        rw [le_add_iff_nonneg_left]
        apply Finset.sum_nonneg
        intro i hi
        apply sub_nonneg.mpr
        apply hf
        exact F.intervalGapsWithin_fst_le_snd rfl _ (by norm_num)
          hF_bounds hF_disjoint
      _ = f (5 / 4) - f (1 / 4) := htel
  have hbad_sum : 60 * ∑ b ∈ v, (b.1.2 - b.1.1) <
      ∑ z ∈ F, (f z.2 - f z.1) := by
    rw [Finset.sum_map]
    simp only [e, Function.Embedding.coeFn_mk]
    rw [Finset.mul_sum]
    exact Finset.sum_lt_sum_of_nonempty hv_nonempty
      (fun b hb ↦ (huBad b.2).2.2.2)
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ExponentialBohrVolume
namespace OAI

section

namespace Erdos3

open AddChar _root_.Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

lemma norm_one_sub_mul_of_norm_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖1 - a * b‖ ≤ ‖1 - a‖ + ‖1 - b‖ := by
  calc
    ‖1 - a * b‖ = ‖(1 - a) + a * (1 - b)‖ := by ring_nf
    _ ≤ ‖1 - a‖ + ‖a * (1 - b)‖ := norm_add_le _ _
    _ ≤ ‖1 - a‖ + ‖1 - b‖ := by
      gcongr
      exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) ha)

end CyclicBohr
end Erdos3

end

section

namespace Erdos3

open AddChar _root_.Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

lemma norm_sub_le_abs_arg_sub_of_norm_eq_one {z w : ℂ}
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖z - w‖ ≤ |z.arg - w.arg| := by
  have hzexp : Complex.exp (z.arg * Complex.I) = z := by
    calc
      Complex.exp (z.arg * Complex.I) =
          ‖z‖ * Complex.exp (z.arg * Complex.I) := by simp [hz]
      _ = z := Complex.norm_mul_exp_arg_mul_I z
  have hwexp : Complex.exp (w.arg * Complex.I) = w := by
    calc
      Complex.exp (w.arg * Complex.I) =
          ‖w‖ * Complex.exp (w.arg * Complex.I) := by simp [hw]
      _ = w := Complex.norm_mul_exp_arg_mul_I w
  calc
    ‖z - w‖ =
        ‖Complex.exp (z.arg * Complex.I) - Complex.exp (w.arg * Complex.I)‖ := by
      rw [hzexp, hwexp]
    _ =
        ‖Complex.exp (w.arg * Complex.I) *
          (Complex.exp ((z.arg - w.arg) * Complex.I) - 1)‖ := by
      congr 1
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      ring
    _ = ‖Complex.exp ((z.arg - w.arg) * Complex.I) - 1‖ := by
      rw [norm_mul, Complex.norm_exp]
      simp
    _ ≤ |z.arg - w.arg| := by
      simpa [mul_comm, Real.norm_eq_abs] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := z.arg - w.arg))

noncomputable def scaledArg (m : ℕ) (z : ℂ) : ℝ :=
  (z.arg + Real.pi) * m / (2 * Real.pi)

lemma scaledArg_le (m : ℕ) (z : ℂ) : scaledArg m z ≤ m := by
  unfold scaledArg
  have hz : z.arg + Real.pi ≤ 2 * Real.pi := by
    linarith [Complex.arg_le_pi z]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [div_le_iff₀ hpi]
  nlinarith

noncomputable def argBin (m : ℕ) (z : ℂ) : Fin (m + 1) :=
  ⟨⌊scaledArg m z⌋₊, by
    rw [Nat.floor_lt' (Nat.add_one_ne_zero m)]
    exact (scaledArg_le m z).trans_lt (by exact_mod_cast Nat.lt_succ_self m)⟩

end CyclicBohr
end Erdos3

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators

variable {N : ℕ} [NeZero N]

lemma norm_one_sub_prod_le_sum {ι : Type*}
    (s : Finset ι) (f : ι → ℂ) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖1 - ∏ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖1 - f i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (norm_one_sub_mul_of_norm_le_one (hf a (by simp))).trans
        (add_le_add le_rfl (ih fun i hi ↦ hf i (by simp [hi])))

end Erdos3.CyclicBohr.Set

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ChordBoxCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def chordBoxCutoff (a : ℝ) (h : ℝ≥0) (z : ι → ℂ) : ℝ :=
  ∏ i, linearCutoff a h ‖1 - z i‖

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TranslatedBohrDifference
namespace OAI

section

open AddChar _root_.Finset
open scoped BigOperators NNReal

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma normalizedSpectrum_translate (A : Finset G)
    (psi : AddChar G ℂ) (t : G) :
    (1 - psi t) * (∑ x : G, (realUniformMass A x : ℂ) * psi x) =
      ∑ x : G,
        ((realUniformMass A x - realUniformMass A (x - t) : ℝ) : ℂ) *
          psi x := by
  classical
  have htranslate :
      (∑ x : G, (realUniformMass A (x - t) : ℂ) * psi x) =
        psi t * ∑ x : G, (realUniformMass A x : ℂ) * psi x := by
    rw [← (Equiv.addRight t).sum_comp]
    · change
        (∑ x : G, (realUniformMass A ((x + t) - t) : ℂ) * psi (x + t)) =
          psi t * ∑ x : G, (realUniformMass A x : ℂ) * psi x
      simp_rw [add_sub_cancel_right, map_add_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    · simp
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, htranslate]
  ring

end

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DifferenceEventProbability
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators Pointwise

variable {N : ℕ}

theorem setAverageTranslate_eq_expect (A : Finset (ZMod N)) (f : ZMod N → ℝ) (x : ZMod N) :
    setAverageTranslate A f x = 𝔼 a ∈ A, f (x - a) := by
  rw [setAverageTranslate, Finset.expect_eq_sum_div_card]

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalizedSiftingAlmostPeriods
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

theorem sqrt_le_exp_of_le_exp_two_mul {beta p : ℝ} (hbeta : beta ≤ Real.exp (2 * p)) :
    Real.sqrt beta ≤ Real.exp p := by
  apply (Real.sqrt_le_left (Real.exp_pos p).le).mpr
  simpa only [two_mul, Real.exp_add, pow_two] using hbeta

theorem chosen_scales_error_le
    {epsilon p d D dim beta : ℝ} (hepsilon : 0 < epsilon) (hd : 0 < d)
    (hD : 0 ≤ D) (hdim0 : 0 ≤ dim) (hdim : dim ≤ D)
    (hbeta : beta ≤ Real.exp (2 * p)) :
    2 * (epsilon / 8) +
      (dim * (epsilon * Real.exp (-p) / (8 * (D + 1))) +
        800 * d * (epsilon * Real.exp (-p) / (6400 * d)) +
        2 * (1 / 2 : ℝ) ^ spectralIterations epsilon p) * Real.sqrt beta ≤ epsilon := by
  have hcancel : Real.exp (-p) * Real.exp p = 1 := by
    rw [← Real.exp_add]
    simp
  have hDpos : 0 < D + 1 := by linarith
  have hnew : dim * (epsilon * Real.exp (-p) / (8 * (D + 1))) * Real.exp p ≤ epsilon / 8 := by
    calc
      _ ≤ (D + 1) * (epsilon * Real.exp (-p) / (8 * (D + 1))) * Real.exp p := by
        gcongr
        linarith
      _ = epsilon / 8 := by
        field_simp
        nlinarith [hcancel]
  have hold : 800 * d * (epsilon * Real.exp (-p) / (6400 * d)) * Real.exp p = epsilon / 8 := by
    field_simp
    nlinarith [hcancel]
  have htail : 2 * (1 / 2 : ℝ) ^ spectralIterations epsilon p * Real.exp p ≤ epsilon / 8 := by
    have h := half_pow_spectralIterations_mul_exp_le (p := p) hepsilon
    linarith
  have hsqrt := sqrt_le_exp_of_le_exp_two_mul hbeta
  have hfactor : 0 ≤ dim * (epsilon * Real.exp (-p) / (8 * (D + 1))) +
      800 * d * (epsilon * Real.exp (-p) / (6400 * d)) +
      2 * (1 / 2 : ℝ) ^ spectralIterations epsilon p := by positivity
  have hbound := mul_le_mul_of_nonneg_left hsqrt hfactor
  nlinarith

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeOutside
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

def outsideAssignment (K : Finset ι) (base : ∀ i, Value i)
    (x : ∀ i : {i // i ∉ K}, Value i.val) : ∀ i, Value i :=
  fun i => if h : i ∈ K then base i else x ⟨i, h⟩

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeRelabel
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v w

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v} {Other : ι → Type w}

def relabelAssignment (e : ∀ i, Value i ≃ Other i) (x : ∀ i, Value i) : ∀ i, Other i :=
  fun i => e i (x i)

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CircleResiduePartition
namespace OAI

section

namespace Erdos3.CircleFourier

open scoped NNReal

theorem one_le_mul_dist_toAddCircle {q : ℕ} [NeZero q] {j k : ZMod q} (hjk : j ≠ k) :
    1 ≤ (q : ℝ) * dist (ZMod.toAddCircle j) (ZMod.toAddCircle k) := by
  let z := j - k
  have hz : z ≠ 0 := sub_ne_zero.mpr hjk
  have hzval : 0 < z.val := Nat.pos_of_ne_zero (fun h => hz ((ZMod.val_eq_zero z).mp h))
  have hzlt := z.val_lt
  have hmin : 1 ≤ min z.val (q - z.val) := le_min hzval (by omega)
  have hdist : dist (ZMod.toAddCircle j) (ZMod.toAddCircle k) =
      ((min z.val (q - z.val) : ℕ) : ℝ) / q := by
    rw [dist_eq_norm, ← map_sub, ZMod.toAddCircle_apply]
    have hn := AddCircle.norm_div_natCast (p := (1 : ℝ)) (m := z.val) (n := q)
    simpa only [mul_one, one_mul, Nat.mod_eq_of_lt z.val_lt] using hn
  rw [hdist, mul_div_cancel₀ _ (show (q : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne q))]
  exact_mod_cast hmin

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

theorem residue_constraints_iff_lcm {M d : ℕ} {u v c : ℤ}
    (hM : c ≡ u [ZMOD (M : ℤ)]) (hd : c ≡ v [ZMOD (d : ℤ)]) (x : ℤ) :
    (x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ v [ZMOD (d : ℤ)]) ↔
      x ≡ c [ZMOD (Nat.lcm M d : ℤ)] := by
  have hlcm : (M : ℤ).lcm (d : ℤ) = Nat.lcm M d := by simp [Int.lcm_def]
  rw [← hlcm, ← Int.modEq_and_modEq_iff_modEq_lcm]
  exact ⟨fun h => ⟨h.1.trans hM.symm, h.2.trans hd.symm⟩,
    fun h => ⟨h.1.trans hM, h.2.trans hd⟩⟩

theorem exists_integer_coprime_residues {M d : ℕ} (hcop : M.Coprime d) (u v : ℤ) :
    ∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ v [ZMOD (d : ℤ)] := by
  have hbez : (M : ℤ) * Nat.gcdA M d + (d : ℤ) * Nat.gcdB M d = 1 := by
    simpa only [hcop.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab M d).symm
  let c := u * ((d : ℤ) * Nat.gcdB M d) + v * ((M : ℤ) * Nat.gcdA M d)
  refine ⟨c, Int.modEq_iff_dvd.mpr ?_, Int.modEq_iff_dvd.mpr ?_⟩
  · refine ⟨(u - v) * Nat.gcdA M d, ?_⟩
    calc
      u - c = u * ((M : ℤ) * Nat.gcdA M d + (d : ℤ) * Nat.gcdB M d) - c := by rw [hbez, mul_one]
      _ = (M : ℤ) * ((u - v) * Nat.gcdA M d) := by dsimp [c]; ring
  · refine ⟨(v - u) * Nat.gcdB M d, ?_⟩
    calc
      v - c = v * ((M : ℤ) * Nat.gcdA M d + (d : ℤ) * Nat.gcdB M d) - c := by rw [hbez, mul_one]
      _ = (d : ℤ) * ((v - u) * Nat.gcdB M d) := by dsimp [c]; ring

theorem coprime_refinement_preserves_compatibility {M d J : ℕ}
    (hcop : (M * d).Coprime J) (u v w : ℤ) :
    (∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ v [ZMOD (d : ℤ)]) ↔
      ∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ v [ZMOD (d : ℤ)] ∧ c ≡ w [ZMOD (J : ℤ)] := by
  constructor
  · rintro ⟨c, hM, hd⟩
    have hL : (Nat.lcm M d).Coprime J := hcop.of_dvd_left (Nat.lcm_dvd_mul M d)
    obtain ⟨t, ht, htJ⟩ := exists_integer_coprime_residues hL c w
    obtain ⟨htM, htd⟩ := (residue_constraints_iff_lcm hM hd t).mpr ht
    exact ⟨t, htM, htd, htJ⟩
  · rintro ⟨c, hM, hd, _⟩
    exact ⟨c, hM, hd⟩

end Erdos3

end

end OAI
end


