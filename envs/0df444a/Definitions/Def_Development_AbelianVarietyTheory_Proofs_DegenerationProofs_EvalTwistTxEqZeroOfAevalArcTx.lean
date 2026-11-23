-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EvalTwistTxEqZeroOfAevalArcTx
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EvalTwistTxEqZeroOfAevalArcTx
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:46.714521+00:00
-- url     : https://prove2.me/theorems/d42be468-e446-4aa4-af48-647e50a1b8e8
-- title:
--   Eval Twist Tx Eq Zero Of Aeval Arc Tx
-- statement:
--   Definitions and structural lemmas for Eval Twist Tx Eq Zero Of Aeval Arc Tx, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EvalTwistTxEqZeroOfAevalArcTx.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTermsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
namespace GlobalTheory.BddArc
section
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C]
def AbsSumAt (u : C) (f : PowerSeries C) (c : C) : Prop :=
  (Summable fun n => ‖PowerSeries.coeff n f * u ^ n‖) ∧ ∑' n, PowerSeries.coeff n f * u ^ n = c
theorem AbsSumAt.add {u : C} {f g : PowerSeries C} {a b : C} (hf : AbsSumAt u f a) (hg : AbsSumAt u g b) :
    AbsSumAt u (f + g) (a + b) := by
  constructor
  · refine (hf.1.add hg.1).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    rw [map_add, add_mul]
    exact norm_add_le _ _
  · rw [← hf.2, ← hg.2, ← hf.1.of_norm.tsum_add hg.1.of_norm]
    simp only [map_add, add_mul]
open scoped BigOperators in
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C] in
theorem absSumAt_algebraMap (u a : C) :
    _root_.GlobalTheory.BddArc.AbsSumAt u (algebraMap C (PowerSeries C) a) a := by
  have h : (fun n => PowerSeries.coeff n (algebraMap C (PowerSeries C) a) * u ^ n) =
      fun n => if n = 0 then a else 0 := by
    funext n
    rcases n with _ | n <;> simp [PowerSeries.coeff_C]
  refine ⟨?_, ?_⟩
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    rw [congrFun h n, if_neg (by simpa using hn), norm_zero]
  · rw [h]
    simp
open scoped BigOperators in
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C] in
theorem absSumAt_add {u : C} {f g : PowerSeries C} {a b : C}
    (hf : _root_.GlobalTheory.BddArc.AbsSumAt u f a) (hg : _root_.GlobalTheory.BddArc.AbsSumAt u g b) :
    _root_.GlobalTheory.BddArc.AbsSumAt u (f + g) (a + b) := by
  have h : ∀ n, PowerSeries.coeff n (f + g) * u ^ n =
      PowerSeries.coeff n f * u ^ n + PowerSeries.coeff n g * u ^ n := fun n => by
    rw [map_add, add_mul]
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (Summable.add hf.1 hg.1)
    rw [h]
    exact norm_add_le _ _
  · simp_rw [h]
    rw [(hf.1.of_norm).tsum_add hg.1.of_norm, hf.2, hg.2]
open scoped BigOperators in
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C] in
theorem absSumAt_mul {u : C} {f g : PowerSeries C} {a b : C}
    (hf : _root_.GlobalTheory.BddArc.AbsSumAt u f a) (hg : _root_.GlobalTheory.BddArc.AbsSumAt u g b) :
    _root_.GlobalTheory.BddArc.AbsSumAt u (f * g) (a * b) := by
  have h : ∀ n, PowerSeries.coeff n (f * g) * u ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * u ^ kl.1) * (PowerSeries.coeff kl.2 g * u ^ kl.2) := fun n => by
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hkl, pow_add]
    ring
  refine ⟨?_, ?_⟩
  · exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hf.1 hg.1).congr fun n => by rw [h]
  · rw [tsum_congr h, ← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf.1 hg.1, hf.2, hg.2]
open scoped BigOperators in
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C] in
theorem _root_.GlobalTheory.BddArc.AbsSumAt.aeval {u : C} {ι : Type} {f : ι → PowerSeries C} {a : ι → C}
    (h : ∀ i, _root_.GlobalTheory.BddArc.AbsSumAt u (f i) (a i))
    (F : MvPolynomial ι C) :
    _root_.GlobalTheory.BddArc.AbsSumAt u (MvPolynomial.aeval f F) (MvPolynomial.eval a F) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.aeval_C, MvPolynomial.eval_C]
    exact absSumAt_algebraMap u c
  | add p q hp hq =>
    rw [map_add, map_add]
    exact absSumAt_add hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X]
    exact absSumAt_mul hp (h i)
end
end GlobalTheory.BddArc


