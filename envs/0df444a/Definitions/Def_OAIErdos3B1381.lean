-- Prove2me | Definitions.Def_OAIErdos3B1381
-- name    : OAIErdos3B1381
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T04:05:32.52475+00:00
-- url     : https://prove2.me/theorems/dd8a9bbe-82f2-41d7-8d77-060778f4ea20
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1382 of 1394
-- statement:
--   Definitions bundle 1382 of 1394 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1380`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1382 available.
--
--   Modules: `OAI.Erdos3.FiniteProbabilityWeights.complexMean_im`, `OAI.Erdos3.FiniteProbabilityWeights.complexMean_pi_transport`, `OAI.Erdos3.FiniteProbabilityWeights.complexMean_pi_transport_fintype`, `OAI.Erdos3.FiniteProbabilityWeights.pi_uniform_weight`, `OAI.Erdos3.affineProductProfile_compact`, `OAI.Erdos3.affineProductProfile_integrable`, `OAI.Erdos3.allocatedScaleLog_nonneg`, `OAI.Erdos3.coefficientReplacementError_small`, `OAI.Erdos3.fixedPathSlicedGridMeshFloor_lower`, `OAI.Erdos3.fixedPathSlicedGridMeshFloor_pos`, `OAI.Erdos3.fixedPathSlicedGridMesh_of_floor`, `OAI.Erdos3.fixedPathSlicedGridMesh_prefactor`, `OAI.Erdos3.fixedPathSlicedGrid_ratio_le`, `OAI.Erdos3.fixedPathSlicedGrid_sum_ratio_le`, `OAI.Erdos3.forecastJointGridCutoff_div_bound`, `OAI.Erdos3.forecastJointGridCutoff_le_exp`, `OAI.Erdos3.forecastJointGridCutoff_lower`, `OAI.Erdos3.forecastJointGridCutoff_one_le`, `OAI.Erdos3.forecastJointGridCutoff_pos_unconditional`, `OAI.Erdos3.forecastJointGridCutoff_tail_le`, `OAI.Erdos3.forecastJointGridErrorBudget`, `OAI.Erdos3.forecastJointGridError_absorb`, `OAI.Erdos3.forecastJointGridMeshLog_nonneg`, `OAI.Erdos3.forecastJointGridMesh_bounds`, `OAI.Erdos3.forecastJointGridPrefactor_le_exp`, `OAI.Erdos3.forecastModularCharge_exp_bound`, `OAI.Erdos3.integerLongPolynomialOutput_reduce`, `OAI.Erdos3.integerPolynomialCoordinatePMF_active_profile_bound`, `OAI.Erdos3.le_allocatedScaleLog`, `OAI.Erdos3.modularForecastRankConstant_decay`, `OAI.Erdos3.productComplexMean_reindex`, `OAI.Erdos3.rationalOutputDensity_divisor_test`, `OAI.Erdos3.rationalOutputDensity_test`, `OAI.Erdos3.scalarCubeGridBoundaryConstant_pos`, `OAI.Erdos3.scalarCubeRiemannBoundary_le_exp`, `OAI.Erdos3.sigmaFiniteProductMeasure_flatten`, `OAI.Erdos3.tupleResidueReduction_surjective`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1380

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

theorem pi_uniform_weight {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, Nonempty (Ω j)]
    (x : ∀ j, Ω j) :
    (pi (fun j => uniform (Ω j))).weight x = (uniform (∀ j, Ω j)).weight x := by
  simp [pi, uniform, Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalForecastGridTail
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem rationalOutputDensity_test {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    (test : (J → ZMod N) → ℂ) :
    (𝔼 b, (rationalOutputDensity p Y N b : ℂ) * test b) =
      p.complexMean (fun x => test (fun j => (Y x j : ZMod N))) := by
  let F := fun x j => (Y x j : ZMod N)
  have hmass (b) : finiteImageMass p F b = (p.fiberLaw F).weight b := by
    unfold finiteImageMass FiniteProbabilityWeights.fiberLaw FiniteProbabilityWeights.fiberMean
    congr 1
    funext x
    split_ifs <;> rfl
  have hcard : (Fintype.card (J → ZMod N) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [Fintype.expect_eq_sum_div_card]
  simp only [rationalOutputDensity, Complex.ofReal_mul, Complex.ofReal_natCast,
    mul_assoc, ← Finset.mul_sum]
  rw [mul_div_cancel_left₀ _ hcard]
  change (∑ b, (finiteImageMass p F b : ℂ) * test b) = _
  simp_rw [hmass]
  exact p.fiberLaw_complexMean F test

theorem rationalOutputDensity_divisor_test {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ)
    {q N : ℕ} [NeZero N] [NeZero q] (hq : q ∣ N)
    (test : (J → ZMod q) → ℂ) :
    (𝔼 b : J → ZMod N, (rationalOutputDensity p Y N b : ℂ) *
      test (fun j => ZMod.castHom hq (ZMod q) (b j))) =
      p.complexMean (fun x => test (fun j => (Y x j : ZMod q))) := by
  simpa only [map_intCast] using rationalOutputDensity_test p Y N
    (fun b => test (fun j => ZMod.castHom hq (ZMod q) (b j)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {Ω Aux J V : Type*} [Fintype Ω] [Fintype Aux] [Fintype J] [Fintype V]
variable (p : FiniteProbabilityWeights Ω) (Y : Ω → (Aux ⊕ J) → ℤ)
variable {N : ℕ} [NeZero N] (qW : ℕ) (hW : qW ∣ N)
variable (aux : Aux → ZMod N)
variable (g : ((V → ℝ) × (J → ℝ)) → ℝ)
variable (φ : (J → ZMod qW) → ((V → ℝ) × (J → ℝ)) → ℂ)
variable (hg : Continuous g) (hφ : ∀ b, Continuous (φ b))
variable (R : ℝ) (hsupport : ∀ x, R < ‖x‖ → g x = 0)


include hg hφ hsupport

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {Ω O : Type*} [Fintype Ω] [Fintype O] [DecidableEq O]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RationalPolynomialForecastBoxError
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem tupleResidueReduction_surjective {A : Type*} {q N : ℕ} (hq : q ∣ N) :
    Function.Surjective (tupleResidueReduction (A := A) hq) := by
  intro y
  choose x hx using fun a => ZMod.castHom_surjective hq (y a)
  exact ⟨x, funext hx⟩

theorem integerLongPolynomialOutput_reduce {A I J : Type*}
    (poly : J → MvPolynomial (A ⊕ I) ℤ) (inactive : I → ℤ)
    {q N : ℕ} [NeZero N] (hq : q ∣ N) (t : A → ZMod N) :
    (fun j => (integerLongPolynomialOutput poly inactive N t j : ZMod q)) =
      fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim (tupleResidueReduction hq t) (fun i => (inactive i : ZMod q))) (poly j) := by
  funext j
  rw [integerLongPolynomialOutput, integerPolynomial_eval_residue]
  congr 1
  funext v
  cases v with
  | inl a =>
    change (((t a).val : ℤ) : ZMod q) = ZMod.castHom hq (ZMod q) (t a)
    have h := congrArg (ZMod.castHom hq (ZMod q)) (ZMod.natCast_zmod_val (t a))
    simpa only [map_natCast, Int.cast_natCast] using h
  | inr i => rfl

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastModularCutoff
namespace OAI

section

namespace Erdos3

theorem forecastJointGridPrefactor_le_exp (dout dj dc d : ℕ)
    (hdout : dout ≤ d) (hdj : dj ≤ d) (hdc : dc ≤ d)
    {P E T D L C K : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hT : 1 ≤ T) (hTexp : T ≤ Real.exp (P + E + 5))
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hDexp : D ≤ Real.exp P) (hLexp : L ≤ Real.exp P)
    (hCexp : C ≤ Real.exp P) (hKexp : K ≤ Real.exp P) :
    (T ^ (dout + 1) * (2 * 8 ^ dj * (L + C * K)) +
      (D / T) * (8 ^ dj * L)) * 6 ^ dc ≤
      Real.exp (((d : ℝ) + 1) * (P + E + 5) + 6 * d + 2 * P + 4) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have h6 : (6 : ℝ) ≤ Real.exp 3 := (by norm_num : (6 : ℝ) ≤ 8).trans h8
  have hR : 0 ≤ P + E + 5 := by linarith
  have hdoutR : (dout : ℝ) ≤ d := by exact_mod_cast hdout
  have hdjR : (dj : ℝ) ≤ d := by exact_mod_cast hdj
  have hdcR : (dc : ℝ) ≤ d := by exact_mod_cast hdc
  have hTp : T ^ (dout + 1) ≤ Real.exp (((d : ℝ) + 1) * (P + E + 5)) := by
    calc
      _ ≤ (Real.exp (P + E + 5)) ^ (dout + 1) :=
        pow_le_pow_left₀ (by linarith) hTexp _
      _ = Real.exp (((dout : ℝ) + 1) * (P + E + 5)) := by
        rw [← Real.exp_nat_mul]
        simp
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hR)
  have hjp : (8 : ℝ) ^ dj ≤ Real.exp (3 * (d : ℝ)) := by
    calc
      _ ≤ (Real.exp 3) ^ dj := pow_le_pow_left₀ (by norm_num) h8 _
      _ = Real.exp ((dj : ℝ) * 3) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hcp : (6 : ℝ) ^ dc ≤ Real.exp (3 * (d : ℝ)) := by
    calc
      _ ≤ (Real.exp 3) ^ dc := pow_le_pow_left₀ (by norm_num) h6 _
      _ = Real.exp ((dc : ℝ) * 3) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hsum : L + C * K ≤ Real.exp (2 * P + 1) := by
    have hCK : C * K ≤ Real.exp (2 * P) := by
      calc
        _ ≤ Real.exp P * Real.exp P := mul_le_mul hCexp hKexp hK (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hL2 := hLexp.trans (Real.exp_le_exp.mpr (show P ≤ 2 * P by linarith))
    calc
      _ ≤ 2 * Real.exp (2 * P) := by linarith
      _ ≤ Real.exp 1 * Real.exp (2 * P) := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hDT : D / T ≤ Real.exp P :=
    (div_le_self hD hT).trans hDexp
  let H := ((d : ℝ) + 1) * (P + E + 5) + 6 * d + 2 * P + 2
  have hfirst : T ^ (dout + 1) * (2 * 8 ^ dj * (L + C * K)) * 6 ^ dc ≤
      Real.exp H := by
    calc
      _ ≤ Real.exp (((d : ℝ) + 1) * (P + E + 5)) *
          (Real.exp 1 * Real.exp (3 * d) * Real.exp (2 * P + 1)) * Real.exp (3 * d) := by
        gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; dsimp [H]; ring
  have hsecond : (D / T) * (8 ^ dj * L) * 6 ^ dc ≤ Real.exp H := by
    calc
      _ ≤ Real.exp P * (Real.exp (3 * d) * Real.exp P) * Real.exp (3 * d) := by
        gcongr
      _ = Real.exp (6 * (d : ℝ) + 2 * P) := by
        simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hp : 0 ≤ ((d : ℝ) + 1) * (P + E + 5) := mul_nonneg (by positivity) hR
        dsimp [H]
        linarith)
  rw [add_mul]
  calc
    _ ≤ 2 * Real.exp H := by linarith
    _ ≤ Real.exp 1 * Real.exp H := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = Real.exp (H + 1) := by rw [← Real.exp_add, add_comm]
    _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [H]; linarith)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem forecastJointGridCutoff_lower (P E : ℝ) :
    Real.exp (P + E + 4) ≤ (forecastJointGridCutoff P E : ℝ) := Nat.le_ceil _

theorem forecastJointGridCutoff_pos_unconditional (P E : ℝ) : 0 < forecastJointGridCutoff P E := by
  exact_mod_cast (Real.exp_pos (P + E + 4)).trans_le (forecastJointGridCutoff_lower P E)

theorem forecastJointGridCutoff_one_le (P E : ℝ) : 1 ≤ forecastJointGridCutoff P E :=
  forecastJointGridCutoff_pos_unconditional P E

theorem forecastJointGridCutoff_le_exp {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    (forecastJointGridCutoff P E : ℝ) ≤ Real.exp (P + E + 5) := by
  calc
    _ ≤ Real.exp (P + E + 4) + 1 := (Nat.ceil_lt_add_one (Real.exp_nonneg _)).le
    _ = 1 + Real.exp (P + E + 4) := add_comm _ _
    _ ≤ Real.exp ((P + E + 4) + 1) :=
      one_add_le_exp_succ (by linarith) le_rfl
    _ = _ := by congr 1; ring

theorem forecastJointGridCutoff_div_bound {P E D : ℝ} (hD : D ≤ Real.exp P) :
    D / forecastJointGridCutoff P E ≤ Real.exp (-(E + 4)) := by
  have hpos : (0 : ℝ) < forecastJointGridCutoff P E := by
    exact_mod_cast forecastJointGridCutoff_pos_unconditional P E
  apply (div_le_iff₀ hpos).mpr
  calc
    D ≤ Real.exp P := hD
    _ = Real.exp (-(E + 4)) * Real.exp (P + E + 4) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (forecastJointGridCutoff_lower P E) (Real.exp_nonneg _)

theorem forecastJointGridCutoff_tail_le {P E D : ℝ} (_hP : 0 ≤ P) (_hE : 0 ≤ E)
    (hD : D ≤ Real.exp P) :
    D / forecastJointGridCutoff P E ≤ Real.exp (-(E + 4)) :=
  forecastJointGridCutoff_div_bound hD

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem modularForecastRankConstant_decay (s D : ℕ) :
    modularRankDecayExponent s (modularForecastRankConstant s D : ℝ) = (D + 2 : ℕ) := by
  unfold modularRankDecayExponent modularForecastRankConstant
  push_cast
  have htwo : (2 : ℝ) ^ s ≠ 0 := by positivity
  have hfac : (s.factorial : ℝ) ≠ 0 := by positivity
  field_simp

end Erdos3

end

section

namespace Erdos3

theorem forecastJointGridMeshLog_nonneg (d : ℕ) {P E : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) : 0 ≤ forecastJointGridMeshLog d P E := by
  unfold forecastJointGridMeshLog
  positivity

theorem forecastJointGridMesh_bounds (d : ℕ) {P E : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 < forecastJointGridMesh d P E ∧ forecastJointGridMesh d P E ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr
    (forecastJointGridMeshLog_nonneg d hP hE))⟩

theorem forecastJointGridError_absorb
    (dout dj dc d cutoff : ℕ) (hdout : dout ≤ d) (hdj : dj ≤ d) (hdc : dc ≤ d)
    {P E D L C K δ : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hcutoff : 1 ≤ cutoff) (hTexp : (cutoff : ℝ) ≤ Real.exp (P + E + 5))
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hDexp : D ≤ Real.exp P) (hLexp : L ≤ Real.exp P)
    (hCexp : C ≤ Real.exp P) (hKexp : K ≤ Real.exp P)
    (htail : D / cutoff ≤ Real.exp (-(E + 4)))
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ forecastJointGridMesh d P E) :
    forecastJointGridError dout dj dc cutoff D L C K δ ≤ Real.exp (-E) := by
  have hpref := forecastJointGridPrefactor_le_exp dout dj dc d hdout hdj hdc
    hP hE (by exact_mod_cast hcutoff) hTexp hD hL hC hK hDexp hLexp hCexp hKexp
  let H := ((d : ℝ) + 1) * (P + E + 5) + 6 * d + 2 * P + 4
  have hmesh : Real.exp H * δ ≤ Real.exp (-(E + 4)) := by
    calc
      _ ≤ Real.exp H * forecastJointGridMesh d P E :=
        mul_le_mul_of_nonneg_left hδsmall (Real.exp_nonneg _)
      _ = _ := by
        unfold forecastJointGridMesh forecastJointGridMeshLog H
        rw [← Real.exp_add]
        congr 1
        ring
  have hpre : forecastJointGridError dout dj dc cutoff D L C K δ ≤
      Real.exp H * δ + 2 * (D / cutoff) := by
    have hh := mul_le_mul_of_nonneg_right hpref hδ
    unfold forecastJointGridError
    dsimp only [H]
    nlinarith only [hh]
  have htotal : forecastJointGridError dout dj dc cutoff D L C K δ ≤
      3 * Real.exp (-(E + 4)) := by linarith only [hpre, hmesh, htail]
  have hthree : (3 : ℝ) ≤ Real.exp 4 := by linarith only [Real.add_one_le_exp (4 : ℝ)]
  refine htotal.trans ?_
  calc
    _ ≤ Real.exp 4 * Real.exp (-(E + 4)) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem forecastJointGridErrorBudget (d : ℕ) {P E : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) :
    1 ≤ forecastJointGridCutoff P E ∧
    (forecastJointGridCutoff P E : ℝ) ≤ Real.exp (P + E + 5) ∧
    0 < forecastJointGridMesh d P E ∧ forecastJointGridMesh d P E ≤ 1 ∧
    ∀ {dout dj dc : ℕ}, dout ≤ d → dj ≤ d → dc ≤ d →
    ∀ {D L C K δ : ℝ}, 0 ≤ D → 0 ≤ L → 0 ≤ C → 0 ≤ K →
    D ≤ Real.exp P → L ≤ Real.exp P → C ≤ Real.exp P → K ≤ Real.exp P →
    0 ≤ δ → δ ≤ forecastJointGridMesh d P E →
    forecastJointGridError dout dj dc (forecastJointGridCutoff P E) D L C K δ ≤
      Real.exp (-E) := by
  have hm := forecastJointGridMesh_bounds d hP hE
  refine ⟨forecastJointGridCutoff_one_le P E, forecastJointGridCutoff_le_exp hP hE,
    hm.1, hm.2, ?_⟩
  intro dout dj dc hdout hdj hdc D L C K δ hD hL hC hK hDexp hLexp hCexp hKexp hδ hδsmall
  exact forecastJointGridError_absorb dout dj dc d (forecastJointGridCutoff P E)
    hdout hdj hdc hP hE (forecastJointGridCutoff_one_le P E)
    (forecastJointGridCutoff_le_exp hP hE) hD hL hC hK hDexp hLexp hCexp hKexp
    (forecastJointGridCutoff_tail_le hP hE hDexp) hδ hδsmall

end Erdos3

end

section

namespace Erdos3

theorem forecastModularCharge_exp_bound (m D Rbad Qpres : ℕ)
    {Pbad Ppres : ℝ} (hR : (Rbad : ℝ) ≤ Real.exp Pbad)
    (hQ : (Qpres : ℝ) ≤ Real.exp Ppres) :
    ((Rbad * Qpres : ℕ) : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m D : ℝ) *
        modularRankChargeFactor m) ≤
      Real.exp ((Pbad + Ppres) * ((D + 2 : ℕ) : ℝ) * modularRankChargeFactor m) := by
  rw [modularForecastRankConstant_decay]
  have hbase : ((Rbad * Qpres : ℕ) : ℝ) ≤ Real.exp (Pbad + Ppres) := by
    rw [Nat.cast_mul, Real.exp_add]
    exact mul_le_mul hR hQ (Nat.cast_nonneg _) (Real.exp_nonneg _)
  calc
    _ ≤ (Real.exp (Pbad + Ppres)) ^
        (((D + 2 : ℕ) : ℝ) * modularRankChargeFactor m) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hbase (by positivity)
    _ = _ := by rw [← Real.exp_mul, mul_assoc]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPathSlicedGridMeshBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem fixedPathSlicedGrid_ratio_le {S H q : ℕ} {cost : ℝ}
    (hS : 0 < S) (hH : Real.exp (-cost) * S ≤ (H : ℝ)) :
    (q : ℝ) / H ≤ Real.exp cost * ((q : ℝ) / S) := by
  have hs : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  calc
    _ ≤ (q : ℝ) / (Real.exp (-cost) * S) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos (Real.exp_pos _) hs) hH
    _ = _ := by rw [Real.exp_neg]; field_simp

theorem fixedPathSlicedGrid_sum_ratio_le {Input : Type*} [Fintype Input]
    {D cost : ℝ} {S q : ℕ} (H : Input → ℕ)
    (hcard : (Fintype.card Input : ℝ) ≤ D) (hS : 0 < S)
    (hH : ∀ i, Real.exp (-cost) * S ≤ (H i : ℝ)) :
    (∑ i, (q : ℝ) / H i) ≤ D * Real.exp cost * ((q : ℝ) / S) := by
  calc
    _ ≤ ∑ _ : Input, Real.exp cost * ((q : ℝ) / S) :=
      Finset.sum_le_sum (fun i _ => fixedPathSlicedGrid_ratio_le hS (hH i))
    _ = (Fintype.card Input : ℝ) * (Real.exp cost * ((q : ℝ) / S)) := by simp
    _ ≤ D * (Real.exp cost * ((q : ℝ) / S)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem fixedPathSlicedGridMeshFloor_lower (D C V cost E : ℝ) :
    Real.exp (fixedPathSlicedGridMeshLog D C V cost E) ≤
      (fixedPathSlicedGridMeshFloor D C V cost E : ℝ) := Nat.le_ceil _

theorem fixedPathSlicedGridMeshFloor_pos (D C V cost E : ℝ) :
    0 < fixedPathSlicedGridMeshFloor D C V cost E := by
  exact_mod_cast (Real.exp_pos _).trans_le (fixedPathSlicedGridMeshFloor_lower D C V cost E)

theorem fixedPathSlicedGridMesh_prefactor {D C V cost E : ℝ} {q S : ℕ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : fixedPathSlicedGridMeshFloor D C V cost E ≤ S) :
    (D + C + 8) * (Real.exp cost * ((q : ℝ) / S)) ≤ Real.exp (-(E + 2)) := by
  have hp : (0 : ℝ) < D + C + 8 := by linarith
  have hS := (fixedPathSlicedGridMeshFloor_lower D C V cost E).trans
    (show (fixedPathSlicedGridMeshFloor D C V cost E : ℝ) ≤ S by exact_mod_cast hfloor)
  have hs : (0 : ℝ) < S := (Real.exp_pos _).trans_le hS
  have hnum : (D + C + 8) * Real.exp cost * (q : ℝ) ≤
      Real.exp (Real.log (D + C + 8) + V + cost) := by
    calc
      _ ≤ (D + C + 8) * Real.exp cost * Real.exp V :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg hp.le (Real.exp_nonneg _))
      _ = _ := by rw [Real.exp_add, Real.exp_add, Real.exp_log hp]; ring
  rw [← mul_div_assoc, ← mul_div_assoc]
  apply (div_le_iff₀ hs).mpr
  calc
    _ ≤ Real.exp (Real.log (D + C + 8) + V + cost) := by simpa only [mul_assoc] using hnum
    _ = Real.exp (-(E + 2)) * Real.exp (fixedPathSlicedGridMeshLog D C V cost E) := by
      rw [← Real.exp_add]
      congr 1
      unfold fixedPathSlicedGridMeshLog
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hS (Real.exp_nonneg _)

theorem fixedPathSlicedGridMesh_of_floor {D C V cost E : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hE : 0 ≤ E)
    {Input : Type*} [Fintype Input] (H : Input → ℕ)
    (hcard : (Fintype.card Input : ℝ) ≤ D) {q S : ℕ}
    (hq0 : 0 < q) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : fixedPathSlicedGridMeshFloor D C V cost E ≤ S)
    (hH : ∀ i, Real.exp (-cost) * S ≤ (H i : ℝ))
    (mesh : Input → ℝ) (hmesh : ∀ i, mesh i ≤ 2 * Real.exp cost / S) :
    (∑ i, (q : ℝ) / H i) ≤ Real.exp (-E) ∧
      (∀ i, C * ((q : ℝ) / H i) ≤ Real.exp (-E)) ∧
      (∀ i, mesh i ≤ Real.exp (-E)) ∧
      ∀ i, 2 ≤ H i ∧ q ≤ H i ∧
        scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H i) < 1 := by
  have hS := (fixedPathSlicedGridMeshFloor_pos D C V cost E).trans_le hfloor
  have hSr : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  let r := Real.exp cost * ((q : ℝ) / S)
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hbound := fixedPathSlicedGridMesh_prefactor hD hC hq hfloor
  have hsmall : Real.exp (-(E + 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he : Real.exp (-(E + 2)) ≤ Real.exp (-E) := Real.exp_le_exp.mpr (by linarith)
  have hmajor {a : ℝ} (ha : a ≤ D + C + 8) : a * r ≤ Real.exp (-(E + 2)) :=
    (mul_le_mul_of_nonneg_right ha hr).trans hbound
  have hratio (i : Input) : (q : ℝ) / H i ≤ r := fixedPathSlicedGrid_ratio_le hS (hH i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsum := fixedPathSlicedGrid_sum_ratio_le (q := q) H hcard hS hH
    have hsummajor : D * Real.exp cost * ((q : ℝ) / S) ≤ Real.exp (-(E + 2)) := by
      simpa only [mul_assoc, r] using hmajor (show D ≤ D + C + 8 by linarith)
    exact hsum.trans (hsummajor.trans he)
  · intro i
    exact ((mul_le_mul_of_nonneg_left (hratio i) hC).trans
      (hmajor (show C ≤ D + C + 8 by linarith))).trans he
  · intro i
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
    have htwo : 2 * Real.exp cost / S ≤ 2 * r := by
      dsimp only [r]
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (Real.exp_nonneg _) hq1) hSr.le
    exact ((hmesh i).trans htwo).trans
      ((hmajor (show (2 : ℝ) ≤ D + C + 8 by linarith)).trans he)
  · intro i
    have hHi : (0 : ℝ) < H i := (mul_pos (Real.exp_pos _) hSr).trans_le (hH i)
    have hfour : 4 * ((q : ℝ) / H i) < 1 :=
      ((mul_le_mul_of_nonneg_left (hratio i) (by norm_num : (0 : ℝ) ≤ 4)).trans
        (hmajor (show (4 : ℝ) ≤ D + C + 8 by linarith))).trans_lt hsmall
    have hratio1 : (q : ℝ) / H i < 1 := by
      have hn : (0 : ℝ) ≤ (q : ℝ) / H i := by positivity
      linarith
    have hqH : q < H i := Nat.cast_lt.mp ((div_lt_one hHi).mp hratio1)
    refine ⟨by omega, hqH.le, ?_⟩
    have hconst : scalarCubeGridBoundaryConstant Empty = 4 := by
      norm_num [scalarCubeGridBoundaryConstant]
    rwa [hconst]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

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

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem FiniteProbabilityWeights.complexMean_im {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (F : X → ℂ) :
    (p.complexMean F).im = p.mean (fun x => (F x).im) := by
  simp [complexMean, mean, Complex.mul_im]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

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

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubeProductRiemannBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem scalarCubeGridBoundaryConstant_pos (I : Type*) [Fintype I] :
    0 < scalarCubeGridBoundaryConstant I := by
  unfold scalarCubeGridBoundaryConstant
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_finset]
  positivity

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem scalarCubeRiemannBoundary_le_exp (α : Type*) [Fintype α] [DecidableEq α]
    {D : ℝ} (_hD : 0 ≤ D) (hcard : (Fintype.card α : ℝ) ≤ D) :
    scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) ≤
      Real.exp (scalarCubeRiemannLog D) := by
  let q := Fintype.card α
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have h2q : (2 : ℝ) ^ q ≤ Real.exp q := by
    simpa only [← Real.exp_nat_mul, mul_one] using pow_le_pow_left₀ (by norm_num) h2 q
  have h4q : (4 : ℝ) ^ q ≤ Real.exp (2 * q) := by
    simpa only [← Real.exp_nat_mul, mul_comm] using pow_le_pow_left₀ (by norm_num) h4 q
  have hb : scalarCubeGridBoundaryConstant α ≤ Real.exp (4 * q + 2) := by
    simp only [scalarCubeGridBoundaryConstant, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_finset, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    calc
      _ ≤ (Real.exp 1 * Real.exp q) * Real.exp (2 * q) * Real.exp 1 * Real.exp q := by
        gcongr
        exact Real.add_one_le_exp _
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  calc
    _ = scalarCubeGridBoundaryConstant α * scalarCubeDomainDensity α := by
      rw [div_eq_mul_inv]; rfl
    _ ≤ Real.exp (4 * q + 2) * Real.exp (((q : ℝ) + 1) ^ 2) :=
      mul_le_mul hb (scalarCubeDomainDensity_le_exp α)
        (scalarCubeDomainDensity_pos α).le (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp only [scalarCubeRiemannLog]
      have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
      change (q : ℝ) ≤ D at hcard
      nlinarith [sq_nonneg (D - q)]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

theorem affineProductProfile_compact {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : HasCompactSupport (affineProductProfile c w) :=
  tensorCutoffWeight_compact (fun i => affineProbabilityProfile (c i) (w i))
    (fun i => affineProbabilityProfile_compact (c i) (hw i))

theorem affineProductProfile_integrable {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : Integrable (affineProductProfile c w) :=
  (affineProductProfile_contDiff c w).continuous.integrable_of_hasCompactSupport
    (affineProductProfile_compact c w hw)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveShortLogBounds
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

theorem coefficientReplacementError_small {D L target supportLog amplitude ε : ℝ}
    (hD : 0 ≤ D) (hL : 0 ≤ L) (htarget : 0 ≤ target)
    (hSupport : supportLog ≤ L) (ha0 : 0 ≤ amplitude) (ha : amplitude ≤ Real.exp L)
    (output axes : ℕ) (ho : (output : ℝ) ≤ D) (hn : (axes : ℝ) ≤ D)
    (hε0 : 0 ≤ ε)
    (hε : ε ≤ Real.exp (-(target + coefficientReplacementErrorLog D L))) :
    (2 * Real.exp supportLog + 1) ^ output *
      (axes * ε * (1 + amplitude + ε) ^ axes) ≤ Real.exp (-target) := by
  let Q := coefficientReplacementErrorLog D L
  have hQ : 0 ≤ Q := by dsimp [Q, coefficientReplacementErrorLog]; positivity
  have he1 : ε ≤ 1 := hε.trans (Real.exp_le_one_iff.mpr (by change -(target + Q) ≤ 0; linarith))
  have heL : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hbase : 2 * Real.exp supportLog + 1 ≤ Real.exp (L + 3) := by
    calc
      _ ≤ 3 * Real.exp L := by linarith [Real.exp_le_exp.mpr hSupport]
      _ ≤ Real.exp L * Real.exp 3 := by nlinarith [Real.exp_pos L]
      _ = _ := (Real.exp_add _ _).symm
  have hbase' : 1 + amplitude + ε ≤ Real.exp (L + 3) := by
    calc
      _ ≤ 3 * Real.exp L := by linarith only [ha, he1, heL]
      _ ≤ Real.exp L * Real.exp 3 := by nlinarith [Real.exp_pos L]
      _ = _ := (Real.exp_add _ _).symm
  have ho' := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ 2 * Real.exp supportLog + 1)
    hbase (by positivity : 0 ≤ L + 3) output ho
  have hn' := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ 1 + amplitude + ε)
    hbase' (by positivity : 0 ≤ L + 3) axes hn
  have haxes : (axes : ℝ) ≤ Real.exp D := hn.trans (by linarith [Real.add_one_le_exp D])
  have hcost : D * (L + 3) + D + D * (L + 3) ≤ Q := by
    dsimp [Q, coefficientReplacementErrorLog]
    nlinarith [mul_nonneg hD hL]
  have hcoeff : (2 * Real.exp supportLog + 1) ^ output * axes * (1 + amplitude + ε) ^ axes ≤ Real.exp Q := by
    calc
      _ ≤ Real.exp (D * (L + 3)) * Real.exp D * Real.exp (D * (L + 3)) := by gcongr
      _ ≤ _ := by rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr hcost
  calc
    _ = ((2 * Real.exp supportLog + 1) ^ output * axes * (1 + amplitude + ε) ^ axes) * ε := by ring
    _ ≤ Real.exp Q * Real.exp (-(target + Q)) :=
      (mul_le_mul_of_nonneg_right hcoeff hε0).trans (mul_le_mul_of_nonneg_left hε (Real.exp_pos _).le)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
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

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)


end Erdos3

end

section

namespace Erdos3

variable {J V : Type*}
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)

theorem integerPolynomialCoordinatePMF_active_profile_bound
    (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hprincipal : ∀ j ∈ P,
      monomialScale T (e j) = (integerAxisSideLength h K L γ : ℝ) ^ h)
    (hactive : L ^ h < K) (j : J) {k : ℤ}
    (hk : k ∈ (integerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
      ρ γ ε hρ hγ hε hgap hεL j).support) :
    |(k : ℝ) / K * monomialScale T (e j) - coefficientProfileCenter P γ j| ≤
      coefficientProfileWidth P j₀ ρ γ ε j := by
  classical
  by_cases hj : j = j₀
  · subst j
    simp only [integerPolynomialCoordinatePMF, ↓reduceIte] at hk
    have hb := constantIntegerPMF_support K ρ (by exact_mod_cast hK) hρ hk
    simp only [coefficientProfileCenter, coefficientProfileWidth, hj₀, ↓reduceIte,
      he₀, monomialScale_zero, mul_one, sub_zero]
    linarith
  · by_cases hp : j ∈ P
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte] at hk
      have hb := integerAxisPrincipalPMF_active hh hK hL hγ hgap hactive hk
      have hscale : monomialScale T (e j) = (L : ℝ) ^ h := by
        rw [hprincipal j hp]
        simp only [integerAxisSideLength, hactive, ↓reduceIte]
      simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hp, ↓reduceIte, hscale]
      have heq : (k : ℝ) / K * (L : ℝ) ^ h = (L : ℝ) ^ h * (k : ℝ) / K := by ring
      rw [heq, abs_le]
      constructor <;> linarith [hb.1, hb.2]
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte] at hk
      have hb := integerAxisTailPMF_support T hT hK hL hTL hε hεL (e j) (he j) hk
      simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hp, ↓reduceIte,
        sub_zero, abs_mul, abs_of_pos (monomialScale_pos T hT (e j))]
      linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMeanPullback
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productComplexMean_reindex (μ : ∀ i, FiniteProbabilityWeights (X i))
    (e : J ≃ I) (g : (∀ j, X (e j)) → ℂ) :
    (FiniteProbabilityWeights.pi μ).complexMean (fun x => g (fun j => x (e j))) =
      (FiniteProbabilityWeights.pi (fun j => μ (e j))).complexMean g := by
  classical
  apply Fintype.sum_equiv (Equiv.piCongrLeft X e).symm
  intro x
  change ((∏ i, (μ i).weight (x i) : ℝ) : ℂ) * g (fun j => x (e j)) =
    ((∏ j, (μ (e j)).weight (x (e j)) : ℝ) : ℂ) * g (fun j => x (e j))
  rw [e.prod_comp (fun i => (μ i).weight (x i))]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [DecidableEq I] {X : I → Type*}

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [DecidableEq I] [Fintype J] {X : I → Type*}

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedSliceFamilyLaw
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem complexMean_pi_transport {n : ℕ} {X Y Z : Fin n → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (q : ∀ i, FiniteProbabilityWeights (Y i))
    (F : ∀ i, X i → Z i) (G : ∀ i, Y i → Z i)
    (h : ∀ i (f : Z i → ℂ), (p i).complexMean (fun x => f (F i x)) =
      (q i).complexMean (fun y => f (G i y))) (f : (∀ i, Z i) → ℂ) :
    (pi p).complexMean (fun x => f (fun i => F i (x i))) =
      (pi q).complexMean (fun y => f (fun i => G i (y i))) := by
  induction n with
  | zero =>
      rw [complexMean_empty_tuple, complexMean_empty_tuple]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      rw [complexMean_pi_fin_cons, complexMean_pi_fin_cons]
      simp only [dependent_fin_cons_map]
      calc
        _ = (p 0).complexMean (fun a => (pi (fun i : Fin n => q i.succ)).complexMean
            (fun y => f (Fin.cons (F 0 a) (fun i => G i.succ (y i))))) := by
          congr 1
          funext a
          exact ih (fun i => p i.succ) (fun i => q i.succ)
            (fun i => F i.succ) (fun i => G i.succ) (fun i => h i.succ) (fun z => f (Fin.cons (F 0 a) z))
        _ = _ := h 0 (fun z => (pi (fun i : Fin n => q i.succ)).complexMean
          (fun y => f (Fin.cons z (fun i => G i.succ (y i)))))

theorem complexMean_pi_transport_fintype {I : Type*} [Fintype I] [DecidableEq I]
    {X Y Z : I → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (q : ∀ i, FiniteProbabilityWeights (Y i))
    (F : ∀ i, X i → Z i) (G : ∀ i, Y i → Z i)
    (h : ∀ i (f : Z i → ℂ), (p i).complexMean (fun x => f (F i x)) =
      (q i).complexMean (fun y => f (G i y))) (f : (∀ i, Z i) → ℂ) :
    (pi p).complexMean (fun x => f (fun i => F i (x i))) =
      (pi q).complexMean (fun y => f (fun i => G i (y i))) := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let f' : (∀ j, Z (e j)) → ℂ := fun z => f ((Equiv.piCongrLeft Z e) z)
  have hp := productComplexMean_reindex p e
    (fun x => f' (fun j => F (e j) (x j)))
  have hq := productComplexMean_reindex q e
    (fun x => f' (fun j => G (e j) (x j)))
  have ht := complexMean_pi_transport (fun j => p (e j)) (fun j => q (e j))
    (fun j => F (e j)) (fun j => G (e j)) (fun j => h (e j)) f'
  have hcomp (z : ∀ i, Z i) : f' (fun j => z (e j)) = f z := by
    change f ((Equiv.piCongrLeft Z e) ((Equiv.piCongrLeft Z e).symm z)) = f z
    rw [Equiv.apply_symm_apply]
  calc
    _ = (pi p).complexMean (fun x => f' (fun j => F (e j) (x (e j)))) := by
      congr 1
      funext x
      exact (hcomp (fun i => F i (x i))).symm
    _ = (pi q).complexMean (fun x => f' (fun j => G (e j) (x (e j)))) :=
      hp.trans (ht.trans hq.symm)
    _ = _ := by
      congr 1
      funext x
      exact hcomp (fun i => G i (x i))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D]
variable [Fintype α] [DecidableEq α] [IsEmpty α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)

end Erdos3

end

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

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (Pz : Fin n → Finset J) (j₀ : J) (h L s : ℕ) (hh : 0 < h) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 1 ≤ T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : ∀ i, L ^ h < basisAxisScale b i →
  (principalSamplingGapRatio (principalProfileSize R (Pz i).card) * L) ^ h ≤ basisAxisScale b i)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)


variable (Pc : I → Finset J)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (Pz : Fin n → Finset J) (j₀ : J) (h L s : ℕ) (hh : 0 < h) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 1 ≤ T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : ∀ i, L ^ h < basisAxisScale b i →
  (principalSamplingGapRatio (principalProfileSize R (Pz i).card) * L) ^ h ≤ basisAxisScale b i)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)
variable (Pc : I → Finset J)


end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem allocatedScaleLog_nonneg {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedScaleLog P := by
  unfold allocatedScaleLog
  positivity

theorem le_allocatedScaleLog {P : ℝ} (hP : 0 ≤ P) : P ≤ allocatedScaleLog P := by
  have h : 0 ≤ P^2*(5*P+49) := by positivity
  unfold allocatedScaleLog
  nlinarith

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SigmaFiniteProductMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem sigmaFiniteProductMeasure_flatten {D : Type*} [Fintype D] {I : D → Type*}
    [∀ d, Fintype (I d)] {X : (Σ d, I d) → Type*}
    [∀ s, MeasurableSpace (X s)] (μ : ∀ s, Measure (X s)) [∀ s, SigmaFinite (μ s)] :
    (Measure.pi (fun d => Measure.pi (fun i => μ ⟨d, i⟩))).map
      (fun x (s : Σ d, I d) => x s.1 s.2) = Measure.pi μ := by
  have hm : Measurable (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) :=
    measurable_pi_iff.mpr (fun s => (measurable_pi_apply s.2).comp (measurable_pi_apply s.1))
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun d => Set.univ.pi (fun i => s ⟨d, i⟩)) := by
    ext x
    constructor
    · intro hx d _ i _
      exact hx ⟨d, i⟩ (Set.mem_univ _)
    · intro hx t _
      exact hx t.1 (Set.mem_univ _) t.2 (Set.mem_univ _)
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_sigma]

end Erdos3

end

end OAI

end


