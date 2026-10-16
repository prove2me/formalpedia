-- Prove2me | Definitions.Def_OAIErdos3B1399
-- name    : OAIErdos3B1399
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T09:11:10.24277+00:00
-- url     : https://prove2.me/theorems/bafff9da-5765-44f7-b6c5-de1e0c2b53e0
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1400 of 1413
-- statement:
--   Definitions bundle 1400 of 1413 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1398`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1400 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.cumulative_le_preparedFiniteNestedSourceRequired`, `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedSourceRequired_power_budget`, `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedSourceRequired_raised_power_budget`, `OAI.Erdos3.VectorPolynomial.forecastJointOriginalGridMean_reindexed`, `OAI.Erdos3.VectorPolynomial.forecastJoint_rational_reference`, `OAI.Erdos3.finiteImageCharacteristic_axis_reindex`, `OAI.Erdos3.finiteImageCharacteristic_axis_reindex_bound`, `OAI.Erdos3.outputAxisCharacterPullback_order`, `OAI.Erdos3.progression_slice_endpoint_unit_box`, `OAI.Erdos3.rationalInactiveForecast_axis_reindex`, `OAI.Erdos3.rationalOutputDensity_axis_reindex`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1389

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardFixedCenterThreshold
namespace OAI

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

variable {Slot : Type*} [Fintype Slot]
variable (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth cutoff : ℕ)
variable (x anchorGoodRequired conditionalRequired : ℝ) (detectorRequired : Slot → ℝ)

theorem cumulative_le_preparedFiniteNestedSourceRequired
    (outer : Fin (outerDepth + 1)) (degree : Fin (cutoff + 1)) :
    preparedFiniteForwardCumulative A constants degree.val
      (candidateNestedForwardSeed A constants innerDepth outer.val x) ≤
    preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired := by
  have hinner : max 0 (preparedFiniteForwardCumulative A constants degree.val
      (candidateNestedForwardSeed A constants innerDepth outer.val x)) ≤
      ∑ degree : Fin (cutoff + 1), max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) :=
    Finset.single_le_sum
      (f := fun degree : Fin (cutoff + 1) => max 0
        (preparedFiniteForwardCumulative A constants degree.val
          (candidateNestedForwardSeed A constants innerDepth outer.val x)))
      (fun _ _ => le_max_left _ _) (Finset.mem_univ degree)
  have houter : (∑ degree : Fin (cutoff + 1), max 0
      (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x))) ≤
      ∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
        max 0 (preparedFiniteForwardCumulative A constants degree.val
          (candidateNestedForwardSeed A constants innerDepth outer.val x)) :=
    Finset.single_le_sum
      (f := fun outer : Fin (outerDepth + 1) => ∑ degree : Fin (cutoff + 1), max 0
        (preparedFiniteForwardCumulative A constants degree.val
          (candidateNestedForwardSeed A constants innerDepth outer.val x)))
      (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_left _ _)) (Finset.mem_univ outer)
  have hdet : 0 ≤ ∑ slot, max 0 (detectorRequired slot) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  unfold preparedFiniteNestedSourceRequired
  linarith [le_max_left (0 : ℝ) anchorGoodRequired, le_max_left (0 : ℝ) conditionalRequired,
    le_max_right (0 : ℝ) (preparedFiniteForwardCumulative A constants degree.val
      (candidateNestedForwardSeed A constants innerDepth outer.val x))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_preparedFiniteNestedSourceRequired_power_budget
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth inputPower slotBound : ℕ)
    (hA : 2 ≤ A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (Slot : Type*) [Fintype Slot],
      ∀ cutoff ≤ innerDepth, ∀ {x anchorGoodRequired conditionalRequired : ℝ},
      Fintype.card Slot ≤ slotBound → 0 ≤ x →
      anchorGoodRequired ≤ (x + 2) ^ inputPower →
      conditionalRequired ≤ (x + 2) ^ inputPower →
      ∀ (detectorRequired : Slot → ℝ),
      (∀ slot, detectorRequired slot ≤ (x + 2) ^ inputPower) →
      preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff x
        anchorGoodRequired conditionalRequired detectorRequired ≤ (x + 2) ^ C := by
  obtain ⟨D, _, hlocal⟩ :=
    exists_candidateNestedForwardLocal_budget A 0 constants innerDepth outerDepth hA
  let P : Polynomial ℕ := 1 + Polynomial.C (slotBound + 2) *
    (Polynomial.X + Polynomial.C 2) ^ inputPower +
    Polynomial.C ((outerDepth + 1) * (innerDepth + 1)) *
      (Polynomial.X + Polynomial.C 2) ^ D
  obtain ⟨C, hC, hP⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, ?_⟩
  intro Slot _ cutoff hcutoff x anchorGoodRequired conditionalRequired hcard hx
    hanchor hconditional detectorRequired hdetector
  classical
  have hinputNonneg : 0 ≤ (x + 2) ^ inputPower := pow_nonneg (by linarith) _
  have hlocalNonneg : 0 ≤ (x + 2) ^ D := pow_nonneg (by linarith) _
  have hanchor' : max 0 anchorGoodRequired ≤ (x + 2) ^ inputPower :=
    max_le hinputNonneg hanchor
  have hconditional' : max 0 conditionalRequired ≤ (x + 2) ^ inputPower :=
    max_le hinputNonneg hconditional
  have hdetectorSum : (∑ slot, max 0 (detectorRequired slot)) ≤
      (slotBound : ℝ) * (x + 2) ^ inputPower := by
    calc
      _ ≤ ∑ _slot : Slot, (x + 2) ^ inputPower :=
        Finset.sum_le_sum (fun slot _ => max_le hinputNonneg (hdetector slot))
      _ = (Fintype.card Slot : ℝ) * (x + 2) ^ inputPower := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hinputNonneg
  have hcumulative (outer : Fin (outerDepth + 1)) (degree : Fin (cutoff + 1)) :
      max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) ≤ (x + 2) ^ D := by
    have h := hlocal (gainLog := 0) (stageLog := 0) hx ⟨le_rfl, hx⟩ ⟨le_rfl, hx⟩
      outer.val (Nat.le_of_lt_succ outer.isLt) degree.val
      ((Nat.le_of_lt_succ degree.isLt).trans hcutoff)
    exact max_le hlocalNonneg h.2.2.2.1.2
  have hdegreeSum (outer : Fin (outerDepth + 1)) :
      (∑ degree : Fin (cutoff + 1),
        max 0 (preparedFiniteForwardCumulative A constants degree.val
          (candidateNestedForwardSeed A constants innerDepth outer.val x))) ≤
        ((innerDepth + 1 : ℕ) : ℝ) * (x + 2) ^ D := by
    calc
      _ ≤ ∑ _degree : Fin (cutoff + 1), (x + 2) ^ D :=
        Finset.sum_le_sum (fun degree _ => hcumulative outer degree)
      _ = ((cutoff + 1 : ℕ) : ℝ) * (x + 2) ^ D := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Nat.succ_le_succ hcutoff)) hlocalNonneg
  have houterSum :
      (∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
        max 0 (preparedFiniteForwardCumulative A constants degree.val
          (candidateNestedForwardSeed A constants innerDepth outer.val x))) ≤
      (((outerDepth + 1) * (innerDepth + 1) : ℕ) : ℝ) * (x + 2) ^ D := by
    calc
      _ ≤ ∑ _outer : Fin (outerDepth + 1),
          ((innerDepth + 1 : ℕ) : ℝ) * (x + 2) ^ D :=
        Finset.sum_le_sum (fun outer _ => hdegreeSum outer)
      _ = _ := by simp [Nat.cast_mul, mul_assoc]
  have hpoly : 1 + ((slotBound + 2 : ℕ) : ℝ) * (x + 2) ^ inputPower +
      (((outerDepth + 1) * (innerDepth + 1) : ℕ) : ℝ) * (x + 2) ^ D ≤
      (x + 2) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hP x hx
  apply le_trans _ hpoly
  unfold preparedFiniteNestedSourceRequired
  have hmain := add_le_add
    (add_le_add (add_le_add (le_refl (1 : ℝ)) hanchor') hconditional') hdetectorSum
  have htotal := add_le_add hmain houterSum
  convert htotal using 1
  push_cast
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteNestedSourceRequired_raised_power_budget
    (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth outerDepth basePower lateExponent slotBound : ℕ)
    (hA : 2 ≤ A) (hBase : 1 ≤ basePower) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 2 ≤ p →
      ∀ (Slot : Type*) [Fintype Slot], ∀ cutoff ≤ innerDepth,
        Fintype.card Slot ≤ slotBound →
        ∀ detectorRequired : Slot → ℝ,
          (∀ slot, detectorRequired slot ≤ (p + 2) ^ lateExponent) →
          preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
            ((p + 2) ^ basePower) 0 0 detectorRequired ≤ (p + 2) ^ C := by
  obtain ⟨D, _, hrequired⟩ := exists_preparedFiniteNestedSourceRequired_power_budget
    A constants innerDepth outerDepth lateExponent slotBound hA
  let bound : Polynomial ℕ := ((Polynomial.X + 2) ^ basePower + 2) ^ D
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget bound
  refine ⟨C, hC, ?_⟩
  intro p hp Slot _ cutoff hcutoff hcard detectorRequired hdetector
  have hp0 : 0 ≤ p := by linarith
  have hstruct0 : 0 ≤ (p + 2) ^ basePower := by positivity
  have hpStruct : p ≤ (p + 2) ^ basePower := le_power_budget hp0 hBase
  have hinput : (p + 2) ^ lateExponent ≤
      ((p + 2) ^ basePower + 2) ^ lateExponent :=
    pow_le_pow_left₀ (by linarith) (by linarith) lateExponent
  have hactual := hrequired Slot cutoff hcutoff
    (x := (p + 2) ^ basePower) (anchorGoodRequired := 0) (conditionalRequired := 0)
    hcard hstruct0 (by positivity) (by positivity) detectorRequired
    (fun slot => (hdetector slot).trans hinput)
  apply hactual.trans
  simpa [bound, Polynomial.eval₂_pow] using hbound p hp0

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalOutputAxisReindex
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem rationalOutputDensity_axis_reindex {Ω A B : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (p : FiniteProbabilityWeights Ω) (Y : Ω → A → ℤ)
    (N : ℕ) [NeZero N] (r : A → ZMod N) :
    rationalOutputDensity p Y N r =
      rationalOutputDensity p (fun ω b => Y ω (e.symm b)) N (fun b => r (e.symm b)) := by
  have hcard : Fintype.card (A → ZMod N) = Fintype.card (B → ZMod N) :=
    Fintype.card_congr (outputAxisReindexAddEquiv e (ZMod N)).toEquiv
  have heq (ω : Ω) :
      ((fun b : B => (Y ω (e.symm b) : ZMod N)) = fun b => r (e.symm b)) ↔
        ((fun a : A => (Y ω a : ZMod N)) = r) := by
    constructor
    · intro h
      funext a
      simpa only [Equiv.symm_apply_apply] using congrFun h (e a)
    · intro h
      exact congrArg (fun f : A → ZMod N => fun b => f (e.symm b)) h
  unfold rationalOutputDensity finiteImageMass
  simp only [hcard, heq]

theorem rationalInactiveForecast_axis_reindex {I Ω Z A B : Type*}
    [Fintype I] [Fintype Ω] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (inactive : FiniteProbabilityWeights I)
    (active : I → FiniteProbabilityWeights Ω) (gridPoint : I → Z)
    (Y : I → Ω → A → ℤ) (N : ℕ) [NeZero N]
    (gridVolume : ℝ) (z : Z) (r : A → ZMod N) :
    rationalInactiveForecast inactive active gridPoint Y N gridVolume z r =
      rationalInactiveForecast inactive active gridPoint
        (fun i ω b => Y i ω (e.symm b)) N gridVolume z (fun b => r (e.symm b)) := by
  unfold rationalInactiveForecast
  apply congrArg (gridVolume * ·)
  apply congrArg (inactive.fiberMean gridPoint z)
  funext i
  exact rationalOutputDensity_axis_reindex e (active i) (Y i) N r

theorem outputAxisCharacterPullback_order {A B : Type*} (e : A ≃ B)
    (N : ℕ) (χ : AddChar (B → ZMod N) ℂ) :
    orderOf (characterPullback (outputAxisReindexAddEquiv e (ZMod N)).toAddMonoidHom χ) =
      orderOf χ :=
  characterPullback_order _ (outputAxisReindexAddEquiv e (ZMod N)).surjective χ

theorem finiteImageCharacteristic_axis_reindex {Ω A B : Type*} [Fintype Ω]
    (e : A ≃ B) (p : FiniteProbabilityWeights Ω) (Y : Ω → A → ℤ)
    (N : ℕ) (χ : AddChar (B → ZMod N) ℂ) :
    finiteImageCharacteristic p (fun ω b => (Y ω (e.symm b) : ZMod N)) χ =
      finiteImageCharacteristic p (fun ω a => (Y ω a : ZMod N))
        (characterPullback (outputAxisReindexAddEquiv e (ZMod N)).toAddMonoidHom χ) := rfl

theorem finiteImageCharacteristic_axis_reindex_bound {Ω A B : Type*} [Fintype Ω]
    (e : A ≃ B) (p : FiniteProbabilityWeights Ω) (Y : Ω → A → ℤ)
    (N : ℕ) {D P : ℝ}
    (hdecay : ∀ χ : AddChar (A → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun ω a => (Y ω a : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P)) :
    ∀ χ : AddChar (B → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun ω b => (Y ω (e.symm b) : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P) := by
  intro χ
  rw [finiteImageCharacteristic_axis_reindex]
  simpa only [outputAxisCharacterPullback_order] using
    hdecay (characterPullback (outputAxisReindexAddEquiv e (ZMod N)).toAddMonoidHom χ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProgressionEndpointUnitBox
namespace OAI

section

namespace Erdos3

theorem progression_slice_endpoint_unit_box {S step H : ℕ} (c : ℤ)
    (hS : 0 < S) (hstep : 0 < step) (hH : 0 < H)
    (hcontained : integerProgressionSupport c (step : ℤ) H ⊆
      Finset.Ico (0 : ℤ) (S : ℤ)) :
    0 ≤ (c : ℝ) / S ∧
      0 ≤ (step : ℝ) * ((H - 1 : ℕ) : ℝ) / S ∧
      (c : ℝ) / S + (step : ℝ) * ((H - 1 : ℕ) : ℝ) / S ≤ 1 := by
  have hfirst := hcontained (integerProgressionSupport_point c step H hstep 0 hH)
  have hlast := hcontained (integerProgressionSupport_point c step H hstep
    (H - 1) (by omega))
  have hc : (0 : ℝ) ≤ c := by
    have he : (0 : ℤ) ≤ c := by simpa using (Finset.mem_Ico.mp hfirst).1
    exact_mod_cast he
  have hend : (c : ℝ) + (step : ℝ) * ((H - 1 : ℕ) : ℝ) < S := by
    exact_mod_cast (Finset.mem_Ico.mp hlast).2
  have hSreal : (0 : ℝ) < S := by exact_mod_cast hS
  refine ⟨div_nonneg hc hSreal.le, by positivity, ?_⟩
  rw [← add_div]
  exact (div_le_one hSreal).mpr hend.le

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFixedPathRecoveredJointGridComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical
variable {X : Type*} {m : ℕ} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis L

variable [Fintype X] [∀ j, Fintype (E j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis L
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis L
local notation "Cont" => (Σ j : Fin m, I j)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Domain" => (Spatial → ℝ) × (Output → ℝ)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis L hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis L

theorem forecastJoint_rational_reference
    {P Ω Z : Type*} [Fintype P] [Fintype Ω]
    (inactive : FiniteProbabilityWeights P) (active : P → FiniteProbabilityWeights Ω)
    (gridPoint : P → Z) (Y : P → Ω → Out → ℤ)
    (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
    (density : Domain → ℝ) (hdensity : Measurable density)
    (hnonneg : ∀ y, 0 ≤ density y)
    (test : Z → (Out → ZMod q) → Domain → ℂ) :
    (∑' z, 𝔼 r : (Aux ⊕ (X ⊕ IntAxis)) → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint
        (fun i ω a => Y i ω ((axis).symm a)) N gridVolume z r / gridVolume : ℝ) : ℂ) *
      ∫ p : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ),
        (density (join p.1 p.2) : ℂ) *
          test z (fun a => ZMod.castHom hq (ZMod q) (r (axis a))) (join p.1 p.2)) =
    ∑' z, 𝔼 r : Out → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z r / gridVolume : ℝ) : ℂ) *
        ∫ y, test z (fun a => ZMod.castHom hq (ZMod q) (r a)) y
          ∂realDensityMeasure volume density := by
  apply tsum_congr
  intro z
  symm
  apply Fintype.expect_equiv (outputAxisReindexAddEquiv axis (ZMod N)).toEquiv
  intro r
  rw [rationalInactiveForecast_axis_reindex axis]
  congr 1
  rw [realDensityMeasure_integral_complex volume density hdensity hnonneg]
  rw [forecastJointCoordinateJoin_integral U basis L]
  apply integral_congr_ae
  filter_upwards [] with p
  congr 2
  funext a
  exact congrArg (ZMod.castHom hq (ZMod q)) (congrArg r ((axis).symm_apply_apply a).symm)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis Lsize
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Joint" => X ⊕ IntAxis
local notation "Cont" => (Σ j : Fin m, I j)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis Lsize hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis Lsize

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

theorem forecastJointOriginalGridMean_reindexed :
    let g := fun p : (Cont → ℝ) × (Joint → ℝ) => density (join p.1 p.2)
    let φ := fun z (r : (Aux ⊕ Joint) → ZMod q) (p : (Cont → ℝ) × (Joint → ℝ)) =>
      test z (fun a => r (axis a)) (join p.1 p.2)
    let Y' := fun i ω a => Y i ω ((axis).symm a)
    forecastJointOriginalGridMean U basis Lsize hm inactive active gridPoint Y N q hq
      gridVolume density test center scale =
      (𝔼 aux : Aux → ZMod N, ∫ c : Cont → ℝ,
        (∑' z, ∑' k : Joint → ℤ,
          (g (c, fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
          ((rationalInactiveForecast inactive active gridPoint Y' N gridVolume z
            (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
          φ z (Sum.elim (zmodPiReduction hq aux) (fun j => (k j : ZMod q)))
            (c, fun j => ((k j : ℝ) - center j) / scale j)) /
            ((∏ j, scale j : ℝ) : ℂ)) := by
  intro g φ Y'
  have hraw :
      rationalInactiveForecast inactive active gridPoint Y N gridVolume =
        fun z r => rationalInactiveForecast inactive active gridPoint Y' N gridVolume z
          (fun a => r ((axis).symm a)) := by
    funext z r
    exact rationalInactiveForecast_axis_reindex axis inactive active gridPoint Y N gridVolume z r
  unfold forecastJointOriginalGridMean
  simp only [hraw, g, φ, Equiv.apply_symm_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis Lsize
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

variable [NeZero q]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis Lsize
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Output" => (Σ _a : Active, Unit)

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)

local notation "sides" => allocatedPrincipalSides B U basis S

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (Pr : Finset ℕ) [∀ p : Pr, NeZero p.val] (Aexp : ℕ → ℕ)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

end Erdos3.VectorPolynomial

end

end OAI

end


