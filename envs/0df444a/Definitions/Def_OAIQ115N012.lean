-- Prove2me | Definitions.Def_OAIQ115N012
-- name    : OAIQ115N012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:10:43.782885+00:00
-- url     : https://prove2.me/theorems/f292aa0b-b00a-4120-a203-bad230a5506a
-- title:
--   Definitions bundle OAIQ115N012 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 100 declarations of OpenAI's Lean: 41 definitions, 2 inductive types or structures, 4 instances and 53 theorems. The definitions and types are `OAI.NaimarkZFC.HNNFactor`, `OAI.NaimarkZFC.MatrixDiagonalInput`, `OAI.NaimarkZFC.PeakingPairData`, `OAI.NaimarkZFC.PeakingPairData.Corner`, `OAI.NaimarkZFC.PeakingPairData.Model`, `OAI.NaimarkZFC.PeakingPairData.Operators`, `OAI.NaimarkZFC.PeakingPairData.Separated`, `OAI.NaimarkZFC.PeakingPairData.amalgam`, `OAI.NaimarkZFC.PeakingPairData.atoms`, `OAI.NaimarkZFC.PeakingPairData.aux`, `OAI.NaimarkZFC.PeakingPairData.base`, `OAI.NaimarkZFC.PeakingPairData.cornerBase`, `OAI.NaimarkZFC.PeakingPairData.diagonal`, `OAI.NaimarkZFC.PeakingPairData.embedAux`, `OAI.NaimarkZFC.PeakingPairData.embedBase`, `OAI.NaimarkZFC.PeakingPairData.expectation`, `OAI.NaimarkZFC.PeakingPairData.input`, `OAI.NaimarkZFC.PeakingPairData.letter`, `OAI.NaimarkZFC.PeakingPairData.matrixPeak`, `OAI.NaimarkZFC.PeakingPairData.matrixPeaks`, `OAI.NaimarkZFC.PeakingPairData.matrixPure`, `OAI.NaimarkZFC.PeakingPairData.matrixState`, `OAI.NaimarkZFC.PeakingPairData.modelLetter`, `OAI.NaimarkZFC.PeakingPairData.modelPartialOrder`, `OAI.NaimarkZFC.PeakingPairData.stableUnitary`, `OAI.NaimarkZFC.bridgeLetter`, `OAI.NaimarkZFC.cornerLiftState`, `OAI.NaimarkZFC.hnnAmalgamData`, `OAI.NaimarkZFC.hnnMatrixInput`, `OAI.NaimarkZFC.matrixAmalgamData`, `OAI.NaimarkZFC.matrixCornerEntry`, `OAI.NaimarkZFC.matrixInputData`, `OAI.NaimarkZFC.matrixSingleCLM`, `OAI.NaimarkZFC.matrixSinglePositive`, `OAI.NaimarkZFC.matrixStable`, `OAI.NaimarkZFC.matrixStableElement`, `OAI.NaimarkZFC.matrixStableUnitary`, `OAI.NaimarkZFC.matrixTraceState`, `OAI.NaimarkZFC.peakAtomicTraceData`, `OAI.NaimarkZFC.peakingMatrixInput` and 3 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Amalgamation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Amalgamation.lean), [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean), [`Naimark_Peaking`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Peaking.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N010` and `OAIQ115N011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N014`, `OAIQ115N015` and `OAIQ115N016`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N010
import Definitions.Def_OAIQ115N011

section
-- module Solutions.OAIQ115_Naimark.Naimark_Amalgamation
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.constructionIndex_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

attribute [local instance] Classical.propDecidable

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter
open scoped Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter
open scoped Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped InnerProductSpace
variable {V : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace
variable {V A H : Type*} [CStarAlgebra A] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace lp

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] Classical.propDecidable

open scoped InnerProductSpace ENNReal lp

variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type*} {J : ι → Type*} {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, CompleteSpace (H i)]

open scoped InnerProductSpace ENNReal lp

variable {ι : Type*} {H K : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedAddCommGroup (K i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, InnerProductSpace ℂ (K i)]

variable [∀ i, CompleteSpace (H i)] [∀ i, CompleteSpace (K i)]

variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace ENNReal lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

open scoped InnerProductSpace lp
variable {V J : Type*}

open scoped InnerProductSpace ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]

open Filter Topology
open scoped lp
variable {J V : Type*} [DecidableEq V]

variable [DecidableEq J]

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped CStarAlgebra
variable {A B n : Type*} [CStarAlgebra A] [CStarAlgebra B] [Fintype n] [DecidableEq n]

variable [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder CStarAlgebra
variable {A V n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n]

variable [Nonempty n]

open scoped ComplexOrder CStarAlgebra
variable {B n V : Type*} [CStarAlgebra B] [Fintype n] [DecidableEq n] [Nonempty n]

structure MatrixDiagonalInput (A : Type*) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (χ : B → V → ℂ) where
  trace : A →ₚ[ℂ] ℂ
  tracial : IsTracialPositive trace
  normalized : trace 1 = 1
  faithful : ∀ a, trace (star a*a) = 0 → a = 0
  data : n → AtomicTraceData A V
  sameTrace : ∀ i, (data i).trace = trace
  diagonal : n → B →⋆ₐ[ℂ] A
  atom_mul : ∀ i x v, ((data i).atom v).1 * diagonal i x = χ x v • ((data i).atom v).1
  expectation : n → A →L[ℂ] B
  bound : ∀ i a, ‖expectation i a‖ ≤ ‖a‖
  fix : ∀ i x, expectation i (diagonal i x) = x
  left : ∀ i x a, expectation i (diagonal i x * a) = x * expectation i a
  centered : ∀ i a, expectation i a = 0 → ∀ v,
    trace (((data i).atom v).1 * a * ((data i).atom v).1) = 0

variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
  (χ : B → V → ℂ) (c : ∀ j, MatrixDiagonalInput (n := n) (A j) χ)

def matrixInputData (j : I) : AtomicTraceData (CStarMatrix n n (A j)) (n × V) :=
  matrixAtomicTraceData (c j).trace (c j).tracial (c j).normalized (c j).faithful
    (c j).data (c j).sameTrace

def matrixAmalgamData (base : I)
    (weights : ∀ j i v, ((c base).trace (((c base).data i).atom v).1).re =
      ((c j).trace (((c j).data i).atom v).1).re) :
    AtomicAmalgamData (Δ := n → B) (matrixInputData χ c) where
  diagonal j := matrixDiagonalHom (c j).diagonal
  coordinate x v := χ (x v.1) v.2
  atom_mul j x v := by
    change matrixSingle v.1 v.1 _ * matrixDiagonalHom _ x = _
    rw [matrixSingle_diagonal, (c j).atom_mul, matrixSingle_smul]
    rfl
  expectation j := matrixDiagonalExpectation (c j).expectation (c j).bound
  fix j x := by
    funext i
    simp only [matrixDiagonalExpectation_apply, matrixDiagonalHom_apply, ite_true, if_true]
    exact (c j).fix i (x i)
  left j x a := by
    funext i
    simp only [matrixDiagonalExpectation_apply, matrixDiagonalHom_mul_apply, Pi.mul_apply]
    exact (c j).left i (x i) (a i i)
  centered j a ha v := by
    change normalizedMatrixTrace (c j).trace (matrixSingle v.1 v.1 _ * a *
      matrixSingle v.1 v.1 _) = 0
    rw [matrixSingle_compress, normalizedMatrixTrace_single]
    have he : (c j).expectation v.1 (a v.1 v.1) = 0 := congrFun ha v.1
    rw [(c j).centered v.1 _ he v.2, smul_zero]
  base := base
  weights j v := by
    change (normalizedMatrixTrace (c base).trace (matrixSingle v.1 v.1 _)).re =
      (normalizedMatrixTrace (c j).trace (matrixSingle v.1 v.1 _)).re
    simp only [normalizedMatrixTrace_single, Complex.smul_re, smul_eq_mul]
    rw [weights j v.1 v.2]

section
open Filter Topology
open scoped ComplexOrder CStarAlgebra OnePoint
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem AtomicTraceData.separating (d : AtomicTraceData A V) (a b : A)
    (h : ∀ r, (d.atom r).1 * a = (d.atom r).1 * b) : a = b := by
  apply sub_eq_zero.mp
  apply d.faithful
  rw [d.tracial]
  have hs := trace_hasSum_atom_corners d.trace d.tracial d.atom d.orthogonal d.mass
    ((a-b)*star (a-b))
  have hz (r : V) : d.trace ((d.atom r).1 * ((a-b)*star (a-b)) * (d.atom r).1) = 0 := by
    rw [← mul_assoc (d.atom r).1, mul_sub, h r, sub_self, zero_mul, zero_mul, map_zero]
  rw [← hs.tsum_eq]
  simp only [hz, tsum_zero]

def peakAtomicTraceData {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →ₚ[ℂ] ℂ) (htr : IsTracialPositive τ) (hn : τ 1 = 1)
    (hf : ∀ a, τ (star a*a) = 0 → a = 0)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)
    (hlim : Tendsto (fun n => (τ (p n)).re) atTop (𝓝 0)) : AtomicTraceData A ℕ where
  trace := τ
  tracial := htr
  normalized := hn
  faithful := hf
  atom n := ⟨peakAtom p n, hp.peakAtom_projection n⟩
  orthogonal := hp.peakAtom_orthogonal
  positive := hpos
  mass := by
    apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => (hpos n).le) _).mpr
    have he n : ∑ r ∈ Finset.range n, (τ (peakAtom p r)).re = (τ 1).re - (τ (p n)).re := by
      rw [← Complex.re_sum, ← map_sum, peakAtom_sum, hp0, map_sub, Complex.sub_re]
    simp_rw [he]
    simpa using tendsto_const_nhds.sub hlim

variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)

include hp in

theorem sequenceDiagonalMap_atom (g : SequenceDiagonal) (n : ℕ) :
    peakAtom p n * sequenceDiagonalMap p g = g n • peakAtom p n := by
  change peakAtom p n * ((g ∞) • (1 : A) + ∑' i : ℕ, (g i - g ∞) • peakAtom p i) = _
  rw [mul_add, mul_smul_comm, mul_one,
    orthogonalProjection_mul_tsum _ hp.peakAtom_projection hp.peakAtom_orthogonal
      (fun i : ℕ => g i - g ∞) (by simpa using g.tendsto.sub_const (g ∞)) n,
    ← add_smul, add_sub_cancel]

include hp in
theorem sequenceDiagonalMap_atom_right (g : SequenceDiagonal) (n : ℕ) :
    sequenceDiagonalMap p g * peakAtom p n = g n • peakAtom p n := by
  have hs := summable_orthogonalProjection _ hp.peakAtom_projection hp.peakAtom_orthogonal
    (fun i : ℕ => g i - g ∞) (by simpa using g.tendsto.sub_const (g ∞))
  change ((g ∞) • (1 : A) + ∑' i : ℕ, (g i - g ∞) • peakAtom p i) * peakAtom p n = _
  rw [add_mul, smul_mul_assoc, one_mul, ← hs.tsum_mul_right]
  have he : (∑' i : ℕ, ((g i - g ∞) • peakAtom p i) * peakAtom p n) =
      (g n - g ∞) • peakAtom p n := by
    rw [tsum_eq_single n]
    · rw [smul_mul_assoc, (hp.peakAtom_projection n).isIdempotentElem.eq]
    · intro i hi
      rw [smul_mul_assoc, hp.peakAtom_orthogonal hi, smul_zero]
  rw [he, ← add_smul, add_sub_cancel]

variable (d : AtomicTraceData A ℕ) (hd : ∀ n, (d.atom n).1 = peakAtom p n)
include hd

theorem peakAtom_separating (a b : A)
    (h : ∀ n, peakAtom p n * a = peakAtom p n * b) : a = b := by
  apply d.separating
  simpa only [hd] using h

include hp in

def sequenceDiagonalHom : SequenceDiagonal →⋆ₐ[ℂ] A where
  toFun := sequenceDiagonalMap p
  map_one' := by
    apply peakAtom_separating d hd
    intro n
    rw [sequenceDiagonalMap_atom hp, mul_one]
    simp only [ContinuousMap.one_apply, one_smul]
  map_mul' g h := by
    apply peakAtom_separating d hd
    intro n
    rw [sequenceDiagonalMap_atom hp, ContinuousMap.mul_apply, ← mul_assoc,
      sequenceDiagonalMap_atom hp, smul_mul_assoc, sequenceDiagonalMap_atom hp,
      smul_smul]
  map_zero' := by
    apply peakAtom_separating d hd
    intro n
    rw [sequenceDiagonalMap_atom hp, ContinuousMap.zero_apply, zero_smul, mul_zero]
  map_add' g h := by
    apply peakAtom_separating d hd
    intro n
    rw [sequenceDiagonalMap_atom hp, ContinuousMap.add_apply, mul_add,
      sequenceDiagonalMap_atom hp, sequenceDiagonalMap_atom hp, add_smul]
  commutes' z := by
    apply peakAtom_separating d hd
    intro n
    rw [sequenceDiagonalMap_atom hp]
    change z • peakAtom p n = peakAtom p n * algebraMap ℂ A z
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  map_star' g := by
    apply peakAtom_separating d hd
    intro n
    rw [sequenceDiagonalMap_atom hp, ContinuousMap.star_apply]
    have h := congrArg star (sequenceDiagonalMap_atom_right hp g n)
    rw [star_mul, (hp.peakAtom_projection n).isSelfAdjoint.star_eq,
      star_smul, (hp.peakAtom_projection n).isSelfAdjoint.star_eq] at h
    exact h.symm

include hp in
theorem sequenceDiagonalHom_injective : Function.Injective (sequenceDiagonalHom hp d hd) := by
  intro g h he
  have hf (n : ℕ) : g n = h n := by
    have hq : peakAtom p n ≠ 0 := by
      intro hz
      have hp' := d.positive n
      rw [hd, hz, map_zero, Complex.zero_re] at hp'
      exact lt_irrefl 0 hp'
    apply smul_left_injective ℂ hq
    change g n • peakAtom p n = h n • peakAtom p n
    rw [← sequenceDiagonalMap_atom hp, ← sequenceDiagonalMap_atom hp]
    exact congrArg (peakAtom p n * ·) he
  ext n
  induction n using OnePoint.rec with
  | infty => exact tendsto_nhds_unique g.tendsto (by simpa only [hf] using h.tendsto)
  | coe n => exact hf n

end

section
open Filter Topology
open scoped ComplexOrder CStarAlgebra OnePoint
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)
variable (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)

variable (d : AtomicTraceData A ℕ) (hd : ∀ n, (d.atom n).1 = peakAtom p n)

theorem sequenceDiagonalHom_peakingCoefficients (a : A) :
    sequenceDiagonalHom hp d hd (peakingCoefficients hp τ hτ hpos a) =
      peakingExpectation hp hp0 τ hτ hpos a := rfl

include hp0 in
theorem peakingCoefficients_fixes (g : SequenceDiagonal) :
    peakingCoefficients hp τ hτ hpos (sequenceDiagonalHom hp d hd g) = g := by
  apply sequenceDiagonalHom_injective hp d hd
  rw [sequenceDiagonalHom_peakingCoefficients hp hp0]
  exact peakingExpectation_fixes hp hp0 τ hτ hpos _ (sequenceDiagonalMap_mem hp g)

include hp0 in
theorem peakingCoefficients_left (g : SequenceDiagonal) (a : A) :
    peakingCoefficients hp τ hτ hpos (sequenceDiagonalHom hp d hd g * a) =
      g * peakingCoefficients hp τ hτ hpos a := by
  apply sequenceDiagonalHom_injective hp d hd
  rw [map_mul (sequenceDiagonalHom hp d hd), sequenceDiagonalHom_peakingCoefficients hp hp0,
    sequenceDiagonalHom_peakingCoefficients hp hp0]
  exact peakingExpectation_leftBimodule hp hp0 τ hτ hpos _ _ (sequenceDiagonalMap_mem hp g)

end

open scoped ComplexOrder CStarAlgebra
variable {A B V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

section
open Filter Topology
open scoped OnePoint ComplexOrder CStarAlgebra
variable {A n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n] [Nonempty n]

variable (τ : A →ₚ[ℂ] ℂ) (htr : IsTracialPositive τ) (hn : τ 1 = 1)
  (hf : ∀ a, τ (star a*a) = 0 → a = 0)
  (p : n → ℕ → A) (f : n → A →L[ℂ] ℂ) (hp : ∀ i, Peaks (p i) (f i))
  (hp0 : ∀ i, p i 0 = 1) (hpos : ∀ i v, 0 < (τ (peakAtom (p i) v)).re)
  (hlim : ∀ i, Tendsto (fun v => (τ (p i v)).re) atTop (𝓝 0))

def peakingMatrixInput : MatrixDiagonalInput (n := n) A (fun x : SequenceDiagonal => fun v : ℕ => x v) where
  trace := τ
  tracial := htr
  normalized := hn
  faithful := hf
  data i := peakAtomicTraceData (hp i) (hp0 i) τ htr hn hf (hpos i) (hlim i)
  sameTrace _ := rfl
  diagonal i := sequenceDiagonalHom (hp i)
    (peakAtomicTraceData (hp i) (hp0 i) τ htr hn hf (hpos i) (hlim i)) (fun _ => rfl)
  atom_mul i x v := sequenceDiagonalMap_atom (hp i) x v
  expectation i := peakingCoefficients (hp i) (positiveCLM τ) (positiveCLM_isState τ hn) (hpos i)
  bound i a := peakingCoefficientsFun_norm_le (hp i) (positiveCLM τ) (positiveCLM_isState τ hn) (hpos i) a
  fix i x := peakingCoefficients_fixes (hp i) (hp0 i) (positiveCLM τ)
    (positiveCLM_isState τ hn) (hpos i) _ (fun _ => rfl) x
  left i x a := peakingCoefficients_left (hp i) (hp0 i) (positiveCLM τ)
    (positiveCLM_isState τ hn) (hpos i) _ (fun _ => rfl) x a
  centered i a ha v := peakingCoefficients_zero_corners (hp i) (positiveCLM τ)
    (positiveCLM_isState τ hn) (hpos i) a ha v

end

section
open Filter Topology
open scoped OnePoint ComplexOrder CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)
variable (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ v, 0 < (τ (peakAtom p v)).re)
variable (d : AtomicTraceData A ℕ) (hd : ∀ v, (d.atom v).1 = peakAtom p v)

include hp0 in
@[simp] theorem sequenceDiagonalHom_sequenceAtom (v : ℕ) :
    sequenceDiagonalHom hp d hd (sequenceAtom hp τ hτ hpos v) = peakAtom p v := by
  rw [sequenceAtom, sequenceDiagonalHom_peakingCoefficients hp hp0]
  exact peakingExpectation_fixes hp hp0 τ hτ hpos _ (peakAtom_mem_peakAlgebra p v)

def sequenceAtomicTraceData : AtomicTraceData SequenceDiagonal ℕ :=
  d.pullback (sequenceDiagonalHom hp d hd) (sequenceDiagonalHom_injective hp d hd)
    (sequenceAtom hp τ hτ hpos) (fun v => by
      rw [sequenceDiagonalHom_sequenceAtom hp hp0 τ hτ hpos d hd, hd])

theorem sequenceAtomicTraceData_atom_mul (x : SequenceDiagonal) (v : ℕ) :
    ((sequenceAtomicTraceData hp hp0 τ hτ hpos d hd).atom v).1 * x =
      x v • ((sequenceAtomicTraceData hp hp0 τ hτ hpos d hd).atom v).1 := by
  apply sequenceDiagonalHom_injective hp d hd
  change sequenceDiagonalHom hp d hd (sequenceAtom hp τ hτ hpos v * x) =
    sequenceDiagonalHom hp d hd (x v • sequenceAtom hp τ hτ hpos v)
  rw [map_mul, map_smul, sequenceDiagonalHom_sequenceAtom hp hp0]
  exact sequenceDiagonalMap_atom hp x v

def sequenceMatrixInput {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    MatrixDiagonalInput (n := n) SequenceDiagonal (fun x : SequenceDiagonal => fun v : ℕ => x v) where
  trace := (sequenceAtomicTraceData hp hp0 τ hτ hpos d hd).trace
  tracial := (sequenceAtomicTraceData hp hp0 τ hτ hpos d hd).tracial
  normalized := (sequenceAtomicTraceData hp hp0 τ hτ hpos d hd).normalized
  faithful := (sequenceAtomicTraceData hp hp0 τ hτ hpos d hd).faithful
  data _ := sequenceAtomicTraceData hp hp0 τ hτ hpos d hd
  sameTrace _ := rfl
  diagonal _ := StarAlgHom.id ℂ SequenceDiagonal
  atom_mul _ x v := sequenceAtomicTraceData_atom_mul hp hp0 τ hτ hpos d hd x v
  expectation _ := ContinuousLinearMap.id ℂ SequenceDiagonal
  bound _ _ := le_rfl
  fix _ _ := rfl
  left _ _ _ := rfl
  centered _ a ha v := by
    change a = 0 at ha
    simp only [ha, mul_zero, zero_mul, map_zero]

end

section
open Filter Topology
open scoped OnePoint ComplexOrder CStarAlgebra

abbrev HNNFactor (A : Type) : Bool → Type _
  | false => A
  | true => SequenceDiagonal

instance instCStarAlgebraHNNFactor {A : Type} [CStarAlgebra A] : (j : Bool) → CStarAlgebra (HNNFactor A j)
  | false => inferInstanceAs (CStarAlgebra A)
  | true => inferInstanceAs (CStarAlgebra SequenceDiagonal)
instance instPartialOrderHNNFactorOfCStarAlgebra {A : Type} [CStarAlgebra A] [PartialOrder A] :
    (j : Bool) → PartialOrder (HNNFactor A j)
  | false => inferInstanceAs (PartialOrder A)
  | true => inferInstanceAs (PartialOrder SequenceDiagonal)
instance instStarOrderedRingHNNFactor {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    (j : Bool) → StarOrderedRing (HNNFactor A j)
  | false => inferInstanceAs (StarOrderedRing A)
  | true => inferInstanceAs (StarOrderedRing SequenceDiagonal)

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (htr : IsTracialPositive τ) (hn : τ 1 = 1)
  (hf : ∀ a, τ (star a*a) = 0 → a = 0)
  (p : Bool → ℕ → A) (f : Bool → A →L[ℂ] ℂ) (hp : ∀ i, Peaks (p i) (f i))
  (hp0 : ∀ i, p i 0 = 1) (hpos : ∀ i v, 0 < (τ (peakAtom (p i) v)).re)
  (hlim : ∀ i, Tendsto (fun v => (τ (p i v)).re) atTop (𝓝 0))

def hnnMatrixInput : (j : Bool) → MatrixDiagonalInput (n := Bool) (HNNFactor A j)
    (fun x : SequenceDiagonal => fun v : ℕ => x v)
  | false => peakingMatrixInput τ htr hn hf p f hp hp0 hpos hlim
  | true => sequenceMatrixInput (hp false) (hp0 false) (positiveCLM τ)
      (positiveCLM_isState τ hn) (hpos false)
      (peakAtomicTraceData (hp false) (hp0 false) τ htr hn hf (hpos false) (hlim false))
      (fun _ => rfl)

variable (hmatch : ∀ i v, τ (p i v) = τ (p false v))

include hmatch in

theorem hnnMatrixInput_weights (j i : Bool) (v : ℕ) :
    ((hnnMatrixInput τ htr hn hf p f hp hp0 hpos hlim false).trace
      (((hnnMatrixInput τ htr hn hf p f hp hp0 hpos hlim false).data i).atom v).1).re =
    ((hnnMatrixInput τ htr hn hf p f hp hp0 hpos hlim j).trace
      (((hnnMatrixInput τ htr hn hf p f hp hp0 hpos hlim j).data i).atom v).1).re := by
  cases j
  · rfl
  · have he := sequenceDiagonalHom_sequenceAtom (hp false) (hp0 false)
      (positiveCLM τ) (positiveCLM_isState τ hn) (hpos false)
      (peakAtomicTraceData (hp false) (hp0 false) τ htr hn hf (hpos false) (hlim false))
      (fun _ => rfl) v
    have ht : τ (peakAtom (p i) v) = τ (peakAtom (p false) v) := by
      simp only [peakAtom, map_sub, hmatch]
    exact congrArg Complex.re (ht.trans (congrArg τ he).symm)

def hnnAmalgamData : AtomicAmalgamData (Δ := Bool → SequenceDiagonal)
    (matrixInputData (fun x : SequenceDiagonal => fun v : ℕ => x v)
      (hnnMatrixInput τ htr hn hf p f hp hp0 hpos hlim)) :=
  matrixAmalgamData _ _ false (hnnMatrixInput_weights τ htr hn hf p f hp hp0 hpos hlim hmatch)

end

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Peaking
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.constructionIndex_nonempty _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_cstar _root_.OAI.NaimarkZFC.hnnGeneratedCStar _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

section
open scoped CStarAlgebra
variable {A B Z : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra Z]

variable (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)

variable (ψ : CStarMatrix Bool Bool B →⋆ₐ[ℂ] Z)
  (diag : ∀ i : Bool, φ (matrixSingle i i (1 : A)) = ψ (matrixSingle i i (1 : B)))

def matrixStableElement : Z := φ (matrixSingle false true (1 : A)) * ψ (matrixSingle true false (1 : B))

include diag in
theorem matrixStableElement_mem : matrixStableElement φ ψ ∈ cornerSubalgebra
    (matrixCornerProjection φ) (matrixCornerProjection_isProjection φ) := by
  constructor
  · change φ (matrixSingle false false (1 : A)) * (φ _ * ψ _) = φ _ * ψ _
    rw [← mul_assoc, ← map_mul, matrixSingle_mul, one_mul]
  · change (φ _ * ψ _) * φ (matrixSingle false false (1 : A)) = φ _ * ψ _
    rw [mul_assoc, diag false, ← map_mul, matrixSingle_mul, one_mul]

def matrixStable : MatrixHNNCorner φ := ⟨matrixStableElement φ ψ, matrixStableElement_mem φ ψ diag⟩

include diag in
theorem matrixStable_star_mul : star (matrixStable φ ψ diag) * matrixStable φ ψ diag = 1 := by
  apply Subtype.ext
  change star (φ (matrixSingle false true (1 : A)) * ψ (matrixSingle true false (1 : B))) *
    (φ (matrixSingle false true (1 : A)) * ψ (matrixSingle true false (1 : B))) =
    φ (matrixSingle false false (1 : A))
  simp only [star_mul, ← map_star, matrixSingle_star, star_one]
  rw [mul_assoc, ← mul_assoc (φ _), ← map_mul, matrixSingle_mul, one_mul, diag true,
    ← map_mul, matrixSingle_mul, one_mul, ← map_mul, matrixSingle_mul, one_mul, diag false]

include diag in
theorem matrixStable_mul_star : matrixStable φ ψ diag * star (matrixStable φ ψ diag) = 1 := by
  apply Subtype.ext
  change (φ (matrixSingle false true (1 : A)) * ψ (matrixSingle true false (1 : B))) *
    star (φ (matrixSingle false true (1 : A)) * ψ (matrixSingle true false (1 : B))) =
    φ (matrixSingle false false (1 : A))
  simp only [star_mul, ← map_star, matrixSingle_star, star_one]
  rw [mul_assoc, ← mul_assoc (ψ _), ← map_mul, matrixSingle_mul, one_mul, ← diag true,
    ← map_mul, matrixSingle_mul, one_mul, ← map_mul, matrixSingle_mul, one_mul]

def matrixStableUnitary : unitary (MatrixHNNCorner φ) :=
  ⟨matrixStable φ ψ diag, matrixStable_star_mul φ ψ diag, matrixStable_mul_star φ ψ diag⟩

theorem matrixDiagonalHom_single (δ : Bool → B →⋆ₐ[ℂ] A) (i : Bool) (b : B) :
    matrixDiagonalHom δ (Pi.single i b) = matrixSingle i i (δ i b) := by
  ext k l
  cases i <;> cases k <;> cases l <;> simp

variable (δ : Bool → B →⋆ₐ[ℂ] A)
  (hδ : ∀ x, φ (matrixDiagonalHom δ x) =
    ψ (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ B) x))

include hδ in
theorem matrixDiagonal_agrees (i : Bool) (b : B) :
    φ (matrixSingle i i (δ i b)) = ψ (matrixSingle i i b) := by
  have h := hδ (Pi.single i b)
  rw [matrixDiagonalHom_single, matrixDiagonalHom_single] at h
  exact h

include hδ in
theorem matrixDiagonal_units (i : Bool) :
    φ (matrixSingle i i (1 : A)) = ψ (matrixSingle i i (1 : B)) := by
  simpa only [map_one] using matrixDiagonal_agrees φ ψ δ hδ i 1

end

open scoped ComplexOrder CStarAlgebra
section
variable {A n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem matrixSingleHom_apply (i : n) (a : A) :
    matrixSingleHom i a = matrixSingle i i a := rfl

def matrixSinglePositive (i : n) : A →ₚ[ℂ] CStarMatrix n n A :=
  PositiveLinearMap.mk₀
    { toFun := matrixSingle i i
      map_add' a b := map_add (matrixSingleHom i) a b
      map_smul' z a := matrixSingle_smul i i a z } (by
    intro a ha
    change 0 ≤ matrixSingleHom i a
    exact AddSubmonoid.closure_induction (motive := fun a _ => 0 ≤ matrixSingleHom i a)
      (by rintro a ⟨b,rfl⟩; rw [map_mul,map_star]; exact star_mul_self_nonneg _)
      (by rw [map_zero])
      (by intro a b _ _ ha hb; rw [map_add]; exact add_nonneg ha hb) (StarOrderedRing.nonneg_iff.mp ha))

def matrixSingleCLM (i : n) : A →L[ℂ] CStarMatrix n n A :=
  (matrixSinglePositive i).toLinearMap.mkContinuous 1 (fun a => by
    change ‖matrixSingleHom i a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le (matrixSingleHom i) a)

omit [DecidableEq n] in
@[simp] theorem matrixState_apply (f : A →L[ℂ] ℂ) (i : n) (M : CStarMatrix n n A) :
    matrixState f i M = f (M i i) := rfl

theorem matrixState_isState (f : A →L[ℂ] ℂ) (hf : IsState f) (i : n) :
    IsState (matrixState f i) := by
  apply (isState_iff _).mpr
  constructor
  · simpa only [matrixState_apply,CStarMatrix.one_apply_eq] using ((isState_iff f).mp hf).1
  · intro M
    have h := state_nonneg f hf ((matrixEntryPositive i).map_nonneg (star_mul_self_nonneg M))
    exact ⟨h.2.symm,h.1⟩

theorem matrix_state_supported (g : CStarMatrix n n A →L[ℂ] ℂ) (hg : IsState g)
    (i : n) (hi : g (matrixSingle i i (1 : A)) = 1) (M : CStarMatrix n n A) :
    g M = g (matrixSingle i i (M i i)) := by
  have he := state_compression g hg (matrixSingle i i 1)
    ((matrixSingle_projection i 1 (by constructor <;> simp [IsIdempotentElem, IsSelfAdjoint])).norm_le _)
    (matrixSingle_projection i 1 (by constructor <;> simp [IsIdempotentElem, IsSelfAdjoint])).isSelfAdjoint hi M
  rw [matrixSingle_compress,one_mul,mul_one] at he
  exact he.symm

theorem matrix_corner_isState (g : CStarMatrix n n A →L[ℂ] ℂ) (hg : IsState g)
    (i : n) (hi : g (matrixSingle i i (1 : A)) = 1) :
    IsState (g.comp (matrixSingleCLM i)) := by
  apply (isState_iff _).mpr
  refine ⟨hi, ?_⟩
  intro a
  have h := state_nonneg g hg ((matrixSinglePositive i).map_nonneg (star_mul_self_nonneg a))
  exact ⟨h.2.symm,h.1⟩

theorem Peaks.matrix {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (i : n) : Peaks (fun k => matrixSingle i i (p k)) (matrixState f i) := by
  refine ⟨fun k => matrixSingle_projection i _ (hp.1 k), ?_, matrixState_isState f hp.2.2.1 i,
    ?_, ?_⟩
  · intro k l hkl
    exact (matrixSinglePositive i).monotone (hp.2.1 hkl)
  · intro k
    simp [hp.2.2.2.1 k]
  · intro g hg hgp
    have hgi : g (matrixSingle i i (1 : A)) = 1 := by simpa only [hp0] using hgp 0
    have hc := hp.2.2.2.2 (g.comp (matrixSingleCLM i))
      (matrix_corner_isState g hg i hgi) hgp
    ext M
    rw [matrix_state_supported g hg i hgi M,matrixState_apply]
    exact congrArg (fun k : A →L[ℂ] ℂ => k (M i i)) hc

end

open Filter Topology
open scoped ComplexOrder CStarAlgebra OnePoint
section
variable {A n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n] [Nonempty n]

def matrixTraceState (τ : A →L[ℂ] ℂ) (hτ : IsState τ) : CStarMatrix n n A →L[ℂ] ℂ :=
  positiveCLM (normalizedMatrixTrace (positiveOfSquares τ hτ.2))

omit [Nonempty n] in
@[simp] theorem matrixTraceState_single (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (i : n) (a : A) :
    matrixTraceState τ hτ (matrixSingle i i a) = (Fintype.card n : ℝ)⁻¹ • τ a :=
  normalizedMatrixTrace_single _ i a

omit [Nonempty n] in
@[simp] theorem matrix_peakAtom (p : ℕ → A) (i : n) (m : ℕ) :
    peakAtom (fun k => matrixSingle i i (p k)) m = matrixSingle i i (peakAtom p m) :=
  (map_sub (matrixSingleHom i) (p m) (p (m+1))).symm

end

open Filter Topology
open scoped ComplexOrder

open Filter Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

open Filter Topology

open Filter Topology
section

namespace BridgeCore
variable {F B : Type*}

variable [Monoid B]

@[simp] theorem left_cons (i : Bool) (a : F) (w : BridgeCore F) : (w.cons i a).left = i := by
  cases w <;> rfl
@[simp] theorem right_cons (i : Bool) (a : F) (w : BridgeCore F) : (w.cons i a).right = w.right := by
  cases w <;> rfl
@[simp] theorem left_snoc (a : F) (j : Bool) (w : BridgeCore F) : (w.snoc a j).left = w.left := by
  cases w <;> rfl
@[simp] theorem right_snoc (a : F) (j : Bool) (w : BridgeCore F) : (w.snoc a j).right = !j := by
  cases w <;> rfl

variable (φ : F → B) (b e : Bool → B)
  (hleft : ∀ i, e i*b i = b i) (hright : ∀ i, b i*e (!i) = b i)
include hleft in
theorem left_support (w : BridgeCore F) : e w.left*w.eval φ b = w.eval φ b := by
  cases w <;> simp only [left,eval,← mul_assoc,hleft]
include hright in
theorem right_support (w : BridgeCore F) : w.eval φ b*e w.right = w.eval φ b := by
  cases w <;> simp only [right,eval,mul_assoc,hright]
end BridgeCore

variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
  (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I]
  {i j : I} (hij : i ≠ j) (b : Bool → A j)
  (hb : ∀ v r, (d j).trace (((d j).atom r).1*b v*((d j).atom r).1) = 0)
  (K : A i → Prop)
  (hK : ∀ a, K a → ∀ r, (d i).trace (((d i).atom r).1*a*((d i).atom r).1) = 0)

include hij hb hK

theorem BridgeCore.creation (w : BridgeCore (A i)) (hw : w.Centered K)
    (x : AtomicFockSpace (AtomicLetters d))
    (hx : FockAway (AtomicLetters d) j x) :
    FockStarts (AtomicLetters d) j (w.eval (atomicLeft d i) (fun v => atomicLeft d j (b v)) x) := by
  have hg (v : Bool) (z : AtomicFockSpace (AtomicLetters d))
      (hz : FockAway (AtomicLetters d) j z) :
      FockStarts (AtomicLetters d) j (atomicLeft d j (b v) z) := by
    exact atomicLeft_centered d j (b v) (hb v) z hz
  have hf (a : A i) (ha : K a) (z : AtomicFockSpace (AtomicLetters d))
      (hz : FockStarts (AtomicLetters d) j z) :
      FockAway (AtomicLetters d) j (atomicLeft d i a z) := by
    apply fockStarts_away _ hij
    exact atomicLeft_centered d i a (hK a ha) z (fockStarts_away _ hij.symm _ hz)
  induction w generalizing x with
  | single v => exact hg v x hx
  | double v a u =>
    exact hg v _ (hf a hw _ (hg u x hx))
  | flank v a w c u ih =>
    exact hg v _ (hf a hw.1 _ (ih hw.2.1 _ (hf c hw.2.2 _ (hg u x hx))))

theorem BridgeCore.zero_complement (w : BridgeCore (A i)) (hw : w.Centered K) :
    (1-fockStartProjection (AtomicLetters d) j)*
      w.eval (atomicLeft d i) (fun v => atomicLeft d j (b v))*
      (1-fockStartProjection (AtomicLetters d) j) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change (1-fockStartProjection (AtomicLetters d) j)
    (w.eval (atomicLeft d i) (fun v => atomicLeft d j (b v))
      ((1-fockStartProjection (AtomicLetters d) j) x)) = 0
  rw [sub_apply,one_apply_eq_self,fockStartProjection_fix _ _ _
    (w.creation d hij b hb K hK hw _ (fockStartProjection_complement_away _ _ x)),sub_self]

end

section
open scoped CStarAlgebra
variable {A D Z : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra Z]
  [PartialOrder A] [StarOrderedRing A]
  [PartialOrder D] [StarOrderedRing D]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)
  (ψ : CStarMatrix Bool Bool D →⋆ₐ[ℂ] Z)
  (δ : Bool → D →⋆ₐ[ℂ] A)
  (hd : ∀ x, φ (matrixDiagonalHom δ x) =
    ψ (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ D) x))

def bridgeLetter (i : Bool) : Z := ψ (matrixSingle i (!i) (1:D))

omit [PartialOrder D] [StarOrderedRing D] in
@[simp] theorem bridgeLetter_star (i : Bool) : star (bridgeLetter ψ i) = bridgeLetter ψ (!i) := by
  simp only [bridgeLetter,← map_star,matrixSingle_star,star_one,Bool.not_not]

end

section
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
  {d : ∀ i, AtomicTraceData (A i) V} [DecidableEq I] [DecidableEq V]
  {Δ : Type*} [CStarAlgebra Δ] (c : AtomicAmalgamData (Δ := Δ) d)

theorem AtomicAmalgamData.left_agree (i j : I) (x : Δ) :
    atomicLeft d i (c.diagonal i x) = atomicLeft d j (c.diagonal j x) :=
  atomicLeft_diagonal_agree d c.diagonal c.coordinate c.atom_mul i j x

omit [DecidableEq V] in

theorem AtomicAmalgamData.core_zero {i j : I} (hij : i ≠ j) (b : Bool → A j)
    (hb : ∀ k, c.expectation j (b k) = 0)
    (w : BridgeCore (A i)) (hw : w.Centered (fun a => c.expectation i a = 0)) :
    (1-fockStartProjection (AtomicLetters d) j)*
      w.eval (atomicLeft d i) (fun k => atomicLeft d j (b k))*
      (1-fockStartProjection (AtomicLetters d) j) = 0 :=
  w.zero_complement d hij b (fun k => c.centered j _ (hb k))
    (fun a => c.expectation i a = 0) (fun a ha => c.centered i a ha) hw
end

open Filter Topology
open scoped OnePoint ComplexOrder CStarAlgebra

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

structure PeakingPairData (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  trace : A →ₚ[ℂ] ℂ
  tracial : IsTracialPositive trace
  normalized : trace 1 = 1
  faithful : ∀ a, trace (star a*a) = 0 → a = 0
  peak : Bool → ℕ → A
  state : Bool → A →L[ℂ] ℂ
  peaks : ∀ i, Peaks (peak i) (state i)
  peak_zero : ∀ i, peak i 0 = 1
  atom_positive : ∀ i v, 0 < (trace (peakAtom (peak i) v)).re
  trace_null : ∀ i, Tendsto (fun v => (trace (peak i v)).re) atTop (𝓝 0)
  matched : ∀ i v, trace (peak i v) = trace (peak false v)

namespace PeakingPairData
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

local instance matrixFamilyStarOrder : (j : Bool) →
    StarOrderedRing (CStarMatrix Bool Bool (HNNFactor A j)) := fun _ => inferInstance

def input : (j : Bool) → MatrixDiagonalInput (n := Bool) (HNNFactor A j)
    (fun x : SequenceDiagonal => fun v : ℕ => x v) := hnnMatrixInput B.trace B.tracial B.normalized B.faithful B.peak B.state
  B.peaks B.peak_zero B.atom_positive B.trace_null

def atoms : (j : Bool) → AtomicTraceData (CStarMatrix Bool Bool (HNNFactor A j)) (Bool × ℕ) := matrixInputData (fun x : SequenceDiagonal => fun v : ℕ => x v) B.input

def amalgam : AtomicAmalgamData (Δ := Bool → SequenceDiagonal) B.atoms := hnnAmalgamData B.trace B.tracial B.normalized B.faithful B.peak B.state
  B.peaks B.peak_zero B.atom_positive B.trace_null B.matched

abbrev Model := AtomicCStar B.atoms

instance modelCStarAlgebra : CStarAlgebra B.Model := inferInstance

abbrev Operators := AtomicOperators B.atoms
abbrev base := atomicLeft B.atoms false
abbrev aux := atomicLeft B.atoms true
abbrev diagonal := (B.input false).diagonal
abbrev expectation := B.amalgam.expectation false

theorem amalgam_diagonal_false : B.amalgam.diagonal false = matrixDiagonalHom B.diagonal := rfl

theorem amalgam_diagonal_true : B.amalgam.diagonal true =
    matrixDiagonalHom (fun _ => StarAlgHom.id ℂ SequenceDiagonal) := rfl

theorem diagonal_agree (x : Bool → SequenceDiagonal) :
    B.base (matrixDiagonalHom B.diagonal x) =
      B.aux (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ SequenceDiagonal) x) :=
by
  rw [← B.amalgam_diagonal_false, ← B.amalgam_diagonal_true]
  unfold base aux
  exact B.amalgam.left_agree false true x

abbrev letter := bridgeLetter B.aux

def matrixPeak (i : Bool) (n : ℕ) : CStarMatrix Bool Bool A := matrixSingle i i (B.peak i n)

end PeakingPairData

open Filter Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

local instance modelPartialOrder : PartialOrder B.Model := CStarAlgebra.spectralOrder _
local instance modelStarOrderedRing : StarOrderedRing B.Model := CStarAlgebra.spectralOrderedRing _

abbrev embedBase := atomicEmbedding B.atoms false
abbrev embedAux := atomicEmbedding B.atoms true
abbrev modelLetter := bridgeLetter B.embedAux

@[simp] theorem coe_embedBase (a : CStarMatrix Bool Bool A) :
    (B.embedBase a : B.Operators) = B.base a := rfl

@[simp] theorem coe_embedAux (a : CStarMatrix Bool Bool SequenceDiagonal) :
    (B.embedAux a : B.Operators) = B.aux a := rfl

@[simp] theorem coe_modelLetter (i : Bool) :
    (B.modelLetter i : B.Operators) = B.letter i := rfl

theorem model_diagonal_agree (x : Bool → SequenceDiagonal) :
    B.embedBase (matrixDiagonalHom B.diagonal x) =
      B.embedAux (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ SequenceDiagonal) x) := by
  apply Subtype.ext
  exact B.diagonal_agree x

end PeakingPairData

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder

open Filter Topology
open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder

open Filter Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

abbrev matrixState (i : Bool) := NaimarkZFC.matrixState (B.state i) i
abbrev matrixPeaks (i : Bool) : Peaks (B.matrixPeak i) (B.matrixState i) :=
  (B.peaks i).matrix (B.peak_zero i) i
abbrev matrixPure (i : Bool) : IsPureState (B.matrixState i) := (B.matrixPeaks i).isPureState

variable {B}
  {ι : Type*}
  [Preorder ι]

def Separated : Prop := ∀ i j : Bool, i ≠ j →
  ¬ UnitarilyEquivalent (pureGNS (B.matrixState i) (B.matrixPure i))
    (pureGNS (B.matrixState j) (B.matrixPure j))

end PeakingPairData

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]
  [PartialOrder A] [StarOrderedRing A]

variable (e : A) (he : IsStarProjection e)

def cornerLiftState (g : CStarCorner e he →L[ℂ] ℂ) : A →L[ℂ] ℂ :=
  g.comp (cornerCompression e he)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem cornerLiftState_apply (g : CStarCorner e he →L[ℂ] ℂ) (a : A) :
    cornerLiftState e he g a = g (cornerCompression e he a) := rfl

end

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_HNN
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_cstar _root_.OAI.NaimarkZFC.hnnGeneratedCStar _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

abbrev Corner := MatrixHNNCorner B.embedBase
abbrev cornerBase := matrixCornerBase B.embedBase

abbrev stableUnitary : unitary B.Corner :=
  matrixStableUnitary B.embedBase B.embedAux
    (matrixDiagonal_units B.embedBase B.embedAux B.diagonal B.model_diagonal_agree)

end PeakingPairData

open scoped CStarAlgebra Matrix
section
variable {A Z : Type*} [CStarAlgebra A] [CStarAlgebra Z]
    (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)

def matrixCornerEntry (i j : Bool) : Z →L[ℂ] MatrixHNNCorner φ where
  toFun z := ⟨φ (matrixSingle false i 1) * z * φ (matrixSingle j false 1), by
    constructor
    · change φ (matrixSingle false false 1) * (φ _ * z * φ _) = _
      rw [← mul_assoc, ← mul_assoc, ← map_mul, matrixSingle_mul, one_mul]
    · change (φ _ * z * φ _) * φ (matrixSingle false false 1) = _
      rw [mul_assoc, ← map_mul, matrixSingle_mul, one_mul]⟩
  map_add' x y := Subtype.ext (by dsimp; simp only [mul_add,add_mul])
  map_smul' c z := Subtype.ext (by dsimp; simp only [mul_smul_comm, smul_mul_assoc])
  cont := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_id).mul continuous_const

@[simp] theorem matrixCornerEntry_coe (i j : Bool) (z : Z) :
    (matrixCornerEntry φ i j z : Z) =
      φ (matrixSingle false i 1) * z * φ (matrixSingle j false 1) := rfl

@[simp] theorem matrixCornerEntry_corner (z : MatrixHNNCorner φ) :
    matrixCornerEntry φ false false (z : Z) = z := by
  apply Subtype.ext
  exact (congrArg (· * matrixCornerProjection φ) z.2.1).trans z.2.2

theorem matrix_diag_sum_one :
    matrixSingle false false (1:A) + matrixSingle true true 1 = 1 := by
  ext i j
  cases i <;> cases j <;> simp [matrixSingle_apply]

@[simp] theorem matrixCornerEntry_star (i j : Bool) (x : Z) :
    matrixCornerEntry φ i j (star x) = star (matrixCornerEntry φ j i x) := by
  apply Subtype.ext
  change φ (matrixSingle false i 1) * star x * φ (matrixSingle j false 1) =
    star (φ (matrixSingle false j 1) * x * φ (matrixSingle i false 1))
  simp only [star_mul, ← map_star, matrixSingle_star, star_one, mul_assoc]

theorem matrixSingle_sandwich (i j : Bool) (M : CStarMatrix Bool Bool A) :
    matrixSingle false i 1 * M * matrixSingle j false 1 =
      matrixSingle false false (M i j) := by
  calc
    _ = matrixSingle false i 1 *
        (matrixSingle i i 1 * M * matrixSingle j j 1) * matrixSingle j false 1 := by
      symm
      calc
        _ = (matrixSingle false i 1 * matrixSingle i i 1) * M *
            (matrixSingle j j 1 * matrixSingle j false 1) := by simp only [mul_assoc]
        _ = _ := by rw [matrixSingle_mul,matrixSingle_mul,one_mul]
    _ = _ := by
      rw [matrixSingle_compress,one_mul,mul_one,matrixSingle_mul,one_mul,
        matrixSingle_mul,mul_one]

@[simp] theorem matrixCornerEntry_base (i j : Bool) (M : CStarMatrix Bool Bool A) :
    matrixCornerEntry φ i j (φ M) = matrixCornerBase φ (M i j) := by
  apply Subtype.ext
  change φ (matrixSingle false i 1) * φ M * φ (matrixSingle j false 1) =
    φ (matrixSingle false false (M i j))
  rw [← map_mul, ← map_mul, matrixSingle_sandwich]

@[simp] theorem matrixCornerEntry_one (i j : Bool) :
    matrixCornerEntry φ i j 1 = matrixCornerBase φ ((1 : CStarMatrix Bool Bool A) i j) := by
  rw [← map_one φ, matrixCornerEntry_base]

end

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped InnerProductSpace lp

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open scoped ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace
open UniformSpace

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open Topology

open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule CStarAlgebra

open Topology

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

open Topology

end NaimarkZFC

end

end OAI
end


