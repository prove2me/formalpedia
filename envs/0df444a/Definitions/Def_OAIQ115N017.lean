-- Prove2me | Definitions.Def_OAIQ115N017
-- name    : OAIQ115N017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:40:33.66897+00:00
-- url     : https://prove2.me/theorems/ab78faa3-9c65-4592-a23c-cd5aac78992f
-- title:
--   Definitions bundle OAIQ115N017 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 35 declarations of OpenAI's Lean: 4 definitions and 31 theorems. The definitions and types are `OAI.NaimarkZFC.PeakingPairData.expectCorner`, `OAI.NaimarkZFC.PeakingPairData.modelExpectation`, `OAI.NaimarkZFC.PeakingPairData.otherEndpoint`, `OAI.NaimarkZFC.PeakingPairData.peakEndpoint`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean), [`Naimark_Homogeneity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Homogeneity.lean), [`Naimark_Peaking`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Peaking.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N014` and `OAIQ115N015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N023`, `OAIQ115N024` and `OAIQ115N029`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N014
import Definitions.Def_OAIQ115N015

section
-- module Solutions.OAIQ115_Naimark.Naimark_Peaking
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.PeakingPairData.hnnCStar _root_.OAI.NaimarkZFC.PeakingPairData.modelCornerCStarAlgebra _root_.OAI.NaimarkZFC.constructionIndex_nonempty _root_.OAI.NaimarkZFC.omittedAlgebra_isClosed _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_isClosed _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_cstar _root_.OAI.NaimarkZFC.hnnGeneratedCStar _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped ComplexOrder CStarAlgebra

open Filter Topology
open scoped ComplexOrder CStarAlgebra OnePoint
section
variable {A n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n] [Nonempty n]

variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)
  (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ k, 0 < (τ (peakAtom p k)).re)

theorem matrix_peakingCoefficients (i : n) (M : CStarMatrix n n A) :
    peakingCoefficients (hp.matrix hp0 i) (matrixTraceState τ hτ)
      (matrixTraceState_isState τ hτ) (matrix_peakAtom_positive τ hτ hpos i) M =
      peakingCoefficients hp τ hτ hpos (M i i) := by
  ext t
  induction t using OnePoint.rec with
  | infty => rfl
  | coe k =>
    rw [peakingCoefficients_nat,peakingCoefficients_nat,matrix_peakAtom]
    exact matrix_cornerState τ hτ i _ M

end

section
variable {A n ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n] [Nonempty n] [Preorder ι]
  {p : n → ℕ → A} {f : n → A →L[ℂ] ℂ}
  (hp : ∀ j, Peaks (p j) (f j)) (hp0 : ∀ j, p j 0 = 1)
  (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ j k, 0 < (τ (peakAtom (p j) k)).re)

theorem matrix_endpoint_decay (i : n) (M : ι → CStarMatrix n n A)
    (ht : Tendsto (fun k => peakingCoefficients ((hp i).matrix (hp0 i) i)
      (matrixTraceState τ hτ) (matrixTraceState_isState τ hτ)
      (matrix_peakAtom_positive τ hτ (hpos i) i) (M k)) atTop (𝓝 0)) :
    Tendsto (fun k => matrixDiagonalExpectation
      (fun j => peakingCoefficients (hp j) τ hτ (hpos j))
      (fun j a => peakingCoefficientsFun_norm_le (hp j) τ hτ (hpos j) a)
      (matrixSingle i i 1 * M k * matrixSingle i i 1)) atTop (𝓝 0) := by
  have ht' : Tendsto (fun k => peakingCoefficients (hp i) τ hτ (hpos i) (M k i i))
      atTop (𝓝 0) := by
    simpa only [matrix_peakingCoefficients (hp i) (hp0 i) τ hτ (hpos i)] using ht
  apply tendsto_pi_nhds.mpr
  intro j
  change Tendsto (fun k => peakingCoefficients (hp j) τ hτ (hpos j)
    (((matrixSingle i i (1 : A) * M k * matrixSingle i i (1 : A)) : CStarMatrix n n A) j j)) atTop (𝓝 0)
  simp only [matrixSingle_compress,one_mul,mul_one,matrixSingle_apply,and_self]
  by_cases hji : i = j
  · subst j
    simpa only [ite_true, if_true] using ht'
  · simpa only [hji,ite_false, if_false,map_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : SequenceDiagonal)) atTop (𝓝 0))

end

open Filter Topology
open scoped ComplexOrder
section
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
  (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]
  {Δ : Type*} [CStarAlgebra Δ] (c : AtomicAmalgamData (Δ := Δ) d)

omit [DecidableEq V] in

theorem atomicLeft_expectation_bound {i j : I} (hij : i ≠ j) (a : A i) :
    ‖atomicLeft d i a * fockStartProjection (AtomicLetters d) j‖ ≤
      Real.sqrt ‖c.expectation i (star a*a)‖ := by
  apply atomicLeft_start_bound d hij a _ (Real.sqrt_nonneg _)
  intro r
  rw [Real.sq_sqrt (norm_nonneg _), atomicExpectation_corner_formula d c]
  have hp := (d i).trace.map_nonneg ((d i).atom r).2.nonneg
  rw [Complex.mul_re, ← hp.2, Complex.zero_im, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_right
    ((Complex.re_le_norm _).trans (atomicCoordinate_norm_le d c _ r)) ((d i).positive r).le

end

open Filter Topology
section
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
  (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]
  {Δ : Type*} [CStarAlgebra Δ] (c : AtomicAmalgamData (Δ := Δ) d)
  {ι : Type*} {l : Filter ι}

omit [DecidableEq V] in

theorem atomicLeft_endpoint_tendsto {i j : I} (hij : i ≠ j) (a : ι → A i)
    (ha : Tendsto (fun k => c.expectation i (star (a k)*a k)) l (𝓝 0)) :
    Tendsto (fun k => atomicLeft d i (a k)*fockStartProjection (AtomicLetters d) j)
      l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun k => norm_nonneg _) (fun k => atomicLeft_expectation_bound d c hij (a k))
  simpa only [norm_zero, Real.sqrt_zero] using ha.norm.sqrt

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint
section
variable {A n ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n] [Nonempty n] [Preorder ι]
  {p : n → ℕ → A} {f : n → A →L[ℂ] ℂ}
  (hp : ∀ j, Peaks (p j) (f j)) (hp0 : ∀ j, p j 0 = 1)
  (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ j k, 0 < (τ (peakAtom (p j) k)).re)

theorem matrix_excision_square_endpoint
    (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (i : n)
    (h : CStarMatrix n n A →L[ℂ] ℂ) (hh : IsPureState h)
    (x : ι → CStarMatrix n n A) (hx : ∀ k, 0 ≤ x k) (hxn : ∀ k, ‖x k‖ ≤ 1)
    (hm : Antitone x)
    (htrace : Tendsto (fun k => matrixTraceState τ hτ (x k)) atTop (𝓝 0))
    (hexc : ∀ b : CStarMatrix n n A,
      Tendsto (fun k => x k*(b-h b • (1:CStarMatrix n n A))*x k) atTop (𝓝 0))
    (a : CStarMatrix n n A)
    (hcase : ¬ UnitarilyEquivalent (pureGNS h hh)
        (pureGNS (matrixState (f i) i) ((hp i).matrix (hp0 i) i).isPureState) ∨
      h = matrixState (f i) i ∧ matrixState (f i) i a = 0) :
    Tendsto (fun k => matrixPeakingExpectation hp τ hτ hpos
      (star (x k*a*matrixSingle i i 1)*(x k*a*matrixSingle i i 1))) atTop (𝓝 0) := by
  have ht := peaking_endpoint_of_excision ((hp i).matrix (hp0 i) i) h hh
    (matrixTraceState τ hτ) (matrixTraceState_isState τ hτ)
    (matrixTraceState_tracial τ hτ htr)
    (matrix_peakAtom_positive τ hτ (hpos i) i) x hx hxn hm htrace hexc a hcase
  have hwhole := matrix_endpoint_decay hp hp0 τ hτ hpos i
    (fun k => star a*(x k*x k)*a) ht
  have he (k : ι) : star (x k*a*matrixSingle i i (1:A))*(x k*a*matrixSingle i i (1:A)) =
      matrixSingle i i (1:A)*(star a*(x k*x k)*a)*matrixSingle i i (1:A) := by
    rw [star_mul,star_mul,matrixSingle_star,star_one,(IsSelfAdjoint.of_nonneg (hx k)).star_eq]
    simp only [mul_assoc]
  simpa only [he,matrixPeakingExpectation] using hwhole

omit [DecidableEq n] [Nonempty n] in

theorem matrix_centered_state_zero (a : CStarMatrix n n A)
    (ha : matrixPeakingExpectation hp τ hτ hpos a = 0) (i : n) :
    matrixState (f i) i a = 0 := by
  have he : peakingCoefficients (hp i) τ hτ (hpos i) (a i i) = 0 := congrFun ha i
  exact congrArg (fun g : SequenceDiagonal => g ∞) he

end

open Filter Topology

open Filter Topology

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

include hd in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
theorem bridgeLetter_support_left (i : Bool) :
    bridgeSupport φ i * bridgeLetter ψ i = bridgeLetter ψ i := by
  rw [bridgeSupport,matrixDiagonal_units φ ψ δ hd,bridgeLetter,← map_mul,
    matrixSingle_mul,one_mul]

include hd in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
theorem bridgeLetter_support_right (i : Bool) :
    bridgeLetter ψ i * bridgeSupport φ (!i) = bridgeLetter ψ i := by
  rw [bridgeSupport,matrixDiagonal_units φ ψ δ hd,bridgeLetter,← map_mul,
    matrixSingle_mul,mul_one]

theorem bridgeSupport_norm (i : Bool) : ‖bridgeSupport φ i‖ ≤ 1 :=
  (NonUnitalStarAlgHom.norm_apply_le _ _).trans
    ((matrixSingle_projection i (1:A) (by constructor <;> simp [IsIdempotentElem,IsSelfAdjoint])).norm_le _)

end

open Filter Topology
open scoped OnePoint ComplexOrder CStarAlgebra

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

namespace PeakingPairData
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

attribute [local instance] OAI.NaimarkZFC.PeakingPairData.matrixFamilyStarOrder
theorem core_zero (w : BridgeCore (CStarMatrix Bool Bool A))
    (hw : w.Centered (fun a => B.expectation a = 0)) :
    (1-B.start)*w.eval B.base B.letter*(1-B.start) = 0 := by
  unfold start letter base aux bridgeLetter
  exact B.amalgam.core_zero (by decide : false ≠ true)
      (fun i => matrixSingle i (!i) (1:SequenceDiagonal)) B.letter_centered w hw

end PeakingPairData

open Filter Topology
open scoped CStarAlgebra ComplexOrder

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

variable {B} {ι : Type*} [Preorder ι] (X : B.Endpoint ι)

theorem Endpoint.cut (i : Bool) (a : CStarMatrix Bool Bool A)
    (ha : X.tag ≠ some i ∨ B.matrixState i a = 0) :
    Tendsto (fun k => B.base (X.net k)*B.base a*B.support i*B.start) atTop (𝓝 0) := by
  have hcase : ¬ UnitarilyEquivalent (pureGNS X.state X.pure)
      (pureGNS (B.matrixState i) (B.matrixPure i)) ∨
      X.state = B.matrixState i ∧ B.matrixState i a = 0 := by
    by_cases h : X.tag = some i
    · exact Or.inr ⟨X.matchedState i h, ha.resolve_left (not_not.mpr h)⟩
    · exact Or.inl (X.unmatched i h)
  have ht := matrix_excision_square_endpoint B.peaks B.peak_zero (positiveCLM B.trace)
    (positiveCLM_isState B.trace B.normalized) B.atom_positive B.tracial i
    X.state X.pure X.net X.positive X.contractive X.antitone X.trace_null X.excision a hcase
  have he : Tendsto (fun k => B.expectation
      (star (X.net k*a*matrixSingle i i (1:A))*(X.net k*a*matrixSingle i i (1:A)))) atTop (𝓝 0) := by
    simpa only [B.expectation_eq] using ht
  have hb := atomicLeft_endpoint_tendsto B.atoms B.amalgam (by decide : false ≠ true)
    (fun k => X.net k*a*matrixSingle i i (1:A)) he
  simpa only [map_mul, support, bridgeSupport, base, start] using hb

theorem Endpoint.cut_right (i : Bool) (a : CStarMatrix Bool Bool A)
    (ha : X.tag ≠ some i ∨ B.matrixState i a = 0) :
    Tendsto (fun k => B.start*(B.support i*B.base a*B.base (X.net k))) atTop (𝓝 0) := by
  let : ContinuousStar B.Operators := ⟨ContinuousLinearMap.adjoint.continuous⟩
  have ha' : X.tag ≠ some i ∨ B.matrixState i (star a) = 0 := by
    rcases ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr (by rw [state_map_star _ (B.matrixPure i).1,ha,star_zero])
  have ht := (X.cut i (star a) ha').star
  have he (k : ι) : star (B.base (X.net k)*B.base (star a)*B.support i*B.start) =
      B.start*(B.support i*B.base a*B.base (X.net k)) := by
    rw [star_mul,star_mul,star_mul,(fockStartProjection_isProjection _ _).isSelfAdjoint.star_eq]
    rw [show star (B.support i) = B.support i from
      (IsStarProjection.map (matrixSingle_projection i (1:A) (by
        constructor <;> simp [IsIdempotentElem,IsSelfAdjoint])) B.base).isSelfAdjoint.star_eq]
    rw [← map_star,star_star,← map_star,(IsSelfAdjoint.of_nonneg (X.positive k)).star_eq]
    simp only [mul_assoc]
  rw [show star (0 : B.Operators) = 0 from map_zero ContinuousLinearMap.adjoint] at ht
  simpa only [he] using ht

variable (B) in
theorem matrixPeak_trace_null (i : Bool) :
    Tendsto (fun n => B.matrixTrace (B.matrixPeak i n)) atTop (𝓝 0) := by
  have he (n : ℕ) : B.trace (B.peak i n) = ((B.trace (B.peak i n)).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (B.trace.map_nonneg ((B.peaks i).1 n).nonneg).2.symm
  have ht : Tendsto (fun n => B.trace (B.peak i n)) atTop (𝓝 0) := by
    have ht := (Complex.continuous_ofReal.tendsto 0).comp (B.trace_null i)
    exact ht.congr' (Eventually.of_forall (fun n => (he n).symm))
  simpa only [matrixTrace,matrixPeak,matrixTraceState_single,positiveCLM_apply,smul_zero] using
    ht.const_smul (Fintype.card Bool : ℝ)⁻¹

variable (B) in

def peakEndpoint (hs : B.Separated) (i : Bool) : B.Endpoint ℕ where
  state := B.matrixState i
  pure := B.matrixPure i
  net := B.matrixPeak i
  positive n := ((B.matrixPeaks i).1 n).nonneg
  contractive n := ((B.matrixPeaks i).1 n).norm_le _
  antitone := (B.matrixPeaks i).2.1
  excision a := tendsto_zero_iff_norm_tendsto_zero.mpr ((B.matrixPeaks i).excision a)
  trace_null := B.matrixPeak_trace_null i
  peakIndex := id
  peak_tendsto := tendsto_id
  tag := some i
  matchedState j hj := by cases Option.some.inj hj; rfl
  matchedNet j hj := by cases Option.some.inj hj; intro; rfl
  unmatched j hj := hs i j (fun h => hj (congrArg some h))

end PeakingPairData

open Filter Topology
open scoped CStarAlgebra ComplexOrder

namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem centered_state_zero (a : CStarMatrix Bool Bool A) (ha : B.expectation a = 0)
    (i : Bool) : B.matrixState i a = 0 := by
  exact matrix_centered_state_zero B.peaks (positiveCLM B.trace)
    (positiveCLM_isState B.trace B.normalized) B.atom_positive a
    (by simpa only [B.expectation_eq] using ha) i

variable {B} {ι κ : Type*} [Preorder ι] [Preorder κ]
  [IsDirectedOrder ι] [IsDirectedOrder κ] [Nonempty ι] [Nonempty κ]
  (X : B.Endpoint ι) (Y : B.Endpoint κ)

theorem Endpoint.wordData (hs : B.Separated)
    (hex : ∀ i, X.tag = some i → Y.tag ≠ some (!i)) :
    BridgeDecayData B.base B.letter B.support B.start (fun a => B.expectation a = 0)
      (l := atTop) B.matrixState (fun k : ι × κ => B.base (X.net k.1))
      (fun k : ι × κ => B.base (Y.net k.2))
      (fun i k => B.base (B.matrixPeak i (X.peakIndex k.1)))
      (fun i k => B.base (B.matrixPeak i (Y.peakIndex k.2))) X.tag Y.tag where
  normX k := (NonUnitalStarAlgHom.norm_apply_le B.base _).trans (X.contractive _)
  normY k := (NonUnitalStarAlgHom.norm_apply_le B.base _).trans (Y.contractive _)
  normPX i k := (NonUnitalStarAlgHom.norm_apply_le B.base _).trans (((B.matrixPeaks i).1 _).norm_le _)
  normPY i k := (NonUnitalStarAlgHom.norm_apply_le B.base _).trans (((B.matrixPeaks i).1 _).norm_le _)
  normState i := ((isState_iff _).mp (B.matrixPure i).1).1
  matchedX i hi k := congrArg B.base (X.matchedNet i hi k.1)
  matchedY i hi k := congrArg B.base (Y.matchedNet i hi k.2)
  transferX i k := B.peak_transfer i (X.peakIndex k.1)
  transferY i k := (B.peak_transfer i (Y.peakIndex k.2)).symm
  exclude := hex
  cutX i a ha := (X.cut i a ha).comp top_fst
  cutY i a ha := (Y.cut_right i a ha).comp top_snd
  cutPX j i a ha := ((B.peakEndpoint hs j).cut i a (Or.inr (B.centered_state_zero a ha i))).comp
    (X.peak_tendsto.comp top_fst)
  cutPY j i a ha := ((B.peakEndpoint hs j).cut_right i a (Or.inr (B.centered_state_zero a ha i))).comp
    (Y.peak_tendsto.comp top_snd)
  crossX i a _ hj := by
    let hp := B.peakEndpoint hs (!i)
    have ht := state_cross_excision hp.state Y.state hp.pure Y.pure hp.net Y.net
      hp.positive hp.contractive Y.positive Y.contractive Y.antitone hp.excision Y.excision
      (fun h => Y.unmatched (!i) hj h.symm) a
    have hc : Tendsto (fun k : ι × κ => (X.peakIndex k.1,k.2)) atTop atTop :=
      top_pair (X.peak_tendsto.comp top_fst) top_snd
    have ho := ((map_continuous B.base).tendsto 0).comp (ht.comp hc)
    simpa only [Function.comp_def,hp,peakEndpoint,map_zero,map_mul] using ho
  crossY i a _ hi := by
    let hp := B.peakEndpoint hs i
    have ht := state_cross_excision X.state hp.state X.pure hp.pure X.net hp.net
      X.positive X.contractive hp.positive hp.contractive hp.antitone X.excision hp.excision
      (X.unmatched i hi) a
    have hc : Tendsto (fun k : ι × κ => (k.1,Y.peakIndex k.2)) atTop atTop :=
      top_pair top_fst (Y.peak_tendsto.comp top_snd)
    have ho := ((map_continuous B.base).tendsto 0).comp (ht.comp hc)
    simpa only [Function.comp_def,hp,peakEndpoint,map_zero,map_mul] using ho
  rectangle i a ha := by
    have ht := (B.matrixPeaks i).rectangular_excision a (B.centered_state_zero a ha i)
    have hc : Tendsto (fun k : ι × κ => (X.peakIndex k.1,Y.peakIndex k.2)) atTop atTop :=
      top_pair (X.peak_tendsto.comp top_fst)
        (Y.peak_tendsto.comp top_snd)
    have ho := ((map_continuous B.base).tendsto 0).comp (ht.comp hc)
    simpa only [Function.comp_def,map_zero,map_mul] using ho

theorem Endpoint.word_decay (hs : B.Separated)
    (hex : ∀ i, X.tag = some i → Y.tag ≠ some (!i))
    (w : BridgeCore (CStarMatrix Bool Bool A))
    (hw : w.Centered (fun a => B.expectation a = 0)) (a c : CStarMatrix Bool Bool A) :
    Tendsto (fun k : ι × κ => B.base (X.net k.1)*B.base a*w.eval B.base B.letter*
      B.base c*B.base (Y.net k.2)) atTop (𝓝 0) := by
  exact bridge_word_decay B.base B.letter B.support B.start
    (fockStartProjection_isProjection _ _) (bridgeLetter_support_left B.base B.aux B.diagonal B.diagonal_agree)
    (bridgeLetter_support_right B.base B.aux B.diagonal B.diagonal_agree) (bridgeSupport_norm B.base)
    (fun a => B.expectation a = 0) B.core_zero (X.wordData Y hs hex) w hw a c

end PeakingPairData

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule

open Filter Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {B : PeakingPairData A} {ι κ : Type*} [Preorder ι] [Preorder κ]
  [IsDirectedOrder ι] [IsDirectedOrder κ] [Nonempty ι] [Nonempty κ]
  (X : B.Endpoint ι) (Y : B.Endpoint κ)

theorem Endpoint.model_word_decay (hs : B.Separated)
    (hex : ∀ i, X.tag = some i → Y.tag ≠ some (!i))
    (w : BridgeCore (CStarMatrix Bool Bool A))
    (hw : w.Centered (fun a => B.expectation a = 0)) (a c : CStarMatrix Bool Bool A) :
    Tendsto (fun k : ι × κ => B.embedBase (X.net k.1)*B.embedBase a*
      w.eval B.embedBase B.modelLetter*B.embedBase c*B.embedBase (Y.net k.2)) atTop (𝓝 0) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun k : ι × κ => B.base (X.net k.1)*B.base a*
    (↑(w.eval B.embedBase B.modelLetter : B.Model) : B.Operators)*B.base c*B.base (Y.net k.2))
    atTop (𝓝 0)
  simpa only [B.coe_core] using X.word_decay Y hs hex w hw a c

theorem Endpoint.unique_matrix_extension (hs : B.Separated)
    (hval : ∀ k, X.state (X.net k) = 1)
    (g₁ g₂ : B.Model →L[ℂ] ℂ) (hg₁ : IsState g₁) (hg₂ : IsState g₂)
    (hr₁ : restrictState B.embedBase g₁ = X.state)
    (hr₂ : restrictState B.embedBase g₂ = X.state) : g₁ = g₂ := by
  let W : Set B.Model := {z | ∃ (w : BridgeCore (CStarMatrix Bool Bool A))
    (a c : CStarMatrix Bool Bool A), w.Centered (fun d => B.expectation d = 0) ∧
      z = B.embedBase a*w.eval B.embedBase B.modelLetter*B.embedBase c}
  apply unique_extension_of_dense_word_decay (l := atTop) B.embedBase X.state W B.model_words_dense
    X.net X.contractive (fun k => IsSelfAdjoint.of_nonneg (X.positive k)) hval ?_
    g₁ g₂ hg₁ hg₂ hr₁ hr₂
  rintro z ⟨w,a,c,hw,rfl⟩
  have hex : ∀ i, X.tag = some i → X.tag ≠ some (!i) := by
    intro i hi
    rw [hi]
    cases i <;> simp
  have ht := (X.model_word_decay X hs hex w hw a c).comp tendsto_atTop_diagonal
  simpa only [Function.comp_def,mul_assoc] using ht

end PeakingPairData

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

def otherEndpoint (f : CStarMatrix Bool Bool A →L[ℂ] ℂ) (hf : IsPureState f)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ p : CStarMatrix Bool Bool A,
      IsStarProjection p ∧ pureGNS f hf p ≠ 0 ∧ (B.matrixTrace p).re < ε)
    (hne : ∀ i, ¬ UnitarilyEquivalent (pureGNS f hf)
      (pureGNS (B.matrixState i) (B.matrixPure i))) : B.Endpoint (B.pureIndex f hf) :=
  let π := pureGNS f hf
  let ξ := gnsVector (positiveOfSquares f hf.1.2)
  have hπ := pure_gns_irreducible f hf.1 hf
  have hξ : ‖ξ‖ = 1 := gnsVector_norm_eq_one _ ((isState_iff f).mp hf.1).1
  have ht : Tendsto (fun k : B.pureIndex f hf => k.1) atTop atTop := by
    rw [← prod_atTop_atTop_eq]; exact tendsto_fst
  { state := f
    pure := hf
    net := fun k => pureExcisionNet π ξ k.1
    positive k := pureExcisionNet_nonneg π ξ k.1
    contractive k := pureExcisionNet_norm π ξ k.1
    antitone := fun _ _ h => (pureExcisionNet_antitone π ξ) h.1
    excision a := by
      have he := (pureExcisionNet_excision π hπ ξ hξ a).comp ht
      have hc (a) : ⟪ξ, π a ξ⟫_ℂ = f a := gnsVector_coefficient _ a
      simpa only [Function.comp_def,hc] using he
    trace_null := by
      apply (pureExcisionNet_trace_null π hπ ξ hξ B.matrixTrace
        (matrixTraceState_isState (positiveCLM B.trace)
          (positiveCLM_isState B.trace B.normalized)) ?_ hsmall).comp ht
      intro M N
      exact matrixTraceState_tracial (positiveCLM B.trace)
        (positiveCLM_isState B.trace B.normalized) B.tracial M N
    peakIndex := Prod.snd
    peak_tendsto := by rw [← prod_atTop_atTop_eq]; exact tendsto_snd
    tag := none
    matchedState i hi := by cases hi
    matchedNet i hi := by cases hi
    unmatched i _ := hne i }

theorem otherEndpoint_value_one (f : CStarMatrix Bool Bool A →L[ℂ] ℂ) (hf : IsPureState f)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ p : CStarMatrix Bool Bool A,
      IsStarProjection p ∧ pureGNS f hf p ≠ 0 ∧ (B.matrixTrace p).re < ε)
    (hne : ∀ i, ¬ UnitarilyEquivalent (pureGNS f hf)
      (pureGNS (B.matrixState i) (B.matrixPure i))) (k : B.pureIndex f hf) :
    (B.otherEndpoint f hf hsmall hne).state ((B.otherEndpoint f hf hsmall hne).net k) = 1 := by
  let F := positiveOfSquares f hf.1.2
  have hh := pureExcisionNet_fixes (pureGNS f hf) (map_one F.gnsStarAlgHom) (gnsVector F) k.1
  change f (pureExcisionNet (pureGNS f hf) (gnsVector F) k.1) = 1
  change F (pureExcisionNet (pureGNS f hf) (gnsVector F) k.1) = 1
  rw [← gnsVector_coefficient F]
  change ⟪gnsVector F,pureGNS f hf (pureExcisionNet (pureGNS f hf) (gnsVector F) k.1)
    (gnsVector F)⟫_ℂ = 1
  rw [hh,inner_self_eq_norm_sq_to_K,gnsVector_norm_eq_one F ((isState_iff f).mp hf.1).1]
  norm_num

end PeakingPairData

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem supported_small_projections (hA : IsSimpleCStar A)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) (i : Bool) :
    ∀ ε : ℝ, 0 < ε → ∃ p : CStarMatrix Bool Bool A,
      IsStarProjection p ∧
      pureGNS (NaimarkZFC.matrixState f i) (matrixState_isPureState f hf i) p ≠ 0 ∧
      (B.matrixTrace p).re < ε := by
  let π := pureGNS (NaimarkZFC.matrixState f i) (matrixState_isPureState f hf i)
  have hinj := simple_matrix_corner_injective hA π i (matrix_pure_corner_ne_zero f hf i)
  have he (n : ℕ) : (B.matrixTrace (matrixSingle i i (B.peak false n))).re =
      (Fintype.card Bool : ℝ)⁻¹ * (B.trace (B.peak false n)).re := by
    simp only [matrixTrace,matrixTraceState_single,positiveCLM_apply]
    exact Complex.smul_re _ _
  have ht : Tendsto (fun n => (B.matrixTrace (matrixSingle i i (B.peak false n))).re)
      atTop (𝓝 0) := by
    simpa only [he,mul_zero] using (B.trace_null false).const_mul (Fintype.card Bool : ℝ)⁻¹
  intro ε hε
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨matrixSingle i i (B.peak false n),
    matrixSingle_projection i _ ((B.peaks false).1 n), ?_, hn⟩
  apply matrixSingle_representation_ne_zero π i hinj
  intro hp
  have hv := (B.peaks false).2.2.2.1 n
  rw [hp,map_zero] at hv
  exact zero_ne_one hv

end PeakingPairData

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem matrix_unique_of_small (hs : B.Separated)
    (f : CStarMatrix Bool Bool A →L[ℂ] ℂ) (hf : IsPureState f)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ p : CStarMatrix Bool Bool A,
      IsStarProjection p ∧ pureGNS f hf p ≠ 0 ∧ (B.matrixTrace p).re < ε) :
    StateExtensionUnique B.embedBase f := by
  classical
  by_cases he : ∃ i, UnitarilyEquivalent (pureGNS (B.matrixState i) (B.matrixPure i))
      (pureGNS f hf)
  · obtain ⟨i,hi⟩ := he
    have hu : StateExtensionUnique B.embedBase (B.matrixState i) :=
      (B.peakEndpoint hs i).unique_matrix_extension hs (fun n => (B.matrixPeaks i).2.2.2.1 n)
    exact hu.of_equivalent (B.matrixPure i) hf hi
  · have hne : ∀ i, ¬ UnitarilyEquivalent (pureGNS f hf)
        (pureGNS (B.matrixState i) (B.matrixPure i)) := by
      intro i hi
      exact he ⟨i, UnitarilyEquivalent.symm hi⟩
    exact (B.otherEndpoint f hf hsmall hne).unique_matrix_extension hs
      (B.otherEndpoint_value_one f hf hsmall hne)

theorem supported_matrix_unique (hs : B.Separated) (hA : IsSimpleCStar A)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) (i : Bool) :
    StateExtensionUnique B.embedBase (NaimarkZFC.matrixState f i) :=
  B.matrix_unique_of_small hs _ (matrixState_isPureState f hf i)
    (B.supported_small_projections hA f hf i)

end PeakingPairData

open scoped CStarAlgebra ComplexOrder

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

theorem corner_unique (hs : B.Separated) (hA : IsSimpleCStar A)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) : StateExtensionUnique B.cornerBase f :=
  corner_unique_of_matrix B.embedBase f (B.supported_matrix_unique hs hA f hf false)

end PeakingPairData

open scoped CStarAlgebra Matrix

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C)
  (E : C →L[ℂ] CStarMatrix Bool Bool A)

theorem matrixCornerExpectation_base (hfix : ∀ a, E (φ a) = a) (a : A) :
    matrixCornerExpectation φ E (matrixCornerBase φ a) = a := by
  change E (φ (matrixSingle false false a)) false false = a
  rw [hfix,matrixSingle_apply,ite_eq_left ⟨rfl,rfl⟩]

theorem matrixCornerExpectation_supported
    (hleft : ∀ a x, E (φ a*x) = a*E x)
    (hright : ∀ x a, E (x*φ a) = E x*a) (x : MatrixHNNCorner φ) :
    E (x:C) = matrixSingle false false (matrixCornerExpectation φ E x) := by
  have h := x.property
  have hcomp : φ (matrixSingle false false (1:A))*(x:C)*
      φ (matrixSingle false false (1:A)) = (x:C) := by
    exact (congrArg (· * matrixCornerProjection φ) h.1).trans h.2
  calc
    _ = E (φ (matrixSingle false false (1:A))*(x:C)*
      φ (matrixSingle false false (1:A))) := congrArg E hcomp.symm
    _ = matrixSingle false false (1:A)*E (x:C)*matrixSingle false false (1:A) := by
      rw [hright,hleft]
    _ = _ := by rw [matrixSingle_compress,one_mul,mul_one]; rfl

theorem matrixCornerExpectation_faithful
    (hleft : ∀ a x, E (φ a*x) = a*E x)
    (hright : ∀ x a, E (x*φ a) = E x*a)
    (hfaith : ∀ x, E (star x*x) = 0 → x = 0)
    (x : MatrixHNNCorner φ) (hx : matrixCornerExpectation φ E (star x*x) = 0) : x = 0 := by
  apply Subtype.ext
  apply hfaith (x:C)
  have hh := matrixCornerExpectation_supported φ E hleft hright (star x*x)
  change E (star (x:C)*(x:C)) = _ at hh
  rw [hx,matrixSingle_zero] at hh
  exact hh

end

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

abbrev modelExpectation : B.Model →L[ℂ] CStarMatrix Bool Bool A :=
  atomicExpectation B.atoms B.amalgam false

def expectCorner : B.Corner →L[ℂ] A :=
  matrixCornerExpectation B.embedBase B.modelExpectation

theorem expectCorner_base (a : A) : B.expectCorner (B.cornerBase a) = a :=
  matrixCornerExpectation_base B.embedBase B.modelExpectation
    (atomicExpectation_factor B.atoms B.amalgam false) a

theorem expectCorner_faithful (x : B.Corner) (hx : B.expectCorner (star x*x) = 0) : x = 0 :=
  matrixCornerExpectation_faithful B.embedBase B.modelExpectation
    (atomicExpectation_factor_mul B.atoms B.amalgam false)
    (atomicExpectation_mul_factor B.atoms B.amalgam false)
    (atomicExpectation_faithful B.atoms B.amalgam false) x hx

end PeakingPairData

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
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem expectCorner_square_nonneg (x : B.Corner) : 0 ≤ B.expectCorner (star x*x) := by
  apply (matrixEntryPositive false).map_nonneg
  apply atomicExpectation_nonneg B.atoms B.amalgam false
  change 0 ≤ star ((x:B.Model):B.Operators)*((x:B.Model):B.Operators)
  exact star_mul_self_nonneg _

end PeakingPairData

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open Topology
section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

@[simp] theorem restrictState_comp (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C)
    (f : C →L[ℂ] ℂ) : restrictState φ (restrictState ψ f) = restrictState (ψ.comp φ) f := by
  ext a
  rfl

end

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

section
-- module Solutions.OAIQ115_Naimark.Naimark_Homogeneity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Filter Topology
open scoped InnerProductSpace
namespace KOS

section
open Filter Topology
variable {A : Type*} [cStarAlgebraA : CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

omit partialOrderA starOrderedRingA in
@[simp] theorem restrict_trans [PartialOrder A] [StarOrderedRing A] (α θ : A ≃⋆ₐ[ℂ] A) (f : A →L[ℂ] ℂ) :
    restrictState (θ.trans α).toStarAlgHom f =
      restrictState θ.toStarAlgHom (restrictState α.toStarAlgHom f) := by
  ext a
  rfl

end

end KOS

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

end NaimarkZFC

end

end OAI
end


