-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T09:35:59.516256+00:00
-- url     : https://prove2.me/theorems/97913608-29dc-4812-a1ec-92bd24a03f68
-- title:
--   Native Geometric Execution
-- statement:
--   Definitions and structural lemmas for Native Geometric Execution, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26NativeGeometricExecution
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
abbrev NativeTable (S : OddScale) (n : ℕ) := SR.Samples (SR.Index S n)
abbrev OriginalTable (S : OddScale) (n : ℕ) := originalTable (Presentation S n)
abbrev U (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space) (r : ℝ) :=
  keySupport (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J r
abbrev B (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space) (r l : ℝ) (K : ℕ) :=
  keyBad (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J r l K
structure Prefix (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space) (r : ℝ) where
  rows : SR.Rows (SR.Index S n)
  trace : List (Option (LiveRow S n J r))
structure PrefixRun (A : Type*) where
  value : A
  operations : ℕ
def chosenSupport (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space) (r : ℝ) :
    Option (LiveRow S n J r) → List (SR.Index S n)
  | none => []
  | some row => support S n J r row
def prefixQ (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) :
    ℕ → PrefixRun (Prefix S n J r)
  | 0 =>
      let init := SR.initializeQ S n T
      ⟨⟨init.value,[]⟩,init.operations+1⟩
  | m+1 =>
      let prior := prefixQ S n J hr lambda K T m
      let chosen := scanQ S n J hr lambda K prior.value.rows
      let updated := SR.refreshQ T (chosenSupport S n J r chosen.1) prior.value.rows
      let trace := BDL26NativeMasterCandidates.appendQ prior.value.trace [chosen.1]
      ⟨⟨updated.value,trace.value⟩,
        prior.operations+chosen.2+updated.operations+trace.operations+4⟩
def choice (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :=
  (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).1
def originalTrace (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : OriginalTable S n) : ℕ → List (Option (Event S n J r))
  | 0 => []
  | m+1 => originalTrace S n J r lambda K T m ++
      [selected (X := fun _ : Vertex (Presentation S n) => Space) (U S n J r) (B S n J r lambda K) T m]
def supportTrace (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :=
  (prefixQ S n J hr lambda K T m).value.trace.map (chosenSupport S n J r)
def NativeHalts (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) : Prop :=
  ∃ m, choice S n J hr lambda K T m = none
def nativeHaltTime (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) : ℕ :=
  if h : NativeHalts S n J hr lambda K T then Nat.find h else 0
def returned (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) :
    Vertex (Presentation S n) → Space :=
  originalPoints S n (prefixQ S n J hr lambda K T
    (nativeHaltTime S n J hr lambda K T)).value.rows
def nativePrefixCount (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n)
    (m : ℕ) (e : Event S n J r) : ℕ :=
  ((Finset.range m).filter (fun i =>
    (choice S n J hr lambda K T i).map (event S n J r) = some e)).card
def nativeTotalSteps (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) : ℝ≥0∞ :=
  ∑ e, ⨆ m : ℕ, (nativePrefixCount S n J hr lambda K T m e : ℝ≥0∞)
def observation (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) :
    Resampling.VariableRelabeling.Observation (Vertex (Presentation S n)) (Event S n J r) Space :=
  ((fun m v => (SR.readQ ((SR.decode S n).symm v)
      (prefixQ S n J hr lambda K T m).value.rows).value.1),
    (fun m => (choice S n J hr lambda K T m).map (event S n J r)),
    (if NativeHalts S n J hr lambda K T then true else false),
    nativeHaltTime S n J hr lambda K T,
    returned S n J hr lambda K T,
    nativePrefixCount S n J hr lambda K T,
    (fun e => ⨆ m : ℕ, (nativePrefixCount S n J hr lambda K T m e : ℝ≥0∞)),
    nativeTotalSteps S n J hr lambda K T)
def decodedTable (S : OddScale) (n : ℕ) (T : NativeTable S n) : OriginalTable S n :=
  Resampling.VariableRelabeling.decodeTable (SR.decode S n) T
def nativeTableMeasure (S : OddScale) (n : ℕ) {L : ℝ} (p : GeometricParameters L) :
    Measure (NativeTable S n) := by
  letI (a : SR.Index S n) := vertexLaw_probability (Presentation S n)
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 (SR.decode S n a)
  exact tableLaw (fun a : SR.Index S n => vertexLaw (Presentation S n)
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m) (SR.decode S n a))
theorem radius_nonneg {L : ℝ} (p : GeometricParameters L) : 0 ≤ (anchorRadius p.m : ℝ) := by
  unfold anchorRadius
  positivity
def nativeOutput (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {L : ℝ} (p : GeometricParameters L) :=
  returned S n J (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda)
end QEC.Coding.BDL26NativeGeometricExecution


