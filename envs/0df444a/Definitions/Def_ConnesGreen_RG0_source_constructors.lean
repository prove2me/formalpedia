-- Prove2me | Definitions.Def_ConnesGreen_RG0_source_constructors
-- name    : ConnesGreen_RG0_source_constructors
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-07T22:39:04.900982+00:00
-- url     : https://prove2.me/theorems/c66d4088-8649-4f1d-8b2f-167326819526
-- title:
--   Original restricted-window derivative probe constructor
-- statement:
--   Retain the original derivative probe in the two-component restricted-window ambient Hilbert space and the finite-window measure instance. The probe is the native vector with first coordinate the original restricted $L^2$ representative of a function and second coordinate twice the original representative of its derivative. No source identity, positivity or arithmetic bound is postulated; the source normalization theorem proves the required orthogonality and Riesz identity separately.
-- source:
--   Exact declaration spans from the accepted RG-3 proof, reconciled with native ConnesGreen/CanonicalGreenAnalysis: derivativeProbe and windowMeasure_finite; skeleton subtraction uses Lean elaborator declaration metadata.

import Definitions.Def_ConnesGreen_canonical_model
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory Set ConnesRZ ConnesRZFrontier
open scoped BigOperators InnerProductSpace lp ENNReal Classical Topology Interval ComplexConjugate
noncomputable section
namespace WeilDefect
attribute [local instance 1100] NormedSpace.complexToReal
open Filter Set Bornology


































































end WeilDefect

namespace WeilDefect.ConnesNative
open WeilDefect










end WeilDefect.ConnesNative

namespace ConnesGreen


end ConnesGreen
namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative















end ConnesGreen

namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative

instance windowMeasure_finite (t : ℝ) : IsFiniteMeasure (windowMeasure t) := by
  unfold windowMeasure
  infer_instance



/-- A smooth dual probe of the energy graph; this is not a replacement for
the original admissible-test class or a change to the physical carrier. -/
def derivativeProbe (t : ℝ) (φ : ℝ → ℂ) : Ambient t :=
  WithLp.toLp 2 (fun i : Fin 2 =>
    if i = 0 then windowL2 t φ else (2 : ℂ) • windowL2 t (iteratedDeriv 1 φ))









end ConnesGreen

namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative











end ConnesGreen


