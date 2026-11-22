-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:16.805797+00:00
-- url     : https://prove2.me/theorems/a82b6ca5-9e79-4b10-824d-6d5e9d16f0e6
-- title:
--   Idx Change
-- statement:
--   Definitions and structural lemmas for Idx Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
namespace Formalism.DivisionValues
section Gen
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
end Gen
section Lat
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}
def idxChangeAct (e : Fin d → Fin d → K) (γ : Matrix (Fin d) (Fin d) K) : Fin d → Fin d → K :=
  fun i => ∑ k, γ k i • e k
end Lat
section Scale
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}
def IdxChangeP (v : HeightOneSpectrum R) (γ : Matrix (Fin d) (Fin d) K) : Prop :=
  ∀ e : Fin d → Fin d → K, LinearIndependent K e →
    lidx v.asIdeal (Submodule.span R (Set.range e))
        (Submodule.span R (Set.range (idxChangeAct e γ))) =
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ γ.det)
abbrev idxChangeDg (i : Fin d) (x : K) : Matrix (Fin d) (Fin d) K :=
  Matrix.diagonal (Function.update (1 : Fin d → K) i x)
end Scale
section Pi
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}
end Pi
section Main
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}
end Main
section Final
open NumberField
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Final
end Formalism.DivisionValues


