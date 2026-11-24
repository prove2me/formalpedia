-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T19:29:32.165022+00:00
-- url     : https://prove2.me/theorems/c5478b0e-f4b0-4a5f-8d7b-4b39fcbc84ea
-- title:
--   Mem Steps Full
-- statement:
--   Definitions and structural lemmas for Mem Steps Full, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemStepsFull.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def mulCT {nf : ℕ} (t₁ t₂ : CT k r nf) : CT k r nf :=
  ⟨t₁.q * t₂.q, t₁.a + t₂.a, t₁.b + t₂.b, t₁.c + t₂.c, t₁.es ++ t₂.es⟩
def fo {nf : ℕ} (es : List (Fin nf × List (Mat k r))) : ℕ := (es.map fun e => e.2.length).sum
end Formalism.FourierDecayAlt.P.MinorPolynomials


