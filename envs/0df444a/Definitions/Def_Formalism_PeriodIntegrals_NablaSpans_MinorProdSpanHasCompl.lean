-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_NablaSpans_MinorProdSpanHasCompl
-- name    : Formalism_PeriodIntegrals_NablaSpans_MinorProdSpanHasCompl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:56.733724+00:00
-- url     : https://prove2.me/theorems/0bfdf98d-03da-4c74-9bfe-a4986bb6fdf6
-- title:
--   Minor Prod Span Has Compl
-- statement:
--   Definitions and structural lemmas for Minor Prod Span Has Compl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/NablaSpans/MinorProdSpanHasCompl.lean

import Definitions.Def_Formalism_PeriodIntegrals_NablaSpans_ExpansionCoeffValuationGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace CutKW
def minorX (R : Type) [CommRing R] (N p : ℕ) (I : Fin p ↪o Fin N) : MvPolynomial (ℕ × Fin N) R :=
  Matrix.det (Matrix.of fun i k : Fin p => MvPolynomial.X ((i : ℕ), I k))
def nablaSpan (R : Type) [CommRing R] (N : ℕ) (nu : YoungDiagram) :
    Submodule R (MvPolynomial (ℕ × Fin N) R) :=
  Submodule.span R (Set.range fun I : ∀ c : Fin (nu.rowLen 0), Fin (nu.colLen c) ↪o Fin N =>
    ∏ c : Fin (nu.rowLen 0), minorX R N (nu.colLen c) (I c))
def MinorProdSpanHasCompl : Prop :=
  ∀ (R : Type) [CommRing R] (N : ℕ) (nu : YoungDiagram),
    ∃ Cm : Submodule R (MvPolynomial (ℕ × Fin N) R), IsCompl (nablaSpan R N nu) Cm
def KWsb : Prop := MinorProdSpanHasCompl → KW
end CutKW


