-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:54.873662+00:00
-- url     : https://prove2.me/theorems/3f0f6c09-8762-4d49-8479-2d6ce8641245
-- title:
--   Nabla Span C
-- statement:
--   Definitions and structural lemmas for Nabla Span C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/NablaSpanC.lean

import Definitions.Def_Formalism_PeriodIntegrals_NablaSpans_MinorProdSpanHasCompl
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
namespace GenFrameSpan
open CutKW
abbrev nablaSpanC (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 : ℕ)
    (nu : Lt → YoungDiagram) : Submodule ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]) :=
  Submodule.span ℂ_[l] (Set.range fun J : ColChoice N0 nu =>
    MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J))
def StepBack : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (B : ℝ),
    ExpansionCoeffValuationGe N0 N1 l nu Th B → KvalGe N0 N1 l nu Th B
def StepSpan : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (I : ColChoice N1 nu),
    applyAt0 N0 N1 l Th (Gxz N0 N1 nu I) ∈ nablaSpanC Lt l N0 nu
def StepSat : Prop :=
  MinorProdSpanHasCompl → ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 : ℕ)
    (nu : Lt → YoungDiagram) (P : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]) (B : ℝ),
    P ∈ nablaSpanC Lt l N0 nu →
    (∀ m, ‖MvPolynomial.coeff m P‖ ≤ (l : ℝ) ^ (-B)) →
    ∃ c : ColChoice N0 nu →₀ ℂ_[l], (∀ J, ‖c J‖ ≤ (l : ℝ) ^ (-B)) ∧
      P = c.sum fun J a => a • MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J)
end GenFrameSpan


