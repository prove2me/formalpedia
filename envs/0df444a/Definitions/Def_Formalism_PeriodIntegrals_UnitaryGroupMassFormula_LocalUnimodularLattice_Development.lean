-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T12:24:13.969911+00:00
-- url     : https://prove2.me/theorems/760f0709-5192-455b-a9fe-342bd9a8ea8d
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/Development.lean

import Definitions.Def_Formalism_PeriodIntegrals_NUnimodLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_NonstandardUnimodularLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
namespace PI.NUnimodLoc.UnitaryGroupMassFormula
open PI PI.QuotSetU
def FrameConj : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 z : Fin (2 * r + k + 1) → ℂ) (c : ℂ),
    IsFrameJ ε e f wf z0 → c ≠ 0 → z0 = c • z →
    ∃ P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Q * P = 1 ∧ P * Q = 1 ∧
      ∀ g, (Formalism.REAL.inUJ ε g ∧ InN ε e z g) ↔ Q * g * P ∈ Nset k r
def Transfer : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (T S : Set (Matrix (Fin m) (Fin m) ℂ))
    (P Q : Matrix (Fin m) (Fin m) ℂ), Q * P = 1 → P * Q = 1 →
    (∀ g, (Formalism.REAL.inUJ ε g ∧ g ∈ T) ↔ Q * g * P ∈ S) →
    (∀ μ : Measure (MtM m), IsHaarOnM S μ → IsRightInvM S μ) →
    ∀ μ : Measure (Formalism.REAL.UJ ε), SigmaFinite μ → μ ≠ 0 → μ {g : Formalism.REAL.UJ ε | uMat g ∈ T}ᶜ = 0 →
      (∀ s ∈ {g : Formalism.REAL.UJ ε | uMat g ∈ T}, μ.map (fun x => s * x) = μ) →
      ∀ s ∈ {g : Formalism.REAL.UJ ε | uMat g ∈ T}, μ.map (fun x => x * s) = μ
end PI.NUnimodLoc.UnitaryGroupMassFormula


