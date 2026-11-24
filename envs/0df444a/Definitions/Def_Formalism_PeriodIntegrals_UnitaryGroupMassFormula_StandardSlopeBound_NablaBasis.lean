-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:59.604994+00:00
-- url     : https://prove2.me/theorems/04cddc22-139b-40f3-a118-0a0226203658
-- title:
--   Nabla Basis
-- statement:
--   Definitions and structural lemmas for Nabla Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StandardSlopeBound/NablaBasis.lean

import Definitions.Def_Formalism_PeriodIntegrals_HookBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.SlopeSteps
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV
def gramOf {N : ℕ} (ν : Fin N → ℕ) {r : ℕ} (e : Fin r → MvPolynomial (Fin N × Fin N) ℤ) : Matrix (Fin r) (Fin r) ℚ :=
  Matrix.of fun i j =>
    fockQ (map (Int.castRingHom ℚ) (e i)) (map (Int.castRingHom ℚ) (e j)) / fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)
def MonoFactLow : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ), (∀ s, ∑ a, m (a, s) = ν s) →
    ∏ s, (ν s).factorial ≤ N ^ (∑ s, ν s) * ∏ k ∈ m.support, (m k).factorial
def NablaGramLow : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (r : ℕ) (e : Module.Basis (Fin r) ℤ (dualWeyl ℤ N N ν)), Antitone ν →
    (((∏ s, (ν s).factorial : ℕ) : ℚ) / ((N : ℚ) ^ (∑ s, ν s) * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν))) ^ r ≤
      (gramOf ν fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)).det
def GramDual : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (r r' : ℕ) (e : Module.Basis (Fin r) ℤ (weyl ℤ N N le_rfl ν))
    (e' : Module.Basis (Fin r') ℤ (dualWeyl ℤ N N ν)), Antitone ν →
    r = r' ∧ (gramOf ν fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)).det *
      (gramOf ν fun i => (e' i : MvPolynomial (Fin N × Fin N) ℤ)).det = 1
def NablaBasis : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), ∃ (r : ℕ), Nonempty (Module.Basis (Fin r) ℤ (dualWeyl ℤ N N ν))
def StdSlopeLowOf : Prop := NablaGramLow → GramDual → NablaBasis → PI.StdSlopeLow
example {N : ℕ} (ν : Fin N → ℕ) {r : ℕ} (e : Module.Basis (Fin r) ℤ (weyl ℤ N N le_rfl ν)) :
    PI.stdGram ν e = gramOf ν fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ) := rfl
end PI.SlopeSteps


