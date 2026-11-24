-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:13:16.961804+00:00
-- url     : https://prove2.me/theorems/4814a26c-3667-4e36-a7e3-c574734131dc
-- title:
--   MXMul Vec Mid
-- statement:
--   Definitions and structural lemmas for MXMul Vec Mid, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/MXMulVecMid.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
namespace PI.PolynomialProperness.TM
def eIe (k r : ℕ) : Fin r ↪ Fin (2 * r + k + 1) :=
  ⟨eI k r, fun a b h => Fin.ext (by have := congrArg Fin.val h; exact this)⟩
def esIe (k r : ℕ) : Fin r ↪ Fin (2 * r + k + 1) :=
  ⟨esI k r, fun a b h => Fin.ext (by
    have h1 := congrArg Fin.val h
    have ha := a.isLt; have hb := b.isLt
    simp only [esI] at h1; omega)⟩
def pX (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) : Fin r → ℂ := fun a => x (eI k r a)
def qX (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) : Fin r → ℂ := fun a => x (esI k r a)
def midF (k r : ℕ) (x y : Fin (2 * r + k + 1) → ℂ) : ℂ :=
  ∑ i : Fin (2 * r + k + 1), if r ≤ i.val ∧ i.val ≤ r + k then star (y i) * (GBasic.sgn k r i * x i) else 0
end PI.PolynomialProperness.TM
namespace PI.PolynomialProperness
end PI.PolynomialProperness


