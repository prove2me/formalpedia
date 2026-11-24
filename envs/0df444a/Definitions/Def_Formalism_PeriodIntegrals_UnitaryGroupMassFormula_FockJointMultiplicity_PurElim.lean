-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:03.613739+00:00
-- url     : https://prove2.me/theorems/eee1857e-b4ea-4b87-abde-80474e126b40
-- title:
--   Pur Elim
-- statement:
--   Definitions and structural lemmas for Pur Elim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurElim.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
namespace PI.FJMB
variable {σ : Type*}
def HWB {m n : ℕ} (ι : Fin m × Fin n → σ) (f : MvPolynomial σ ℂ) : Prop :=
  (∀ a b : Fin m, a < b → PI.FJM.bRow ι a b f = 0) ∧ (∀ c d : Fin n, c < d → PI.FJM.bCol ι c d f = 0)
def offD {m n : ℕ} (ι : Fin m × Fin n → σ) : Set σ := {v | ∃ i k, ι (i, k) = v ∧ (i : ℕ) ≠ k}
def killS (S : Set σ) : σ → MvPolynomial σ ℂ := fun v => if v ∈ S then 0 else X v
def edge {m n : ℕ} (ι : Fin (m + 1) × Fin (n + 1) → σ) : Set σ :=
  {v | (∃ l : Fin n, ι (0, l.succ) = v) ∨ (∃ j : Fin m, ι (j.succ, 0) = v)}
section Step
variable {m n : ℕ} (ι : Fin (m + 1) × Fin (n + 1) → σ) (hι : Function.Injective ι)
include hι
end Step
end PI.FJMB


