-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_StabBig
-- name    : Formalism_PeriodIntegrals_StabBig
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:44:52.683547+00:00
-- url     : https://prove2.me/theorems/19d32d12-0062-4a7d-bb89-8e6e47b54b34
-- title:
--   Stab Big
-- statement:
--   Definitions and structural lemmas for Stab Big, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/StabBig.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI
open Formalism.QuantumDeterminants
def RStab (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {a | a ∈ Nset k r ∧ g⁻¹ * a * g ∈ Nset k r}
def StabBig : Prop :=
  ∀ (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    (∀ a, c a ≠ 0) → μᴴ * Hb k * μ = Hb k → RStab k r (bigCell k r c μ) = {1}
end PI


