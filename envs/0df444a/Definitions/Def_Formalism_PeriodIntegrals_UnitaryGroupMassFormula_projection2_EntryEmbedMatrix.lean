-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_EntryEmbedMatrix
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_EntryEmbedMatrix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:10.831092+00:00
-- url     : https://prove2.me/theorems/9150d3ab-fdc1-4405-8402-430416e828ec
-- title:
--   Entry Embed Matrix
-- statement:
--   Definitions and structural lemmas for Entry Embed Matrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.OneCosetSharp.W.C2
open Loc LocE
variable {k : Type} [Field k]
def xj0 (k₀ n' n : ℕ) : (Fin n' → k) →ₗ[k] (Fin n → k) :=
  Matrix.toLin' (Matrix.of fun (l : Fin n) (s : Fin n') =>
    if l.1 = (if s.1 < k₀ then s.1 else s.1 + 1) then (1 : k) else 0)
def τ0 (k₀ n' c n : ℕ) : FC n' (c + 1) n c → k := fun q =>
  if q.1.2.1 = n' + c ∧ q.1.1.1 = k₀ then 1 else 0
end PI.OneCosetSharp.W.C2


