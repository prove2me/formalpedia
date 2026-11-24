-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericCertificatesCore
-- name    : Sensitivity214439_Phase0_Solutions_LocalNumericCertificatesCore
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:48:20.592092+00:00
-- url     : https://prove2.me/theorems/419f1e14-ef4e-4bb5-afe3-4d89de3b16cd
-- title:
--   Combined promotion and joint certificate predicates
-- statement:
--   A promotion certificate for source $a$, destination $n$, and bound $b$ requires the numerical promotion bound check, the occupied-guard interval check, and the cold-no-gain check all to return true.
--
--   A joint certificate for weak/source/destination ranks $(w,a,n)$ requires the numerical joint bound check, its interval check, and the cold-endpoint check. It also receives the already selected promotion bound and updated parent profile for the separate-loss-plus-promotion alternative. These predicates package the exact finite obligations consumed by the semantic transfers.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/LocalNumericCertificatesCore.lean lines 6–24; SHA256 1809fe142e26c959e4526988fed1fef1c77c36dfa006293cf073e7516183909a; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range

namespace SensitivityLocalNumeric
end SensitivityLocalNumeric



/-! The exact finite obligations carried by each local recurrence certificate. -/
namespace SensitivityLocalNumeric

def PromotionCertified (r : Recipe) (v : Bounds) (x n : Fin 12) (bound : ℕ) : Prop :=
  promotionCheck r v x n bound = true ∧
    promotionIntervalsCheck r x n = true ∧ coldNoGainCheck r x n = true

instance (r : Recipe) (v : Bounds) (x n : Fin 12) (bound : ℕ) :
    Decidable (PromotionCertified r v x n bound) := by
  unfold PromotionCertified
  infer_instance

def JointCertified (r : Recipe) (v : Bounds) (updated : Array ℕ)
    (c x n : Fin 12) (promotion bound : ℕ) : Prop :=
  jointCheck r v updated c x n promotion bound = true ∧
    jointIntervalsCheck r c x n = true ∧ coldEndpointCheck r c x n = true

instance (r : Recipe) (v : Bounds) (updated : Array ℕ)
    (c x n : Fin 12) (promotion bound : ℕ) :
    Decidable (JointCertified r v updated c x n promotion bound) := by
  unfold JointCertified
  infer_instance

end SensitivityLocalNumeric


