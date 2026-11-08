-- Prove2me | Definitions.Def_MaxCompForest_liftLabels
-- name    : MaxCompForest_liftLabels
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:50.711762+00:00
-- url     : https://prove2.me/theorems/9b968d8e-d990-48e2-9187-0ef0ee1e713d
-- title:
--   Original labels of a set of quotient labels
-- statement:
--   A label of the quotient $G/S$ is an original label of $G$; this map sends a set $J$ of quotient labels to the same labels viewed in $G$, so that $S\cup J$ is a set of original labels.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), p.38

import Mathlib
import Definitions.Def_MaxCompForest_contract
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*}  [DecidableEq E]

/-- **The original labels of a set `J` of labels of `G/S`.**
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.38: "using only original physical labels". -/
def liftLabels (G : WGraph V E) (S : Finset E) (J : Finset (ContractE G S)) : Finset E :=
  J.map ⟨Subtype.val, Subtype.val_injective⟩

end MaxCompForest


