-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_LowPackingResidual
-- name    : Sensitivity214439_PairedSemantic_Solutions_LowPackingResidual
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:56:30.02491+00:00
-- url     : https://prove2.me/theorems/8387b997-06a0-4d0e-b9ac-4d9d7b1f7aec
-- title:
--   Conditioned bases and live packing candidates
-- statement:
--   After fixing vertices $F$, add their outgoing multiplicity load to each base:
--
--   $$b'_v=b_v+\sum_{w\in F:D(v,w)}n_w.$$
--
--   Possible fixed zeros are the fixed vertices with $0<n_v\le2$ and $b'_v=0$. Live candidates are unfixed vertices with conditioned base at most one whose occupation by one copy would not violate any occupied fixed predecessor's budget. These filters retain every feasible occupied or zero vertex in a completion and support residual upper bounds.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/LowPackingResidual.lean lines 13–21; SHA256 9462682cea40addd8b31518ac1b7573598350c02319b958a9868c1d396528a14; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_LowPackingCliqueBounds
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

namespace SensitivityLowPacking
end SensitivityLowPacking
namespace SensitivityPseudoforest
end SensitivityPseudoforest



/-! Conditioning a low packing on a partial assignment preserves exact guard budgets. -/
namespace SensitivityLowPacking

noncomputable section
open scoped Classical BigOperators
open SensitivityPseudoforest
set_option autoImplicit false

variable {V : Type} [DecidableEq V]

def fixedBase (D : V → V → Prop) (fixed : Finset V) (count base : V → ℕ) (v : V) : ℕ :=
  base v + weightedOut D fixed count v

def fixedZeros (D : V → V → Prop) (fixed : Finset V) (count base : V → ℕ) : Finset V :=
  fixed.filter fun v => 0 < count v ∧ count v ≤ 2 ∧ fixedBase D fixed count base v = 0

def liveCandidates (D : V → V → Prop) (vertices fixed : Finset V) (count base : V → ℕ) : Finset V :=
  (vertices \ fixed).filter fun v => fixedBase D fixed count base v ≤ 1 ∧
    ∀ w ∈ fixed, 0 < count w → D w v → count w + 2 * (fixedBase D fixed count base w + 1) ≤ 3



















end
end SensitivityLowPacking


