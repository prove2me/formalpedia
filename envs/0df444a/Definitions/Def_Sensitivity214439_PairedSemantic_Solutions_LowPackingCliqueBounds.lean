-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_LowPackingCliqueBounds
-- name    : Sensitivity214439_PairedSemantic_Solutions_LowPackingCliqueBounds
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:45:41.129534+00:00
-- url     : https://prove2.me/theorems/f5026cc3-83a8-4d0e-87f8-eb8abf12fa86
-- title:
--   Weighted directed load and occupied support
-- statement:
--   For a directed relation $D$, a finite vertex set $S$, and multiplicities $n_v$, define
--
--   $$\mathrm{weightedOut}(v)=\sum_{w\in S:D(v,w)}n_w.$$
--
--   The occupied support is $\{v\in S:0<n_v\}$. These quantities separate the number of occupied destinations from the full multiplicity load that an external guard conflict imposes.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/LowPackingCliqueBounds.lean lines 14–18; SHA256 f49a462857aa906089c62a7604e447a0314c8882355e349f20cb7a2912a3b74b; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

namespace SensitivityLowPacking
end SensitivityLowPacking
namespace SensitivityPseudoforest
end SensitivityPseudoforest



/-! The weighted clique leaves used by the exact low-one branch certificates. -/
namespace SensitivityLowPacking

noncomputable section
open scoped Classical BigOperators
open SensitivityPseudoforest
set_option autoImplicit false

variable {V : Type} [DecidableEq V]

def weightedOut (D : V → V → Prop) (vertices : Finset V) (count : V → ℕ) (v : V) : ℕ :=
  ∑ w ∈ vertices.filter (D v), count w

def Support (vertices : Finset V) (count : V → ℕ) : Finset V :=
  vertices.filter fun v => 0 < count v
















end
end SensitivityLowPacking


