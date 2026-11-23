-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
-- name    : ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:21.558794+00:00
-- url     : https://prove2.me/theorems/bd1378b4-655c-4881-84b4-dd1d284c1571
-- title:
--   Colength Sq Block Vandermonde
-- statement:
--   Definitions and structural lemmas for Colength Sq Block Vandermonde, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean

import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {v : Valuation C NNReal}
def sumLat {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) : Lat v (Fin n × Fin s) :=
  ⟨Matrix.reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
      (Matrix.blockDiagonal fun τ => (Mτ τ).B), by
    rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => (Mτ τ).det_ne⟩
end ReciprocityTheory.PGsh.Up


