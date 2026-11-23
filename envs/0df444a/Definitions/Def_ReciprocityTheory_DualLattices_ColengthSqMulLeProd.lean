-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqMulLeProd
-- name    : ReciprocityTheory_DualLattices_ColengthSqMulLeProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:06.601805+00:00
-- url     : https://prove2.me/theorems/44ba2d53-537f-4445-bbe3-a92c5538c809
-- title:
--   Colength Sq Mul Le Prod
-- statement:
--   Definitions and structural lemmas for Colength Sq Mul Le Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqMulLeProd.lean

import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatementHolds
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
variable {C : Type} [Field C] {v : Valuation C NNReal}
def blkLat {n s : ℕ} (Ls : Fin n → Lat v (Fin s)) : Lat v (Fin n × Fin s) where
  B := Matrix.of fun x y => if x.1 = y.1 then (Ls x.1).B x.2 y.2 else 0
  det_ne := by
    have h : (Matrix.of fun x y : Fin n × Fin s => if x.1 = y.1 then (Ls x.1).B x.2 y.2 else 0) =
        (Matrix.blockDiagonal fun τ => (Ls τ).B).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
      ext x y
      simp [Matrix.blockDiagonal_apply, eq_comm]
    rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => (Ls τ).det_ne
end ReciprocityTheory.PGsh.Up


