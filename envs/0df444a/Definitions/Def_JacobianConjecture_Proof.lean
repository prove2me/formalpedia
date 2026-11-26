-- Prove2me | Definitions.Def_JacobianConjecture_Proof
-- name    : JacobianConjecture_Proof
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T07:58:46.185897+00:00
-- url     : https://prove2.me/theorems/3253ae75-2a4d-43db-b068-23b17c91986d
-- title:
--   Proof
-- statement:
--   Definitions and structural lemmas for Proof, from Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz (Arthur742Ramos/jacobian-conjecture-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Alpöge-Fable 3D Jacobian conjecture counterexample development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/jacobian-conjecture-lean/blob/8db55ea3ffa8ba90094d6ef78ee3351ddfce01ca/JacobianConjecture/Proof.lean

import Definitions.Def_JacobianConjecture_Definitions
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit true
noncomputable section
open Matrix Function
open MvPolynomial
namespace JacobianCounterexample
variable (K : Type*) [Field K]
variable {K}
end JacobianCounterexample


