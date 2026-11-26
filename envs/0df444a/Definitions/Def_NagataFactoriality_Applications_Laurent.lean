-- Prove2me | Definitions.Def_NagataFactoriality_Applications_Laurent
-- name    : NagataFactoriality_Applications_Laurent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:58:40.919821+00:00
-- url     : https://prove2.me/theorems/1896454e-988a-54ea-b9dd-197adf345dcd
-- title:
--   Laurent
-- statement:
--   Definitions and structural lemmas for Laurent, from Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz (Arthur742Ramos/NagataFactoriality; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Prime-generated Nagata factoriality theorem for Noetherian integral domains development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Laurent.lean

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
set_option autoImplicit false
namespace NagataFactoriality
open scoped LaurentPolynomial
open Polynomial
end NagataFactoriality


