-- Prove2me | Definitions.Def_NagataFactoriality_Applications_FractionField
-- name    : NagataFactoriality_Applications_FractionField
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:59:11.772513+00:00
-- url     : https://prove2.me/theorems/c20590be-e714-4bec-8493-caacc2a9018d
-- title:
--   Fraction Field
-- statement:
--   Definitions and structural lemmas for Fraction Field, from Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz (Arthur742Ramos/NagataFactoriality; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Prime-generated Nagata factoriality theorem for Noetherian integral domains development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/FractionField.lean

import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Nagata_Theorem
set_option autoImplicit false
namespace NagataFactoriality
open Polynomial
section FractionFieldRoute
noncomputable section
variable (R : Type*) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
abbrev constPrimeSubmonoid : Submonoid R[X] :=
  Submonoid.closure (C '' {r : R | Prime r})
abbrev nzdMapC : Submonoid R[X] :=
  (nonZeroDivisors R).map (C : R →+* R[X])
variable {R}
variable (R)
end
end FractionFieldRoute
end NagataFactoriality


