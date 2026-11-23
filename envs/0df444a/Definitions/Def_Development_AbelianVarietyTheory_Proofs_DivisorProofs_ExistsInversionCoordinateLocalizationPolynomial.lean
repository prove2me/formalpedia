-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInversionCoordinateLocalizationPolynomial
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInversionCoordinateLocalizationPolynomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:04.473809+00:00
-- url     : https://prove2.me/theorems/1cacef91-534b-42c2-91d1-7ed7d9d68903
-- title:
--   Exists Inversion Coordinate Localization Polynomial
-- statement:
--   Definitions and structural lemmas for Exists Inversion Coordinate Localization Polynomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInversionCoordinateLocalizationPolynomial.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace GlobalTheory
noncomputable def awayLiftAlgHom {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    (P : k[X]) (f : k[X] →ₐ[k] B) (h : IsUnit (f P)) : Localization.Away P →ₐ[k] B :=
  IsLocalization.liftAlgHom (M := Submonoid.powers P) (f := f)
    (by rintro ⟨_, n, rfl⟩; simpa using h.pow n)
end GlobalTheory


