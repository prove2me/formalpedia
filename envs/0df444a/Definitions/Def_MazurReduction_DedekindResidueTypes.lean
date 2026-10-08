-- Prove2me | Definitions.Def_MazurReduction_DedekindResidueTypes
-- name    : MazurReduction_DedekindResidueTypes
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T11:43:17.66148+00:00
-- url     : https://prove2.me/theorems/44e70b4a-9903-4ec3-bbd2-536dacedc4d2
-- title:
--   Canonical field structure on a Dedekind prime quotient
-- statement:
--   For a height-one prime v of a Dedekind domain R, this module exposes the canonical field structure on R/v. This is a structural type interface using Mathlib’s maximal-ideal quotient construction. Named downstream consumer: the full torsion bound at an unramified odd prime of the fraction field.
-- source:
--   Adapted from Michael Stoll’s instance in EllipticCurves/Mathlib/AdicValuation.lean at 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f, as integrated in the user MazurTheorem WIP. Original Apache-2.0 provenance retained.

/-
Copyright (c) 2026 Michael Stoll, Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Vasily Ilin

Adapted from Michael Stoll's height-one-prime residue-field instance,
MichaelStollBayreuth/EllipticCurves at 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f,
as integrated in the user's MazurTheorem WIP.
-/
import Mathlib
namespace MazurReduction
/-- Structural boundary: the canonical quotient by a height-one prime of a
Dedekind domain is a field. Named downstream consumer: the full torsion
bound over a fraction field at an unramified odd prime. -/
noncomputable instance instFieldDedekindQuotient
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : IsDedekindDomain.HeightOneSpectrum R) : Field (R ⧸ v.asIdeal) :=
  Ideal.Quotient.field _
end MazurReduction


