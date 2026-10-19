-- Prove2me | Definitions.Def_MazurTransfer_Order13CanonicalRationalScalarMap
-- name    : MazurTransfer_Order13CanonicalRationalScalarMap
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T08:40:03.033553+00:00
-- url     : https://prove2.me/theorems/b87d7fcc-0f0b-4dcc-b527-d4c1fa9c5755
-- title:
--   The canonical scalar map from Z[1/104] to the rational field
-- statement:
--   Put $B=\mathbb Z[1/104]$. The specified rational scalar map is the original localization lift $$B\longrightarrow\mathbb Q.$$ Its construction is retained exactly. This fixes the algebra structure used for the rational fibre of the one actual integral Picard family and its scheme-level comparison with the actual rational Picard designation.
-- source:
--   Original canonicalRationalMap declaration from MazurTheorem Order13SameIntegralPicardFamilyFiniteFibres.lean, Apache-2.0, Vas and contributors. The original constructor body is unchanged, with the public integral base/map Definition imported. Its complete original closed type and value are kernel-compared. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: Order13SameIntegralPicardRationalSchemeComparison and actual rational torsion specialization.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: one actual Picard abelian scheme over Z[1/104] has exactly
19 relative points over each canonical scalar map to F3 and F5.
Named downstream consumer: specialization of rational torsion into these
same-family finite-field groups. No torsion injectivity is assumed here.
-/
/- Public constructor boundary: the original canonical map from Z[1/104]
to the rational field. Named downstream consumer: the same integral
Picard family's rational fibre and actual rational scheme comparison. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13IntegralBaseAndFieldMaps
noncomputable section
namespace MazurTransfer.Order13SameIntegralPicardFamilyFiniteFibres
open MazurTransfer.Order13IntegralBase
def canonicalRationalMap : BaseRing →+* ℚ := mapToRing ℚ (by norm_num)
end MazurTransfer.Order13SameIntegralPicardFamilyFiniteFibres
#print axioms MazurTransfer.Order13SameIntegralPicardFamilyFiniteFibres.canonicalRationalMap


