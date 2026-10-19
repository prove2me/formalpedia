-- Prove2me | Definitions.Def_MazurTransfer_Order13DyadicOriginalScalarNormScopedGroupProvidersV220261019
-- name    : MazurTransfer_Order13DyadicOriginalScalarNormScopedGroupProvidersV220261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T10:12:07.66631+00:00
-- url     : https://prove2.me/theorems/8dab3257-f977-4f69-b04f-07df509b2c22
-- title:
--   Original rational Picard group structures for scalar descent
-- statement:
--   Let $P$ be the fixed arithmetic Picard scheme over $\mathbf{Q}$, and let $J_{\mathbf{Q}}$ be the rational fibre of the original chosen dyadic Picard scheme. Retain their original group objects for scalar and norm descent.
--
--   $$G_P=\operatorname{Grp}(P),\qquad G_J=\operatorname{Grp}(J_{\mathbf{Q}}).$$
--
--   The chosen structures are exactly those induced by the original Picard representations. Their whole constructor values are preserved. Named downstream consumer: scalar nineteen and finite etale actual norm fibres.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: retain ONLY the original closed scoped prime and group-object constructors, with their exact original names and whole nonproof values. Substantial norm proofs are theorem submissions.
Named downstream consumer: original scalar-nineteen and finite-etale norm-fibre theorem bundle.
-/
import Definitions.Def_MazurTransfer_Order13DyadicOriginalIntegralNormGroupLawAndCompositionData20261019
noncomputable section
namespace MazurTransfer.Order13DyadicMixedIntegralNormEtale
local instance instFactPrimeOfNatNat_order13DyadicMixedIntegralNormEtale : Fact (Nat.Prime 2) := ⟨by decide⟩
end MazurTransfer.Order13DyadicMixedIntegralNormEtale
namespace MazurTransfer.Order13DyadicMixedIntegralNormFinite
local instance instFactPrimeOfNatNat_order13DyadicMixedIntegralNormFinite : Fact (Nat.Prime 2) := ⟨by decide⟩
end MazurTransfer.Order13DyadicMixedIntegralNormFinite
namespace MazurTransfer.Order13DyadicMixedIntegralScalarNineteen
local instance instFactPrimeOfNatNat_order13DyadicMixedIntegralScalarNineteen : Fact (Nat.Prime 2) := ⟨by decide⟩
end MazurTransfer.Order13DyadicMixedIntegralScalarNineteen
namespace MazurTransfer.Order13DyadicMixedScalarInputs
local instance instFactPrimeOfNatNat_order13DyadicMixedScalarInputs : Fact (Nat.Prime 2) := ⟨by decide⟩
end MazurTransfer.Order13DyadicMixedScalarInputs
namespace MazurTransfer.Order13DyadicMixedIntegralScalarNineteen
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralScalarNineteen : CategoryTheory.GrpObj (CategoryTheory.Over.mk MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism.actualPicard.toBase) := MazurTransfer.Order13DyadicMixedRationalPicardComparison.actualGroup
end MazurTransfer.Order13DyadicMixedIntegralScalarNineteen
namespace MazurTransfer.Order13DyadicMixedIntegralScalarNineteen
local instance instGrpObjOverSchemeSpecOfRatMkToBaseRationalPicard_order13DyadicMixedIntegralScalarNineteen : CategoryTheory.GrpObj (CategoryTheory.Over.mk MazurTransfer.Order13DyadicMixedRationalPicardComparison.rationalPicard.toBase) := MazurTransfer.Order13DyadicMixedGenericGroupIdentity.genericRepresentationGroup.grpObj
end MazurTransfer.Order13DyadicMixedIntegralScalarNineteen
end
#print axioms MazurTransfer.Order13DyadicMixedIntegralScalarNineteen.instFactPrimeOfNatNat_order13DyadicMixedIntegralScalarNineteen
#print axioms MazurTransfer.Order13DyadicMixedIntegralScalarNineteen.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralScalarNineteen
#print axioms MazurTransfer.Order13DyadicMixedScalarInputs.instFactPrimeOfNatNat_order13DyadicMixedScalarInputs
#print axioms MazurTransfer.Order13DyadicMixedIntegralNormFinite.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormFinite
#print axioms MazurTransfer.Order13DyadicMixedIntegralScalarNineteen.instGrpObjOverSchemeSpecOfRatMkToBaseRationalPicard_order13DyadicMixedIntegralScalarNineteen
#print axioms MazurTransfer.Order13DyadicMixedIntegralNormEtale.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormEtale


