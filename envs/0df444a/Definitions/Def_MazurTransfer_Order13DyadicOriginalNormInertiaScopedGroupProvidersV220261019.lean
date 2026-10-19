-- Prove2me | Definitions.Def_MazurTransfer_Order13DyadicOriginalNormInertiaScopedGroupProvidersV220261019
-- name    : MazurTransfer_Order13DyadicOriginalNormInertiaScopedGroupProvidersV220261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T10:28:46.920469+00:00
-- url     : https://prove2.me/theorems/34dd3d68-e0ac-44cf-9095-4e707a4b39b3
-- title:
--   Original rational Picard group structures for dyadic norm inertia
-- statement:
--   Let $P$ be the fixed arithmetic Picard scheme over $\mathbf{Q}$. Retain the original group object used to transport its norm maps to the chosen dyadic Picard model.
--
--   $$G_P=\operatorname{Grp}(P).$$
--
--   The whole original constructor value is preserved. Named downstream consumer: internal integral norm morphisms and genuine valuation inertia at two.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: retain ONLY the original closed scoped prime and group-object constructors, with their exact original names and whole nonproof values. Substantial norm proofs are theorem submissions.
Named downstream consumer: original internal norm-morphism and dyadic inertia theorem bundle.
-/
import Definitions.Def_MazurTransfer_Order13DyadicOriginalScalarNormScopedGroupProvidersV220261019
noncomputable section
namespace MazurTransfer.Order13DyadicMixedActualNormInertia
local instance instFactPrimeOfNatNat_order13DyadicMixedActualNormInertia : Fact (Nat.Prime 2) := ⟨by decide⟩
end MazurTransfer.Order13DyadicMixedActualNormInertia
namespace MazurTransfer.Order13DyadicMixedIntegralNormInertia
local instance instFactPrimeOfNatNat_order13DyadicMixedIntegralNormInertia : Fact (Nat.Prime 2) := ⟨by decide⟩
end MazurTransfer.Order13DyadicMixedIntegralNormInertia
namespace MazurTransfer.Order13DyadicMixedIntegralNormInternalMorphism
local instance instFactPrimeOfNatNat_order13DyadicMixedIntegralNormInternalMorphism : Fact (Nat.Prime 2) := ⟨by decide⟩
end MazurTransfer.Order13DyadicMixedIntegralNormInternalMorphism
namespace MazurTransfer.Order13DyadicMixedIntegralNormInternalMorphism
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormInternalMorphism : CategoryTheory.GrpObj (CategoryTheory.Over.mk MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism.actualPicard.toBase) := MazurTransfer.Order13DyadicMixedRationalPicardComparison.actualGroup
end MazurTransfer.Order13DyadicMixedIntegralNormInternalMorphism
end
#print axioms MazurTransfer.Order13DyadicMixedIntegralNormInternalMorphism.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormInternalMorphism
#print axioms MazurTransfer.Order13DyadicMixedIntegralNormInertia.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormInertia
#print axioms MazurTransfer.Order13DyadicMixedIntegralNormInternalMorphism.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormInternalMorphism
#print axioms MazurTransfer.Order13DyadicMixedActualNormInertia.instFactPrimeOfNatNat_order13DyadicMixedActualNormInertia


