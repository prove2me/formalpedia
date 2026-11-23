-- Prove2me | Definitions.Def_SumProduct_PartialZetaMellin
-- name    : SumProduct_PartialZetaMellin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T00:27:53.279231+00:00
-- url     : https://prove2.me/theorems/e3488712-6094-45ba-839c-3dde98fdd233
-- title:
--   Partial Zeta Mellin
-- statement:
--   Definitions and structural lemmas for Partial Zeta Mellin, from Mathlib Initiative and contributors's pinned A real sum-product counterexample conditional on Martinet’s tower theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean

import Definitions.Def_DedekindZeta_PerClass
import Definitions.Def_DedekindZeta_ConeMellinBridge
set_option autoImplicit true
open scoped NumberField nonZeroDivisors
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
namespace SumProduct
variable (K : Type*) [Field K] [NumberField K]
noncomputable def partialCompletedZetaResidue (K : Type*) [Field K] [NumberField K] : ℝ :=
  (2 : ℝ) ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K / torsionOrder K
open DedekindZeta DedekindZeta.ConeRadialReduction DedekindZeta.ConeMellinBridge
  DedekindZeta.MellinPrinciple
open scoped nonZeroDivisors
end SumProduct


