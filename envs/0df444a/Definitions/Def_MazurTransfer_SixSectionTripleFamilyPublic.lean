-- Prove2me | Definitions.Def_MazurTransfer_SixSectionTripleFamilyPublic
-- name    : MazurTransfer_SixSectionTripleFamilyPublic
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T04:28:16.630207+00:00
-- url     : https://prove2.me/theorems/eecc7ce0-ed69-4667-8eb8-96198db49c60
-- title:
--   The indexed triple family from six sections of a relative curve
-- statement:
--   Let $R$ be a commutative ring, $c:C\to\operatorname{Spec}R$ a scheme morphism, and $\sigma_0,\ldots,\sigma_5$ six sections of $c$. Index the $6^3=216$ functions $\mu:\{0,1,2\}\to\{0,\ldots,5\}$ by the canonical finite-type enumeration. The associated family of triples is $$T_{i,j}=\sigma_{\mu_i(j)}\qquad(0\leq i<216,\ 0\leq j<3).$$ This constructor supplies the chart-section family used by the six-section Picard chart criterion and then by the actual integral order-thirteen Picard representation.
-- source:
--   The unchanged tripleFamily constructor from checked MazurTheorem SixSectionPicardChartCriterion.lean, selected using complete Lean frontend declaration and command ranges. The complete original kernel type is verified by a closed witness. The retained original header records adaptation of the section-selection argument from official Anthropic FLT at commit 6e837e75355538c7f80bab5b956861e86c4eacc2. No section-distinctness or chart-existence theorem is asserted by this constructor. Vas and contributors, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted the complete section-selection argument from official Anthropic FLT
exists_finite_etale_hasChartSections_of_field at exact pin
6e837e75355538c7f80bab5b956861e86c4eacc2. Original attribution retained.
Design boundary: six fibrewise distinct sections and genus-two geometric
Riemann-Roch models give original HasChartSections, with all triples indexed.
Named downstream consumer: the six actual marked order-13 integral sections.
Their distinctness and geometric model inputs remain explicit obligations.
-/
import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections


noncomputable section
universe u
namespace MazurTransfer.SixSectionPicardChartCriterion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra
variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
variable (σ : Fin 6 → SchemeHomOver (𝟙 (Spec (.of R))) c)

def tripleFamily : Fin (Fintype.card (Fin 3 → Fin 6)) → Fin (5-2) →
    SchemeHomOver (𝟙 (Spec (.of R))) c :=
  fun i j => σ ((Fintype.equivFin (Fin 3 → Fin 6)).symm i j)

end MazurTransfer.SixSectionPicardChartCriterion

#print axioms MazurTransfer.SixSectionPicardChartCriterion.tripleFamily


