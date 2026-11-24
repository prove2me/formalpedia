-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsHomogeneousGrL
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsHomogeneousGrL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:29.027554+00:00
-- url     : https://prove2.me/theorems/cfe95059-c56e-48e8-b77d-9fc8cd726005
-- title:
--   Is Homogeneous Gr L
-- statement:
--   Definitions and structural lemmas for Is Homogeneous Gr L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsHomogeneousGrL.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsPrimeFiltrationOfIsMultiHomogIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def lexDeg (a : K → ℕ) : Lex (Fin (Fintype.card K) → ℕ) := toLex (a ∘ (Fintype.equivFin K).symm)
variable (ι) in

abbrev grL : Lex (Fin (Fintype.card K) → ℕ) → Submodule ℤ (MRing ι) :=
  weightedHomogeneousSubmodule ℤ (lexW (ι := ι) (Fintype.equivFin K))
def pieceMap (J : Ideal (MRing ι)) (a : K → ℕ) : mHom ι a →ₗ[ℤ] MRing ι ⧸ J :=
  (Ideal.Quotient.mkₐ ℤ J).toLinearMap ∘ₗ (mHom ι a).subtype
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


