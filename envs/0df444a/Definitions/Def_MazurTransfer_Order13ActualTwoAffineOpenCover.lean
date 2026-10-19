-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualTwoAffineOpenCover
-- name    : MazurTransfer_Order13ActualTwoAffineOpenCover
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T02:51:07.752899+00:00
-- url     : https://prove2.me/theorems/39def65b-af1f-408b-926b-ff8fdfe45595
-- title:
--   The actual two affine charts of the order-thirteen curve
-- statement:
--   Let $K$ be a field with $104\ne0$, and let $C_K$ be the fixed order-thirteen curve formed by gluing its ordinary and reciprocal hyperelliptic charts. If $U_0$ and $U_1$ are their open images, then
--   $$C_K=U_0\cup U_1,$$
--   and both opens and their intersection are affine.
--
--   The interface constructs this particular two-affine-open cover from the actual chart maps and the separatedness of the proper curve. It supplies the cover input to the general finite-map existence theorem, which gives affine neighborhoods of finite sets of actual curve points.
-- source:
--   Five exact checked declarations from AcceptedOrder13GoodCharacteristicPicardCache.lean, lines 277–305, selected by the Lean declaration and syntax oracles. Declaration bodies are unchanged, and their complete closed kernel types are checked against the originals. Vas and contributors, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
Design boundary: actual good-characteristic represented Picard scheme and pointed
Abel-Jacobi morphism. Named downstream consumer: the finite-field divisor-class/
Jacobian point comparison for the order-13 campaign branch.
Full original Picard dependencies: official Anthropic FLT, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2. Actual curve: MazurTheorem,
54d43d8dda8a6fcf069cc02a815f850d762c5c0c. No Picard, group-law, finite-map,
or geometric-integrality assumption is added to the target.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover




namespace GoodCharacteristicGeometryPublicProof


section
noncomputable section
open AlgebraicGeometry CategoryTheory
open _root_.MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13GoodCharacteristicGeometry
universe u
variable (K : Type u) [Field K] (h104 : (104 : K) ≠ 0)
include h104



end MazurTransfer.Order13GoodCharacteristicGeometry
namespace MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]


end MazurTransfer.Order13GoodCharacteristicCurveModel
end
end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: coefficient coordinates for the monic quadratic algebra.
Named downstream consumer: actual hyperelliptic overlap and chart sections.
-/

noncomputable section
namespace MazurTransfer.QuadraticCoordinates
open Polynomial Module
variable (R : Type*) [CommRing R] [Nontrivial R] (f : R)



















end MazurTransfer.QuadraticCoordinates


end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: actual function-field places and closed points from the
literal good-characteristic curve's checked geometry, with every geometry
instance explicit. Named downstream consumer: public effective degree-two
divisor counts. No supplied model or finite-set affine-open hypothesis is
used by this smaller place foundation.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]





















end MazurTransfer.Order13GoodCharacteristicCurveModel

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the literal order-13 curve's genuine place/cohomology and
Riemann–Roch infrastructure over every perfect field where 104 is nonzero.
Named downstream consumer: finite-field degree-two divisor classes and
the actual Picard cardinality calculation over F3 and F5.
Adapted from the previously checked owned characteristic-zero bridge by
using the actual good-characteristic CurveModel and its proved geometry.
Complete official Anthropic FLT mathematical APIs retain their source pin
6e837e75355538c7f80bab5b956861e86c4eacc2 and Apache-2.0 provenance.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]



end MazurTransfer.Order13GoodCharacteristicCurveModel

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the genuine two-affine-open cover of the unchanged glued
order-thirteen curve. Named downstream consumer: the actual structure-sheaf
section comparison with the complete official FLT Cech interface.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]

def ordinaryOpen : (curveScheme K).Opens := (ordinaryChartMap K).opensRange
def reciprocalOpen : (curveScheme K).Opens := (reciprocalChartMap K).opensRange

theorem chart_opens_sup_eq_top : ordinaryOpen K ⊔ reciprocalOpen K = ⊤ := by
  apply top_unique
  intro x _
  change x ∈ Set.range (ordinaryChartMap K) ∨ x ∈ Set.range (reciprocalChartMap K)
  obtain ⟨i, y, hy⟩ := (glueData K).ι_jointly_surjective x
  cases i
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

theorem curveScheme_isSeparated : (curveScheme K).IsSeparated := by
  have h : IsSeparated (curveToBase K ≫ terminal.from (Spec (.of K))) := inferInstance
  refine ⟨?_⟩
  simpa only [terminal.comp_from] using h

def actualTwoAffineOpenCover : (curveScheme K).TwoAffineOpenCover := by
  haveI := curveScheme_isSeparated K
  exact {
    U0 := ordinaryOpen K
    U1 := reciprocalOpen K
    isAffineOpen_U0 := isAffineOpen_opensRange (ordinaryChartMap K)
    isAffineOpen_U1 := isAffineOpen_opensRange (reciprocalChartMap K)
    sup_eq_top := chart_opens_sup_eq_top K
    isAffineOpen_inf := (isAffineOpen_opensRange (ordinaryChartMap K)).inf
      (isAffineOpen_opensRange (reciprocalChartMap K)) }

end MazurTorsion.XOneThirteenProjectiveCurve

end

end



end GoodCharacteristicGeometryPublicProof
#print axioms GoodCharacteristicGeometryPublicProof.MazurTorsion.XOneThirteenProjectiveCurve.actualTwoAffineOpenCover


