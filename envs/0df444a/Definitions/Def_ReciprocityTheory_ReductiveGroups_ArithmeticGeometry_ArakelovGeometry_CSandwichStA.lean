-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStA
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:52:51.84949+00:00
-- url     : https://prove2.me/theorems/fa8ff6e9-54db-4cb0-9833-81468a1f4097
-- title:
--   CSandwich St A
-- statement:
--   Definitions and structural lemmas for CSandwich St A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CNormSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_HadZSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
def secTraceHom {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ} (x : κ → Ω)
    (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) (n : ℕ) : sec ℤ x n →+ Ω :=
  AddMonoidHom.mk' (fun s => secTrace x e n s) fun s t => secTrace_add x e h n s.2 t.2
def adtEnum (D N : ℕ) (i : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card) : Fin (D + 1) → ℕ :=
  ((Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm i).1
def monoDiag (D N δ : ℕ) : Matrix (Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card))
    (Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card)) ℂ :=
  Matrix.diagonal fun p => ((monoNormSq (adtEnum D N (finProdFinEquiv.symm p).2) : ℝ) : ℂ)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


