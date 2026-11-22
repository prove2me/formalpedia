-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
-- name    : Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:31:21.561842+00:00
-- url     : https://prove2.me/theorems/cd4b2fb3-44e8-4672-833d-e7245eeb5c62
-- title:
--   Matrix Subst Transvection Monomial Of Fixed
-- statement:
--   Definitions and structural lemmas for Matrix Subst Transvection Monomial Of Fixed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/MatrixSubstTransvectionMonomialOfFixed.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G
section mono
variable {B : Type*} [CommRing B] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
  (a b : Fin n) (t : B) (m : ι × Fin n →₀ ℕ)
open Classical in

def sourceExp (l : ι) : ℕ := if l ∈ S then m (sourceVar LL a b l) else 0
def sourceVariableExponent : ι × Fin n →₀ ℕ := ∑ l : ι, Finsupp.single (sourceVar LL a b l) (sourceExp LL S a b m l)
def shiftedExponent (p : ι → ℕ) : ι × Fin n →₀ ℕ :=
  (m - ∑ l : ι, Finsupp.single (sourceVar LL a b l) (p l)) + ∑ l : ι, Finsupp.single (targetVar LL a b l) (p l)
def rootShiftCoefficient (B : Type*) [CommRing B] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (a b : Fin n)
    (m : ι × Fin n →₀ ℕ) (p : ι → ℕ) : B :=
  ∏ l : ι, (if LL.vec l then ((m (l, b)).choose (p l) : B) else (-1 : B) ^ (p l) * ((m (l, a)).choose (p l) : B))
variable {R : Type*} [CommRing R] (φ : R →+* B)
end mono
end Formalism.MainNotions.G.GLWeightTheory


