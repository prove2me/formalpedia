-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:47.246008+00:00
-- url     : https://prove2.me/theorems/92ed3150-fe17-4090-9295-e4bd61ca0cb1
-- title:
--   Point Height Degree Hypotheses
-- statement:
--   Definitions and structural lemmas for Point Height Degree Hypotheses, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)
noncomputable section
section Homogenize
variable (K : Type) [Field K] (r : ℕ)
def homExp : (Fin (r + 1) →₀ ℕ) →+ (Unit ⊕ Fin r →₀ ℕ) where
  toFun a := Finsupp.equivFunOnFinite.symm (Sum.elim (fun _ ↦ ∑ i, a i) fun k ↦ a k.succ)
  map_zero' := by ext o; cases o <;> simp
  map_add' a b := by ext o; cases o <;> simp [Finset.sum_add_distrib]
def homMap : MvPolynomial (Fin (r + 1)) K →+* MvPolynomial (Unit ⊕ Fin r) K :=
  AddMonoidAlgebra.mapDomainRingHom K (homExp r)
def fieldMap :
    MvPolynomial (Unit ⊕ Fin r) K →+* MvPolynomial Unit (FractionRing (MvPolynomial (Fin r) K)) :=
  (MvPolynomial.map (algebraMap (MvPolynomial (Fin r) K) _)).comp
    (sumAlgEquiv K Unit (Fin r)).toRingEquiv.toRingHom
def coneAff : MvPolynomial (Fin (r + 1)) K →+* MvPolynomial Unit (FractionRing (MvPolynomial (Fin r) K)) :=
  (fieldMap K r).comp (homMap K r)
end Homogenize
section Kernels
variable {K : Type} [Field K] [NumberField K] {e r : ℕ}
variable (e r) in

def oneBlockReindex : Coord (oneBlockSizes e r) → (Σ _ : Unit, Fin (e + 1) × Fin (r + 1)) :=
  fun v ↦ ⟨(), oneBlockIndex e r v.2⟩
variable (e r) in

def oneBlockReindexInv : (Σ _ : Unit, Fin (e + 1) × Fin (r + 1)) → Coord (oneBlockSizes e r) :=
  fun p ↦ ⟨(), (oneBlockIndex e r).symm p.2⟩
end Kernels
section Points
variable {K : Type} [Field K] [NumberField K] {e r : ℕ}
def coneToPairs {F : Type*} (z : Cone (oneBlockSizes e r) F) :
    (Σ _ : Unit, Fin (e + 1) × Fin (r + 1)) → F :=
  fun p ↦ z () ((oneBlockIndex e r).symm p.2)
end Points
section Metric
open Matrix
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {e r : ℕ}
end Metric
section Line
variable {K : Type} [Field K] [NumberField K] {K' : Type} [Field K'] [NumberField K'] [Algebra K K']
  {n : ℕ}
variable (K' n) in

def intoField : (Fin n → 𝓞 K') →ₗ[𝓞 K'] (Fin n → K') :=
  LinearMap.compLeft (Algebra.linearMap (𝓞 K') K') (Fin n)
variable (K K' n) in

abbrev stdLatticeExt : Submodule (𝓞 K') (Fin n → K') :=
  Submodule.span (𝓞 K')
    ((fun w : Fin n → K ↦ fun j ↦ algebraMap K K' (w j)) '' (HermLattice.standard K n).lattice)
end Line
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close


