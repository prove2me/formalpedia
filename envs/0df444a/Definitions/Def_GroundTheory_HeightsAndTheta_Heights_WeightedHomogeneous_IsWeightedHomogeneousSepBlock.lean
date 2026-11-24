-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:21.655711+00:00
-- url     : https://prove2.me/theorems/79c0b4a6-d490-4528-a45a-68053ef34895
-- title:
--   Is Weighted Homogeneous Sep Block
-- statement:
--   Definitions and structural lemmas for Is Weighted Homogeneous Sep Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Module
noncomputable section
namespace BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
abbrev BlockRing (n : ι → ℕ) (k₀ : ι) : Type := MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ
def sepBlock (k₀ : ι) : MvPolynomial (Coord n) ℤ →ₐ[ℤ] MvPolynomial (Coord n) (BlockRing n k₀) :=
  aeval fun v ↦ if h : v.1 = k₀ then C (X ⟨(), Fin.cast (by rw [h]) v.2⟩) else X v
def joinBlock (k₀ : ι) : MvPolynomial (Coord n) (BlockRing n k₀) →+* MvPolynomial (Coord n) ℤ :=
  eval₂Hom (rename (blockIncl (n := n) k₀)).toRingHom X
def evalBlock {k₀ : ι} (w : Cone (fun _ : Unit ↦ n k₀) ℂ) : BlockRing n k₀ →+* ℂ :=
  eval₂Hom (Int.castRingHom ℂ) fun v ↦ w v.1 v.2
def atBlock (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) :
    MvPolynomial (Coord n) ℤ →+* MvPolynomial (Coord n) ℂ :=
  (map (evalBlock w)).comp (sepBlock k₀).toRingHom
def withBlock (k₀ : ι) (w₀ : Fin (n k₀ + 1) → ℂ) (x : Coord n → ℂ) : Cone n ℂ :=
  Function.update (fun k (i : Fin (n k + 1)) ↦ x ⟨k, i⟩) k₀ w₀
def offDeg (k₀ : ι) (D : ℕ) : ι → ℕ := Function.update (fun _ ↦ D) k₀ 0
variable (n) in

def offMonos (k₀ : ι) (D : ℕ) : Finset (Coord n →₀ ℕ) :=
  (Finset.finsuppAntidiag Finset.univ (∑ k, offDeg k₀ D k)).filter
    fun μ ↦ Finsupp.weight (coordDeg n) μ = offDeg k₀ D
def fibreIdeal (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) :
    Ideal (MvPolynomial (Coord n) ℂ) :=
  Ideal.span (atBlock k₀ w '' P.ideal)
def coeffVec (M : Finset (Coord n →₀ ℕ)) : MvPolynomial (Coord n) ℂ →ₗ[ℂ] (M → ℂ) :=
  LinearMap.pi fun μ ↦ lcoeff ℂ μ.1
variable (n) in

def homogIn (P : ArithVariety n) (k₀ : ι) (D : ℕ) : Set (MvPolynomial (Coord n) ℤ) :=
  {q | q ∈ P.ideal ∧ IsWeightedHomogeneous (coordDeg n) (sepBlock k₀ q) (offDeg k₀ D)}
end BlockSurjectivity
end
end GroundTheory.Heights₂.Heights


