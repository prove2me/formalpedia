-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMultiHomog
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMultiHomog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:29.422804+00:00
-- url     : https://prove2.me/theorems/0ea38487-8ec2-4244-9e65-5cffd0e0b2dc
-- title:
--   PFlag Multi Homog
-- statement:
--   Definitions and structural lemmas for PFlag Multi Homog, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMultiHomog.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace FlagMultiHomog
section Kernel
end Kernel
section Scale
variable {L : Type} [DecidableEq L] {κ : L → Type} {R : Type} [CommRing R]
def scaleHom (φ : MvPolynomial (Σ b, κ b) ℤ →+* R) : MvPolynomial (Σ b, κ b) ℤ →+* MvPolynomial L R :=
  eval₂Hom (Int.castRingHom _) fun q => C (φ (X q)) * X q.1
end Scale
section Flag
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {N1 n : ℕ}
abbrev TRing (P : Ideal (MRing ι)) (n : ℕ) : Type := MvPolynomial (Fin n × Fin n) (FnField P)
abbrev LRing (P : Ideal (MRing ι)) (n : ℕ) : Type := MvPolynomial (K ⊕ Fin (n - 1)) (TRing P n)
abbrev OmegaF (P : Ideal (MRing ι)) (n : ℕ) : Type := FractionRing (LRing P n)
def iota (P : Ideal (MRing ι)) (n : ℕ) : FnField P →+* OmegaF P n :=
  (algebraMap (LRing P n) (OmegaF P n)).comp (C.comp C)
def lam (P : Ideal (MRing ι)) (n : ℕ) (b : K ⊕ Fin (n - 1)) : OmegaF P n :=
  algebraMap (LRing P n) (OmegaF P n) (X b)
def zScale (P : Ideal (MRing ι)) (n : ℕ) : MRing ι →+* LRing P n :=
  eval₂Hom (Int.castRingHom (LRing P n)) fun p => C (C (genPt P p)) * X (Sum.inl p.1)
end Flag
section Minor
end Minor
section Flag2
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {N1 n : ℕ}
def lamN (P : Ideal (MRing ι)) (n : ℕ) (i : ℕ) : OmegaF P n :=
  if h : i + 1 < n then lam P n (Sum.inr ⟨i, by omega⟩) else 1
def diagE (P : Ideal (MRing ι)) [P.IsPrime] (n : ℕ) (i : ℕ) : OmegaF P n :=
  lamN P n i / (if i = 0 then 1 else lamN P n (i - 1))
end Flag2
end FlagMultiHomog
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


