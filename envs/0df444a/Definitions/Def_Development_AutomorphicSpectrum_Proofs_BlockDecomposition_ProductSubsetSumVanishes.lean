-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSubsetSumVanishes
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSubsetSumVanishes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:29.754545+00:00
-- url     : https://prove2.me/theorems/d1bfaf29-fe96-4761-8471-b00eb65550e7
-- title:
--   Product Subset Sum Vanishes
-- statement:
--   Definitions and structural lemmas for Product Subset Sum Vanishes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSubsetSumVanishes.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace GlobalTheory.CompanionTheory.SubsetSum
noncomputable def subsetPoly {R : Type*} [CommRing R] (r : ℕ) (M : Multiset R) : R[X] :=
  ((M.powersetCard r).map fun S => X - C S.sum).prod
noncomputable def evalCoef {R : Type*} [CommRing R] (n : ℕ) (P : R[X]) :
    MvPolynomial (Fin n) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) fun j => P.coeff (n - (j + 1))
def IsUniv (n r : ℕ) (Φ : (MvPolynomial (Fin n) ℤ)[X]) : Prop :=
  ∀ (R : Type) [CommRing R] (M : Multiset R), Multiset.card M = n →
    Φ.map (evalCoef n (M.map fun x => X + C x).prod) = subsetPoly r M
noncomputable def gen {S : Type*} [CommRing S] (d : ℕ) (c : Fin d → S) : Polynomial S :=
  Polynomial.X ^ d + ∑ i : Fin d, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)
end GlobalTheory.CompanionTheory.SubsetSum


