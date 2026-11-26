-- Prove2me | Definitions.Def_LeanNct_Auto_Preliminaries_Notation
-- name    : LeanNct_Auto_Preliminaries_Notation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:37:52.269643+00:00
-- url     : https://prove2.me/theorems/c05af76f-764f-504f-9041-d1bf4534c2fb
-- title:
--   Notation
-- statement:
--   Definitions and structural lemmas for Notation, from Floris van Doorn, Polona Durcik, Joris Roos, Lenka Slavíková, Christoph Thiele (roos-j/lean-nct; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Norm-variation of multiple ergodic averages for commuting transformations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Notation.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Auto
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable def ntnCoordinateSum {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, x i
noncomputable def coordinateRestriction {n : ℕ} (I : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 fun i ↦ x i
noncomputable def gaussian (x : ℝ) : ℝ :=
  Real.exp (-Real.pi * x ^ 2)
noncomputable def rescaled {n : ℕ} (t : ℝ)
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x ↦ t⁻¹ ^ n * ψ (t⁻¹ • x)
noncomputable def tensorProduct {n m : ℕ} {𝕜 : Type*} [Mul 𝕜]
    (φ : EuclideanSpace ℝ (Fin n) → 𝕜) (ψ : EuclideanSpace ℝ (Fin m) → 𝕜) :
    EuclideanSpace ℝ (Fin (n + m)) → 𝕜 :=
  fun z ↦ φ (EuclideanSpace.finAddEquivProd z).1 * ψ (EuclideanSpace.finAddEquivProd z).2
noncomputable def tensorPower {𝕜 : Type*} [CommMonoid 𝕜]
    (χ : ℝ → 𝕜) (d : ℕ) : EuclideanSpace ℝ (Fin d) → 𝕜 :=
  fun x ↦ ∏ i, χ (x i)
noncomputable def bracketBump (x : ℝ) : ℝ :=
  (1 + |x|)⁻¹
noncomputable def scaledBracketBump (N : ℕ) (s x : ℝ) : ℝ :=
  s⁻¹ * (1 + |s⁻¹ * x|)⁻¹ ^ N
noncomputable def scaledBracketBumpReal (N s x : ℝ) : ℝ :=
  s⁻¹ * Real.rpow (1 + |s⁻¹ * x|) (-N)
end Auto


