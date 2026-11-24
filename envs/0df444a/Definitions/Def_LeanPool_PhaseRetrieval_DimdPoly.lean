-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly
-- name    : LeanPool_PhaseRetrieval_DimdPoly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:23:51.011696+00:00
-- url     : https://prove2.me/theorems/1540de23-1a54-4376-bed0-2ea183afea36
-- title:
--   Dimd Poly
-- statement:
--   Definitions and structural lemmas for Dimd Poly, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Auxiliary
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
noncomputable section
namespace DimdPolyShowcaseChallenge
def HermitePoly (k n : ℕ) (z : ℂ) : ℂ :=
  (((Real.sqrt ((Nat.factorial n : ℝ) * (Nat.factorial k : ℝ))) : ℂ)⁻¹) *
    ∑ j ∈ Finset.range (min n k + 1),
      ((-1 : ℂ) ^ j) * (Nat.factorial j : ℂ) *
        (Nat.choose n j : ℂ) * (Nat.choose k j : ℂ) *
        z ^ (n - j) * (star z) ^ (k - j)
variable {d : ℕ}
def Φ (κ α : Fin d -> ℕ) (z : Fin d -> ℂ) : ℂ :=
  ∏ q : Fin d, HermitePoly (κ q) (α q) (z q)
def TrueHermitePoly (κ : Fin d -> ℕ)
    (F : Finsupp (Fin d -> ℕ) ℂ) : (Fin d -> ℂ) -> ℂ :=
  fun z => F.sum fun α c => c * Φ κ α z
def TrueHermitePolys (κ : Fin d -> ℕ) :
    Set ((Fin d -> ℂ) -> ℂ) :=
  Set.range (TrueHermitePoly κ)
def gaussianDensity (z : Fin d -> ℂ) : ℝ :=
  (1 / Real.pi ^ d) * Real.exp (-Finset.sum Finset.univ fun q : Fin d => ‖z q‖ ^ 2)
def γ : MeasureTheory.Measure (Fin d -> ℂ) :=
  MeasureTheory.volume.withDensity fun z => ENNReal.ofReal (gaussianDensity z)
def TrueHermiteFunctions (κ : Fin d -> ℕ) :
    Set (MeasureTheory.Lp ℂ (p:=2) (γ (d := d))) :=
  closure { f | ∃ P ∈ TrueHermitePolys κ, f =ᵐ[γ] P }
end DimdPolyShowcaseChallenge


