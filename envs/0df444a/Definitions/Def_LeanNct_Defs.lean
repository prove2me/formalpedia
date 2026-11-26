-- Prove2me | Definitions.Def_LeanNct_Defs
-- name    : LeanNct_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:37:53.281834+00:00
-- url     : https://prove2.me/theorems/0afb7d12-1035-545f-883b-ab7feaa6950a
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Floris van Doorn, Polona Durcik, Joris Roos, Lenka Slavíková, Christoph Thiele (roos-j/lean-nct; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Norm-variation of multiple ergodic averages for commuting transformations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Defs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
namespace nCT
@[expose] public section
noncomputable section
open MeasureTheory Set ENNReal
variable {n : ℕ}
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
def multipleErgodicAverage (f : Fin n → X → ℂ) (T : Fin n → X → X) (N : ℕ) (x : X) :=
  (N : ℝ)⁻¹ * ∑ i : Fin N, ∏ j : Fin n, (f j) ((T j)^[i] x)
def variationSeminorm {B : Type*} [AddCommGroup B]
    (enorm : B → ℝ≥0∞) (r : ℝ) (a : ℕ → B) :=
  ⨆ (J : ℕ) (t : {t : Fin (J + 1) → ℕ // StrictMono t ∧ ∀ j, 0 < t j}),
    (∑ j : Fin J, enorm (a (t.1 j.succ) - a (t.1 j.castSucc)) ^ r) ^ r⁻¹
scoped notation:max "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
def rescale (χ : ℝ → ℝ) (t : ℝ) (x : ℝ) := t⁻¹ * χ (t⁻¹ * x)
abbrev unitVector (i : Fin n) : ℝ^n := EuclideanSpace.single i (1 : ℝ)
@[inherit_doc unitVector]
scoped notation "𝐞" => unitVector
scoped notation "𝟙" => indicator (f := (1 : ℝ → ℝ))
def twistedAverage (χ : ℝ → ℝ) (f : Fin n → ℝ^n → ℝ)
    (x : ℝ^n) := ∫ s, χ s * ∏ i, f i (x + s • 𝐞 i)
def rescaledTwistedAverage (t : ℝ) (χ : ℝ → ℝ) (f : Fin n → ℝ^n → ℝ) :=
    twistedAverage (rescale χ t) f
@[inherit_doc rescaledTwistedAverage]
scoped notation "𝐀" => rescaledTwistedAverage
end
end
end nCT


