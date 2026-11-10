-- Prove2me | Definitions.Def_BooleanHiddenPartition_LowerBounds_Scalar
-- name    : BooleanHiddenPartition_LowerBounds_Scalar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T15:20:17.773967+00:00
-- url     : https://prove2.me/theorems/521c7bd9-165b-4f3d-92ab-d8e6d7f33f1f
-- title:
--   Boolean cube masses, moments and scalar norms
-- statement:
--   A cube point is a function from Fin n to Bool, with true read as −1 and false as +1. Uniform expectation, parity, Fourier coefficients and the noise operator are aliases of the referenced cube package. A counting mass q has values in [0,1] summing to one; moments f q d means that every parity of size less than d has zero q-weighted correlation with f.
--
--   $$\widehat h(S)=2^{-n}\sum_xh(x)\chi_S(x),\qquad \sum_xq(x)f(x)\chi_S(x)=0\quad(|S|<d).$$
--
--   The scalar Lp norm uses uniform expectation at finite p and the maximum absolute value at infinity. NoiseRange records the complete endpoint conventions: all noise parameters in [0,1] for p=q=1 or p=q=infinity, zero noise for finite p and q=infinity, and the printed square-root threshold for finite q>1. logCost is minus the base-two logarithm. These definitions support the scalar Fourier and posterior estimates; no hypercontractive inequality is assumed.
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, STOC 2027 submission #1085 (October 2026), pp. 13–15, definitions and conventions.

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Cube

open scoped BigOperators ENNReal
open Classical
set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds

noncomputable section

abbrev Cube (n : ℕ) := Fin n → Bool
abbrev sign := OptInapprox.MaxCut.pm
abbrev cubeMean {n : ℕ} := @OptInapprox.MaxCut.cubeE n
abbrev parity {n : ℕ} := @OptInapprox.MaxCut.chi n
abbrev fourier {n : ℕ} := @OptInapprox.MaxCut.fourier n
abbrev noise {n : ℕ} := @OptInapprox.MaxCut.bonamiBeckner n

/-- A counting-measure mass function, including possible zero masses. -/
def IsMass {X : Type} [Fintype X] (q : X → ℝ) : Prop :=
  (∀ x, 0 ≤ q x ∧ q x ≤ 1) ∧ ∑ x, q x = 1

def moments {k : ℕ} (f : Cube k → Bool) (q : Cube k → ℝ) (d : ℕ) : Prop :=
  ∀ S : Finset (Fin k), S.card < d → ∑ x, q x * sign (f x) * parity S x = 0

/-- The uniform cube Lᵖ norm, with the maximum norm at infinity. -/
def cubeNorm {n : ℕ} (p : ℝ≥0∞) (f : Cube n → ℝ) : ℝ :=
  if p = ⊤ then sSup (Set.range (fun x => |f x|))
  else (cubeMean (fun x => |f x| ^ p.toReal)) ^ (1 / p.toReal)

/-- Limiting conventions for the endpoints in Fact 3. -/
def NoiseRange (p q : ℝ≥0∞) (δ : ℝ) : Prop :=
  0 ≤ δ ∧ δ ≤ 1 ∧
  (q = 1 ∨ (q = ⊤ ∧ (p = ⊤ ∨ δ = 0)) ∨
    (q ≠ ⊤ ∧ 1 < q.toReal ∧ δ ≤ Real.sqrt ((p.toReal - 1) / (q.toReal - 1))))

def logCost (Q : ℝ) : ℝ := - Real.log Q / Real.log 2

end

end BooleanHiddenPartition.LowerBounds


