-- Prove2me | Definitions.Def_D1Bound5_FiniteMMatrix_Definitions
-- name    : D1Bound5_FiniteMMatrix_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:25:18.151223+00:00
-- url     : https://prove2.me/theorems/d2cb784d-7ec1-43a6-b825-a224a4f32133
-- title:
--   Finite MMatrix
-- statement:
--   An integer factored monomial in the ordinary three-anchor order-two residue matrix. Exponents are stored explicitly so the height certificate can be checked over a finite list of natural numbers. The named objects in this bundle include `FiniteMTerm`, `FiniteMTerm.abp`, `FiniteMTerm.ap`, `FiniteMTerm.asp`, `FiniteMTerm.bp`, `FiniteMTerm.bsp`, `FiniteMTerm.coeff`, `FiniteMTerm.sp` and 11 further declarations.
-- source:
--   D1Bound5/FiniteMMatrix.lean, lines 10-22, SHA-256 8af7f9699b9fc84a48e57a25795d84c9aefe6f4ade8e20a65b9b82216db511c9; D1Bound5/FiniteMMatrix.lean, lines 24-26, SHA-256 8af7f9699b9fc84a48e57a25795d84c9aefe6f4ade8e20a65b9b82216db511c9; D1Bound5/FiniteMMatrix.lean, lines 28-118, SHA-256 8af7f9699b9fc84a48e57a25795d84c9aefe6f4ade8e20a65b9b82216db511c9; D1Bound5/FiniteMMatrix.lean, lines 120-121, SHA-256 8af7f9699b9fc84a48e57a25795d84c9aefe6f4ade8e20a65b9b82216db511c9; D1Bound5/FiniteMMatrix.lean, lines 123-126, SHA-256 8af7f9699b9fc84a48e57a25795d84c9aefe6f4ade8e20a65b9b82216db511c9; D1Bound5/FiniteMMatrix.lean, lines 128-130, SHA-256 8af7f9699b9fc84a48e57a25795d84c9aefe6f4ade8e20a65b9b82216db511c9; D1Bound5/FiniteMMatrix.lean, lines 132-135, SHA-256 8af7f9699b9fc84a48e57a25795d84c9aefe6f4ade8e20a65b9b82216db511c9; D1Bound5/FiniteMMatrix.lean, lines 137-139, SHA-256 8af7f9699b9fc84a48e57a25795d84c9aefe6f4ade8e20a65b9b82216db511c9; D1Bound5/FiniteMMatrix.lean, lines 141-143, SHA-256 8af7f9699b9fc84a48e57a25795d84c9aefe6f4ade8e20a65b9b82216db511c9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- An integer factored monomial in the ordinary three-anchor order-two
residue matrix. Exponents are stored explicitly so the height certificate
can be checked over a finite list of natural numbers. -/
structure FiniteMTerm where
  coeff : ℤ
  ap : ℕ
  bp : ℕ
  sp : ℕ
  abp : ℕ
  asp : ℕ
  bsp : ℕ
  vp : ℕ
  deriving DecidableEq

def finiteMTermEval {R : Type*} [CommRing R] (t : FiniteMTerm)
    (a b s v : R) : R :=
  (t.coeff : R)*a^t.ap*b^t.bp*s^t.sp*(a-b)^t.abp*(a-s)^t.asp*(b-s)^t.bsp*v^t.vp

/-- The exact finite Taylor residue terms after both the manuscript's row
factors and the three root-column anchor factors have been removed. -/
def finiteMTerms : Fin 4 → Fin 4 → List FiniteMTerm :=
  ![![[⟨48, 0, 0, 2, 3, 3, 3, 2⟩,
      ⟨64, 0, 1, 1, 3, 3, 3, 2⟩,
      ⟨48, 0, 2, 0, 3, 3, 3, 2⟩,
      ⟨64, 1, 0, 1, 3, 3, 3, 2⟩,
      ⟨64, 1, 1, 0, 3, 3, 3, 2⟩,
      ⟨48, 2, 0, 0, 3, 3, 3, 2⟩,
      ⟨80, 0, 0, 1, 3, 3, 3, 1⟩,
      ⟨80, 0, 1, 0, 3, 3, 3, 1⟩,
      ⟨80, 1, 0, 0, 3, 3, 3, 1⟩,
      ⟨30, 0, 0, 0, 3, 3, 3, 0⟩],
    [⟨32, 3, 0, 1, 1, 0, 3, 2⟩,
      ⟨32, 3, 1, 0, 0, 1, 3, 2⟩,
      ⟨40, 3, 0, 0, 1, 1, 3, 1⟩,
      ⟨-48, 3, 0, 0, 1, 1, 3, 2⟩],
    [⟨32, 0, 3, 1, 1, 3, 0, 2⟩,
      ⟨40, 0, 3, 0, 1, 3, 1, 1⟩,
      ⟨-32, 1, 3, 0, 0, 3, 1, 2⟩,
      ⟨-48, 0, 3, 0, 1, 3, 1, 2⟩],
    [⟨40, 0, 0, 3, 3, 1, 1, 1⟩,
      ⟨-32, 0, 1, 3, 3, 1, 0, 2⟩,
      ⟨-32, 1, 0, 3, 3, 0, 1, 2⟩,
      ⟨-48, 0, 0, 3, 3, 1, 1, 2⟩]],
  ![[⟨-32, 0, 0, 1, 4, 4, 3, 2⟩,
      ⟨-32, 0, 1, 0, 4, 4, 3, 2⟩,
      ⟨-48, 1, 0, 0, 4, 4, 3, 2⟩,
      ⟨-40, 0, 0, 0, 4, 4, 3, 1⟩],
    [⟨48, 2, 0, 2, 2, 0, 3, 2⟩,
      ⟨64, 2, 1, 1, 1, 1, 3, 2⟩,
      ⟨48, 2, 2, 0, 0, 2, 3, 2⟩,
      ⟨80, 2, 0, 1, 2, 1, 3, 1⟩,
      ⟨80, 2, 1, 0, 1, 2, 3, 1⟩,
      ⟨30, 2, 0, 0, 2, 2, 3, 0⟩,
      ⟨-64, 2, 0, 1, 2, 1, 3, 2⟩,
      ⟨-64, 2, 1, 0, 1, 2, 3, 2⟩,
      ⟨-80, 2, 0, 0, 2, 2, 3, 1⟩,
      ⟨48, 2, 0, 0, 2, 2, 3, 2⟩],
    [⟨32, 0, 3, 1, 1, 4, 0, 2⟩,
      ⟨40, 0, 3, 0, 1, 4, 1, 1⟩,
      ⟨-48, 1, 3, 0, 0, 4, 1, 2⟩,
      ⟨-32, 0, 3, 0, 1, 4, 1, 2⟩],
    [⟨40, 0, 0, 3, 4, 1, 1, 1⟩,
      ⟨-32, 0, 1, 3, 4, 1, 0, 2⟩,
      ⟨-48, 1, 0, 3, 4, 0, 1, 2⟩,
      ⟨-32, 0, 0, 3, 4, 1, 1, 2⟩]],
  ![[⟨-32, 0, 0, 1, 4, 3, 4, 2⟩,
      ⟨-48, 0, 1, 0, 4, 3, 4, 2⟩,
      ⟨-32, 1, 0, 0, 4, 3, 4, 2⟩,
      ⟨-40, 0, 0, 0, 4, 3, 4, 1⟩],
    [⟨-32, 3, 0, 1, 1, 0, 4, 2⟩,
      ⟨-48, 3, 1, 0, 0, 1, 4, 2⟩,
      ⟨-40, 3, 0, 0, 1, 1, 4, 1⟩,
      ⟨32, 3, 0, 0, 1, 1, 4, 2⟩],
    [⟨48, 0, 2, 2, 2, 3, 0, 2⟩,
      ⟨80, 0, 2, 1, 2, 3, 1, 1⟩,
      ⟨30, 0, 2, 0, 2, 3, 2, 0⟩,
      ⟨-64, 1, 2, 1, 1, 3, 1, 2⟩,
      ⟨-80, 1, 2, 0, 1, 3, 2, 1⟩,
      ⟨48, 2, 2, 0, 0, 3, 2, 2⟩,
      ⟨-64, 0, 2, 1, 2, 3, 1, 2⟩,
      ⟨-80, 0, 2, 0, 2, 3, 2, 1⟩,
      ⟨64, 1, 2, 0, 1, 3, 2, 2⟩,
      ⟨48, 0, 2, 0, 2, 3, 2, 2⟩],
    [⟨40, 0, 0, 3, 4, 1, 1, 1⟩,
      ⟨-48, 0, 1, 3, 4, 1, 0, 2⟩,
      ⟨-32, 1, 0, 3, 4, 0, 1, 2⟩,
      ⟨-32, 0, 0, 3, 4, 1, 1, 2⟩]],
  ![[⟨-48, 0, 0, 1, 3, 4, 4, 2⟩,
      ⟨-32, 0, 1, 0, 3, 4, 4, 2⟩,
      ⟨-32, 1, 0, 0, 3, 4, 4, 2⟩,
      ⟨-40, 0, 0, 0, 3, 4, 4, 1⟩],
    [⟨-48, 3, 0, 1, 1, 0, 4, 2⟩,
      ⟨-32, 3, 1, 0, 0, 1, 4, 2⟩,
      ⟨-40, 3, 0, 0, 1, 1, 4, 1⟩,
      ⟨32, 3, 0, 0, 1, 1, 4, 2⟩],
    [⟨-48, 0, 3, 1, 1, 4, 0, 2⟩,
      ⟨-40, 0, 3, 0, 1, 4, 1, 1⟩,
      ⟨32, 1, 3, 0, 0, 4, 1, 2⟩,
      ⟨32, 0, 3, 0, 1, 4, 1, 2⟩],
    [⟨30, 0, 0, 2, 3, 2, 2, 0⟩,
      ⟨-80, 0, 1, 2, 3, 2, 1, 1⟩,
      ⟨48, 0, 2, 2, 3, 2, 0, 2⟩,
      ⟨-80, 1, 0, 2, 3, 1, 2, 1⟩,
      ⟨64, 1, 1, 2, 3, 1, 1, 2⟩,
      ⟨48, 2, 0, 2, 3, 0, 2, 2⟩,
      ⟨-80, 0, 0, 2, 3, 2, 2, 1⟩,
      ⟨64, 0, 1, 2, 3, 2, 1, 2⟩,
      ⟨64, 1, 0, 2, 3, 1, 2, 2⟩,
      ⟨48, 0, 0, 2, 3, 2, 2, 2⟩]]]

def finiteMRowFactor {R : Type*} [CommRing R] (a b s : R) : Fin 4 → R :=
  ![(a-b)*(a-s)*(b-s), a*(b-s), b*(a-s), s*(a-b)]

def finiteMDividedMatrix {R : Type*} [CommRing R] (a b s c : R) :
    Matrix (Fin 4) (Fin 4) R :=
  Matrix.of (fun i j => ((finiteMTerms i j).map
    (fun t => finiteMTermEval t a b s (![c,a*c+1,b*c+1,s*c+1] j))).sum)

def finiteMMatrix {R : Type*} [CommRing R] (a b s c : R) :
    Matrix (Fin 4) (Fin 4) R :=
  finiteMDividedMatrix a b s c * Matrix.diagonal ![1,a,b,s]

/-- Integer coefficient weight using |a-b|≤2B, |a-s|,|b-s|≤2S,
and |u*c+1|≤2SC. -/
def finiteMTermWeight (t : FiniteMTerm) : ℕ :=
  t.coeff.natAbs * 2^(t.abp+t.asp+t.bsp+t.vp)

def finiteMTermAdmissible (t : FiniteMTerm) : Prop :=
  t.sp+t.asp+t.bsp+t.vp ≤ 8 ∧
  t.ap+t.bp+t.sp+t.abp+t.asp+t.bsp+t.vp ≤ 11 ∧ t.vp ≤ 2

instance (t : FiniteMTerm) : Decidable (finiteMTermAdmissible t) := by
  unfold finiteMTermAdmissible
  infer_instance










end D1Bound5
end


