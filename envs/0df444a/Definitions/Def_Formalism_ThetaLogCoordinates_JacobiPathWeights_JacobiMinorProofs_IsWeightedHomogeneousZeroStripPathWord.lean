-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:21:57.616948+00:00
-- url     : https://prove2.me/theorems/af6dbbff-84ad-4d5d-86c6-ba353d64ef88
-- title:
--   Is Weighted Homogeneous Zero Strip Path Word
-- statement:
--   Definitions and structural lemmas for Is Weighted Homogeneous Zero Strip Path Word, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace A1
section Top
variable {σ R M : Type*} [CommRing R] [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]
def LeadAt (w : σ → M) (γ : M) (f t : MvPolynomial σ R) : Prop :=
  (∀ e ∈ f.support, Finsupp.weight w e ≤ γ) ∧ weightedHomogeneousComponent w γ f = t
end Top
def rw_ {n : ℕ} (v : Bool) (j : Fin n) : Fin n := if v then Fin.rev j else j
def rho (n N : ℕ) (v : Bool) : (ℕ × Fin n →₀ ℕ) →+ Lex (Fin n → ℕ) where
  toFun e := toLex fun j => e (N, rw_ v j)
  map_zero' := rfl
  map_add' _ _ := rfl
def wt (n N : ℕ) (v : Bool) : ℕ × Fin n → Lex (Fin n → ℕ) := fun x => rho n N v (Finsupp.single x 1)
abbrev XR (R : Type*) [CommRing R] (n : ℕ) : ℕ → Fin n → MvPolynomial (ℕ × Fin n) R := fun i a => X (i, a)
section Col
variable {R M : Type*} [CommRing R] [AddCommMonoid M] {n : ℕ}
end Col
def Dc {n : ℕ} (μ : ℕ → Fin n → ℤ) (N : ℕ) (c : ℤ) : ℕ × Fin n →₀ ℕ :=
  ∑ m : Fin n, if colHeight (μ (N + 1)) c ≠ colHeight (μ N) c ∧
      m.val = min (colHeight (μ (N + 1)) c) (colHeight (μ N) c) then Finsupp.single (N, m) 1 else 0
def DD {n : ℕ} (μ : ℕ → Fin n → ℤ) (N : ℕ) : ℕ × Fin n →₀ ℕ :=
  ∑ m : Fin n, Finsupp.single (N, m) (|μ (N + 1) m - μ N m|).toNat
end A1
namespace A1
abbrev Idx (n : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (N : ℕ) (ν : Fin n → ℤ) :=
  {μ : ℕ → Fin n → ℤ // IsPath n isVec B μ N ∧ μ N = ν ∧ ∀ i, N < i → μ i = 0}
end A1
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


