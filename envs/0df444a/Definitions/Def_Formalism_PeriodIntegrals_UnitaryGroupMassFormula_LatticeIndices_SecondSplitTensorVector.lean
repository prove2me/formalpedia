-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitTensorVector
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitTensorVector
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:57.586049+00:00
-- url     : https://prove2.me/theorems/4f11cc17-47f5-4f4c-bae9-36f2d1fa6f60
-- title:
--   Second Split Tensor Vector
-- statement:
--   Definitions and structural lemmas for Second Split Tensor Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondSplitTensorVector.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_StRedCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]
def IntV (v : n → K) : Prop := ∀ i, v i ∈ O
def IntM (M : Matrix n n K) : Prop := ∀ i j, M i j ∈ O
variable (θ : T ≃ₐ[K] K × K) (J : Matrix n n T) (P : GL n K)
def Lat : Set (n → T) :=
  {x | IntV O (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ fun j => t1 θ (x j)) ∧
    IntV O (((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) *ᵥ fun j => t2 θ (x j))}
def tv (j : n) : n → T := fun i => θ.symm ((P : Matrix n n K) i j, 0)
def conjPrime₂ (g : GL n T) : Matrix n n K :=
  ((P⁻¹ : GL n K) : Matrix n n K) * (g : Matrix n n T).map (t1 θ) * (P : Matrix n n K)
end MassDataIdxCore


