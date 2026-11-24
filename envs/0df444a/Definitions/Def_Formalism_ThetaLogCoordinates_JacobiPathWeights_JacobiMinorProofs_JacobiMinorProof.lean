-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:31.200714+00:00
-- url     : https://prove2.me/theorems/c34f2380-b1b6-4ece-a879-c97b7d7b4942
-- title:
--   Jacobi Minor Proof
-- statement:
--   Definitions and structural lemmas for Jacobi Minor Proof, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/JacobiMinorProof.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_genMat_inv_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_genMat_mul_inv

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
namespace SignTwistStarLemmas
variable {R : Type} [CommRing R] {n : ℕ}
def epsN (J : Finset (Fin n)) : ℕ := ∑ j ∈ J, (n + 1 + j.val)
def star (A : Form R n) : Form R n := fun J => (-1) ^ epsN J * A Jᶜ
end SignTwistStarLemmas
open SignTwistStarLemmas
namespace SignTwistStarLemmas
variable {k : Type} [Field k] {n : ℕ}
def genU (k : Type) [Field k] (n : ℕ) : (Matrix (Fin n) (Fin n) (GenField k n))ˣ :=
  ⟨genMat k n, (genMat k n)⁻¹, genMat_mul_inv k n, genMat_inv_mul k n⟩
def colT (lo : ℤ) (C : ℕ) (I : ℤ → Finset (Fin n)) : Fin C → Finset (Fin n) :=
  fun t => hatIdx I (lo + 1 + (t.val : ℤ))
def sgnU (k : Type) [Field k] (μ : Fin n → ℤ) (I : ℤ → Finset (Fin n)) (c : ℤ) : kˣ :=
  if 1 ≤ c then 1 else (-1) ^ (epsN (canIdx μ c)ᶜ + epsN (I c)ᶜ)
end SignTwistStarLemmas
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


