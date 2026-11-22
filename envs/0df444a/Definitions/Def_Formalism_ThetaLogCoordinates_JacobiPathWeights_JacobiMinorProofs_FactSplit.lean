-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:30:52.843526+00:00
-- url     : https://prove2.me/theorems/a4950331-404b-4cb3-bda9-dfbe01aee56f
-- title:
--   Fact Split
-- statement:
--   Definitions and structural lemmas for Fact Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/FactSplit.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
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
namespace LowHighPartSplit
variable {n : ℕ}
def lowP (i : ℕ) (e : ℕ × Fin n →₀ ℕ) : ℕ × Fin n →₀ ℕ := e.filter fun x => x.1 < i
def highP (i : ℕ) (e : ℕ × Fin n →₀ ℕ) : ℕ × Fin n →₀ ℕ := e.filter fun x => ¬ x.1 < i
def Gc {k : Type*} [CommRing k] (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) (β : ℕ × Fin n →₀ ℕ) :
    MvPolynomial (ℕ × Fin n) k :=
  ∑ e ∈ G.support.filter (fun e => highP i e = β), monomial (lowP i e) (coeff e G)
variable {k : Type*} [Field k] (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]
def Psi : MvPolynomial (ℕ × Fin n) k →+* MvPolynomial (LVar ℕ Empty n) (GenField k n) :=
  ((sharpHom isVec S (genMat k n)⁻¹ (genMat k n)).toRingHom.comp (map (genφ k n))).comp
    (rename (R := k) (Sum.inl : ℕ × Fin n → LVar ℕ Empty n)).toRingHom
def loSet (n : ℕ) (S : Set ℕ) : Set (LVar ℕ Empty n) := {x | ∃ j a, j ∈ S ∧ x = Sum.inl (j, a)}
end LowHighPartSplit
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


