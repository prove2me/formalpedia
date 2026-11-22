-- Prove2me | Definitions.Def_Formalism_FockGram_FockGramProofs_DetSymPow
-- name    : Formalism_FockGram_FockGramProofs_DetSymPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:35.89807+00:00
-- url     : https://prove2.me/theorems/608cf618-7b79-4657-af17-7d93b9438d53
-- title:
--   Det Sym Pow
-- statement:
--   Definitions and structural lemmas for Det Sym Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/DetSymPow.lean

import Definitions.Def_Formalism_FockGram_StatementFock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix MvPolynomial
noncomputable section
namespace Formalism.E
section SlopeTestRemainingChoices
variable {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]
def spLin (A : Matrix σ σ R) (i : σ) : MvPolynomial σ R := ∑ j, C (A i j) * X j
def spRow (A : Matrix σ σ R) (s : Multiset σ) : MvPolynomial σ R := (s.map (spLin A)).prod
def spHom (A : Matrix σ σ R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R := aeval (spLin A)
end SlopeTestRemainingChoices
section Field
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type*} [Field K] [CharZero K]
end Field
def genMat (σ : Type*) : Matrix σ σ (MvPolynomial (σ × σ) ℤ) := Matrix.of fun i j => X (i, j)
end Formalism.E


