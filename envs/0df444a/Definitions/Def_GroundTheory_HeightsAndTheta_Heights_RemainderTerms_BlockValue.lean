-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:50.363639+00:00
-- url     : https://prove2.me/theorems/e3a900b9-295e-4df7-8fb4-77bcf7d4abcb
-- title:
--   Block Value
-- statement:
--   Definitions and structural lemmas for Block Value, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
namespace RestTerms
namespace Top
open MvPolynomial Finset
noncomputable section
def gmf (f r a : ℕ) (c : SmallBlock) (q : Fin f → ℕ) (e : ℕ) : RootRing f (r + a) :=
  (∏ σ, blockEmb f (r + a) σ (yEval r a c (extraFactor r (q σ)))) * smallBlockMu f r a c ^ e *
    fibreClass f r a c
def gmfOut (f r a : ℕ) (c : SmallBlock) (κ : ℚ) (q : Fin f → ℕ) (e : ℕ) : RootRing f (r + a) :=
  ∑ m ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e,
    (Nat.multinomial Finset.univ m : ℚ) •
      ∏ σ, blockEmb f (r + a) σ (blockOut r a c κ (q σ) (m σ))
def toN (N : ℕ) : RootRing 1 N →ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
  aeval (fun p : Fin 1 × Fin N => X p.2)
def mstar (f r a : ℕ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f) : Fin f → ℕ :=
  fun σ => if σ = τ then e - ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') else r * a - q σ
end
end Top
end RestTerms
end GroundTheory.Heights₂.Heights


