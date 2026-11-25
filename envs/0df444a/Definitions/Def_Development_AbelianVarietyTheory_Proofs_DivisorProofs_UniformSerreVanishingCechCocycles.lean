-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreVanishingCechCocycles
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreVanishingCechCocycles
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:43:29.581798+00:00
-- url     : https://prove2.me/theorems/6acd7dab-a8fa-4614-a768-4275ef8ab797
-- title:
--   Uniform Serre Vanishing Cech Cocycles
-- statement:
--   Definitions and structural lemmas for Uniform Serre Vanishing Cech Cocycles, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreVanishingCechCocycles.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoboundaryOfFractionCocycleHomogeneousIdeaStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace GlobalTheory.UniformCocycle
variable {R : Type} [CommRing R] {σ : Type}
noncomputable def proj (I : Ideal R) (e : ℕ) (P : MvPolynomial σ (reesAlgebra I)) :
    MvPolynomial σ R :=
  ∑ m ∈ P.support, monomial m (((coeff m P : reesAlgebra I) : Polynomial R).coeff e)
open Classical in

noncomputable def liftCoeff (I : Ideal R) (e : ℕ) (r : R) : reesAlgebra I :=
  if h : r ∈ I ^ e then ⟨Polynomial.monomial e r, reesAlgebra.monomial_mem.mpr h⟩ else 0
noncomputable def liftE (I : Ideal R) (e : ℕ) (F : MvPolynomial σ R) :
    MvPolynomial σ (reesAlgebra I) :=
  ∑ m ∈ F.support, monomial m (liftCoeff I e (coeff m F))
end GlobalTheory.UniformCocycle
namespace GlobalTheory
end GlobalTheory


