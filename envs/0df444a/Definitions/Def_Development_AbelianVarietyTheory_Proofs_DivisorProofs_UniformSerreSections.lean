-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreSections
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreSections
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:47:07.274914+00:00
-- url     : https://prove2.me/theorems/aeb3cac2-d680-42a3-9925-1f6f8139c668
-- title:
--   Uniform Serre Sections
-- statement:
--   Definitions and structural lemmas for Uniform Serre Sections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreSections.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormOfCompatibleFractionsStatement
import Theorems.Thm_GlobalTheory_IsGradedMap_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace GlobalTheory.UniformSerre
variable {R : Type} [CommRing R] {I : Ideal R} {σ : Type}
noncomputable def comp (e : ℕ) (Q : MvPolynomial σ (reesAlgebra I)) : MvPolynomial σ R :=
  ∑ m ∈ Q.support, monomial m ((coeff m Q).val.coeff e)
open scoped Classical in

noncomputable def liftFun (I : Ideal R) (e : ℕ) (r : R) : reesAlgebra I :=
  if h : r ∈ I ^ e then ⟨Polynomial.monomial e r, (mem_reesAlgebra_iff I _).2 (fun i => by
    rw [Polynomial.coeff_monomial]; split_ifs with hi
    · subst hi; exact h
    · exact zero_mem _)⟩ else 0
noncomputable def lift (I : Ideal R) (e : ℕ) (P : MvPolynomial σ R) : MvPolynomial σ (reesAlgebra I) :=
  ∑ m ∈ P.support, monomial m (liftFun I e (coeff m P))
end GlobalTheory.UniformSerre


