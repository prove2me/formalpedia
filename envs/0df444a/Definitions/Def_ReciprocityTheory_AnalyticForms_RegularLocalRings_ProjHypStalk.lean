-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypStalk
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypStalk
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:37.786863+00:00
-- url     : https://prove2.me/theorems/4960b7a1-c31a-5a56-804d-032df3ea3e59
-- title:
--   Proj Hyp Stalk
-- statement:
--   Definitions and structural lemmas for Proj Hyp Stalk, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypStalk.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
section Loc
variable {σ : Type}
def kerPt (z : σ → ℂ) : Ideal (MvPolynomial σ ℂ) :=
  RingHom.ker (MvPolynomial.eval z : MvPolynomial σ ℂ →+* ℂ)
instance kerPt_isPrime (z : σ → ℂ) : (kerPt z).IsPrime :=
  RingHom.ker_isPrime _
def kerPtQ (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) : Ideal (MvPolynomial σ ℂ ⧸ I) :=
  (kerPt z).map (Ideal.Quotient.mk I)
theorem kerPtQ_isPrime {I : Ideal (MvPolynomial σ ℂ)} {z : σ → ℂ} (hI : I ≤ kerPt z) :
    (kerPtQ I z).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hI)
abbrev locQ (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) : Type :=
  Localization.AtPrime (kerPt z) ⧸
    Ideal.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (kerPt z))) I
end Loc
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
end
end ReciprocityTheory.AnForm.R


