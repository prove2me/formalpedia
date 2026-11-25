-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T13:34:37.002018+00:00
-- url     : https://prove2.me/theorems/d3868cfd-8f65-4311-8503-8d0b8dbc92cb
-- title:
--   Proj Hyp
-- statement:
--   Definitions and structural lemmas for Proj Hyp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHyp.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypStalk
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypC
import Theorems.Thm_ReciprocityTheory_AnForm_R_iSup_chartOpen_eq_top
import Theorems.Thm_ReciprocityTheory_AnForm_R_isNoetherianRing_gammaChart

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
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
instance isNoetherian_projX {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    IsNoetherian (projX P hP) :=
  (isNoetherian_iff_of_finite_iSup_eq_top (S := chartOpen hP) (iSup_chartOpen_eq_top hP)).mpr
    (isNoetherianRing_gammaChart hP)
def projB (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) :
    TopologicalSpace.Closeds (projX P hP) :=
  letI := segreGraded hP
  ⟨ProjectiveSpectrum.zeroLocus (segreGrading P) (Ideal.Quotient.mk (segreIdeal P) '' (segreIdeal D : Set _)),
    ProjectiveSpectrum.isClosed_zeroLocus _ _⟩
def ptIdealOf {σ : Type} (z : σ → ℂ) : Ideal (MvPolynomial σ ℂ) :=
  RingHom.ker (MvPolynomial.eval z : MvPolynomial σ ℂ →+* ℂ)
instance ptIdealOf_isPrime {σ : Type} (z : σ → ℂ) : (ptIdealOf z).IsPrime :=
  RingHom.ker_isPrime _
abbrev locAt {σ : Type} (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) : Type :=
  Localization.AtPrime (ptIdealOf z) ⧸
    Ideal.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z))) I
abbrev chartLocRing (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ) :
    Type :=
  locAt (chartIdeal P p) y
end
end ReciprocityTheory.AnForm.R


