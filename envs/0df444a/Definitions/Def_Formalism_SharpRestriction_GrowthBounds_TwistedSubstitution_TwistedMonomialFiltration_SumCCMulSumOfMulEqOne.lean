-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
-- name    : Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:15.496839+00:00
-- url     : https://prove2.me/theorems/d2e3a84e-ea09-4a64-8645-7a44f0ddc133
-- title:
--   Sum CCMul Sum Of Mul Eq One
-- statement:
--   Definitions and structural lemmas for Sum CCMul Sum Of Mul Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/SumCCMulSumOfMulEqOne.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
def flt_tay (R : Type*) [CommRing R] (σ : Type*) : MvPolynomial σ R →+* MvPolynomial σ (MvPolynomial σ R) :=
  eval₂Hom (C.comp C) (fun v => C (X v) + X v)
def flt_g (R : Type*) [CommRing R] {σ : Type*} (m be : σ →₀ ℕ) : MvPolynomial σ R :=
  monomial (m - be) (((be.prod fun k j => (m k).choose j : ℕ)) : R)
open Classical in

def flt_Th {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) :
    MvPolynomial (ι × Fin n) (GLLaurent R n) →+*
      MvPolynomial (ι × Fin n) (MvPolynomial (ι × Fin n) (GLLaurent R n)) :=
  eval₂Hom (C.comp C) fun w => C (X w) +
    (if w.1 ∈ S then
      (if LL.vec w.1 then ∑ c : Fin n, C (C (twistMat R n j (-1) c w.2)) * X (w.1, c)
       else ∑ c : Fin n, C (C (twistMat R n j 1 w.2 c)) * X (w.1, c))
     else X w)
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1


