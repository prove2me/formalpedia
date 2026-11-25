-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
-- name    : Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T13:56:27.635254+00:00
-- url     : https://prove2.me/theorems/fb754b60-06f5-52da-a22e-c6661c4b3f7b
-- title:
--   Ch Prime
-- statement:
--   Definitions and structural lemmas for Ch Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/ChPrime.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open ReciprocityTheory.AnForm.R
def chPrime {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (g : MvPolynomial (Fin m) ℂ) :
    Ideal (MvPolynomial (Fin m) ℂ) :=
  (Ideal.span {algebraMap _ (locRing I t) g}).comap (algebraMap _ (locRing I t))
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par


