-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:41:26.465089+00:00
-- url     : https://prove2.me/theorems/ca06d07b-b1b4-4ed0-a009-c83aee06eeb6
-- title:
--   Prod Initial Minors Mem Det Span
-- statement:
--   Definitions and structural lemmas for Prod Initial Minors Mem Det Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
def la_xy (R : Type) [CommRing R] {n : ℕ} (s : Fin n) (p q : ℕ) : MvPolynomial (Fin 2 × Fin n) R :=
  X ((0 : Fin 2), s) ^ p * X ((1 : Fin 2), s) ^ q
def la_monLat (R : Type) [CommRing R] {n : ℕ} (s : Fin n) (d : ℕ) :
    Submodule R (MvPolynomial (Fin 2 × Fin n) R) :=
  Submodule.span R {f | ∃ p q, p + q = d ∧ f = la_xy R s p q}
def la_binLat (R : Type) [CommRing R] {n : ℕ} (s : Fin n) (d : ℕ) :
    Submodule R (MvPolynomial (Fin 2 × Fin n) R) :=
  Submodule.span R {f | ∃ p q, p + q = d ∧
    f = ((p + q).choose q : MvPolynomial (Fin 2 × Fin n) R) * la_xy R s p q}
def la_mono {n : ℕ} (s : Fin n) (p q : ℕ) : Fin 2 × Fin n →₀ ℕ :=
  Finsupp.single ((0 : Fin 2), s) p + Finsupp.single ((1 : Fin 2), s) q
def la_det (R : Type) [CommRing R] : MvPolynomial (Fin 2 × Fin 2) R :=
  X ((0 : Fin 2), (0 : Fin 2)) * X ((1 : Fin 2), (1 : Fin 2)) -
    X ((0 : Fin 2), (1 : Fin 2)) * X ((1 : Fin 2), (0 : Fin 2))
def detPowMulMonomialSpan (c d : ℕ) : Submodule ℤ (MvPolynomial (Fin 2 × Fin 2) ℤ) :=
  (la_monLat ℤ (0 : Fin 2) d).map (LinearMap.mulLeft ℤ (la_det ℤ ^ c))
end Formalism.CohomologicalDescent.LA


