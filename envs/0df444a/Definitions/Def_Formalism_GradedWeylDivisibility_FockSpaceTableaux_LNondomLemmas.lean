-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:53.529582+00:00
-- url     : https://prove2.me/theorems/628c8d52-e3f5-4400-aa02-23d515945c3b
-- title:
--   LNondom Lemmas
-- statement:
--   Definitions and structural lemmas for LNondom Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LNondomLemmas.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
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
namespace Formalism.GradedWeylDivisibility
set_option linter.unusedSimpArgs false
section NonDom
variable {R : Type*} [CommRing R] {r n : ℕ}
def ndEul (R : Type*) [CommRing R] (r n : ℕ) (s : Fin n) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => (colW r n v s) • X v
def ndE (R : Type*) [CommRing R] (r n : ℕ) (l j : Fin n) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => if v.2 = j then X (v.1, l) else 0
def ndF (R : Type*) [CommRing R] (r n : ℕ) (l j : Fin n) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => if v.2 = l then X (v.1, j) else 0
end NonDom
end Formalism.GradedWeylDivisibility


