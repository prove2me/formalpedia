-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:18.002798+00:00
-- url     : https://prove2.me/theorems/671a06d7-6444-4cb5-800e-2e331f051af4
-- title:
--   LRowdiv Lemmas
-- statement:
--   Definitions and structural lemmas for LRowdiv Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LRowdivLemmas.lean

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
theorem rowDiv_add (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f g : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (f + g) = rowDiv R a b k f + rowDiv R a b k g := by
  simp only [rowDiv, map_add, Polynomial.coeff_add]
theorem rowDiv_smul (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (c : R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (c • f) = c • rowDiv R a b k f := by
  simp only [rowDiv, map_smul, Polynomial.coeff_smul]
def rowDivL (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) :
    MvPolynomial (Fin r × Fin n) R →ₗ[R] MvPolynomial (Fin r × Fin n) R where
  toFun := rowDiv R a b k
  map_add' := rowDiv_add R a b k
  map_smul' := rowDiv_smul R a b k
end Formalism.GradedWeylDivisibility


