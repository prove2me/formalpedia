-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:06.596295+00:00
-- url     : https://prove2.me/theorems/30c3c642-ce4c-446b-bbde-dccc1c2585c7
-- title:
--   Lrfc Apply Word Append Single
-- statement:
--   Definitions and structural lemmas for Lrfc Apply Word Append Single, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
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
namespace Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
section
variable {R : Type*} [CommRing R] {r n : ℕ}
def lrfc_iota : MvPolynomial (Fin r × Fin n) R →+*
    MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) :=
  MvPolynomial.map (C : R →+* MvPolynomial (Fin r × Fin n) R)
def lrfc_coeffT (d : Fin r × Fin n →₀ ℕ)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    MvPolynomial (Fin r × Fin n) R :=
  ∑ m ∈ G.support, monomial m (coeff d (coeff m G))
end
section
variable {R : Type*} [CommRing R] {r n : ℕ}
def lrfc_tau (l : Fin r × Fin r × (Fin r × Fin n)) :
    MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) →ₐ[MvPolynomial (Fin r × Fin n) R]
      MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) :=
  aeval fun v => X v + if v.1 = l.2.1 then C (X l.2.2) * X (l.1, v.2) else 0
def lrfc_Phi (L : List (Fin r × Fin r × (Fin r × Fin n))) :
    MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) →ₐ[MvPolynomial (Fin r × Fin n) R]
      MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) :=
  L.foldr (fun l φ => (lrfc_tau l).comp φ) (AlgHom.id _ _)
end
section
variable {R : Type*} [CommRing R] {r n : ℕ}
def lrf_L (r n : ℕ) : List (Fin r × Fin r × (Fin r × Fin n)) :=
  (List.finRange n).reverse.flatMap fun s =>
    (List.finRange r).filterMap fun a =>
      if h : s.val < a.val ∧ s.val < r then some ((⟨s.val, h.2⟩ : Fin r), a, (a, s)) else none
def lrf_idS (R : Type*) [CommRing R] (r n : ℕ) : Fin r × Fin n → MvPolynomial (Fin r × Fin n) R :=
  fun u => C (idFrame R r n u)
def lrf_ell (R : Type*) [CommRing R] (r n : ℕ) : Fin r × Fin n → MvPolynomial (Fin r × Fin n) R :=
  fun v => C (idFrame R r n v) + if v.2.val < v.1.val then X v else 0
def lrf_off (m : Fin r × Fin n →₀ ℕ) : Fin r × Fin n →₀ ℕ := m.filter fun v => v.2.val < v.1.val
end
end Formalism.CohomologicalDescent.LR


