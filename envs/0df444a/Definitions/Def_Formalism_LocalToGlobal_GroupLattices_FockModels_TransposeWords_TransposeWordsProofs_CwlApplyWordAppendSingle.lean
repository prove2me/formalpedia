-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
-- name    : Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:24.487048+00:00
-- url     : https://prove2.me/theorems/fa33e3bf-8eee-428d-8a4b-d98254032d35
-- title:
--   Cwl Apply Word Append Single
-- statement:
--   Definitions and structural lemmas for Cwl Apply Word Append Single, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
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
namespace Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
section
variable {R : Type*} [CommRing R] {r n : ℕ}
def cwl_iota : MvPolynomial (Fin r × Fin n) R →+*
    MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) :=
  MvPolynomial.map (C : R →+* MvPolynomial (Fin r × Fin n) R)
def cwl_coeffT (d : Fin r × Fin n →₀ ℕ)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    MvPolynomial (Fin r × Fin n) R :=
  ∑ m ∈ G.support, monomial m (coeff d (coeff m G))
def cwl_tau (l : Fin r × Fin r × (Fin r × Fin n)) :
    MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) →ₐ[MvPolynomial (Fin r × Fin n) R]
      MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) :=
  aeval fun v => X v + if v.1 = l.2.1 then C (X l.2.2) * X (l.1, v.2) else 0
def cwl_Phi (L : List (Fin r × Fin r × (Fin r × Fin n))) :
    MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) →ₐ[MvPolynomial (Fin r × Fin n) R]
      MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) :=
  L.foldr (fun l φ => (cwl_tau l).comp φ) (AlgHom.id _ _)
def cwUpd (l : Fin r × Fin r × (Fin r × Fin n)) (y : Fin r × Fin n → MvPolynomial (Fin r × Fin n) R) :
    Fin r × Fin n → MvPolynomial (Fin r × Fin n) R :=
  fun v => y v + if v.1 = l.2.1 then X l.2.2 * y (l.1, v.2) else 0
def cwLetters (r n : ℕ) : List (Fin r × Fin r × (Fin r × Fin n)) :=
  ((List.finRange n).reverse.flatMap fun s =>
    (List.finRange r).filterMap fun a =>
      if h : s.val < a.val ∧ s.val < r then some (⟨s.val, h.2⟩, a, (a, s)) else none)
def cwStrict (m : Fin r × Fin n →₀ ℕ) : Fin r × Fin n →₀ ℕ := m.filter fun v => v.2.val < v.1.val
def cwPt : Fin r × Fin n → MvPolynomial (Fin r × Fin n) R := fun v =>
  idFrame (MvPolynomial (Fin r × Fin n) R) r n v + if v.2.val < v.1.val then X v else 0
end
end Formalism.L2.G.Model.TS


