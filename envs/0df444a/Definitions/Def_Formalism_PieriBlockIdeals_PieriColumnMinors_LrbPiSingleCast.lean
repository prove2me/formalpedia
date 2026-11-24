-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrbPiSingleCast
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_LrbPiSingleCast
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:41:52.461977+00:00
-- url     : https://prove2.me/theorems/fbf60f60-d10b-4599-acd7-7dc52d0ef543
-- title:
--   Lrb Pi Single Cast
-- statement:
--   Definitions and structural lemmas for Lrb Pi Single Cast, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
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
def resVar (R : Type*) [CommRing R] (p q : ℕ) (v : Fin (p + q) × Fin (p + q)) : MvPolynomial (Fin q × Fin q) R :=
  Fin.addCases (motive := fun _ => MvPolynomial (Fin q × Fin q) R)
    (fun a => Fin.addCases (motive := fun _ => MvPolynomial (Fin q × Fin q) R)
      (fun s => if a = s then 1 else 0) (fun _ => 0) v.2)
    (fun b => Fin.addCases (motive := fun _ => MvPolynomial (Fin q × Fin q) R)
      (fun _ => 0) (fun t => X (b, t)) v.2) v.1
def res (R : Type*) [CommRing R] (p q : ℕ) :
    MvPolynomial (Fin (p + q) × Fin (p + q)) R →ₐ[R] MvPolynomial (Fin q × Fin q) R :=
  aeval (resVar R p q)
def liftWord (p : ℕ) {q : ℕ} (ω : List (Fin q × Fin q × ℕ)) : List (Fin (p + q) × Fin (p + q) × ℕ) :=
  ω.map fun x => (Fin.natAdd p x.1, Fin.natAdd p x.2.1, x.2.2)
section
variable (R : Type*) [CommRing R] (p q : ℕ)
end
section
variable (R : Type*) [CommRing R] (p q : ℕ)
def lrbPi : (Fin (p + q) → ℕ) →+ (Fin q → ℕ) where
  toFun g := fun t => g (Fin.natAdd p t)
  map_zero' := rfl
  map_add' _ _ := rfl
def lrbResO : MvPolynomial (Option (Fin (p + q) × Fin (p + q))) R →ₐ[R] MvPolynomial (Option (Fin q × Fin q)) R :=
  aeval fun o => o.elim (X none) fun v => rename some (resVar R p q v)
end
end Formalism.CohomologicalDescent.LR


