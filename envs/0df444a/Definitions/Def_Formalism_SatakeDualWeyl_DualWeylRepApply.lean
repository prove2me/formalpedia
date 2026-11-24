-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_DualWeylRepApply
-- name    : Formalism_SatakeDualWeyl_DualWeylRepApply
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:34:32.51145+00:00
-- url     : https://prove2.me/theorems/615d1cf5-6715-4068-ad9b-bb8baabba7a6
-- title:
--   Dual Weyl Rep Apply
-- statement:
--   Definitions and structural lemmas for Dual Weyl Rep Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/DualWeylRepApply.lean

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_DualWeylModuleStable
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_UG_P_dual_weyl_action_mul
import Theorems.Thm_Formalism_UG_P_dual_weyl_module_stable
import Theorems.Thm_Formalism_UG_P_weyl_module_GL_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace Formalism.UG
def dualWeylRep (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) :
    Representation R (GL (Fin r) R) (Formalism.GradedWeylDivisibility.dualWeyl R r n ν) where
  toFun g := (dwAct R r n g).toLinearMap.restrict
    (fun f hf => Formalism.UG.P.dual_weyl_module_stable R r n ν g f hf)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change dwAct R r n 1 (f : MvPolynomial (Fin r × Fin n) R) = (f : MvPolynomial (Fin r × Fin n) R)
    rw [(Formalism.UG.P.dual_weyl_action_mul R r n 1 1).2]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change dwAct R r n (g * h) (f : MvPolynomial (Fin r × Fin n) R) =
      dwAct R r n g (dwAct R r n h f)
    rw [(Formalism.UG.P.dual_weyl_action_mul R r n g h).1]
    rfl
def weylRepW (R : Type) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) :
    Representation R (GL (Fin r) R) (Formalism.GradedWeylDivisibility.weyl R r n hn ν) where
  toFun g := (dwAct R r n g).toLinearMap.restrict
    (fun f hf => Formalism.UG.P.weyl_module_GL_stable R r n hn ν g f hf)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change dwAct R r n 1 (f : MvPolynomial (Fin r × Fin n) R) = (f : MvPolynomial (Fin r × Fin n) R)
    rw [(Formalism.UG.P.dual_weyl_action_mul R r n 1 1).2]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change dwAct R r n (g * h) (f : MvPolynomial (Fin r × Fin n) R) =
      dwAct R r n g (dwAct R r n h f)
    rw [(Formalism.UG.P.dual_weyl_action_mul R r n g h).1]
    rfl
end Formalism.UG


