-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_NablaRepApply
-- name    : Formalism_SatakeDualWeyl_NablaRepApply
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T13:16:42.473435+00:00
-- url     : https://prove2.me/theorems/a0b6bc6c-99c9-4a9d-9159-306441811f70
-- title:
--   Nabla Rep Apply
-- statement:
--   Definitions and structural lemmas for Nabla Rep Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/NablaRepApply.lean

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Actions
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
import Theorems.Thm_Formalism_UG_P_UG_inclusion_injective
import Theorems.Thm_Formalism_UG_P_nabla_subspace_stable
import Theorems.Thm_Formalism_UG_P_polynomial_action_mul_holds
import Theorems.Thm_Formalism_UG_P_standard_action_mul_holds
import Theorems.Thm_Formalism_UG_P_tensor_action_mul_holds
import Theorems.Thm_Formalism_UG_P_weyl_module_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
namespace Formalism.UG
def stdRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Representation O (GL n O) (n → O) where
  toFun := stdAct O n
  map_one' := (P.standard_action_mul_holds O n 1 1).2
  map_mul' g h := (P.standard_action_mul_holds O n g h).1
def tensRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] (k : ℕ) :
    Representation O (GL n O) (⨂[O]^k (n → O)) where
  toFun := tensAct O n k
  map_one' := (P.tensor_action_mul_holds O n k 1 1).2
  map_mul' g h := (P.tensor_action_mul_holds O n k g h).1
def polyRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Representation O (GL n O) (MvPolynomial n O) where
  toFun g := (polyAct O n g).toLinearMap
  map_one' := by
    rw [(P.polynomial_action_mul_holds O n 1 1).2, AlgHom.toLinearMap_id]
    rfl
  map_mul' g h := by
    rw [(P.polynomial_action_mul_holds O n g h).1, AlgHom.comp_toLinearMap]
    rfl
def nablaRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] (k : ℕ) :
    Representation O (GL n O) (nabla O n k) where
  toFun g := (polyAct O n g).toLinearMap.restrict (fun P hP => Formalism.UG.P.nabla_subspace_stable O n k g P hP)
  map_one' := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change polyAct O n 1 (P : MvPolynomial n O) = (P : MvPolynomial n O)
    rw [(Formalism.UG.P.polynomial_action_mul_holds O n 1 1).2]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change polyAct O n (g * h) (P : MvPolynomial n O) = polyAct O n g (polyAct O n h P)
    rw [(Formalism.UG.P.polynomial_action_mul_holds O n g h).1]
    rfl
def weylRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] (k : ℕ) :
    Representation O (GL n O) (weylSub O n k) where
  toFun g := (polyAct O n g).toLinearMap.restrict
    (fun P hP => Formalism.UG.P.weyl_module_stable O n k g P hP)
  map_one' := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change polyAct O n 1 (P : MvPolynomial n O) = (P : MvPolynomial n O)
    rw [(Formalism.UG.P.polynomial_action_mul_holds O n 1 1).2]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change polyAct O n (g * h) (P : MvPolynomial n O) = polyAct O n g (polyAct O n h P)
    rw [(Formalism.UG.P.polynomial_action_mul_holds O n g h).1]
    rfl
def ratEquiv {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n]
    [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (R : Type) [CommRing R] [Algebra F R]
    [Nontrivial R] : UJ (σ : E →+* E) J ≃* ratPts σ J R :=
  Subgroup.equivMapOfInjective (UJ (σ : E →+* E) J) (bc (inclE (F := F) R))
    (Formalism.UG.P.UG_inclusion_injective F E n R inferInstance)
end Formalism.UG


