-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:42.072805+00:00
-- url     : https://prove2.me/theorems/e3f175fa-cb76-4dbe-9070-46498c475a39
-- title:
--   Afsplit B
-- statement:
--   Definitions and structural lemmas for Afsplit B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitB.lean

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitA
import Theorems.Thm_Formalism_UG_P_afsplitI_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.UG.P
open Formalism.UG
section Tens
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
def afsplitIE (v : HeightOneSpectrum (𝓞 F)) : E ⊗[F] v.adicCompletion F →ₙ+* E ⊗[F] 𝔸 where
  toFun := LinearMap.lTensor E (afsplitI v)
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
    | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
      | tmul c d =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul, afsplitI_mul]
def afsplitEps (E : Type) [CommRing E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) : E ⊗[F] 𝔸 :=
  afsplitIE v 1
end Tens
section Inj
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
end Inj
end Formalism.UG.P


