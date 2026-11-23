-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_MemHatMapGlob
-- name    : Formalism_LocalToGlobal_GlobalTheory_MemHatMapGlob
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:42:25.75581+00:00
-- url     : https://prove2.me/theorems/0b953b95-f243-4270-bb72-a8f93ad11c10
-- title:
--   Mem Hat Map Glob
-- statement:
--   Definitions and structural lemmas for Mem Hat Map Glob, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/MemHatMapGlob.lean

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.L2.GlobalTheoryTheory.Comp
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
def mapQ (Q : Matrix m n E) (Λ : Submodule (𝓞 E) (n → E)) : Submodule (𝓞 E) (m → E) :=
  Λ.map ((Matrix.mulVecLin Q).restrictScalars (𝓞 E))
theorem map_mul_map (Q : Matrix m n E) (Q' : Matrix n m E) (h : Q * Q' = 1) :
    Q.map ιA * Q'.map ιA = (1 : Matrix m m 𝒜) := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
def conjQ (Q : Matrix m n E) (Q' : Matrix n m E) (h1 : Q * Q' = 1) (h2 : Q' * Q = 1) (g : GL n 𝒜) : GL m 𝒜 where
  val := Q.map ιA * (g : Matrix n n 𝒜) * Q'.map ιA
  inv := Q.map ιA * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) * Q'.map ιA
  val_inv := by
    have e : Q'.map ιA * Q.map ιA = (1 : Matrix n n 𝒜) := map_mul_map Q' Q h2
    calc Q.map ιA * (g : Matrix n n 𝒜) * Q'.map ιA * (Q.map ιA * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) * Q'.map ιA)
        = Q.map ιA * ((g : Matrix n n 𝒜) * (Q'.map ιA * Q.map ιA) * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜)) * Q'.map ιA := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [e, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, map_mul_map Q Q' h1]
  inv_val := by
    have e : Q'.map ιA * Q.map ιA = (1 : Matrix n n 𝒜) := map_mul_map Q' Q h2
    calc Q.map ιA * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) * Q'.map ιA * (Q.map ιA * (g : Matrix n n 𝒜) * Q'.map ιA)
        = Q.map ιA * (((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) * (Q'.map ιA * Q.map ιA) * (g : Matrix n n 𝒜)) * Q'.map ιA := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [e, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one, map_mul_map Q Q' h1]
end Formalism.L2.GlobalTheoryTheory.Comp
end


