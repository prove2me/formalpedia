-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:24.296794+00:00
-- url     : https://prove2.me/theorems/630a4295-3a2d-4690-b0d0-f6670a36dff0
-- title:
--   Afsplit C
-- statement:
--   Definitions and structural lemmas for Afsplit C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitC.lean

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Theorems.Thm_Formalism_UG_P_afsplit_decomp
import Theorems.Thm_Formalism_UG_P_afsplit_eps_idem
import Theorems.Thm_Formalism_UG_P_afsplit_eps_mul_IE

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
section Mat
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n] (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "R" => E ⊗[F] 𝔸
def afsplitC (M : Matrix n n Rv) (N : Matrix n n R) : Matrix n n R :=
  M.map (afsplitIE v) + (1 - afsplitEps E v) • N
theorem afsplit_om_eps_IE (x : Rv) : (1 - afsplitEps E v) * afsplitIE v x = 0 := by
  rw [sub_mul, one_mul, afsplit_eps_mul_IE, sub_self]
theorem afsplit_om_idem : (1 - afsplitEps E v) * (1 - afsplitEps E v) = 1 - afsplitEps E v := by
  linear_combination (afsplit_eps_idem (E := E) v)
theorem afsplit_smul_map (M : Matrix n n Rv) : (1 - afsplitEps E v) • M.map (afsplitIE v) = 0 := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
  exact afsplit_om_eps_IE v (M i j)
theorem afsplitC_mul (M M' : Matrix n n Rv) (N N' : Matrix n n R) :
    afsplitC v M N * afsplitC v M' N' = afsplitC v (M * M') (N * N') := by
  unfold afsplitC
  have h1 : M.map (afsplitIE v) * ((1 - afsplitEps E v) • N') = 0 := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul, afsplit_smul_map, Matrix.zero_mul]
  have h2 : ((1 - afsplitEps E v) • N) * M'.map (afsplitIE v) = 0 := by
    rw [Matrix.smul_mul, ← Matrix.mul_smul, afsplit_smul_map, Matrix.mul_zero]
  have h3 : ((1 - afsplitEps E v) • N) * ((1 - afsplitEps E v) • N') =
      (1 - afsplitEps E v) • (N * N') := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, afsplit_om_idem]
  rw [add_mul, mul_add, mul_add, h1, h2, h3, Matrix.map_mul, add_zero, zero_add]
theorem afsplit_one_map : (1 : Matrix n n Rv).map (afsplitIE v) = afsplitEps E v • (1 : Matrix n n R) := by
  have h1 : afsplitIE v (1 : Rv) = afsplitEps E v := by
    have h := afsplit_decomp (E := E) v 1
    rwa [map_one, mul_one] at h
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply, h1]
  · simp [Matrix.one_apply, h]
theorem afsplitC_one : afsplitC v (1 : Matrix n n Rv) (1 : Matrix n n R) = 1 := by
  unfold afsplitC
  rw [afsplit_one_map, ← add_smul]
  simp
def afsplitU (h : GL n Rv) (k : GL n R) : GL n R where
  val := afsplitC v h k
  inv := afsplitC v (h⁻¹ : GL n Rv) (k⁻¹ : GL n R)
  val_inv := by rw [afsplitC_mul, Units.mul_inv, Units.mul_inv, afsplitC_one]
  inv_val := by rw [afsplitC_mul, Units.inv_mul, Units.inv_mul, afsplitC_one]
end Mat
end Formalism.UG.P


