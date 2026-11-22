-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:44.293126+00:00
-- url     : https://prove2.me/theorems/faa0473a-5f4f-4603-929c-f46059c937e1
-- title:
--   Adelstab
-- statement:
--   Definitions and structural lemmas for Adelstab, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Theorems.Thm_Formalism_UG_P_levelaf_tmul_mem

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
section Trace
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
variable (F E) in

def adelstabT : E ⊗[F] FiniteAdeleRing (𝓞 F) F →ₗ[F] FiniteAdeleRing (𝓞 F) F :=
  (TensorProduct.lid F _).toLinearMap ∘ₗ (Algebra.trace F E).rTensor _
theorem adelstab_incl_int (b : 𝓞 E) :
    inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E b) ∈ 𝒮 :=
  levelaf_tmul_mem b (one_mem _)
end Trace
section Lattice
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
variable (F E) in

def adelstabLam (G : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (L : Submodule 𝒮 (n → 𝒜)) :
    Submodule (𝓞 E) (n → E) where
  carrier := {x | ((G⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι (x i)) ∈ L}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, Pi.add_apply, map_add] at *
    rw [show (fun i => ι (x i) + ι (y i)) = (fun i => ι (x i)) + (fun i => ι (y i)) from rfl,
      mulVec_add]
    exact add_mem hx hy
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, map_zero]
    rw [show (fun _ : n => (0 : 𝒜)) = 0 from rfl, mulVec_zero]
    exact zero_mem _
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_ofPred_eq, Pi.smul_apply] at *
    have : (fun i => ι (a • x i)) = (ι (algebraMap (𝓞 E) E a)) • (fun i => ι (x i)) := by
      ext i; simp [Algebra.smul_def]
    rw [this, mulVec_smul]
    exact L.smul_mem ⟨_, adelstab_incl_int a⟩ hx
end Lattice
section Fin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
end Fin
section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
end Main
end Formalism.UG.P


