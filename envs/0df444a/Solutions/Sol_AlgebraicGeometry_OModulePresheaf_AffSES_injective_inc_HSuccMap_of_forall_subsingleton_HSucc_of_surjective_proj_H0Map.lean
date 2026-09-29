-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.AffSES.injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8b40c003-605c-5f6a-b9e1-6c66d4b22011

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map

open AlgebraicGeometry

universe u

set_option autoImplicit false

namespace RM3SOL

open AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
  {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover)

theorem injective_HSuccMap_succ (i : ℕ) [Subsingleton (F₃.HSucc K i)] :
    Function.Injective (S.inc.HSuccMap K (i + 1)) := by
  obtain ⟨δ₀, δ, -, -, -, h4⟩ := S.exists_connectingHom K
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := h4 i hx
  rw [Subsingleton.elim y 0, map_zero]
  exact Submodule.zero_mem _

theorem cochainMap_inc_injective (i : ℕ) : Function.Injective (S.inc.cochainMap K i) := by
  intro f g h
  funext s
  apply S.injective (K.affineInter π s)
  have := congr_fun h s
  rwa [AffHom.cochainMap_apply, AffHom.cochainMap_apply] at this

theorem cochainMap_proj_inc (i : ℕ) (f : F₁.cochain K i) :
    S.proj.cochainMap K i (S.inc.cochainMap K i f) = 0 := by
  funext s
  rw [AffHom.cochainMap_apply, AffHom.cochainMap_apply, Pi.zero_apply, ← LinearMap.mem_ker, ← S.exact]
  exact ⟨f s, rfl⟩

theorem exists_cochainMap_inc_eq (i : ℕ) (g : F₂.cochain K i) (hg : S.proj.cochainMap K i g = 0) :
    ∃ f : F₁.cochain K i, S.inc.cochainMap K i f = g := by
  have h : ∀ s : K.Idx i, ∃ x : F₁.obj (K.inter s), S.inc.app (K.affineInter π s) x = g s := by
    intro s
    have hs : g s ∈ LinearMap.ker (S.proj.app (K.affineInter π s)) := by
      rw [LinearMap.mem_ker, ← AffHom.cochainMap_apply, hg, Pi.zero_apply]
    rw [← S.exact] at hs
    exact hs
  choose f hf using h
  exact ⟨f, funext fun s => by rw [AffHom.cochainMap_apply, hf]⟩

theorem injective_HSuccMap_zero (hs : Function.Surjective (S.proj.H0Map K)) :
    Function.Injective (S.inc.HSuccMap K 0) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [LinearMap.mem_ker, Submodule.mkQ_apply, AffHom.HSuccMap_mk, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap] at hx
  obtain ⟨y, hy⟩ := hx
  rw [Submodule.subtype_apply, AffHom.kerMap_coe] at hy

  have hp : S.proj.cochainMap K 0 y ∈ F₃.H0 K := by
    show F₃.d K 0 (S.proj.cochainMap K 0 y) = 0
    rw [← LinearMap.comp_apply, ← AffHom.cochainMap_comp_d, LinearMap.comp_apply, hy, cochainMap_proj_inc]
  obtain ⟨y', hy'⟩ := hs ⟨_, hp⟩
  have hy'v : S.proj.cochainMap K 0 (y'.1) = S.proj.cochainMap K 0 y := by
    have := congr_arg Subtype.val hy'
    rwa [AffHom.kerMap_coe] at this
  obtain ⟨w, hw⟩ := exists_cochainMap_inc_eq S K 0 (y - y'.1) (by rw [map_sub, hy'v, sub_self])
  have hdw : S.inc.cochainMap K 1 (F₁.d K 0 w) = S.inc.cochainMap K 1 z.1 := by
    rw [← LinearMap.comp_apply, AffHom.cochainMap_comp_d, LinearMap.comp_apply, hw, map_sub, hy,
      LinearMap.mem_ker.1 y'.2, sub_zero]
  have := cochainMap_inc_injective S K 1 hdw
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  exact ⟨w, by rw [Submodule.subtype_apply]; exact this⟩

end RM3SOL

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
    {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover)
    (h₃ : ∀ i : ℕ, Subsingleton (F₃.HSucc K i))
    (hsurj : Function.Surjective (S.proj.H0Map K)) :
    ∀ i : ℕ, Function.Injective (S.inc.HSuccMap K i) := by
  intro i
  cases i with
  | zero => exact RM3SOL.injective_HSuccMap_zero S K hsurj
  | succ i => haveI := h₃ i; exact RM3SOL.injective_HSuccMap_succ S K i

end S_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map (solution)
