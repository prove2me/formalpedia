-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
-- name    : GroundTheory_AutomorphicForms_HermitianOrthogonal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:57.441362+00:00
-- url     : https://prove2.me/theorems/581546b4-6991-4db0-864c-2427c7707ef6
-- title:
--   Hermitian Orthogonal
-- statement:
--   Definitions and structural lemmas for Hermitian Orthogonal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Theorems.Thm_GroundTheory_Automorphic_conj_algebraMap
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj


set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open Module
section Conj
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
instance finiteDimensional_of_isQuadraticExtension : FiniteDimensional F E :=
  Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two F E)
theorem conjHom_apply (x : E) : conjHom F E x = conj F E x :=
  rfl
end Conj
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' V'' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  [AddCommGroup V''] [Module E V'']
namespace HermitianForm
def Isometric (h : HermitianForm F E V) (h' : HermitianForm F E V') : Prop :=
  ∃ e : V ≃ₗ[E] V', ∀ x y, h'.toSesq (e x) (e y) = h.toSesq x y
theorem conj_toSesq (h : HermitianForm F E V) (x y : V) :
    conj F E (h.toSesq x y) = h.toSesq y x :=
  h.isSymm.eq x y
theorem toSesq_eq_zero_comm (h : HermitianForm F E V) {x y : V} :
    h.toSesq x y = 0 ↔ h.toSesq y x = 0 := by
  rw [← h.conj_toSesq x y]
  constructor
  · intro hxy; rw [hxy, map_zero]
  · intro hxy
    rw [← conj_conj (F := F) (h.toSesq x y), hxy, map_zero]
namespace Isometric
theorem symm {h : HermitianForm F E V} {h' : HermitianForm F E V'} (H : Isometric h h') :
    Isometric h' h := by
  obtain ⟨e, he⟩ := H
  refine ⟨e.symm, fun x y => ?_⟩
  rw [← he, e.apply_symm_apply, e.apply_symm_apply]
end Isometric
def prod (h : HermitianForm F E V) (h' : HermitianForm F E V') : HermitianForm F E (V × V') where
  toSesq := LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E)
    (fun p q => h.toSesq p.1 q.1 + h'.toSesq p.2 q.2)
    (fun p p' q => by simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]; ring)
    (fun c p q => by
      simp only [Prod.smul_fst, Prod.smul_snd, LinearMap.map_smulₛₗ₂, smul_eq_mul]; ring)
    (fun p q q' => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring)
    (fun c p q => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, RingHom.id_apply]; ring)
  isSymm := ⟨fun p q => by
    simp only [LinearMap.mk₂'ₛₗ_apply, map_add]
    rw [h.isSymm.eq, h'.isSymm.eq]⟩
  nonsingular := by
    constructor
    · intro p q hpq
      have H : ∀ r : V × V', h.toSesq p.1 r.1 + h'.toSesq p.2 r.2 =
          h.toSesq q.1 r.1 + h'.toSesq q.2 r.2 := fun r => LinearMap.congr_fun hpq r
      have h1 : h.toSesq p.1 = h.toSesq q.1 := LinearMap.ext fun y => by
        simpa using H (y, 0)
      have h2 : h'.toSesq p.2 = h'.toSesq q.2 := LinearMap.ext fun y => by
        simpa using H (0, y)
      exact Prod.ext (h.nonsingular.1 h1) (h'.nonsingular.1 h2)
    · intro f
      obtain ⟨x, hx⟩ := h.nonsingular.2 (f.comp (LinearMap.inl E V V'))
      obtain ⟨x', hx'⟩ := h'.nonsingular.2 (f.comp (LinearMap.inr E V V'))
      refine ⟨(x, x'), LinearMap.ext fun r => ?_⟩
      simp only [LinearMap.mk₂'ₛₗ_apply, hx, hx', LinearMap.comp_apply, LinearMap.inl_apply,
        LinearMap.inr_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
@[simp]
theorem prod_apply (h : HermitianForm F E V) (h' : HermitianForm F E V') (p q : V × V') :
    (h.prod h').toSesq p q = h.toSesq p.1 q.1 + h'.toSesq p.2 q.2 := rfl
theorem Isometric.prod {h₁ : HermitianForm F E V} {h₂ : HermitianForm F E V'}
    {V₃ V₄ : Type*} [AddCommGroup V₃] [Module E V₃] [AddCommGroup V₄] [Module E V₄]
    {h₃ : HermitianForm F E V₃} {h₄ : HermitianForm F E V₄}
    (H : Isometric h₁ h₂) (H' : Isometric h₃ h₄) : Isometric (h₁.prod h₃) (h₂.prod h₄) := by
  obtain ⟨e, he⟩ := H
  obtain ⟨e', he'⟩ := H'
  exact ⟨e.prodCongr e', fun p q => by
    show h₂.toSesq (e p.1) (e q.1) + h₄.toSesq (e' p.2) (e' q.2) = _
    rw [he, he']
    rfl⟩
def ofUnit (a : Fˣ) : HermitianForm F E E where
  toSesq := LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E)
    (fun x y => conj F E x * algebraMap F E a * y)
    (fun x x' y => by rw [map_add]; ring)
    (fun c x y => by simp only [map_mul, smul_eq_mul, conjHom_apply]; ring)
    (fun x y y' => by ring)
    (fun c x y => by simp only [smul_eq_mul, RingHom.id_apply]; ring)
  isSymm := ⟨fun x y => by
    simp only [LinearMap.mk₂'ₛₗ_apply, conjHom_apply, map_mul, conj_conj, conj_algebraMap]
    ring⟩
  nonsingular := by
    have ha : algebraMap F E a ≠ 0 := by simp
    constructor
    · intro x y hxy
      have := LinearMap.congr_fun hxy 1
      simp only [LinearMap.mk₂'ₛₗ_apply, mul_one] at this
      have h2 := mul_right_cancel₀ ha this
      rw [← conj_conj (F := F) x, h2, conj_conj]
    · intro f
      refine ⟨conj F E (f 1 * (algebraMap F E a)⁻¹), LinearMap.ext fun y => ?_⟩
      simp only [LinearMap.mk₂'ₛₗ_apply, conj_conj]
      have hf : f y = f 1 * y := by
        rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
      rw [hf]
      field_simp
@[simp]
theorem ofUnit_apply (a : Fˣ) (x y : E) :
    (ofUnit (E := E) a).toSesq x y = conj F E x * algebraMap F E a * y := rfl
def IsOrthoCompl (h : HermitianForm F E V) (W W' : Submodule E V) : Prop :=
  IsCompl W W' ∧ ∀ x ∈ W, ∀ y ∈ W', h.toSesq x y = 0
theorem IsOrthoCompl.symm {h : HermitianForm F E V} {W W' : Submodule E V}
    (hW : h.IsOrthoCompl W W') : h.IsOrthoCompl W' W :=
  ⟨hW.1.symm, fun x hx y hy => h.toSesq_eq_zero_comm.1 (hW.2 y hy x hx)⟩
def restrict (h : HermitianForm F E V) (W W' : Submodule E V) (hW : h.IsOrthoCompl W W') :
    HermitianForm F E W where
  toSesq := h.toSesq.domRestrict₁₂ W W
  isSymm := h.isSymm.domRestrict W
  nonsingular := by
    constructor
    · intro a b hab
      have key : ∀ v : V, h.toSesq (a : V) v = h.toSesq (b : V) v := by
        intro v
        have hv : v ∈ W ⊔ W' := by rw [hW.1.sup_eq_top]; trivial
        obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.1 hv
        have h1 := LinearMap.congr_fun hab ⟨w, hw⟩
        simp only [LinearMap.domRestrict₁₂_apply] at h1
        rw [map_add, map_add, h1, hW.2 _ a.2 _ hw', hW.2 _ b.2 _ hw']
      exact Subtype.ext (h.nonsingular.1 (LinearMap.ext key))
    · intro f
      obtain ⟨x, hx⟩ := h.nonsingular.2 (f.comp (Submodule.projectionOnto W W' hW.1))
      have hv : x ∈ W ⊔ W' := by rw [hW.1.sup_eq_top]; trivial
      obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.1 hv
      refine ⟨⟨w, hw⟩, LinearMap.ext fun y => ?_⟩
      have h1 := LinearMap.congr_fun hx (y : V)
      rw [map_add, LinearMap.add_apply, h.toSesq_eq_zero_comm.1 (hW.2 _ y.2 _ hw'), add_zero,
        LinearMap.comp_apply, Submodule.projectionOnto_apply_left] at h1
      exact h1
section Separable
variable [Algebra.IsSeparable F E]
end Separable
end HermitianForm
end GroundTheory.Automorphic
end


