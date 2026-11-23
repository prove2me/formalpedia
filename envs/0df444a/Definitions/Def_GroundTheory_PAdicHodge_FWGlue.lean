-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_FWGlue
-- name    : GroundTheory_PAdicHodge_FWGlue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:34.13944+00:00
-- url     : https://prove2.me/theorems/bdfa21cc-adbc-4474-a56b-598a877c927d
-- title:
--   FWGlue
-- statement:
--   Definitions and structural lemmas for FWGlue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWGlue.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
section Restrict
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
def restrictAut (Ω : IntermediateField F E) (τ : Ω ≃ₐ[F] Ω) (N : IntermediateField F E)
    (hN : N ≤ Ω) [Normal F N] : N ≃ₐ[F] N :=
  haveI : Normal F (IntermediateField.restrict hN) :=
    Normal.of_algEquiv (IntermediateField.restrictAlgEquiv hN)
  (IntermediateField.restrictAlgEquiv hN).trans
    ((τ.restrictNormal (IntermediateField.restrict hN)).trans
      (IntermediateField.restrictAlgEquiv hN).symm)
end Restrict
section Glue
variable {F E : Type*} [Field F] [Field E] [Algebra F E] {ι : Type*}
variable (Ω : IntermediateField F E) (N : ι → IntermediateField F E) (hN : ∀ i, N i ≤ Ω)
  (hdir : Directed (· ≤ ·) N) (hcov : ∀ x ∈ Ω, ∃ i, x ∈ N i) (f : ∀ i, N i →ₐ[F] N i)
  (hf : ∀ i j (h : N i ≤ N j) (x : N i), ((f j ⟨x, h x.2⟩ : N j) : E) = ((f i x : N i) : E))
def glueFun (x : Ω) : E :=
  ((f (hcov x x.2).choose ⟨x, (hcov x x.2).choose_spec⟩ : N (hcov x x.2).choose) : E)
include hdir hf in
theorem glueFun_eq (i : ι) (x : Ω) (hx : (x : E) ∈ N i) :
    glueFun Ω N hcov f x = ((f i ⟨x, hx⟩ : N i) : E) := by
  obtain ⟨j, hj1, hj2⟩ := hdir (hcov x x.2).choose i
  unfold glueFun
  rw [← hf _ j hj1, ← hf i j hj2]
include hN in
theorem glueFun_mem (x : Ω) : glueFun Ω N hcov f x ∈ Ω :=
  hN _ (f _ _).2
def glueHom : Ω →ₐ[F] Ω where
  toFun x := ⟨glueFun Ω N hcov f x, glueFun_mem Ω N hN hcov f x⟩
  map_one' := by
    obtain ⟨i, hi⟩ := hcov 1 (one_mem Ω)
    apply Subtype.ext
    change glueFun Ω N hcov f 1 = ((1 : Ω) : E)
    rw [glueFun_eq Ω N hdir hcov f hf i 1 hi]
    have : (⟨((1 : Ω) : E), hi⟩ : N i) = 1 := rfl
    rw [this, map_one]; rfl
  map_mul' x y := by
    obtain ⟨i, hi⟩ := hcov x x.2
    obtain ⟨j, hj⟩ := hcov y y.2
    obtain ⟨k, hik, hjk⟩ := hdir i j
    apply Subtype.ext
    change glueFun Ω N hcov f (x * y) = glueFun Ω N hcov f x * glueFun Ω N hcov f y
    rw [glueFun_eq Ω N hdir hcov f hf k x (hik hi), glueFun_eq Ω N hdir hcov f hf k y (hjk hj),
      glueFun_eq Ω N hdir hcov f hf k (x * y) (mul_mem (hik hi) (hjk hj))]
    have : (⟨((x * y : Ω) : E), mul_mem (hik hi) (hjk hj)⟩ : N k) =
        ⟨(x : E), hik hi⟩ * ⟨(y : E), hjk hj⟩ := rfl
    rw [this, map_mul]; rfl
  map_zero' := by
    obtain ⟨i, hi⟩ := hcov 0 (zero_mem Ω)
    apply Subtype.ext
    change glueFun Ω N hcov f 0 = ((0 : Ω) : E)
    rw [glueFun_eq Ω N hdir hcov f hf i 0 hi]
    have : (⟨((0 : Ω) : E), hi⟩ : N i) = 0 := rfl
    rw [this, map_zero]; rfl
  map_add' x y := by
    obtain ⟨i, hi⟩ := hcov x x.2
    obtain ⟨j, hj⟩ := hcov y y.2
    obtain ⟨k, hik, hjk⟩ := hdir i j
    apply Subtype.ext
    change glueFun Ω N hcov f (x + y) = glueFun Ω N hcov f x + glueFun Ω N hcov f y
    rw [glueFun_eq Ω N hdir hcov f hf k x (hik hi), glueFun_eq Ω N hdir hcov f hf k y (hjk hj),
      glueFun_eq Ω N hdir hcov f hf k (x + y) (add_mem (hik hi) (hjk hj))]
    have : (⟨((x + y : Ω) : E), add_mem (hik hi) (hjk hj)⟩ : N k) =
        ⟨(x : E), hik hi⟩ + ⟨(y : E), hjk hj⟩ := rfl
    rw [this, map_add]; rfl
  commutes' c := by
    obtain ⟨i, hi⟩ := hcov _ (algebraMap_mem Ω c)
    apply Subtype.ext
    change glueFun Ω N hcov f (algebraMap F Ω c) = ((algebraMap F Ω c : Ω) : E)
    rw [glueFun_eq Ω N hdir hcov f hf i _ hi]
    have : (⟨((algebraMap F Ω c : Ω) : E), hi⟩ : N i) = algebraMap F (N i) c := rfl
    rw [this, AlgHom.commutes]; rfl
def glueAut [Algebra.IsAlgebraic F Ω] : Ω ≃ₐ[F] Ω :=
  (Algebra.IsAlgebraic.algEquivEquivAlgHom F Ω).symm (glueHom Ω N hN hdir hcov f hf)
end Glue
section AutCongr
variable {F A B : Type*} [Field F] [Field A] [Field B] [Algebra F A] [Algebra F B]
theorem continuous_autCongr (e : A ≃ₐ[F] B) : Continuous (e.autCongr : Gal(A/F) → Gal(B/F)) := by
  apply continuous_of_continuousAt_one e.autCongr (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E, hE, hsub⟩ := hU
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨E.map e.symm.toAlgHom, ?_, ?_⟩
  · exact LinearEquiv.finiteDimensional (IntermediateField.equivMap E e.symm.toAlgHom).toLinearEquiv
  · intro σ hσ
    apply hsub
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    change e (σ (e.symm x)) = x
    rw [hσ (e.symm x) ⟨x, hx, rfl⟩, AlgEquiv.apply_symm_apply]
def autCongrHomeomorph (e : A ≃ₐ[F] B) : Gal(A/F) ≃ₜ* Gal(B/F) where
  toMulEquiv := e.autCongr
  continuous_toFun := continuous_autCongr e
  continuous_invFun := continuous_autCongr e.symm
end AutCongr
end GroundTheory.PAdicHodge


