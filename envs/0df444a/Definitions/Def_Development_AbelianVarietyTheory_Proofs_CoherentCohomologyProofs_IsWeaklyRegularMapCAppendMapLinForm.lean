-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:55.75394+00:00
-- url     : https://prove2.me/theorems/c6c6a517-9858-4573-b55c-6aa04633b026
-- title:
--   Is Weakly Regular Map CAppend Map Lin Form
-- statement:
--   Definitions and structural lemmas for Is Weakly Regular Map CAppend Map Lin Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
namespace GlobalTheory
section Variables
variable {R : Type*} [CommRing R] {σ : Type*}
def killVars (R : Type*) [CommRing R] (S : Set σ) :
    MvPolynomial σ R →ₐ[R] MvPolynomial {x : σ // x ∉ S} R :=
  killCompl (f := (Subtype.val : {x : σ // x ∉ S} → σ)) Subtype.val_injective
theorem killVars_rename (S : Set σ) (p : MvPolynomial {x : σ // x ∉ S} R) :
    killVars R S (rename Subtype.val p) = p :=
  killCompl_rename_app _ p
theorem killVars_X_of_notMem {S : Set σ} {x : σ} (hx : x ∉ S) :
    killVars R S (X x) = X ⟨x, hx⟩ := by
  rw [← killVars_rename S (X ⟨x, hx⟩), rename_X]
theorem killVars_X_of_mem {S : Set σ} {x : σ} (hx : x ∈ S) :
    killVars R S (X x) = 0 := by
  have : x ∉ Set.range (Subtype.val : {x : σ // x ∉ S} → σ) := by simpa using hx
  simp only [killVars, killCompl, aeval_X]
  rw [dif_neg this]
theorem killVars_C (S : Set σ) (r : R) : killVars R S (C r) = C r :=
  (killVars R S).commutes r
theorem killVars_surjective (S : Set σ) : Function.Surjective (killVars R S) :=
  fun p => ⟨_, killVars_rename S p⟩
theorem sub_rename_killVars_mem (S : Set σ) (p : MvPolynomial σ R) :
    p - rename Subtype.val (killVars R S p) ∈ Ideal.span (X '' S : Set (MvPolynomial σ R)) := by
  rw [← Ideal.Quotient.eq]
  have : (Ideal.Quotient.mkₐ R (Ideal.span (X '' S : Set (MvPolynomial σ R)))) =
      (Ideal.Quotient.mkₐ R (Ideal.span (X '' S : Set (MvPolynomial σ R)))).comp
        ((rename Subtype.val).comp (killVars R S)) := by
    ext x
    by_cases hx : x ∈ S
    · simp only [Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, killVars_X_of_mem hx, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨x, hx, rfl⟩)
    · simp [killVars_X_of_notMem hx]
  exact DFunLike.congr_fun this p
theorem comap_killVars_map_C (S : Set σ) (I : Ideal R) :
    (I.map (C : R →+* MvPolynomial {x : σ // x ∉ S} R)).comap (killVars R S) =
      I.map (C : R →+* MvPolynomial σ R) ⊔ Ideal.span (X '' S) := by
  apply le_antisymm
  · intro p hp
    rw [Ideal.mem_comap] at hp
    have h1 : rename Subtype.val (killVars R S p) ∈ I.map (C : R →+* MvPolynomial σ R) := by
      have h2 := Ideal.mem_map_of_mem
        (rename (Subtype.val : {x : σ // x ∉ S} → σ) : _ →ₐ[R] _).toRingHom hp
      rw [Ideal.map_map] at h2
      have h3 : (rename (Subtype.val : {x : σ // x ∉ S} → σ) : _ →ₐ[R] _).toRingHom.comp C
          = (C : R →+* MvPolynomial σ R) := by
        ext r : 1; simp
      rwa [h3] at h2
    have := Ideal.add_mem _ (Ideal.mem_sup_left h1)
      (Ideal.mem_sup_right (sub_rename_killVars_mem S p))
    simpa using this
  · refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, killVars_C]
      exact Ideal.mem_map_of_mem _ hr
    · rw [Ideal.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp [killVars_X_of_mem hx]
theorem ker_killVars (S : Set σ) :
    RingHom.ker (killVars R S) = Ideal.span (X '' S) := by
  have := comap_killVars_map_C (R := R) S ⊥
  simpa [RingHom.ker_eq_comap_bot] using this
def quotientSpanXEquiv (R : Type*) [CommRing R] (S : Set σ) :
    (MvPolynomial σ R ⧸ Ideal.span (X '' S : Set (MvPolynomial σ R))) ≃ₐ[R]
      MvPolynomial {x : σ // x ∉ S} R :=
  (Ideal.quotientEquivAlgOfEq R (ker_killVars S).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (killVars_surjective S))
@[simp] theorem quotientSpanXEquiv_mk (S : Set σ) (p : MvPolynomial σ R) :
    quotientSpanXEquiv R S (Ideal.Quotient.mk _ p) = killVars R S p := rfl
end Variables
section LinearForms
variable {R : Type*} [CommRing R] {ι J : Type*} [Fintype J]
def linForm (u : J → R) (i : ι) : MvPolynomial (ι × J) R :=
  ∑ j, C (u j) * X (i, j)
def elimIndices (S : Set ι) (j₀ : J) : Set (ι × J) := {x | x.1 ∈ S ∧ x.2 = j₀}
omit [Fintype J] in
@[simp] theorem mem_elimIndices {S : Set ι} {j₀ : J} {x : ι × J} :
    x ∈ elimIndices S j₀ ↔ x.1 ∈ S ∧ x.2 = j₀ := Iff.rfl
theorem linForm_eq [DecidableEq J] (u : J → R) (i : ι) (j₀ : J) :
    linForm u i = C (u j₀) * X (i, j₀) + ∑ j ∈ Finset.univ.erase j₀, C (u j) * X (i, j) :=
  (Finset.add_sum_erase _ (fun j => (C (u j) * X (i, j) : MvPolynomial (ι × J) R))
    (Finset.mem_univ j₀)).symm
open Classical in

def linFormHom (u : J → R) (S : Set ι) (j₀ : J) :
    MvPolynomial (ι × J) R →ₐ[R] MvPolynomial (ι × J) R :=
  aeval fun x => if x ∈ elimIndices S j₀ then linForm u x.1 else X x
theorem linFormHom_X_of_mem (u : J → R) {S : Set ι} (j₀ : J) {i : ι} (hi : i ∈ S) :
    linFormHom u S j₀ (X (i, j₀)) = linForm u i := by
  rw [linFormHom, aeval_X, if_pos (by exact ⟨hi, rfl⟩)]
theorem linFormHom_X_of_notMem (u : J → R) {S : Set ι} {j₀ : J} {x : ι × J}
    (hx : x ∉ elimIndices S j₀) : linFormHom u S j₀ (X x) = X x := by
  rw [linFormHom, aeval_X, if_neg hx]
theorem linFormHom_linForm [DecidableEq J] (u v : J → R) {S : Set ι} (j₀ : J) {i : ι}
    (hi : i ∈ S) : linFormHom u S j₀ (linForm v i) =
      linForm (fun j => if j = j₀ then v j₀ * u j₀ else v j₀ * u j + v j) i := by
  rw [linForm_eq v i j₀, map_add, map_mul, linFormHom_X_of_mem u j₀ hi, map_sum,
    linForm_eq u i j₀, linForm_eq _ i j₀, if_pos rfl, algHom_C, algebraMap_eq, mul_add,
    Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib, C_mul, mul_assoc]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.ne_of_mem_erase hj
  rw [map_mul, linFormHom_X_of_notMem u (by simp [hj']), if_neg hj', algHom_C, algebraMap_eq,
    C_add, C_mul]
  ring
theorem linFormHom_comp_eq_id {u v : J → R} (S : Set ι) {j₀ : J} (h₀ : v j₀ * u j₀ = 1)
    (h : ∀ j, j ≠ j₀ → v j₀ * u j + v j = 0) :
    (linFormHom u S j₀).comp (linFormHom v S j₀) = AlgHom.id R _ := by
  classical
  refine MvPolynomial.algHom_ext fun x => ?_
  by_cases hx : x ∈ elimIndices S j₀
  · obtain ⟨i, j⟩ := x
    obtain ⟨hi, rfl⟩ : i ∈ S ∧ j = j₀ := hx
    rw [AlgHom.comp_apply, linFormHom_X_of_mem v j hi, linFormHom_linForm u v j hi,
      linForm_eq _ i j, if_pos rfl, h₀, Finset.sum_eq_zero]
    · simp
    · intro k hk
      have hk' := Finset.ne_of_mem_erase hk
      rw [if_neg hk', h k hk', C_0, zero_mul]
  · simp [linFormHom_X_of_notMem _ hx]
open Classical in

def linFormInvCoeff (u : J → R) (j₀ : J) (hu : IsUnit (u j₀)) (j : J) : R :=
  if j = j₀ then (↑hu.unit⁻¹ : R) else -((↑hu.unit⁻¹ : R) * u j)
def linFormEquiv (u : J → R) (S : Set ι) (j₀ : J) (hu : IsUnit (u j₀)) :
    MvPolynomial (ι × J) R ≃ₐ[R] MvPolynomial (ι × J) R :=
  AlgEquiv.ofAlgHom (linFormHom u S j₀) (linFormHom (linFormInvCoeff u j₀ hu) S j₀)
    (linFormHom_comp_eq_id S (by simp [linFormInvCoeff])
      (fun j hj => by simp [linFormInvCoeff, hj]))
    (linFormHom_comp_eq_id S (by simp [linFormInvCoeff])
      (fun j hj => by simp [linFormInvCoeff, hj, ← mul_assoc]))
variable (u : J → R) {j₀ : J} (hu : IsUnit (u j₀))
theorem linFormEquiv_X_of_mem {S : Set ι} {i : ι} (hi : i ∈ S) :
    linFormEquiv u S j₀ hu (X (i, j₀)) = linForm u i :=
  linFormHom_X_of_mem u j₀ hi
theorem linFormEquiv_C (S : Set ι) (r : R) : linFormEquiv u S j₀ hu (C r) = C r :=
  (linFormEquiv u S j₀ hu).commutes r
theorem linFormEquiv_symm_X_of_notMem {S : Set ι} {x : ι × J} (hx : x ∉ elimIndices S j₀) :
    (linFormEquiv u S j₀ hu).symm (X x) = X x :=
  linFormHom_X_of_notMem _ hx
theorem image_linFormEquiv_X (S : Set ι) :
    linFormEquiv u S j₀ hu '' (X '' elimIndices S j₀) = linForm u '' S := by
  ext p
  constructor
  · rintro ⟨_, ⟨⟨i, j⟩, ⟨hi, rfl⟩, rfl⟩, rfl⟩
    exact ⟨i, hi, (linFormEquiv_X_of_mem u hu hi).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, ⟨(i, j₀), ⟨hi, rfl⟩, rfl⟩, linFormEquiv_X_of_mem u hu hi⟩
def linFormElim (S : Set ι) :
    MvPolynomial (ι × J) R →ₐ[R] MvPolynomial {x : ι × J // x ∉ elimIndices S j₀} R :=
  (killVars R (elimIndices S j₀)).comp (linFormEquiv u S j₀ hu).symm.toAlgHom
theorem linFormElim_apply (S : Set ι) (p : MvPolynomial (ι × J) R) :
    linFormElim u hu S p = killVars R (elimIndices S j₀) ((linFormEquiv u S j₀ hu).symm p) := rfl
theorem linFormElim_X_of_notMem {S : Set ι} {x : ι × J} (hx : x ∉ elimIndices S j₀) :
    linFormElim u hu S (X x) = X ⟨x, hx⟩ := by
  rw [linFormElim_apply, linFormEquiv_symm_X_of_notMem u hu hx, killVars_X_of_notMem hx]
theorem linFormElim_rename (S : Set ι)
    (p : MvPolynomial {x : ι × J // x ∉ elimIndices S j₀} R) :
    linFormElim u hu S (rename Subtype.val p) = p := by
  have : (linFormElim u hu S).comp (rename Subtype.val) = AlgHom.id R _ := by
    refine MvPolynomial.algHom_ext fun x => ?_
    simp [linFormElim_X_of_notMem u hu x.2]
  exact DFunLike.congr_fun this p
theorem linFormElim_surjective (S : Set ι) : Function.Surjective (linFormElim u hu S) :=
  fun p => ⟨_, linFormElim_rename u hu S p⟩
theorem map_linFormEquiv_map_C_sup_span_X (S : Set ι) (I : Ideal R) :
    (I.map (C : R →+* MvPolynomial (ι × J) R) ⊔ Ideal.span (X '' elimIndices S j₀)).map
      (linFormEquiv u S j₀ hu) = I.map C ⊔ Ideal.span (linForm u '' S) := by
  rw [Ideal.map_sup, Ideal.map_span, image_linFormEquiv_X]
  congr 1
  have h : (linFormEquiv u S j₀ hu).toRingEquiv.toRingHom.comp C =
      (C : R →+* MvPolynomial (ι × J) R) := RingHom.ext (linFormEquiv_C u hu S)
  conv_rhs => rw [← h, ← Ideal.map_map]
  rfl
theorem comap_linFormElim_map_C (S : Set ι) (I : Ideal R) :
    (I.map (C : R →+* MvPolynomial {x : ι × J // x ∉ elimIndices S j₀} R)).comap
      (linFormElim u hu S) = I.map C ⊔ Ideal.span (linForm u '' S) := by
  rw [← map_linFormEquiv_map_C_sup_span_X u hu, ← comap_killVars_map_C]
  ext p
  rw [Ideal.mem_comap, linFormElim_apply, Ideal.mem_map_of_equiv]
  constructor
  · intro h
    exact ⟨_, h, AlgEquiv.apply_symm_apply _ p⟩
  · rintro ⟨x, hx, rfl⟩
    rwa [AlgEquiv.symm_apply_apply]
theorem ker_linFormElim (S : Set ι) :
    RingHom.ker (linFormElim u hu S) = Ideal.span (linForm u '' S) := by
  have := comap_linFormElim_map_C u hu S ⊥
  simpa [RingHom.ker_eq_comap_bot] using this
theorem ker_map_comp_linFormElim (S : Set ι) (I : Ideal R) :
    RingHom.ker ((MvPolynomial.map (Ideal.Quotient.mk I)).comp (linFormElim u hu S).toRingHom) =
      I.map C ⊔ Ideal.span (linForm u '' S) := by
  rw [← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker, ← comap_linFormElim_map_C u hu]
  rfl
def quotientSpanLinFormEquiv (S : Set ι) :
    (MvPolynomial (ι × J) R ⧸ Ideal.span (linForm u '' S)) ≃ₐ[R]
      MvPolynomial {x : ι × J // x ∉ elimIndices S j₀} R :=
  (Ideal.quotientEquivAlgOfEq R (ker_linFormElim u hu S).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (linFormElim_surjective u hu S))
def quotientMapCSupSpanLinFormEquiv (S : Set ι) (I : Ideal R) :
    (MvPolynomial (ι × J) R ⧸
      (I.map (C : R →+* MvPolynomial (ι × J) R) ⊔ Ideal.span (linForm u '' S))) ≃+*
      MvPolynomial {x : ι × J // x ∉ elimIndices S j₀} (R ⧸ I) :=
  (Ideal.quotEquivOfEq (ker_map_comp_linFormElim u hu S I).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      ((MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective).comp
        (linFormElim_surjective u hu S)))
include hu
end LinearForms
end GlobalTheory


