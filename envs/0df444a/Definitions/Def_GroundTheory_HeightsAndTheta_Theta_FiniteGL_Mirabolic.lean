-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FiniteGL_Mirabolic
-- name    : GroundTheory_HeightsAndTheta_Theta_FiniteGL_Mirabolic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:40.731925+00:00
-- url     : https://prove2.me/theorems/21fbade2-dbfe-47a2-bf36-255482f9f115
-- title:
--   Mirabolic
-- statement:
--   Definitions and structural lemmas for Mirabolic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FiniteGL/Mirabolic.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Theta
namespace FinGL
open Matrix
noncomputable section
section Groups
variable (n : ℕ) (F : Type*) [Field F]
def upperUnipotent : Subgroup (GL (Fin n) F) where
  carrier := {g | (∀ i j, j < i → (g : Matrix (Fin n) (Fin n) F) i j = 0) ∧
    ∀ i, (g : Matrix (Fin n) (Fin n) F) i i = 1}
  one_mem' := by
    refine ⟨fun i j h ↦ ?_, fun i ↦ ?_⟩
    · simp [Matrix.one_apply_ne (ne_of_gt h)]
    · simp
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun i j hij ↦ ?_, fun i ↦ ?_⟩
    · simp only [Units.val_mul, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rcases lt_or_ge k i with hk | hk
      · simp [ha i k hk]
      · simp [hb k j (lt_of_lt_of_le hij hk)]
    · simp only [Units.val_mul, Matrix.mul_apply]
      rw [Finset.sum_eq_single i]
      · simp [ha' i, hb' i]
      · intro k _ hki
        rcases lt_or_gt_of_ne hki with hk | hk
        · simp [ha i k hk]
        · simp [hb k i hk]
      · simp
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    let _ := g.invertible
    have ht : BlockTriangular (g : Matrix (Fin n) (Fin n) F) id := fun i j h ↦ hg i j h
    have hinv : BlockTriangular ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) id := by
      rw [Matrix.coe_units_inv]
      exact blockTriangular_inv_of_blockTriangular ht
    refine ⟨fun i j hij ↦ hinv hij, fun i ↦ ?_⟩
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) F ↦ M i i)
      (congrArg Units.val (inv_mul_cancel g))
    simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_eq] at h1
    rw [Finset.sum_eq_single i] at h1
    · simpa [hg' i] using h1
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with hk | hk
      · simp [hinv hk]
      · simp [hg k i hk]
    · simp
variable {n} in

def lastIdx [NeZero n] : Fin n := ⟨n - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne n)) one_pos⟩
def mirabolic [NeZero n] : Subgroup (GL (Fin n) F) where
  carrier := {g | ∀ j, (g : Matrix (Fin n) (Fin n) F) lastIdx j = if j = lastIdx then 1 else 0}
  one_mem' := by
    intro j
    by_cases h : j = lastIdx
    · subst h; simp
    · simp [h, Matrix.one_apply_ne (Ne.symm h)]
  mul_mem' := by
    intro a b ha hb j
    have ha' : ∀ k, (a : Matrix (Fin n) (Fin n) F) lastIdx k = if k = lastIdx then 1 else 0 := ha
    simp only [Units.val_mul, Matrix.mul_apply, ha', ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hb j
  inv_mem' := by
    intro g hg j
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) F ↦ M lastIdx j)
      (congrArg Units.val (mul_inv_cancel g))
    have hg' : ∀ k, (g : Matrix (Fin n) (Fin n) F) lastIdx k = if k = lastIdx then 1 else 0 := hg
    simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, hg', ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    rw [h1, Matrix.one_apply]
    by_cases h : j = lastIdx
    · simp [h]
    · simp [h, Ne.symm h]
theorem upperUnipotent_le_mirabolic [NeZero n] : upperUnipotent n F ≤ mirabolic n F := by
  rintro g ⟨hg, hg'⟩ j
  by_cases h : j = lastIdx
  · subst h; simp [hg']
  · have hj : j < lastIdx := by
      have := j.2
      rw [Fin.lt_def]
      have : (j : ℕ) ≠ n - 1 := fun e ↦ h (Fin.ext e)
      simp only [lastIdx]; omega
    simp [h, hg lastIdx j hj]
end Groups
section Generic
variable {n : ℕ} {F : Type*} [Field F]
def superdiagSum (u : Matrix (Fin n) (Fin n) F) : F :=
  ∑ i : Fin n, ∑ j : Fin n, if (j : ℕ) = i + 1 then u i j else 0
theorem superdiag_mul {a b : GL (Fin n) F} (ha : a ∈ upperUnipotent n F)
    (hb : b ∈ upperUnipotent n F) {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    ((a * b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (a : Matrix (Fin n) (Fin n) F) i j + (b : Matrix (Fin n) (Fin n) F) i j := by
  obtain ⟨ha, ha'⟩ := ha
  obtain ⟨hb, hb'⟩ := hb
  have hne : i ≠ j := fun e ↦ by rw [e] at hij; omega
  simp only [Units.val_mul, Matrix.mul_apply]
  rw [Fintype.sum_eq_add i j hne]
  · simp [ha' i, hb' j, add_comm]
  · rintro k ⟨hki, hkj⟩
    rcases lt_or_gt_of_ne hki with hk | hk
    · simp [ha i k hk]
    · have : j < k := by
        rw [Fin.lt_def] at hk ⊢
        have : (k : ℕ) ≠ j := fun e ↦ hkj (Fin.ext e)
        omega
      simp [hb k j this]
theorem superdiagSum_mul {a b : GL (Fin n) F} (ha : a ∈ upperUnipotent n F)
    (hb : b ∈ upperUnipotent n F) :
    superdiagSum ((a * b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      superdiagSum (a : Matrix (Fin n) (Fin n) F) + superdiagSum (b : Matrix (Fin n) (Fin n) F) := by
  simp only [superdiagSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs with h
  · exact superdiag_mul ha hb h
  · simp
theorem superdiagSum_one : superdiagSum (1 : Matrix (Fin n) (Fin n) F) = 0 := by
  refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
  split_ifs with h
  · have : i ≠ j := fun e ↦ by rw [e] at h; omega
    simp [Matrix.one_apply_ne this]
  · rfl
variable (n F)
def genericChar (ψ₀ : AddChar F ℂ) : upperUnipotent n F →* ℂ where
  toFun u := ψ₀ (superdiagSum ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
  map_one' := by simp [superdiagSum_one]
  map_mul' a b := by
    simp only [Subgroup.coe_mul]
    rw [superdiagSum_mul a.2 b.2, AddChar.map_add_eq_mul]
def genericRep (ψ₀ : AddChar F ℂ) : Representation ℂ (upperUnipotent n F) ℂ where
  toFun u := genericChar n F ψ₀ u • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp [mul_comm]
variable [NeZero n]
abbrev MirabolicInducedSpace (ψ₀ : AddChar F ℂ) :=
  Representation.coindV (Subgroup.inclusion (upperUnipotent_le_mirabolic n F)) (genericRep n F ψ₀)
def mirabolicInduced (ψ₀ : AddChar F ℂ) :
    Representation ℂ (mirabolic n F) (MirabolicInducedSpace n F ψ₀) :=
  Representation.coind (Subgroup.inclusion (upperUnipotent_le_mirabolic n F)) (genericRep n F ψ₀)
end Generic
section Flags
variable (n : ℕ) (F : Type*) [Field F]
structure Flag where

  length : ℕ

  space : Fin (length + 1) → Submodule F (Fin n → F)
  mono : Monotone space
  space_zero : space 0 = ⊥
  space_last : space (Fin.last length) = ⊤
variable {n F}
def Flag.IsProper (𝓕 : Flag n F) : Prop := ∃ i, 𝓕.space i ≠ ⊥ ∧ 𝓕.space i ≠ ⊤
def Flag.radical (𝓕 : Flag n F) : Subgroup (GL (Fin n) F) where
  carrier := {g | ∀ i : Fin 𝓕.length, ∀ v ∈ 𝓕.space i.succ,
    (g : Matrix (Fin n) (Fin n) F) *ᵥ v - v ∈ 𝓕.space i.castSucc}
  one_mem' := by intro i v _; simp
  mul_mem' := by
    intro a b ha hb i v hv
    have hle : 𝓕.space i.castSucc ≤ 𝓕.space i.succ := 𝓕.mono Fin.castSucc_lt_succ.le
    have hbv : (b : Matrix (Fin n) (Fin n) F) *ᵥ v ∈ 𝓕.space i.succ := by
      have := (𝓕.space i.succ).add_mem (hle (hb i v hv)) hv
      simpa using this
    have key : ((a * b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v - v =
        ((a : Matrix (Fin n) (Fin n) F) *ᵥ ((b : Matrix (Fin n) (Fin n) F) *ᵥ v) -
          (b : Matrix (Fin n) (Fin n) F) *ᵥ v) + ((b : Matrix (Fin n) (Fin n) F) *ᵥ v - v) := by
      simp [Matrix.mulVec_mulVec]
    rw [key]
    exact (𝓕.space i.castSucc).add_mem (ha i _ hbv) (hb i v hv)
  inv_mem' := by
    intro g hg i v hv
    have hle : 𝓕.space i.castSucc ≤ 𝓕.space i.succ := 𝓕.mono Fin.castSucc_lt_succ.le
    have hmaps : ∀ w ∈ 𝓕.space i.succ,
        Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) F) w ∈ 𝓕.space i.succ := by
      intro w hw
      have := (𝓕.space i.succ).add_mem (hle (hg i w hw)) hw
      simpa using this
    let f : 𝓕.space i.succ →ₗ[F] 𝓕.space i.succ :=
      (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) F)).restrict hmaps
    have hinv : ∀ w : Fin n → F, ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ
        ((g : Matrix (Fin n) (Fin n) F) *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hinj : Function.Injective f := by
      intro x y hxy
      have h1 : (g : Matrix (Fin n) (Fin n) F) *ᵥ (x : Fin n → F) =
          (g : Matrix (Fin n) (Fin n) F) *ᵥ (y : Fin n → F) := by
        simpa [f, LinearMap.restrict_apply] using congrArg Subtype.val hxy
      apply Subtype.ext
      rw [← hinv x, ← hinv y, h1]
    obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨v, hv⟩
    have hw' : (g : Matrix (Fin n) (Fin n) F) *ᵥ (w : Fin n → F) = v := by
      simpa [f, LinearMap.restrict_apply] using congrArg Subtype.val hw
    have hgv : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v = w := by
      rw [← hw', hinv]
    rw [hgv, ← hw']
    have := (𝓕.space i.castSucc).neg_mem (hg i w w.2)
    simpa using this
variable (n F) in

def IsCuspidal {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) : Prop :=
  ∀ 𝓕 : Flag n F, 𝓕.IsProper → ∀ v : V, (∀ g ∈ 𝓕.radical, ρ g v = v) → v = 0
end Flags
section Inhabitants
variable {n : ℕ} {F : Type*} [Field F]
def Flag.ofSubspace (W : Submodule F (Fin n → F)) : Flag n F where
  length := 2
  space := ![⊥, W, ⊤]
  mono := by
    refine Fin.monotone_iff_le_succ.mpr fun i ↦ ?_
    fin_cases i <;> simp
  space_zero := rfl
  space_last := rfl
variable (n F) in

def lineFlag (hn : 1 < n) : Flag n F :=
  Flag.ofSubspace (Submodule.span F {Pi.single (⟨0, by omega⟩ : Fin n) (1 : F)})
def upperTwo (x : F) : GL (Fin 2) F :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
theorem upperTwo_mem (x : F) : upperTwo x ∈ upperUnipotent 2 F := by
  refine ⟨fun i j hij ↦ ?_, fun i ↦ ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [upperTwo]
  · fin_cases i <;> simp [upperTwo]
variable [NeZero n]
open Classical in
variable (n F) in

def mirabolicDeltaFun (ψ₀ : AddChar F ℂ) (p : mirabolic n F) : ℂ :=
  if h : (p : GL (Fin n) F) ∈ upperUnipotent n F then genericChar n F ψ₀ ⟨p, h⟩ else 0
theorem mirabolicDeltaFun_mem (ψ₀ : AddChar F ℂ) :
    mirabolicDeltaFun n F ψ₀ ∈ MirabolicInducedSpace n F ψ₀ := by
  rw [Representation.mem_coindV]
  intro u p
  by_cases hp : (p : GL (Fin n) F) ∈ upperUnipotent n F
  · have hup : (u : GL (Fin n) F) * p ∈ upperUnipotent n F := mul_mem u.2 hp
    have hup' : ((Subgroup.inclusion (upperUnipotent_le_mirabolic n F) u * p : mirabolic n F) :
        GL (Fin n) F) ∈ upperUnipotent n F := hup
    simp only [mirabolicDeltaFun, dif_pos hp]
    rw [dif_pos hup']
    change genericChar n F ψ₀ (u * ⟨p, hp⟩) = _
    rw [map_mul]
    simp [genericRep]
  · have hup : (u : GL (Fin n) F) * p ∉ upperUnipotent n F := fun h ↦
      hp (by simpa using mul_mem (inv_mem u.2) h)
    have hup' : ((Subgroup.inclusion (upperUnipotent_le_mirabolic n F) u * p : mirabolic n F) :
        GL (Fin n) F) ∉ upperUnipotent n F := hup
    simp only [mirabolicDeltaFun, dif_neg hp, map_zero]
    rw [dif_neg hup']
variable (n F) in

def mirabolicDelta (ψ₀ : AddChar F ℂ) : MirabolicInducedSpace n F ψ₀ :=
  ⟨mirabolicDeltaFun n F ψ₀, mirabolicDeltaFun_mem ψ₀⟩
end Inhabitants
end
end FinGL
end GroundTheory.Heights₂.Theta


