-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
-- name    : GroundTheory_AutomorphicForms_Iwasawa
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:02.05827+00:00
-- url     : https://prove2.me/theorems/5eed9eaf-4a68-439d-b51c-315db32f6c55
-- title:
--   Iwasawa
-- statement:
--   Definitions and structural lemmas for Iwasawa, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_eventually_pow_mul_mem
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk


set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open ValuativeRel Matrix Filter
open scoped Pointwise
namespace Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)
section Subgroups
def blockUpper {α : Type*} [LinearOrder α] (β : Fin n → α) : Subgroup (GL (Fin n) F) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) F).BlockTriangular β}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Units.val_mul]
    exact hg.mul hh
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Units.val_one]
    exact blockTriangular_one
  inv_mem' {g} hg := by
    let := g.invertible
    simp only [Set.mem_ofPred_eq, coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hg
def borel : Subgroup (GL (Fin n) F) :=
  blockUpper F n id
theorem mem_borel {g : GL (Fin n) F} :
    g ∈ borel F n ↔ (g : Matrix (Fin n) (Fin n) F).IsUpperTriangular :=
  Iff.rfl
theorem upper_mul_apply_self {A C : Matrix (Fin n) (Fin n) F} (hA : A.IsUpperTriangular)
    (hC : C.IsUpperTriangular) (i : Fin n) : (A * C) i i = A i i * C i i := by
  rw [mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA h, zero_mul]
    · rw [hC h, mul_zero]
  · simp
theorem mul_apply_self_of_mem_borel {g h : GL (Fin n) F} (hg : g ∈ borel F n)
    (hh : h ∈ borel F n) (i : Fin n) : (g * h : GL (Fin n) F) i i = g i i * h i i := by
  rw [Units.val_mul]
  exact upper_mul_apply_self F n hg hh i
theorem apply_self_ne_zero_of_mem_borel {g : GL (Fin n) F} (hg : g ∈ borel F n) (i : Fin n) :
    g i i ≠ 0 := by
  have hdet : (g : Matrix (Fin n) (Fin n) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  rw [det_of_isUpperTriangular hg, Finset.prod_ne_zero_iff] at hdet
  exact hdet i (Finset.mem_univ _)
theorem inv_apply_self_of_mem_borel {g : GL (Fin n) F} (hg : g ∈ borel F n) (i : Fin n) :
    (g⁻¹ : GL (Fin n) F) i i = (g i i)⁻¹ := by
  have h := mul_apply_self_of_mem_borel F n ((borel F n).inv_mem hg) hg i
  rw [inv_mul_cancel, Units.val_one, one_apply_eq] at h
  exact eq_inv_of_mul_eq_one_left h.symm
def unipotent : Subgroup (GL (Fin n) F) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) F).IsUpperTriangular ∧ ∀ i, g i i = 1}
  mul_mem' {g h} hg hh := ⟨(borel F n).mul_mem hg.1 hh.1, fun i => by
    rw [mul_apply_self_of_mem_borel F n hg.1 hh.1, hg.2, hh.2, one_mul]⟩
  one_mem' := ⟨(borel F n).one_mem, fun i => by simp⟩
  inv_mem' {g} hg := ⟨(borel F n).inv_mem hg.1, fun i => by
    rw [inv_apply_self_of_mem_borel F n hg.1, hg.2, inv_one]⟩
def diagGL : (Fin n → Fˣ) →* GL (Fin n) F where
  toFun d := ⟨diagonal fun i => (d i : F), diagonal fun i => ((d i)⁻¹ : Fˣ),
    by simp [diagonal_mul_diagonal], by simp [diagonal_mul_diagonal]⟩
  map_one' := Units.ext (by simp)
  map_mul' d e := Units.ext (by simp [diagonal_mul_diagonal])
@[simp]
theorem coe_diagGL (d : Fin n → Fˣ) :
    ((diagGL F n d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal fun i => (d i : F) :=
  rfl
theorem diagGL_mem_borel (d : Fin n → Fˣ) : diagGL F n d ∈ borel F n := by
  rw [mem_borel, coe_diagGL]
  exact blockTriangular_diagonal _
end Subgroups
section Integral
variable [ValuativeRel F]
theorem diagGL_map_mem_integralGL (e : Fin n → (𝒪[F])ˣ) :
    diagGL F n (fun i => Units.map (𝒪[F]).subtype.toMonoidHom (e i)) ∈ integralGL F n := by
  have hinv : ∀ i, (((e i : 𝒪[F]) : F))⁻¹ = ((((e i)⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) := fun i =>
    (eq_inv_of_mul_eq_one_left (by
      have h := congrArg Subtype.val (e i).inv_mul
      rwa [MulMemClass.coe_mul, OneMemClass.coe_one] at h)).symm
  rw [mem_integralGL_iff, ← map_inv]
  constructor <;> intro i j <;> rw [coe_diagGL, diagonal_apply] <;> split_ifs <;>
    simp [Units.coe_map, hinv]
end Integral
section Local
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
def uniformizerUnit : Fˣ :=
  Units.mk0 (GLnLocal.uniformizer F : F) fun h => (irreducible_uniformizer F).ne_zero (Subtype.ext h)
@[simp]
theorem coe_uniformizerUnit : ((uniformizerUnit F : Fˣ) : F) = GLnLocal.uniformizer F :=
  rfl
def torusPow (l : Fin n → ℤ) : GL (Fin n) F :=
  diagGL F n fun i => uniformizerUnit F ^ l i
theorem exists_zpow_mul_unit {x : F} (hx : x ≠ 0) :
    ∃ (z : ℤ) (u : (𝒪[F])ˣ), x = (GLnLocal.uniformizer F : F) ^ z * ((u : 𝒪[F]) : F) := by
  obtain ⟨m, hm⟩ := (eventually_pow_mul_mem F x).exists
  have hπ : (GLnLocal.uniformizer F : F) ≠ 0 := (uniformizerUnit F).ne_zero
  have hy : (⟨_, hm⟩ : 𝒪[F]) ≠ 0 := fun h => by
    have h' := congrArg Subtype.val h
    simp only [ZeroMemClass.coe_zero] at h'
    exact mul_ne_zero (pow_ne_zero _ hπ) hx h'
  obtain ⟨k, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy (irreducible_uniformizer F)
  refine ⟨(k : ℤ) - m, u, ?_⟩
  have h := congrArg Subtype.val hu
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow] at h
  rw [zpow_sub₀ hπ, zpow_natCast, zpow_natCast, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ hπ),
    mul_comm, h, mul_comm]
section Decomposition
theorem exists_borel_mul_integralGL (g : GL (Fin n) F) :
    ∃ b ∈ borel F n, ∃ k ∈ integralGL F n, g = b * k := by
  classical
  set L := mapSubmodule F n g (standardLattice F n) with hL
  have hπ : (GLnLocal.uniformizer F : F) ≠ 0 := (uniformizerUnit F).ne_zero

  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ i j, (GLnLocal.uniformizer F : F) ^ m * g i j ∈ 𝒪[F] :=
    (eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_pow_mul_mem F (g i j)).exists
  set d : F := (GLnLocal.uniformizer F : F) ^ m with hd
  have hd0 : d ≠ 0 := pow_ne_zero _ hπ
  have hbdd : ∀ v ∈ L, ∀ i, d * v i ∈ 𝒪[F] := by
    rintro _ ⟨w, hw, rfl⟩ i
    rw [glLin_apply, mulVec, dotProduct, Finset.mul_sum]
    exact Subring.sum_mem _ fun j _ => by
      rw [← mul_assoc]
      exact Subring.mul_mem _ (hm i j) (hw j)

  have hfull : ∀ j, ∃ c : F, c ≠ 0 ∧ c • Pi.single j (1 : F) ∈ L := by
    intro j
    obtain ⟨m', hm'⟩ : ∃ m' : ℕ, ∀ i, (GLnLocal.uniformizer F : F) ^ m' * (g⁻¹ : GL (Fin n) F) i j ∈ 𝒪[F] :=
      (eventually_all.mpr fun i => eventually_pow_mul_mem F ((g⁻¹ : GL (Fin n) F) i j)).exists
    refine ⟨(GLnLocal.uniformizer F : F) ^ m', pow_ne_zero _ hπ, ?_⟩
    refine ⟨((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ
      ((GLnLocal.uniformizer F : F) ^ m' • Pi.single j 1), fun i => ?_, ?_⟩
    · rw [mulVec_smul, mulVec_single_one, Pi.smul_apply, col_apply, smul_eq_mul]
      exact hm' i
    · rw [glLin_apply, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

  let Z : Fin n → Submodule 𝒪[F] (Fin n → F) := fun j =>
    ⨅ (i : Fin n) (_ : j < i), LinearMap.ker (LinearMap.proj i : (Fin n → F) →ₗ[𝒪[F]] F)
  have hZ : ∀ j v, v ∈ Z j ↔ ∀ i, j < i → v i = 0 := by
    intro j v
    simp [Z, Submodule.mem_iInf]
  let S : Fin n → Submodule 𝒪[F] F := fun j =>
    (L ⊓ Z j).map (LinearMap.proj j : (Fin n → F) →ₗ[𝒪[F]] F)
  have hS : ∀ j t, t ∈ S j ↔ ∃ v ∈ L, (∀ i, j < i → v i = 0) ∧ v j = t := by
    intro j t
    constructor
    · rintro ⟨v, ⟨hvL, hvZ⟩, rfl⟩
      exact ⟨v, hvL, (hZ j v).1 hvZ, rfl⟩
    · rintro ⟨v, hvL, hvZ, rfl⟩
      exact ⟨v, ⟨hvL, (hZ j v).2 hvZ⟩, rfl⟩

  have hgen : ∀ j, ∃ t ∈ S j, ∀ s ∈ S j, ∃ r : 𝒪[F], s = (r : F) * t := by
    intro j
    let J : Ideal 𝒪[F] := (S j).comap (LinearMap.toSpanSingleton 𝒪[F] F d⁻¹)
    have : J.IsPrincipal := IsPrincipalIdealRing.principal J
    refine ⟨((Submodule.IsPrincipal.generator J : 𝒪[F]) : F) * d⁻¹, ?_, ?_⟩
    · have h : LinearMap.toSpanSingleton 𝒪[F] F d⁻¹ (Submodule.IsPrincipal.generator J) ∈ S j :=
        Submodule.IsPrincipal.generator_mem J
      rwa [LinearMap.toSpanSingleton_apply, Subring.smul_def, smul_eq_mul] at h
    · intro s hs
      obtain ⟨v, hvL, -, rfl⟩ := (hS j s).1 hs
      have hmem : (⟨d * v j, hbdd v hvL j⟩ : 𝒪[F]) ∈ J := by
        show LinearMap.toSpanSingleton 𝒪[F] F d⁻¹ _ ∈ S j
        rw [LinearMap.toSpanSingleton_apply, Subring.smul_def, smul_eq_mul]
        convert hs using 1
        field_simp
      obtain ⟨r, hr⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator J).1 hmem
      refine ⟨r, ?_⟩
      have h := congrArg Subtype.val hr
      simp only [smul_eq_mul, MulMemClass.coe_mul] at h
      field_simp
      linear_combination h
  choose t htS htgen using hgen
  choose v hvL hvZ hvt using fun j => (hS j (t j)).1 (htS j)
  have ht0 : ∀ j, t j ≠ 0 := by
    intro j h
    obtain ⟨c, hc, hcL⟩ := hfull j
    have hcS : c ∈ S j := (hS j c).2 ⟨_, hcL, fun i hi => by simp [hi.ne'],
      by simp⟩
    obtain ⟨r, hr⟩ := htgen j c hcS
    exact hc (by rw [hr, h, mul_zero])

  have hspan : ∀ x ∈ L, x ∈ Submodule.span 𝒪[F] (Set.range v) := by
    suffices ∀ k : ℕ, ∀ x ∈ L, (∀ i : Fin n, k ≤ (i : ℕ) → x i = 0) →
        x ∈ Submodule.span 𝒪[F] (Set.range v) from
      fun x hx => this n x hx fun i hi => absurd i.isLt (not_lt.mpr hi)
    intro k
    induction k with
    | zero =>
      intro x _ hx
      rw [show x = 0 from funext fun i => hx i (Nat.zero_le _)]
      exact Submodule.zero_mem _
    | succ k ih =>
      intro x hxL hx
      by_cases hk : k < n
      · obtain ⟨r, hr⟩ := htgen ⟨k, hk⟩ (x ⟨k, hk⟩) ((hS _ _).2 ⟨x, hxL, fun i hi => hx i (by
          rw [Fin.lt_def] at hi
          simp only at hi
          omega), rfl⟩)
        have h1 : x - r • v ⟨k, hk⟩ ∈ Submodule.span 𝒪[F] (Set.range v) := by
          refine ih _ (L.sub_mem hxL (L.smul_mem r (hvL _))) fun i hi => ?_
          rw [Pi.sub_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul]
          rcases Nat.lt_or_eq_of_le hi with h | h
          · have hji : (⟨k, hk⟩ : Fin n) < i := by
              rw [Fin.lt_def]
              exact h
            rw [hx i (by omega), hvZ _ i hji, mul_zero, sub_zero]
          · obtain rfl : i = ⟨k, hk⟩ := Fin.ext h.symm
            rw [hvt, ← hr, sub_self]
        have h2 := Submodule.add_mem _ h1
          (Submodule.smul_mem _ r (Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩))
        rwa [sub_add_cancel] at h2
      · exact ih x hxL fun i _ => absurd i.isLt (by omega)

  let B : Matrix (Fin n) (Fin n) F := Matrix.of fun i j => v j i
  have hBu : B.IsUpperTriangular := fun i j hij => hvZ j i hij
  have hBdet : B.det ≠ 0 := by
    rw [det_of_isUpperTriangular hBu, Finset.prod_ne_zero_iff]
    intro i _
    simp only [B, of_apply, hvt]
    exact ht0 i
  let b : GL (Fin n) F := nonsingInvUnit B (isUnit_iff_ne_zero.mpr hBdet)
  have hb : (b : Matrix (Fin n) (Fin n) F) = B := rfl
  have hbL : mapSubmodule F n b (standardLattice F n) = L := by
    rw [mapSubmodule, standardLattice_eq_span, Submodule.map_span, ← Set.range_comp]
    have : (glLin F n b ∘ fun j => Pi.single j (1 : F)) = v := funext fun j => by
      ext i
      simp only [Function.comp, glLin_apply, mulVec_single_one, col_apply, hb, B, of_apply]
    rw [this]
    exact le_antisymm (Submodule.span_le.mpr (Set.range_subset_iff.mpr hvL)) hspan
  refine ⟨b, hBu, b⁻¹ * g, ?_, (mul_inv_cancel_left b g).symm⟩
  rw [← mapSubmodule_standardLattice_eq_iff, mapSubmodule_mul, ← hL, ← hbL,
    mapSubmodule_inv_mapSubmodule]
end Decomposition
section Coordinates
theorem exists_iwasawa (g : GL (Fin n) F) :
    ∃ u ∈ unipotent F n, ∃ l : Fin n → ℤ, ∃ k ∈ integralGL F n, g = u * torusPow F n l * k := by
  obtain ⟨b, hb, k, hk, rfl⟩ := exists_borel_mul_integralGL F n g
  have hne := apply_self_ne_zero_of_mem_borel F n hb
  choose l e he using fun i => exists_zpow_mul_unit F (hne i)
  let δ : Fin n → Fˣ := fun i => Units.mk0 (b i i) (hne i)
  let E : GL (Fin n) F := diagGL F n fun i => Units.map (𝒪[F]).subtype.toMonoidHom (e i)
  have hDE : diagGL F n δ = torusPow F n l * E := by
    rw [torusPow, ← map_mul]
    congr 1
    funext i
    ext
    simp [δ, he i, Units.val_zpow_eq_zpow_val, Units.coe_map]
  have hDinv : (diagGL F n δ)⁻¹ ∈ borel F n := (borel F n).inv_mem (diagGL_mem_borel F n δ)
  refine ⟨b * (diagGL F n δ)⁻¹, ⟨(borel F n).mul_mem hb hDinv, fun i => ?_⟩, l, E * k,
    (integralGL F n).mul_mem (diagGL_map_mem_integralGL F n e) hk, ?_⟩
  · rw [mul_apply_self_of_mem_borel F n hb hDinv, ← map_inv, coe_diagGL, diagonal_apply_eq]
    simp [δ, hne i]
  · rw [show b * (diagGL F n δ)⁻¹ * torusPow F n l * (E * k) =
      b * (diagGL F n δ)⁻¹ * (torusPow F n l * E) * k by group, ← hDE]
    group
def iwasawaExponent (g : GL (Fin n) F) : Fin n → ℤ :=
  (exists_iwasawa F n g).choose_spec.2.choose
end Coordinates
end Local
end Iwasawa
end GroundTheory.Automorphic


