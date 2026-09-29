-- Prove2me | solution 1 for AutomorphicForm.exists_forall_isHeckeCosetEigenfunctionAt_finTranslateSum_of_levelOne_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f11a701d-0c68-577e-8fe6-5fa12ebd882d

import Mathlib
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_isHeckeCosetEigenfunctionAt_finTranslateSum_of_levelOne_invariant

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.SmoothCusp HeckeIntegralSeam AdelicDock

noncomputable section

namespace HeckeLocalitySol

variable {F : Type} [Field F] [NumberField F]

local notation "𝓡" => (𝓞 F)

abbrev U (N : Ideal (𝓞 F)) : Subgroup (AdelicGL2 (𝓞 F) F) :=
  levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F

theorem isLevelOneMatrix_iff_forall {N : Ideal (𝓞 F)} (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    IsLevelOneMatrix (𝓞 F) F N m ↔
      ∀ ℓ : HeightOneSpectrum (𝓞 F), IsLocalLevelOne (𝓞 F) F ℓ N (fun i j => m i j ℓ) := by
  constructor
  · rintro ⟨⟨hint, hll⟩, hlr⟩ ℓ
    exact ⟨fun i j => hint i j ℓ, hll ℓ, by have := hlr ℓ; rwa [coe_sub_apply, coe_one_apply] at this⟩
  · intro h
    refine ⟨⟨fun i j ℓ => (h ℓ).integral i j, fun ℓ => (h ℓ).lowerLeft⟩, fun ℓ => ?_⟩
    rw [coe_sub_apply, coe_one_apply]; exact (h ℓ).lowerRight

theorem coe_finComponent (ℓ : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ((finComponent (𝓞 F) F ℓ g : GL (Fin 2) (ℓ.adicCompletion F)) : Matrix _ _ _)
      = fun i j => (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j ℓ := by
  ext i j; rfl

theorem mem_finiteLevelOne_iff_forall {N : Ideal (𝓞 F)} (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    g ∈ finiteLevelOne (𝓞 F) F N ↔
      ∀ ℓ : HeightOneSpectrum (𝓞 F), finComponent (𝓞 F) F ℓ g ∈ localLevelOne (𝓞 F) F ℓ N := by
  rw [mem_finiteLevelOne_iff, isLevelOneMatrix_iff_forall, isLevelOneMatrix_iff_forall]
  simp only [mem_localLevelOne_iff, ← map_inv, coe_finComponent]
  exact ⟨fun h ℓ => ⟨h.1 ℓ, h.2 ℓ⟩, fun h => ⟨fun ℓ => (h ℓ).1, fun ℓ => (h ℓ).2⟩⟩

private theorem _root_.HeckeLocalitySol.mem_U_iff {N : Ideal (𝓞 F)} (g : AdelicGL2 (𝓞 F) F) :
    g ∈ U N ↔ glArch (𝓞 F) F g = 1 ∧
      ∀ ℓ : HeightOneSpectrum (𝓞 F), finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F g) ∈ localLevelOne (𝓞 F) F ℓ N := by
  rw [Subgroup.mem_inf, mem_levelOne_iff, mem_finiteLevelOne_iff_forall, mem_finiteAdelicGL2Subgroup_iff]
  tauto

p2m_export "HeckeLocalitySol" "mem_U_iff"

theorem isLocalLevelOne_iff_of_idealBound {N : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
    (hv : idealBound (𝓞 F) N v = 1) (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) :
    IsLocalLevelOne (𝓞 F) F v N m ↔ ∀ i j, m i j ∈ v.adicCompletionIntegers F := by
  constructor
  · exact fun h => h.integral
  · intro h
    refine ⟨h, ?_, ?_⟩
    · rw [hv]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
    · rw [hv]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (sub_mem (h 1 1) (one_mem _))

def Kv (v : HeightOneSpectrum (𝓞 F)) : Subgroup (GL (Fin 2) (v.adicCompletion F)) :=
  localLevelOne (𝓞 F) F v ⊤

theorem mem_Kv_iff {v : HeightOneSpectrum (𝓞 F)} (k : GL (Fin 2) (v.adicCompletion F)) :
    k ∈ Kv v ↔
      (∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F) ∧
      ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
        ∈ v.adicCompletionIntegers F := by
  show k ∈ localLevelOne (𝓞 F) F v ⊤ ↔ _
  rw [mem_localLevelOne_iff, isLocalLevelOne_iff_of_idealBound (idealBound_top v),
    isLocalLevelOne_iff_of_idealBound (idealBound_top v)]

theorem localLevelOne_eq_Kv {N : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
    (hv : idealBound (𝓞 F) N v = 1) : localLevelOne (𝓞 F) F v N = Kv v := by
  ext k
  rw [mem_localLevelOne_iff, isLocalLevelOne_iff_of_idealBound hv,
    isLocalLevelOne_iff_of_idealBound hv, mem_Kv_iff]

theorem eq_of_glArch_eq_of_forall_finComponent_eq {g g' : AdelicGL2 (𝓞 F) F}
    (h₁ : glArch (𝓞 F) F g = glArch (𝓞 F) F g')
    (h₂ : ∀ ℓ, finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F g) = finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F g')) :
    g = g' := by
  apply Units.ext
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_
  · exact congrArg Units.val h₁
  · refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 F) F fun ℓ => ?_
    exact congrArg Units.val (h₂ ℓ)

def lv (v : HeightOneSpectrum (𝓞 F)) : GL (Fin 2) (v.adicCompletion F) →* AdelicGL2 (𝓞 F) F :=
  (finEmbed (𝓞 F) F).comp (localEmbed (𝓞 F) F v)

theorem glArch_lv (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (v.adicCompletion F)) :
    glArch (𝓞 F) F (lv v k) = 1 := glArch_finEmbed (𝓞 F) F _

theorem finComponent_lv_self (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (v.adicCompletion F)) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (lv v k)) = k := by
  rw [lv, MonoidHom.comp_apply, glFin_finEmbed, finComponent_localEmbed_self]

theorem finComponent_lv_of_ne (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (v.adicCompletion F))
    {ℓ : HeightOneSpectrum (𝓞 F)} (hℓ : ℓ ≠ v) :
    finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F (lv v k)) = 1 := by
  rw [lv, MonoidHom.comp_apply, glFin_finEmbed, finComponent_localEmbed_of_ne (𝓞 F) F v k hℓ]

theorem lv_mem_fin (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (v.adicCompletion F)) :
    lv v k ∈ finiteAdelicGL2Subgroup F :=
  (mem_finiteAdelicGL2Subgroup_iff F _).mpr (glArch_lv v k)

theorem lv_mem_U_iff {N : Ideal (𝓞 F)} (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (v.adicCompletion F)) :
    lv v k ∈ U N ↔ k ∈ localLevelOne (𝓞 F) F v N := by
  rw [mem_U_iff]
  constructor
  · intro h
    have := h.2 v
    rwa [finComponent_lv_self] at this
  · intro hk
    refine ⟨glArch_lv v k, fun ℓ => ?_⟩
    by_cases hℓ : ℓ = v
    · subst hℓ; rwa [finComponent_lv_self]
    · rw [finComponent_lv_of_ne v k hℓ]; exact one_mem _

def loc (v : HeightOneSpectrum (𝓞 F)) : AdelicGL2 (𝓞 F) F →* AdelicGL2 (𝓞 F) F :=
  (lv v).comp ((finComponent (𝓞 F) F v).comp (glFin (𝓞 F) F))

theorem loc_apply (v : HeightOneSpectrum (𝓞 F)) (x : AdelicGL2 (𝓞 F) F) :
    loc v x = lv v (finComponent (𝓞 F) F v (glFin (𝓞 F) F x)) := rfl

def IsLocalAt (v : HeightOneSpectrum (𝓞 F)) (x : AdelicGL2 (𝓞 F) F) : Prop :=
  glArch (𝓞 F) F x = 1 ∧ ∀ ℓ, ℓ ≠ v → finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F x) = 1

theorem isLocalAt_lv (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (v.adicCompletion F)) :
    IsLocalAt v (lv v k) :=
  ⟨glArch_lv v k, fun _ hℓ => finComponent_lv_of_ne v k hℓ⟩

theorem isLocalAt_loc (v : HeightOneSpectrum (𝓞 F)) (x : AdelicGL2 (𝓞 F) F) : IsLocalAt v (loc v x) :=
  isLocalAt_lv v _

theorem IsLocalAt.eq_lv {v : HeightOneSpectrum (𝓞 F)} {x : AdelicGL2 (𝓞 F) F} (hx : IsLocalAt v x) :
    x = lv v (finComponent (𝓞 F) F v (glFin (𝓞 F) F x)) := by
  refine eq_of_glArch_eq_of_forall_finComponent_eq ?_ fun ℓ => ?_
  · rw [hx.1, glArch_lv]
  · by_cases hℓ : ℓ = v
    · subst hℓ; rw [finComponent_lv_self]
    · rw [hx.2 ℓ hℓ, finComponent_lv_of_ne v _ hℓ]

theorem IsLocalAt.mul {v : HeightOneSpectrum (𝓞 F)} {x y : AdelicGL2 (𝓞 F) F} (hx : IsLocalAt v x)
    (hy : IsLocalAt v y) : IsLocalAt v (x * y) :=
  ⟨by rw [map_mul, hx.1, hy.1, mul_one], fun ℓ hℓ => by rw [map_mul, map_mul, hx.2 ℓ hℓ, hy.2 ℓ hℓ, mul_one]⟩

theorem IsLocalAt.inv {v : HeightOneSpectrum (𝓞 F)} {x : AdelicGL2 (𝓞 F) F} (hx : IsLocalAt v x) :
    IsLocalAt v x⁻¹ :=
  ⟨by rw [map_inv, hx.1, inv_one], fun ℓ hℓ => by rw [map_inv, map_inv, hx.2 ℓ hℓ, inv_one]⟩

theorem IsLocalAt.mem_U_iff {N : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)} {x : AdelicGL2 (𝓞 F) F}
    (hx : IsLocalAt v x) :
    x ∈ U N ↔ finComponent (𝓞 F) F v (glFin (𝓞 F) F x) ∈ localLevelOne (𝓞 F) F v N := by
  conv_lhs => rw [hx.eq_lv]
  exact lv_mem_U_iff v _

theorem heckeGen_eq_lv (v : HeightOneSpectrum (𝓞 F)) :
    heckeGen (𝓞 F) F v = lv v (diagOne (uniformizerUnit F v)) := by
  refine eq_of_glArch_eq_of_forall_finComponent_eq ?_ fun ℓ => ?_
  · rw [glArch_lv]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [glArch_apply, Units.val_one]
    exact heckeGenAt_fst _ i j
  · by_cases hℓ : ℓ = v
    · subst hℓ
      rw [finComponent_lv_self]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [finComponent_apply, glFin_apply, diagOne_coe_apply]
      exact heckeGenAt_snd_apply_self _ i j
    · rw [finComponent_lv_of_ne v _ hℓ]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [finComponent_apply, glFin_apply, Units.val_one]
      exact heckeGenAt_snd_apply_of_ne _ hℓ i j

theorem isLocalAt_heckeGen (v : HeightOneSpectrum (𝓞 F)) : IsLocalAt v (heckeGen (𝓞 F) F v) := by
  rw [heckeGen_eq_lv]; exact isLocalAt_lv v _

theorem heckeGen_mem_fin (v : HeightOneSpectrum (𝓞 F)) : heckeGen (𝓞 F) F v ∈ finiteAdelicGL2Subgroup F := by
  rw [heckeGen_eq_lv]; exact lv_mem_fin v _

section Cosets

variable {G : Type*} [Group G] {W : Subgroup G} {g : G} {ι : Type*} {reps : ι → G}

theorem isHeckeCosetSystem_mul (hsys : IsHeckeCosetSystem W g reps) (u : ι → G) (hu : ∀ i, u i ∈ W) :
    IsHeckeCosetSystem W g (fun i => reps i * u i) := by
  have hmk : ∀ i, (QuotientGroup.mk (reps i * u i) : G ⧸ W) = QuotientGroup.mk (reps i) := by
    intro i
    rw [QuotientGroup.eq]
    simpa using W.inv_mem (hu i)
  refine ⟨fun i => ?_, fun x hx => ?_, fun i j hij => ?_⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    exact HeckePair.mem_doubleCoset_iff.mpr ⟨a, ha, b * u i, W.mul_mem hb (hu i), by rw [← hab]; group⟩
  · obtain ⟨i, hi⟩ := hsys.covers x hx
    exact ⟨i, by rw [hmk i]; exact hi⟩
  · have h : (QuotientGroup.mk (reps i) : G ⧸ W) = QuotientGroup.mk (reps j) := by
      have := hij
      simp only [hmk] at this
      exact this
    exact hsys.mk_injective h

end Cosets

variable {N N' : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}

theorem finComponent_mem_of_mem_U {x : AdelicGL2 (𝓞 F) F} (hx : x ∈ U N) (ℓ : HeightOneSpectrum (𝓞 F)) :
    finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F x) ∈ localLevelOne (𝓞 F) F ℓ N :=
  ((mem_U_iff x).mp hx).2 ℓ

theorem inv_mul_loc_mem_U {x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ HeckePair.doubleCoset (U N) (heckeGen (𝓞 F) F v)) : x⁻¹ * loc v x ∈ U N := by
  obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  rw [mem_U_iff]
  have haf := ((mem_U_iff a).mp ha).1
  have hbf := ((mem_U_iff b).mp hb).1
  have hgf := (mem_finiteAdelicGL2Subgroup_iff F _).mp (heckeGen_mem_fin (F := F) v)
  refine ⟨?_, fun ℓ => ?_⟩
  · simp only [map_mul, map_inv, haf, hbf, hgf, loc_apply, glArch_lv, mul_one, inv_one]
  · by_cases hℓ : ℓ = v
    · subst hℓ
      have e : finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F ((a * heckeGen (𝓞 F) F ℓ * b)⁻¹
          * loc ℓ (a * heckeGen (𝓞 F) F ℓ * b))) = 1 := by
        rw [map_mul, map_mul, loc_apply, finComponent_lv_self, ← map_mul, ← map_mul, inv_mul_cancel,
          map_one, map_one]
      rw [e]; exact one_mem _
    · have e : finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F ((a * heckeGen (𝓞 F) F v * b)⁻¹
          * loc v (a * heckeGen (𝓞 F) F v * b)))
          = (finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F a) * finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F b))⁻¹ := by
        rw [map_mul, map_mul, loc_apply, finComponent_lv_of_ne v _ hℓ, mul_one, map_inv, map_inv,
          map_mul, map_mul, map_mul, map_mul, (isLocalAt_heckeGen v).2 ℓ hℓ, mul_one]
      rw [e]
      exact Subgroup.inv_mem _
        (Subgroup.mul_mem _ (finComponent_mem_of_mem_U ha ℓ) (finComponent_mem_of_mem_U hb ℓ))

theorem isHeckeCosetSystem_loc {n : ℕ} {reps : Fin n → AdelicGL2 (𝓞 F) F}
    (hsys : IsHeckeCosetSystem (U N) (heckeGen (𝓞 F) F v) reps) :
    IsHeckeCosetSystem (U N) (heckeGen (𝓞 F) F v) (fun i => loc v (reps i)) := by
  have h := isHeckeCosetSystem_mul hsys (fun i => (reps i)⁻¹ * loc v (reps i))
    (fun i => inv_mul_loc_mem_U (hsys.mem_doubleCoset i))
  convert h using 2 with i
  rw [mul_inv_cancel_left]

theorem exists_local_decomp (hv : idealBound (𝓞 F) N v = 1) {x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ HeckePair.doubleCoset (U N) (heckeGen (𝓞 F) F v)) :
    ∃ a ∈ Kv v, ∃ b ∈ Kv v,
      finComponent (𝓞 F) F v (glFin (𝓞 F) F x) = a * diagOne (uniformizerUnit F v) * b := by
  obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  refine ⟨finComponent (𝓞 F) F v (glFin (𝓞 F) F a), ?_, finComponent (𝓞 F) F v (glFin (𝓞 F) F b), ?_, ?_⟩
  · rw [← localLevelOne_eq_Kv hv]; exact finComponent_mem_of_mem_U ha v
  · rw [← localLevelOne_eq_Kv hv]; exact finComponent_mem_of_mem_U hb v
  · simp only [map_mul]
    rw [heckeGen_eq_lv, finComponent_lv_self]

theorem mem_doubleCoset_of_isLocalAt {M : Ideal (𝓞 F)} (hv : idealBound (𝓞 F) M v = 1)
    {x : AdelicGL2 (𝓞 F) F} (hx : IsLocalAt v x) {a b : GL (Fin 2) (v.adicCompletion F)}
    (ha : a ∈ Kv v) (hb : b ∈ Kv v)
    (hxv : finComponent (𝓞 F) F v (glFin (𝓞 F) F x) = a * diagOne (uniformizerUnit F v) * b) :
    x ∈ HeckePair.doubleCoset (U M) (heckeGen (𝓞 F) F v) := by
  refine HeckePair.mem_doubleCoset_iff.mpr ⟨lv v a, ?_, lv v b, ?_, ?_⟩
  · rw [lv_mem_U_iff, localLevelOne_eq_Kv hv]; exact ha
  · rw [lv_mem_U_iff, localLevelOne_eq_Kv hv]; exact hb
  · rw [hx.eq_lv, hxv, heckeGen_eq_lv, ← map_mul, ← map_mul]

theorem isHeckeCosetSystem_conj (hv : idealBound (𝓞 F) N v = 1) (hv' : idealBound (𝓞 F) N' v = 1)
    {n : ℕ} {α : Fin n → AdelicGL2 (𝓞 F) F}
    (hsys : IsHeckeCosetSystem (U N) (heckeGen (𝓞 F) F v) α) (hloc : ∀ i, IsLocalAt v (α i))
    {h : AdelicGL2 (𝓞 F) F} (hh : h ∈ finiteAdelicGL2Subgroup F)
    (hhv : finComponent (𝓞 F) F v (glFin (𝓞 F) F h) ∈ Kv v) :
    IsHeckeCosetSystem (U N') (heckeGen (𝓞 F) F v) (fun i => h⁻¹ * α i * h) := by
  have hharch : glArch (𝓞 F) F h = 1 := (mem_finiteAdelicGL2Subgroup_iff F h).mp hh
  set hv0 := finComponent (𝓞 F) F v (glFin (𝓞 F) F h) with hhv0

  have hconj_loc : ∀ {x : AdelicGL2 (𝓞 F) F}, IsLocalAt v x → IsLocalAt v (h⁻¹ * x * h) := by
    intro x hx
    refine ⟨?_, fun ℓ hℓ => ?_⟩
    · simp only [map_mul, map_inv, hx.1, hharch, mul_one, inv_one]
    · simp only [map_mul, map_inv, hx.2 ℓ hℓ, mul_one, inv_mul_cancel]
  have hconj_v : ∀ x : AdelicGL2 (𝓞 F) F, finComponent (𝓞 F) F v (glFin (𝓞 F) F (h⁻¹ * x * h))
      = hv0⁻¹ * finComponent (𝓞 F) F v (glFin (𝓞 F) F x) * hv0 := by
    intro x
    simp only [map_mul, map_inv, ← hhv0]
  refine ⟨fun i => ?_, fun x hx => ?_, fun i j hij => ?_⟩
  ·
    obtain ⟨a, ha, b, hb, hab⟩ := exists_local_decomp hv (hsys.mem_doubleCoset i)
    refine mem_doubleCoset_of_isLocalAt hv' (hconj_loc (hloc i)) ((Kv v).mul_mem ((Kv v).inv_mem hhv) ha)
      ((Kv v).mul_mem hb hhv) ?_
    rw [hconj_v, hab]; group
  ·
    obtain ⟨a, ha, b, hb, hab⟩ := exists_local_decomp hv' hx
    obtain ⟨a', ha', b', hb', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx

    set z : AdelicGL2 (𝓞 F) F := lv v (hv0 * (a * diagOne (uniformizerUnit F v) * b) * hv0⁻¹) with hz
    have hzD : z ∈ HeckePair.doubleCoset (U N) (heckeGen (𝓞 F) F v) := by
      refine mem_doubleCoset_of_isLocalAt hv (isLocalAt_lv v _) ((Kv v).mul_mem hhv ha)
        ((Kv v).mul_mem hb ((Kv v).inv_mem hhv)) ?_
      rw [hz, finComponent_lv_self]; group
    obtain ⟨i, hi⟩ := hsys.covers z hzD
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢

    rw [mem_U_iff]
    have ha'f := ((mem_U_iff a').mp ha').1
    have hb'f := ((mem_U_iff b').mp hb').1
    have hgf := (mem_finiteAdelicGL2Subgroup_iff F _).mp (heckeGen_mem_fin (F := F) v)
    refine ⟨?_, fun ℓ => ?_⟩
    · simp only [map_mul, map_inv, (hloc i).1, hharch, ha'f, hb'f, hgf, mul_one, inv_one]
    · by_cases hℓ : ℓ = v
      · subst hℓ
        rw [localLevelOne_eq_Kv hv']
        have hiv : finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F (z⁻¹ * α i)) ∈ Kv ℓ := by
          rw [← localLevelOne_eq_Kv hv]; exact finComponent_mem_of_mem_U hi ℓ
        rw [map_mul, map_mul, map_inv, map_inv, hz, finComponent_lv_self] at hiv
        have e : finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F ((a' * heckeGen (𝓞 F) F ℓ * b')⁻¹
            * (h⁻¹ * α i * h))) = (a * diagOne (uniformizerUnit F ℓ) * b)⁻¹
              * (hv0⁻¹ * finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F (α i)) * hv0) := by
          rw [map_mul, map_mul, hconj_v, map_inv, map_inv, hab]
        have key : (a * diagOne (uniformizerUnit F ℓ) * b)⁻¹
              * (hv0⁻¹ * finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F (α i)) * hv0)
            = hv0⁻¹ * ((hv0 * (a * diagOne (uniformizerUnit F ℓ) * b) * hv0⁻¹)⁻¹
              * finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F (α i))) * hv0 := by group
        rw [e, key]
        exact (Kv ℓ).mul_mem ((Kv ℓ).mul_mem ((Kv ℓ).inv_mem hhv) hiv) hhv
      · have e : finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F ((a' * heckeGen (𝓞 F) F v * b')⁻¹
            * (h⁻¹ * α i * h)))
            = (finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F a') * finComponent (𝓞 F) F ℓ (glFin (𝓞 F) F b'))⁻¹ := by
          simp only [map_mul, map_inv, (hloc i).2 ℓ hℓ, (isLocalAt_heckeGen v).2 ℓ hℓ, mul_one,
            inv_mul_cancel]
        rw [e]
        exact Subgroup.inv_mem _
          (Subgroup.mul_mem _ (finComponent_mem_of_mem_U ha' ℓ) (finComponent_mem_of_mem_U hb' ℓ))
  ·
    apply hsys.mk_injective
    have hij' : (QuotientGroup.mk (h⁻¹ * α i * h) : AdelicGL2 (𝓞 F) F ⧸ U N')
        = QuotientGroup.mk (h⁻¹ * α j * h) := hij
    rw [QuotientGroup.eq] at hij' ⊢
    have hloc_ij : IsLocalAt v ((α i)⁻¹ * α j) := (hloc i).inv.mul (hloc j)
    rw [hloc_ij.mem_U_iff, localLevelOne_eq_Kv hv]
    have hmem := finComponent_mem_of_mem_U hij' v
    rw [localLevelOne_eq_Kv hv'] at hmem
    have hrw : (h⁻¹ * α i * h)⁻¹ * (h⁻¹ * α j * h) = h⁻¹ * ((α i)⁻¹ * α j) * h := by group
    rw [hrw, hconj_v] at hmem
    have key : finComponent (𝓞 F) F v (glFin (𝓞 F) F ((α i)⁻¹ * α j))
        = hv0 * (hv0⁻¹ * finComponent (𝓞 F) F v (glFin (𝓞 F) F ((α i)⁻¹ * α j)) * hv0) * hv0⁻¹ := by
      group
    rw [key]
    exact (Kv v).mul_mem ((Kv v).mul_mem hhv hmem) ((Kv v).inv_mem hhv)

theorem finite_setOf_not_mem_Kv (h : AdelicGL2 (𝓞 F) F) :
    {v : HeightOneSpectrum (𝓞 F) | finComponent (𝓞 F) F v (glFin (𝓞 F) F h) ∉ Kv v}.Finite := by

  have hent : ∀ (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) (i j : Fin 2),
      ∀ᶠ v in Filter.cofinite, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v
        ∈ v.adicCompletionIntegers F :=
    fun g i j => ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j).2
  have hall : ∀ᶠ v in Filter.cofinite,
      (∀ i j, ((glFin (𝓞 F) F h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F) ∧
      (∀ i j, (((glFin (𝓞 F) F h)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F) := by
    refine Filter.Eventually.and ?_ ?_
    · exact Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hent _ i j
    · exact Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hent _ i j
  refine (Filter.eventually_cofinite.mp hall).subset fun v hv => ?_
  intro hv'
  apply hv
  rw [mem_Kv_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [finComponent_apply]; exact hv'.1 i j
  · rw [← map_inv, finComponent_apply]; exact hv'.2 i j

theorem main (N N' : Ideal (𝓞 F)) (hN : N ≠ ⊥) (hN' : N' ≠ ⊥)
    (a : HeightOneSpectrum (𝓞 F) → ℂ) (φ' : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ'U : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U N', φ' (g * k) = φ' g)
    (S' : Finset (HeightOneSpectrum (𝓞 F)))
    (hφ' : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' →
      IsHeckeCosetEigenfunctionAt F (U N') (heckeGen (𝓞 F) F v) v φ' (a v))
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (hsys : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S₀ →
      ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
        IsHeckeCosetSystem (U N) (heckeGen (𝓞 F) F v) reps)
    (t : Finset (AdelicGL2 (𝓞 F) F)) (l : AdelicGL2 (𝓞 F) F → ℂ)
    (ht : ∀ h ∈ t, h ∈ finiteAdelicGL2Subgroup F)
    (hU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U N,
      ∑ h ∈ t, l h * φ' (g * k * h) = ∑ h ∈ t, l h * φ' (g * h)) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      IsHeckeCosetEigenfunctionAt F (U N) (heckeGen (𝓞 F) F v) v (fun g => ∑ h ∈ t, l h * φ' (g * h)) (a v) := by
  classical

  have hbadN := finite_setOf_idealBound_ne_one (R := 𝓞 F) hN
  have hbadN' := finite_setOf_idealBound_ne_one (R := 𝓞 F) hN'
  have hbadt : {v : HeightOneSpectrum (𝓞 F) | ∃ h ∈ t, finComponent (𝓞 F) F v (glFin (𝓞 F) F h) ∉ Kv v}.Finite := by
    have : {v : HeightOneSpectrum (𝓞 F) | ∃ h ∈ t, finComponent (𝓞 F) F v (glFin (𝓞 F) F h) ∉ Kv v}
        = ⋃ h ∈ t, {v | finComponent (𝓞 F) F v (glFin (𝓞 F) F h) ∉ Kv v} := by
      ext v; simp
    rw [this]
    exact Set.Finite.biUnion t.finite_toSet fun h _ => finite_setOf_not_mem_Kv h
  refine ⟨S' ∪ S₀ ∪ hbadN.toFinset ∪ hbadN'.toFinset ∪ hbadt.toFinset, fun v hv => ?_⟩
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not,
    not_exists, not_and] at hv
  obtain ⟨⟨⟨⟨hvS', hvS₀⟩, hvN⟩, hvN'⟩, hvt⟩ := hv
  obtain ⟨reps, hreps⟩ := hsys v hvS₀
  obtain ⟨reps', hreps', heig⟩ := hφ' v hvS'
  refine ⟨reps, hreps, fun g => ?_⟩

  set Ψ : AdelicGL2 (𝓞 F) F → ℂ := fun g => ∑ h ∈ t, l h * φ' (g * h) with hΨdef
  have hΨinv : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U N, Ψ (g * k) = Ψ g := fun g k hk => hU g k hk
  have hloc_sys := isHeckeCosetSystem_loc hreps
  show ∑ i, Ψ (g * reps i) = a v * Ψ g
  rw [heckeCosetSum_eq_of_isHeckeCosetSystem (φ := Ψ) hloc_sys hreps hΨinv g]
  simp only [hΨdef, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h hh => ?_

  have hht := ht h hh
  have hhv : finComponent (𝓞 F) F v (glFin (𝓞 F) F h) ∈ Kv v := hvt h hh
  have hconj := isHeckeCosetSystem_conj hvN hvN' hloc_sys (fun i => isLocalAt_loc v (reps i)) hht hhv
  have hφ'inv : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U N', φ' (g * k) = φ' g := hφ'U
  have h1 : ∑ i, l h * φ' (g * loc v (reps i) * h) = l h * ∑ i, φ' (g * h * (h⁻¹ * loc v (reps i) * h)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2; group
  rw [h1, heckeCosetSum_eq_of_isHeckeCosetSystem (φ := φ') hreps' hconj hφ'inv (g * h)]
  have h2 := heig (g * h)
  unfold heckeCosetSum at h2
  rw [h2]
  ring

end HeckeLocalitySol

end

open HeckeLocalitySol in
theorem solution
    (F : Type) [Field F] [NumberField F] (N N' : Ideal (𝓞 F)) (hN : N ≠ ⊥) (hN' : N' ≠ ⊥)
    (a : HeightOneSpectrum (𝓞 F) → ℂ) (φ' : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ'U : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N' ⊓ finiteAdelicGL2Subgroup F,
      φ' (g * k) = φ' g)
    (S' : Finset (HeightOneSpectrum (𝓞 F)))
    (hφ' : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' →
      IsHeckeCosetEigenfunctionAt F (levelOne (𝓞 F) F N' ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) v φ' (a v))
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (hsys : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S₀ →
      ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
        IsHeckeCosetSystem (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v) reps)
    (t : Finset (AdelicGL2 (𝓞 F) F)) (l : AdelicGL2 (𝓞 F) F → ℂ)
    (ht : ∀ h ∈ t, h ∈ finiteAdelicGL2Subgroup F)
    (hU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      ∑ h ∈ t, l h * φ' (g * k * h) = ∑ h ∈ t, l h * φ' (g * h)) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      IsHeckeCosetEigenfunctionAt F (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) v (fun g => ∑ h ∈ t, l h * φ' (g * h)) (a v) :=
  HeckeLocalitySol.main N N' hN hN' a φ' hφ'U S' hφ' S₀ hsys t l ht hU

end S_AutomorphicForm_exists_forall_isHeckeCosetEigenfunctionAt_finTranslateSum_of_levelOne_invariant
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_isHeckeCosetEigenfunctionAt_finTranslateSum_of_levelOne_invariant (solution)
