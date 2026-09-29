-- Prove2me | solution 1 for AutomorphicForm.exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/fbef60af-0791-5e8d-ba93-fc6bda236345

import Mathlib
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot

set_option autoImplicit false

open Module MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped ComplexConjugate

noncomputable section

namespace P2mK3AdmDim

section Tensor

variable {X Y : Type*}

def tensorSpace (U : Submodule ℂ (X → ℂ)) (V : Submodule ℂ (Y → ℂ)) : Submodule ℂ (X × Y → ℂ) where
  carrier := {F | (∀ y, (fun x => F (x, y)) ∈ U) ∧ ∀ x, (fun y => F (x, y)) ∈ V}
  zero_mem' := ⟨fun _ => U.zero_mem, fun _ => V.zero_mem⟩
  add_mem' := fun ha hb => ⟨fun y => U.add_mem (ha.1 y) (hb.1 y), fun x => V.add_mem (ha.2 x) (hb.2 x)⟩
  smul_mem' := fun c _ ha => ⟨fun y => U.smul_mem c (ha.1 y), fun x => V.smul_mem c (ha.2 x)⟩

def evalForm (U : Submodule ℂ (X → ℂ)) (x : X) : Module.Dual ℂ U :=
  (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ U.subtype

theorem mem_span_evalForm (U : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ U] (θ : Module.Dual ℂ U) :
    θ ∈ Submodule.span ℂ (Set.range (evalForm U)) := by
  refine FiniteDimensional.mem_span_of_iInf_ker_le_ker ?_
  have h : ⨅ x, LinearMap.ker (evalForm U x) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_iInf] at hu
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext x
    exact hu x
  rw [h]
  exact bot_le

theorem finite_and_finrank_tensorSpace_le (U : Submodule ℂ (X → ℂ)) (V : Submodule ℂ (Y → ℂ))
    [FiniteDimensional ℂ U] [FiniteDimensional ℂ V] :
    Module.Finite ℂ (tensorSpace U V) ∧ finrank ℂ (tensorSpace U V) ≤ finrank ℂ U * finrank ℂ V := by
  set a := finrank ℂ U with ha
  let bU : Basis (Fin a) ℂ U := Module.finBasis ℂ U
  have hspan : ∀ (c : Y → U), (∀ x, (fun y => ((c y : U) : X → ℂ) x) ∈ V) →
      ∀ θ ∈ Submodule.span ℂ (Set.range (evalForm U)), (fun y => θ (c y)) ∈ V := by
    intro c hc θ hθ
    induction hθ using Submodule.span_induction with
    | mem θ hθ =>
        obtain ⟨x, rfl⟩ := hθ
        exact hc x
    | zero => exact V.zero_mem
    | add θ₁ θ₂ _ _ h₁ h₂ => exact V.add_mem h₁ h₂
    | smul r θ _ h => exact V.smul_mem r h
  let col : tensorSpace U V → Y → U := fun F y => ⟨fun x => (F : X × Y → ℂ) (x, y), F.2.1 y⟩
  have hcol : ∀ (F : tensorSpace U V) (x : X), (fun y => ((col F y : U) : X → ℂ) x) ∈ V :=
    fun F x => F.2.2 x
  let β : tensorSpace U V →ₗ[ℂ] (Fin a → V) :=
    { toFun := fun F i => ⟨fun y => bU.coord i (col F y), hspan (col F) (hcol F) _ (mem_span_evalForm U _)⟩
      map_add' := fun F G => by
        funext i
        apply Subtype.ext
        funext y
        change bU.coord i (col (F + G) y) = bU.coord i (col F y) + bU.coord i (col G y)
        rw [← map_add]
        rfl
      map_smul' := fun r F => by
        funext i
        apply Subtype.ext
        funext y
        change bU.coord i (col (r • F) y) = r • bU.coord i (col F y)
        rw [← map_smul]
        rfl }
  have hβ : Function.Injective β := by
    intro F G hFG
    rw [← sub_eq_zero] at hFG ⊢
    rw [← map_sub] at hFG
    set D := F - G
    apply Subtype.ext
    funext p
    obtain ⟨x, y⟩ := p
    have hy : col D y = 0 := by
      rw [← bU.forall_coord_eq_zero_iff]
      intro i
      exact congrArg (fun T : Fin a → V => ((T i : V) : Y → ℂ) y) hFG
    exact congrArg (fun u : U => (u : X → ℂ) x) hy
  haveI : Module.Finite ℂ (tensorSpace U V) := Module.Finite.of_injective β hβ
  refine ⟨inferInstance, ?_⟩
  calc finrank ℂ (tensorSpace U V) ≤ finrank ℂ (Fin a → V) := LinearMap.finrank_le_finrank_of_injective hβ
    _ = a * finrank ℂ V := by
        rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end Tensor

section Coeff

variable {H G : Type*} [Group H] [Group G]

def coeffMap {n : ℕ} (ρ : Representation ℂ H (Fin n → ℂ)) :
    Module.Dual ℂ (Module.End ℂ (Fin n → ℂ)) →ₗ[ℂ] (H → ℂ) where
  toFun θ k := θ (ρ k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coeffMapFamily {m : ℕ} {n : Fin m → ℕ} (ρ : ∀ i, Representation ℂ H (Fin (n i) → ℂ)) :
    (∀ i, Module.Dual ℂ (Module.End ℂ (Fin (n i) → ℂ))) →ₗ[ℂ] (H → ℂ) :=
  ∑ i, (coeffMap (ρ i)).comp (LinearMap.proj i)

def coeffSpaceFamily {m : ℕ} {n : Fin m → ℕ} (ρ : ∀ i, Representation ℂ H (Fin (n i) → ℂ)) :
    Submodule ℂ (H → ℂ) :=
  LinearMap.range (coeffMapFamily ρ)

scoped instance coeffSpaceFamily.finite {m : ℕ} {n : Fin m → ℕ} (ρ : ∀ i, Representation ℂ H (Fin (n i) → ℂ)) :
    FiniteDimensional ℂ (coeffSpaceFamily ρ) :=
  LinearMap.finiteDimensional_range _

p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.P2mK3AdmDim.coeffSpaceFamily"
theorem coeffMap_mem_coeffSpaceFamily {m : ℕ} {n : Fin m → ℕ} (ρ : ∀ i, Representation ℂ H (Fin (n i) → ℂ))
    (i : Fin m) (θ : Module.Dual ℂ (Module.End ℂ (Fin (n i) → ℂ))) :
    coeffMap (ρ i) θ ∈ coeffSpaceFamily ρ := by
  classical
  refine ⟨Pi.single i θ, ?_⟩
  change (∑ j, (coeffMap (ρ j)).comp (LinearMap.proj j)) (Pi.single i θ) = _
  rw [LinearMap.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

def evalMap (ι : H →* G) (g : G) : (G → ℂ) →ₗ[ℂ] (H → ℂ) where
  toFun f k := f (g * ι k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem map_evalMap_typeSubmodule_le (ι : H →* G) {m : ℕ} {n : Fin m → ℕ}
    (ρ : ∀ i, Representation ℂ H (Fin (n i) → ℂ)) (i : Fin m) (g : G) :
    (typeSubmodule ι (ρ i)).map (evalMap ι g) ≤ coeffSpaceFamily ρ := by
  rw [Submodule.map_le_iff_le_comap]
  refine Submodule.span_le.mpr ?_
  rintro f ⟨T, hT, v, rfl⟩
  let θ : Module.Dual ℂ (Module.End ℂ (Fin (n i) → ℂ)) :=
    { toFun := fun A => T (A v) g
      map_add' := fun A B => by simp
      map_smul' := fun c A => by simp }
  have hmem := coeffMap_mem_coeffSpaceFamily ρ i θ
  refine (Submodule.mem_comap).mpr ?_
  convert hmem using 1
  funext k
  show T v (g * ι k) = T ((ρ i k) v) g
  exact (hT k v g).symm

theorem evalMap_mem_coeffSpaceFamily (ι : H →* G) {m : ℕ} {n : Fin m → ℕ}
    (ρ : ∀ i, Representation ℂ H (Fin (n i) → ℂ)) (g : G) {f : G → ℂ}
    (hf : f ∈ ⨆ i, typeSubmodule ι (ρ i)) :
    evalMap ι g f ∈ coeffSpaceFamily ρ := by
  have h : (⨆ i, typeSubmodule ι (ρ i)).map (evalMap ι g) ≤ coeffSpaceFamily ρ := by
    rw [Submodule.map_iSup]
    exact iSup_le fun i => map_evalMap_typeSubmodule_le ι ρ i g
  exact h ⟨f, hf, rfl⟩

end Coeff
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.P2mK3AdmDim.coeffSpaceFamily"

section Adelic

variable (K : Type) [Field K] [NumberField K]

local notation "𝔾" => AdelicGL2 (𝓞 K) K
local notation "𝕂" => adelicMaximalCompact K

abbrev Hw (w : InfinitePlace K) : Type := ↥(rowIsometrySubgroup₀ w.Completion)

abbrev ιw (w : InfinitePlace K) : Hw K w →* 𝔾 := rowIsometryInclAt₀ K w

abbrev archAt (w : InfinitePlace K) : GL (Fin 2) w.Completion →* 𝔾 := adelicArchGLInclAt K w

theorem glArch_archAt (w : InfinitePlace K) (y : GL (Fin 2) w.Completion) :
    glArch (𝓞 K) K (archAt K w y) = archGLIncl K w y := by
  rw [archAt, adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl]

theorem glFin_archAt (w : InfinitePlace K) (y : GL (Fin 2) w.Completion) : glFin (𝓞 K) K (archAt K w y) = 1 := by
  rw [archAt, adelicArchGLInclAt, MonoidHom.comp_apply, glFin_adelicArchGLIncl]

theorem eq_of_glArch_eq_of_glFin_eq {x y : 𝔾}
    (h₁ : glArch (𝓞 K) K x = glArch (𝓞 K) K y) (h₂ : glFin (𝓞 K) K x = glFin (𝓞 K) K y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg
    (fun m : GL (Fin 2) (InfiniteAdeleRing K) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) h₁
  have h₂' := congrArg
    (fun m : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) =>
      (m : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j) h₂
  exact Prod.ext h₁' h₂'

omit [NumberField K] in
theorem eq_of_forall_archComponent_eq (a b : GL (Fin 2) (InfiniteAdeleRing K))
    (h : ∀ v : InfinitePlace K, archComponent K v a = archComponent K v b) : a = b := by
  apply Units.ext
  refine Matrix.ext fun i j => funext fun v => ?_
  exact congrArg (fun m : GL (Fin 2) v.Completion => (m : Matrix (Fin 2) (Fin 2) v.Completion) i j) (h v)

theorem commute_of_glFin_eq_one_of_glArch_eq_one {a b : 𝔾} (ha : glFin (𝓞 K) K a = 1)
    (hb : glArch (𝓞 K) K b = 1) : Commute a b := by
  change a * b = b * a
  apply eq_of_glArch_eq_of_glFin_eq K
  · rw [map_mul, map_mul, hb, mul_one, one_mul]
  · rw [map_mul, map_mul, ha, mul_one, one_mul]

theorem archAt_mem_adelicBorel (w : InfinitePlace K) {b : GL (Fin 2) w.Completion}
    (hb : (b : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0) : archAt K w b ∈ adelicBorel (𝓞 K) K := by
  show ((archAt K w b : 𝔾) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0
  refine Prod.ext (funext fun v => ?_) ?_
  · change (archComponent K v (glArch (𝓞 K) K (archAt K w b)) : Matrix (Fin 2) (Fin 2) v.Completion) 1 0 = _
    rw [glArch_archAt]
    by_cases hv : v = w
    · subst hv
      rw [archComponent_archGLIncl_self, hb]
      rfl
    · rw [archComponent_archGLIncl_of_ne K hv, Units.val_one, Matrix.one_apply_ne (by decide)]
      rfl
  · change (glFin (𝓞 K) K (archAt K w b) : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) 1 0 = _
    rw [glFin_archAt, Units.val_one, Matrix.one_apply_ne (by decide)]
    rfl

def AOf : (l : List (InfinitePlace K)) → (∀ w : InfinitePlace K, GL (Fin 2) w.Completion) → 𝔾
  | [] => fun _ => 1
  | w :: l => fun x => AOf l x * archAt K w (x w)

theorem glFin_AOf (l : List (InfinitePlace K)) (x : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion) :
    glFin (𝓞 K) K (AOf K l x) = 1 := by
  induction l with
  | nil => exact map_one _
  | cons w l ih =>
      change glFin (𝓞 K) K (AOf K l x * archAt K w (x w)) = 1
      rw [map_mul, ih, glFin_archAt, mul_one]

open scoped Classical in
theorem archComponent_glArch_AOf (l : List (InfinitePlace K)) (hl : l.Nodup)
    (x : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion) (v : InfinitePlace K) :
    archComponent K v (glArch (𝓞 K) K (AOf K l x)) = if v ∈ l then x v else 1 := by
  induction l with
  | nil => simp [AOf]
  | cons w l ih =>
      have hwl : w ∉ l := (List.nodup_cons.mp hl).1
      change archComponent K v (glArch (𝓞 K) K (AOf K l x * archAt K w (x w))) = _
      rw [map_mul, map_mul, ih (List.nodup_cons.mp hl).2, glArch_archAt]
      by_cases hv : v = w
      · subst hv
        rw [archComponent_archGLIncl_self, if_neg hwl, one_mul, if_pos List.mem_cons_self]
      · rw [archComponent_archGLIncl_of_ne K hv, mul_one]
        by_cases hvl : v ∈ l
        · rw [if_pos hvl, if_pos (List.mem_cons_of_mem w hvl)]
        · rw [if_neg hvl, if_neg (by simp [hv, hvl])]

theorem commute_archAt_AOf {w : InfinitePlace K} (l : List (InfinitePlace K)) (hw : w ∉ l)
    (a : GL (Fin 2) w.Completion) (y : ∀ v : InfinitePlace K, GL (Fin 2) v.Completion) :
    Commute (archAt K w a) (AOf K l y) := by
  induction l with
  | nil => exact Commute.one_right _
  | cons v l ih =>
      have hvw : w ≠ v := fun h => hw (h ▸ List.mem_cons_self)
      have hwl : w ∉ l := fun h => hw (List.mem_cons_of_mem v h)
      change Commute (archAt K w a) (AOf K l y * archAt K v (y v))
      exact (ih hwl).mul_right (commute_adelicArchGLInclAt_of_ne K hvw a (y v))

theorem AOf_mul (l : List (InfinitePlace K)) (hl : l.Nodup)
    (x y : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion) :
    AOf K l (fun w => x w * y w) = AOf K l x * AOf K l y := by
  induction l with
  | nil => exact (one_mul _).symm
  | cons w l ih =>
      have hwl : w ∉ l := (List.nodup_cons.mp hl).1
      change AOf K l (fun w => x w * y w) * archAt K w (x w * y w) =
        AOf K l x * archAt K w (x w) * (AOf K l y * archAt K w (y w))
      rw [ih (List.nodup_cons.mp hl).2, map_mul]
      have hc := (commute_archAt_AOf K l hwl (x w) y).eq
      calc AOf K l x * AOf K l y * (archAt K w (x w) * archAt K w (y w))
          = AOf K l x * (AOf K l y * archAt K w (x w)) * archAt K w (y w) := by simp only [mul_assoc]
        _ = AOf K l x * (archAt K w (x w) * AOf K l y) * archAt K w (y w) := by rw [hc]
        _ = AOf K l x * archAt K w (x w) * (AOf K l y * archAt K w (y w)) := by simp only [mul_assoc]

theorem AOf_mem_adelicBorel (l : List (InfinitePlace K)) (x : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion)
    (hx : ∀ w, (x w : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0) : AOf K l x ∈ adelicBorel (𝓞 K) K := by
  induction l with
  | nil => exact Subgroup.one_mem _
  | cons w l ih => exact Subgroup.mul_mem _ ih (archAt_mem_adelicBorel K w (hx w))

def κOf : (l : List (InfinitePlace K)) → (∀ w : InfinitePlace K, Hw K w) → 𝔾
  | [] => fun _ => 1
  | w :: l => fun h => κOf l h * ιw K w (h w)

theorem AOf_coe (l : List (InfinitePlace K)) (h : ∀ w : InfinitePlace K, Hw K w) :
    AOf K l (fun w => ((h w : Hw K w) : GL (Fin 2) w.Completion)) = κOf K l h := by
  induction l with
  | nil => rfl
  | cons w l ih =>
      change AOf K l _ * archAt K w _ = κOf K l h * ιw K w (h w)
      rw [ih]
      rfl

def ZTy (R₀ : Type) : List (InfinitePlace K) → Type
  | [] => R₀
  | w :: l => Hw K w × ZTy R₀ l

def πZ {R₀ : Type} (rep : R₀ → 𝔾) : (l : List (InfinitePlace K)) → ZTy K R₀ l → 𝔾
  | [] => fun r => rep r
  | w :: l => fun p => πZ rep l p.2 * ιw K w p.1

def zOf {R₀ : Type} : (l : List (InfinitePlace K)) → (∀ w : InfinitePlace K, Hw K w) → R₀ → ZTy K R₀ l
  | [] => fun _ r => r
  | w :: l => fun h r => (h w, zOf l h r)

theorem πZ_zOf {R₀ : Type} (rep : R₀ → 𝔾) (l : List (InfinitePlace K)) (h : ∀ w : InfinitePlace K, Hw K w) (r : R₀) :
    πZ K rep l (zOf K l h r) = rep r * κOf K l h := by
  induction l with
  | nil => exact (mul_one _).symm
  | cons w l ih =>
      change πZ K rep l (zOf K l h r) * ιw K w (h w) = rep r * (κOf K l h * ιw K w (h w))
      rw [ih, mul_assoc]

def ResZ {R₀ : Type} (rep : R₀ → 𝔾) (l : List (InfinitePlace K)) : (𝔾 → ℂ) →ₗ[ℂ] (ZTy K R₀ l → ℂ) where
  toFun f z := f (πZ K rep l z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Adelic
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.P2mK3AdmDim.coeffSpaceFamily"

section W

variable (K : Type) [Field K] [NumberField K]

local notation "𝔾" => AdelicGL2 (𝓞 K) K
local notation "𝕂" => adelicMaximalCompact K

def levelSubmodule (P : Subgroup 𝔾) : Submodule ℂ (𝔾 → ℂ) where
  carrier := {f | ∀ (g : 𝔾), ∀ u ∈ P, f (g * u) = f g}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := by
    intro a b ha hb g u hu
    show a (g * u) + b (g * u) = a g + b g
    rw [ha g u hu, hb g u hu]
  smul_mem' := by
    intro c a ha g u hu
    show c • a (g * u) = c • a g
    rw [ha g u hu]

def Wsp (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (N : Ideal (𝓞 K)) (tys : ArchTypeFamily K) : Submodule ℂ (𝔾 → ℂ) :=
  inducedSectionSubmodule χ₁ χ₂ ⊓ levelSubmodule K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) ⊓
    archCutSubmodule K tys

variable {K}

theorem mem_Wsp_iff {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {N : Ideal (𝓞 K)} {tys : ArchTypeFamily K} {f : 𝔾 → ℂ} :
    f ∈ Wsp K χ₁ χ₂ N tys ↔
      IsInducedSection (𝓞 K) K χ₁ χ₂ f ∧
        (∀ (g : 𝔾), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, f (g * u) = f g) ∧
          f ∈ archCutSubmodule K tys := by
  simp only [Wsp, Submodule.mem_inf, mem_inducedSectionSubmodule_iff, and_assoc]
  rfl

theorem transl_mem_iSup_typeSubmodule (tys : ArchTypeFamily K) (w v : InfinitePlace K) (h : Hw K w)
    {f : 𝔾 → ℂ} (hf : f ∈ ⨆ i, archTypeSubmoduleAt K v (tys.rep v i)) :
    (fun x => f (x * ιw K w h)) ∈ ⨆ i, archTypeSubmoduleAt K v (tys.rep v i) := by
  have key := comp_mul_mem_iSup_of_forall (fun x : 𝔾 => x * ιw K w h) (fun _ => (1 : ℂ))
    (fun i => archTypeSubmoduleAt K v (tys.rep v i)) (fun i => archTypeSubmoduleAt K v (tys.rep v i)) ?_ hf
  · have heq : (fun x => f (x * ιw K w h) * (fun _ : 𝔾 => (1 : ℂ)) x) = fun x => f (x * ιw K w h) :=
      funext fun x => mul_one _
    rwa [heq] at key
  · intro i fa hfa
    have heq : (fun x => fa (x * ιw K w h) * (fun _ : 𝔾 => (1 : ℂ)) x) = fun x => fa (x * ιw K w h) :=
      funext fun x => mul_one _
    rw [heq]
    by_cases hv : v = w
    · subst hv
      exact comp_mul_mem_typeSubmodule hfa h
    · refine comp_mul_mem_typeSubmodule_of_commute hfa (ιw K w h) fun k => ?_
      exact commute_adelicArchGLInclAt_of_ne K (Ne.symm hv) _ _

theorem transl_mem_Wsp {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {N : Ideal (𝓞 K)} {tys : ArchTypeFamily K}
    (w : InfinitePlace K) (h : Hw K w) {f : 𝔾 → ℂ} (hf : f ∈ Wsp K χ₁ χ₂ N tys) :
    (fun x => f (x * ιw K w h)) ∈ Wsp K χ₁ χ₂ N tys := by
  rw [mem_Wsp_iff] at hf ⊢
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨h1.rightTranslate _, ?_, ?_⟩
  · intro g u hu
    have hu2 : glArch (𝓞 K) K u = 1 := (mem_finiteAdelicGL2Subgroup_iff K u).mp (Subgroup.mem_inf.mp hu).2
    have hc : Commute (ιw K w h) u := commute_of_glFin_eq_one_of_glArch_eq_one K (glFin_archAt K w _) hu2
    change f (g * u * ιw K w h) = f (g * ιw K w h)
    rw [mul_assoc, ← hc.eq, ← mul_assoc, h2 _ u hu]
  · rw [mem_archCutSubmodule_iff] at h3 ⊢
    exact fun v => transl_mem_iSup_typeSubmodule tys w v h (h3 v)

theorem evalMap_mem_of_mem_Wsp {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {N : Ideal (𝓞 K)} {tys : ArchTypeFamily K}
    (w : InfinitePlace K) (g : 𝔾) {f : 𝔾 → ℂ} (hf : f ∈ Wsp K χ₁ χ₂ N tys) :
    evalMap (ιw K w) g f ∈ coeffSpaceFamily (fun i : Fin (tys.card w) => (tys.rep w i).ρ) := by
  rw [mem_Wsp_iff] at hf
  have h3 := (mem_archCutSubmodule_iff K tys f).mp hf.2.2 w
  exact evalMap_mem_coeffSpaceFamily (ιw K w) (fun i : Fin (tys.card w) => (tys.rep w i).ρ) g h3

theorem finite_and_finrank_map_ResZ_le {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {N : Ideal (𝓞 K)}
    {tys : ArchTypeFamily K} {R₀ : Type} [Fintype R₀] (rep : R₀ → 𝔾) (l : List (InfinitePlace K)) :
    Module.Finite ℂ ((Wsp K χ₁ χ₂ N tys).map (ResZ K rep l)) ∧
      finrank ℂ ((Wsp K χ₁ χ₂ N tys).map (ResZ K rep l)) ≤
        Fintype.card R₀ * (l.map fun w => finrank ℂ (coeffSpaceFamily (fun i : Fin (tys.card w) => (tys.rep w i).ρ))).prod := by
  induction l with
  | nil =>
      haveI : Module.Finite ℂ (ZTy K R₀ [] → ℂ) := (inferInstance : Module.Finite ℂ (R₀ → ℂ))
      refine ⟨inferInstance, ?_⟩
      rw [List.map_nil, List.prod_nil, mul_one]
      calc finrank ℂ ((Wsp K χ₁ χ₂ N tys).map (ResZ K rep [])) ≤ finrank ℂ (ZTy K R₀ [] → ℂ) :=
            Submodule.finrank_le _
        _ = Fintype.card R₀ := (Module.finrank_fintype_fun_eq_card ℂ : finrank ℂ (R₀ → ℂ) = _)
  | cons w l ih =>
      obtain ⟨hfin, hle⟩ := ih

      let S : Submodule ℂ (Hw K w × ZTy K R₀ l → ℂ) := (Wsp K χ₁ χ₂ N tys).map (ResZ K rep (w :: l))
      let U : Submodule ℂ (Hw K w → ℂ) := coeffSpaceFamily (fun i : Fin (tys.card w) => (tys.rep w i).ρ)
      let V : Submodule ℂ (ZTy K R₀ l → ℂ) := (Wsp K χ₁ χ₂ N tys).map (ResZ K rep l)
      haveI hUfin : Module.Finite ℂ U := coeffSpaceFamily.finite _
      haveI hVfin : Module.Finite ℂ V := hfin
      have hsub : S ≤ tensorSpace U V := by
        intro F hF
        have hF' : F ∈ (Wsp K χ₁ χ₂ N tys).map (ResZ K rep (w :: l)) := hF
        obtain ⟨f, hf, rfl⟩ := hF'
        refine ⟨fun z => ?_, fun h => ?_⟩
        · change (fun h : Hw K w => f (πZ K rep l z * ιw K w h)) ∈ U
          exact evalMap_mem_of_mem_Wsp w (πZ K rep l z) hf
        · change (fun z : ZTy K R₀ l => f (πZ K rep l z * ιw K w h)) ∈ V
          exact ⟨fun x => f (x * ιw K w h), transl_mem_Wsp w h hf, rfl⟩
      obtain ⟨hTfin, hT⟩ := finite_and_finrank_tensorSpace_le U V
      haveI : Module.Finite ℂ (tensorSpace U V) := hTfin
      have hSfin : Module.Finite ℂ S := Submodule.finiteDimensional_of_le hsub
      have hSrank : finrank ℂ S ≤ Fintype.card R₀ * ((w :: l).map fun w =>
          finrank ℂ (coeffSpaceFamily (fun i : Fin (tys.card w) => (tys.rep w i).ρ))).prod :=
        calc finrank ℂ S
            ≤ finrank ℂ (tensorSpace U V) := Submodule.finrank_mono hsub
          _ ≤ finrank ℂ U * finrank ℂ V := hT
          _ ≤ finrank ℂ U * (Fintype.card R₀ *
                (l.map fun w => finrank ℂ (coeffSpaceFamily (fun i : Fin (tys.card w) => (tys.rep w i).ρ))).prod) :=
              Nat.mul_le_mul_left _ hle
          _ = Fintype.card R₀ * ((w :: l).map fun w =>
                finrank ℂ (coeffSpaceFamily (fun i : Fin (tys.card w) => (tys.rep w i).ρ))).prod := by
              rw [List.map_cons, List.prod_cons, Nat.mul_left_comm]
      exact ⟨hSfin, hSrank⟩

end W
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.P2mK3AdmDim.coeffSpaceFamily"

section Level

variable (K : Type) [Field K] [NumberField K]

local notation "𝔾" => AdelicGL2 (𝓞 K) K
local notation "𝕂" => adelicMaximalCompact K

def Kf : Subgroup 𝔾 := adelicMaximalCompact K ⊓ finiteAdelicGL2Subgroup K

scoped instance compactSpace_Kf : CompactSpace (Kf K) :=
  isCompact_iff_compactSpace.mp
    ((isCompact_adelicMaximalCompact K).inter_right (isClosed_finiteAdelicGL2Subgroup K))

def Qf (N : Ideal (𝓞 K)) : Subgroup (Kf K) := (principalLevel (𝓞 K) K N).subgroupOf (Kf K)

theorem isOpen_principalLevel {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) :
    IsOpen (principalLevel (𝓞 K) K N : Set 𝔾) := by
  have h1 : IsOpen (levelOne (𝓞 K) K N : Set 𝔾) := isOpen_levelOne (𝓞 K) K hN
  have h2 : IsOpen (((levelOne (𝓞 K) K N).map (MulAut.conj (weyl (𝓞 K) K)).toMonoidHom : Subgroup 𝔾) : Set 𝔾) := by
    rw [Subgroup.coe_map]
    have he : ((MulAut.conj (weyl (𝓞 K) K)).toMonoidHom : 𝔾 → 𝔾) =
        (Homeomorph.mulLeft (weyl (𝓞 K) K)).trans (Homeomorph.mulRight (weyl (𝓞 K) K)⁻¹) := by
      funext g
      simp [MulAut.conj_apply]
    rw [he]
    exact (Homeomorph.isOpenMap _) _ h1
  change IsOpen (((levelOne (𝓞 K) K N ⊓ (levelOne (𝓞 K) K N).map (MulAut.conj (weyl (𝓞 K) K)).toMonoidHom :
    Subgroup 𝔾)) : Set 𝔾)
  rw [Subgroup.coe_inf]
  exact h1.inter h2

theorem isOpen_Qf {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) : IsOpen (Qf K N : Set (Kf K)) := by
  rw [Qf, Subgroup.coe_subgroupOf]
  exact (isOpen_principalLevel K hN).preimage continuous_subtype_val

scoped instance finite_quotient_Qf (N : Ideal (𝓞 K)) [Fact (N ≠ ⊥)] : Finite (Kf K ⧸ Qf K N) :=
  Subgroup.quotient_finite_of_isOpen _ (isOpen_Qf K (Fact.out))

def repQ (N : Ideal (𝓞 K)) (c : Kf K ⧸ Qf K N) : 𝔾 := ((Quotient.out c : Kf K) : 𝔾)

theorem repQ_mem_fin (N : Ideal (𝓞 K)) (c : Kf K ⧸ Qf K N) : glArch (𝓞 K) K (repQ K N c) = 1 :=
  (mem_finiteAdelicGL2Subgroup_iff K _).mp (Subgroup.mem_inf.mp (Quotient.out c : Kf K).2).2

theorem exists_repQ_mul (N : Ideal (𝓞 K)) (k : 𝔾) (hk : k ∈ Kf K) :
    ∃ (c : Kf K ⧸ Qf K N) (u : 𝔾), u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ k = repQ K N c * u := by
  set kk : Kf K := ⟨k, hk⟩
  set c : Kf K ⧸ Qf K N := QuotientGroup.mk kk
  have hq : ((Quotient.out c : Kf K))⁻¹ * kk ∈ Qf K N := by
    rw [← QuotientGroup.eq]
    exact (QuotientGroup.out_eq' c)
  refine ⟨c, (((Quotient.out c : Kf K))⁻¹ * kk : Kf K), Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · exact (Subgroup.mem_subgroupOf).mp hq
  · exact (Subgroup.mem_inf.mp ((Quotient.out c : Kf K)⁻¹ * kk).2).2
  · change k = ((Quotient.out c : Kf K) : 𝔾) * (((Quotient.out c : Kf K) : 𝔾)⁻¹ * k)
    rw [mul_inv_cancel_left]

end Level
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.P2mK3AdmDim.coeffSpaceFamily"

section Inject

variable (K : Type) [Field K] [NumberField K]

local notation "𝔾" => AdelicGL2 (𝓞 K) K
local notation "𝕂" => adelicMaximalCompact K

def PL : List (InfinitePlace K) := (Finset.univ : Finset (InfinitePlace K)).toList

theorem PL_nodup : (PL K).Nodup := Finset.nodup_toList _

theorem mem_PL (w : InfinitePlace K) : w ∈ PL K := Finset.mem_toList.mpr (Finset.mem_univ w)

theorem AOf_PL_eq_archPart (k : 𝔾) :
    AOf K (PL K) (fun w => archComponent K w (glArch (𝓞 K) K k)) = adelicArchGLIncl K (glArch (𝓞 K) K k) := by
  apply eq_of_glArch_eq_of_glFin_eq K
  · rw [glArch_adelicArchGLIncl]
    apply eq_of_forall_archComponent_eq K
    intro v
    rw [archComponent_glArch_AOf K (PL K) (PL_nodup K), if_pos (mem_PL K v)]
  · rw [glFin_AOf, glFin_adelicArchGLIncl]

section DiagOne

variable {L : Type*} [NormedField L]

omit [Field K] [NumberField K] in
theorem diagOne_apply_00 (a : Lˣ) : ((diagOne a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = a := by
  rw [diagOne_coe_apply]; simp
omit [Field K] [NumberField K] in
theorem diagOne_apply_01 (a : Lˣ) : ((diagOne a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
  rw [diagOne_coe_apply]; simp
omit [Field K] [NumberField K] in
theorem diagOne_apply_10 (a : Lˣ) : ((diagOne a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  rw [diagOne_coe_apply]; simp
omit [Field K] [NumberField K] in
theorem diagOne_apply_11 (a : Lˣ) : ((diagOne a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by
  rw [diagOne_coe_apply]; simp

omit [Field K] [NumberField K] in
theorem det_diagOne (a : Lˣ) : ((diagOne a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det = a := by
  rw [Matrix.det_fin_two, diagOne_apply_00, diagOne_apply_01, diagOne_apply_10, diagOne_apply_11]
  ring

omit [Field K] [NumberField K] in
theorem det_diagOne_unit (a : Lˣ) : Matrix.GeneralLinearGroup.det (diagOne a : GL (Fin 2) L) = a :=
  Units.ext (det_diagOne a)

omit [Field K] [NumberField K] in

theorem isRowIsometry_diagOne {a : Lˣ} (ha : ‖(a : L)‖ = 1) : IsRowIsometry (diagOne a) := by
  refine ⟨?_, fun x y => ?_⟩
  · rw [det_diagOne, ha]
  · rw [diagOne_apply_00, diagOne_apply_01, diagOne_apply_10, diagOne_apply_11, mul_zero, add_zero,
      mul_zero, zero_add, norm_mul, ha, mul_one, mul_one]

end DiagOne
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.P2mK3AdmDim.coeffSpaceFamily"

omit [NumberField K] in

theorem exists_diagOne_mul (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k) :
    ∃ κ : Hw K w, k = diagOne (Matrix.GeneralLinearGroup.det k) * (κ : GL (Fin 2) w.Completion) := by
  set d := Matrix.GeneralLinearGroup.det k with hd
  have hdn : ‖((d : (w.Completion)ˣ) : w.Completion)‖ = 1 := hk.1
  have hdi : ‖((d⁻¹ : (w.Completion)ˣ) : w.Completion)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hdn, inv_one]
  have hri : IsRowIsometry (diagOne d⁻¹ : GL (Fin 2) w.Completion) := isRowIsometry_diagOne hdi
  refine ⟨⟨(diagOne d)⁻¹ * k, ?_⟩, ?_⟩
  · rw [mem_rowIsometrySubgroup₀_iff]
    refine ⟨?_, ?_⟩
    · have h1 : Matrix.GeneralLinearGroup.det ((diagOne d)⁻¹ * k) = 1 := by
        rw [map_mul, map_inv, ← hd, det_diagOne_unit, inv_mul_cancel]
      exact Units.val_eq_one.mpr h1
    · rw [← map_inv]
      exact hri.mul hk
  · change k = diagOne d * ((diagOne d)⁻¹ * k)
    rw [mul_inv_cancel_left]

theorem exists_decomposition (N : Ideal (𝓞 K)) [Fact (N ≠ ⊥)] (g : 𝔾) :
    ∃ (b : 𝔾) (_ : b ∈ adelicBorel (𝓞 K) K) (h : ∀ w : InfinitePlace K, Hw K w) (c : Kf K ⧸ Qf K N) (u : 𝔾),
      u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧
        g = b * πZ K (repQ K N) (PL K) (zOf K (PL K) h c) * u := by
  obtain ⟨b₀v, kv, hb₀, hkfin, hkri, hgk⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq K g
  have hk : kv ∈ 𝕂 := mem_adelicMaximalCompact_iff.mpr ⟨hkfin, hkri⟩
  set b₀ : ↥(adelicBorel (𝓞 K) K) := ⟨b₀v, hb₀⟩ with hb₀def
  set k : ↥𝕂 := ⟨kv, hk⟩ with hkdef
  replace hgk : g = (b₀ : 𝔾) * (k : 𝔾) := hgk

  have hri : ∀ w, IsRowIsometry (archComponent K w (glArch (𝓞 K) K (k : 𝔾))) :=
    fun w => (mem_adelicMaximalCompact_iff.mp hk).2 w
  choose κ hκ using fun w => exists_diagOne_mul K w _ (hri w)
  set bfam : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion :=
    fun w => diagOne (Matrix.GeneralLinearGroup.det (archComponent K w (glArch (𝓞 K) K (k : 𝔾)))) with hbfam
  set kinf : 𝔾 := adelicArchGLIncl K (glArch (𝓞 K) K (k : 𝔾)) with hkinf
  set binf : 𝔾 := AOf K (PL K) bfam with hbinf
  have hbinfB : binf ∈ adelicBorel (𝓞 K) K := AOf_mem_adelicBorel K (PL K) bfam fun w => diagOne_apply_10 _
  have hkinfeq : kinf = binf * κOf K (PL K) κ := by
    rw [hkinf, ← AOf_PL_eq_archPart, hbinf, ← AOf_coe, ← AOf_mul K (PL K) (PL_nodup K)]
    congr 1
    funext w
    exact hκ w

  set kf : 𝔾 := kinf⁻¹ * (k : 𝔾) with hkf
  have hkinfK : kinf ∈ 𝕂 := by
    rw [mem_adelicMaximalCompact_iff]
    refine ⟨?_, fun w => ?_⟩
    · rw [hkinf, glFin_adelicArchGLIncl]; exact Subgroup.one_mem _
    · rw [hkinf, glArch_adelicArchGLIncl]; exact hri w
  have hkfK : kf ∈ Kf K := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hkinfK) hk, ?_⟩
    rw [mem_finiteAdelicGL2Subgroup_iff, hkf, map_mul, map_inv, hkinf, glArch_adelicArchGLIncl, inv_mul_cancel]
  obtain ⟨c, u, hu, hkfeq⟩ := exists_repQ_mul K N kf hkfK
  have hcomm : Commute (κOf K (PL K) κ) (repQ K N c) := by
    refine commute_of_glFin_eq_one_of_glArch_eq_one K ?_ (repQ_mem_fin K N c)
    rw [← AOf_coe, glFin_AOf]
  refine ⟨b₀ * binf, Subgroup.mul_mem _ b₀.2 hbinfB, κ, c, u, hu, ?_⟩
  rw [πZ_zOf, ← hcomm.eq]
  calc g = (b₀ : 𝔾) * (k : 𝔾) := hgk
    _ = (b₀ : 𝔾) * (kinf * kf) := by rw [hkf, mul_inv_cancel_left]
    _ = (b₀ : 𝔾) * (binf * κOf K (PL K) κ * (repQ K N c * u)) := by rw [← hkinfeq, ← hkfeq]
    _ = (b₀ : 𝔾) * binf * (κOf K (PL K) κ * repQ K N c) * u := by simp only [mul_assoc]

theorem eq_zero_of_ResZ_eq_zero {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {N : Ideal (𝓞 K)} [Fact (N ≠ ⊥)]
    {tys : ArchTypeFamily K} {f : 𝔾 → ℂ} (hf : f ∈ Wsp K χ₁ χ₂ N tys)
    (h0 : ResZ K (repQ K N) (PL K) f = 0) : f = 0 := by
  rw [mem_Wsp_iff] at hf
  obtain ⟨h1, h2, -⟩ := hf
  funext g
  obtain ⟨b, hb, h, c, u, hu, rfl⟩ := exists_decomposition K N g
  rw [h2 _ u hu, h1 b hb]
  have : f (πZ K (repQ K N) (PL K) (zOf K (PL K) h c)) = 0 :=
    congrFun h0 (zOf K (PL K) h c)
  rw [this, mul_zero]
  rfl

end Inject
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.P2mK3AdmDim.coeffSpaceFamily"

section Ortho

variable (K : Type) [Field K] [NumberField K]

local notation "𝔾" => AdelicGL2 (𝓞 K) K
local notation "𝕂" => adelicMaximalCompact K

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem integrable_restrict {F : 𝔾 → ℂ} (hF : Continuous F) :
    Integrable (fun k : 𝕂 => F (k : 𝔾)) (maximalCompactHaar K) :=
  (hF.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_mul_conj {n : ℕ} (φ : Fin n → 𝔾 → ℂ) (hφc : ∀ j, Continuous (φ j)) (i j : Fin n) :
    Integrable (fun k : 𝕂 => φ j (k : 𝔾) * conj (φ i (k : 𝔾))) (maximalCompactHaar K) := by
  have hc : Continuous fun g : 𝔾 => φ j g * conj (φ i g) := by fun_prop
  exact integrable_restrict K (F := fun g : 𝔾 => φ j g * conj (φ i g)) hc

theorem sum_mul_integral_eq {n : ℕ} (φ : Fin n → 𝔾 → ℂ)
    (hφon : ∀ i j, ∫ k, φ i (k : 𝔾) * conj (φ j (k : 𝔾)) ∂(maximalCompactHaar K) = if i = j then 1 else 0)
    (s : Finset (Fin n)) (c : Fin n → ℂ) (i : Fin n) (hi : i ∈ s) :
    ∑ j ∈ s, c j * ∫ k, φ j (k : 𝔾) * conj (φ i (k : 𝔾)) ∂(maximalCompactHaar K) = c i := by
  have : ∀ j ∈ s, c j * ∫ k, φ j (k : 𝔾) * conj (φ i (k : 𝔾)) ∂(maximalCompactHaar K) =
      if j = i then c j else 0 := by
    intro j _
    rw [hφon j i]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' s i, if_pos hi]

theorem sum_mul_integral_eq_integral {n : ℕ} (φ : Fin n → 𝔾 → ℂ) (hφc : ∀ j, Continuous (φ j))
    (s : Finset (Fin n)) (c : Fin n → ℂ) (i : Fin n) :
    ∑ j ∈ s, c j * ∫ k, φ j (k : 𝔾) * conj (φ i (k : 𝔾)) ∂(maximalCompactHaar K) =
      ∫ k, (∑ j ∈ s, c j * (φ j (k : 𝔾) * conj (φ i (k : 𝔾)))) ∂(maximalCompactHaar K) := by
  rw [integral_finsetSum s (fun j _ => (integrable_mul_conj K φ hφc i j).const_mul (c j))]
  exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm

theorem linearIndependent_of_orthonormal {n : ℕ} (φ : Fin n → 𝔾 → ℂ) (hφc : ∀ j, Continuous (φ j))
    (hφon : ∀ i j, ∫ k, φ i (k : 𝔾) * conj (φ j (k : 𝔾)) ∂(maximalCompactHaar K) = if i = j then 1 else 0) :
    LinearIndependent ℂ φ := by
  rw [linearIndependent_iff']
  intro s c hsum i hi
  have hpt : ∀ x : 𝔾, ∑ j ∈ s, c j * φ j x = 0 := by
    intro x
    have := congrFun hsum x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
  have h3 : (fun k : 𝕂 => ∑ j ∈ s, c j * (φ j (k : 𝔾) * conj (φ i (k : 𝔾)))) = fun _ => 0 := by
    funext k
    calc ∑ j ∈ s, c j * (φ j (k : 𝔾) * conj (φ i (k : 𝔾)))
        = (∑ j ∈ s, c j * φ j (k : 𝔾)) * conj (φ i (k : 𝔾)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
      _ = 0 := by rw [hpt, zero_mul]
  rw [← sum_mul_integral_eq K φ hφon s c i hi, sum_mul_integral_eq_integral K φ hφc s c i, h3, integral_zero]

end Ortho
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.P2mK3AdmDim.coeffSpaceFamily"

section Main

variable (K : Type) [Field K] [NumberField K]

local notation "𝔾" => AdelicGL2 (𝓞 K) K
local notation "𝕂" => adelicMaximalCompact K

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

def Dbound (N : Ideal (𝓞 K)) (tys : ArchTypeFamily K) : ℕ :=
  Nat.card (Kf K ⧸ Qf K N) *
    ((PL K).map fun w => finrank ℂ (coeffSpaceFamily (fun i : Fin (tys.card w) => (tys.rep w i).ρ))).prod

theorem main (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : ArchTypeFamily K)
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (n : ℕ) (φ : Fin n → 𝔾 → ℂ)
    (hφ : ∀ j, IsInducedSection (𝓞 K) K χ₁ χ₂ (φ j)) (hφc : ∀ j, Continuous (φ j))
    (hφlev : ∀ j (g : 𝔾), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ j (g * u) = φ j g)
    (hφty : ∀ j, φ j ∈ archCutSubmodule K tys)
    (hφon : ∀ i j, ∫ k, φ i (k : 𝔾) * conj (φ j (k : 𝔾)) ∂(maximalCompactHaar K) = if i = j then 1 else 0) :
    n ≤ Dbound K N tys := by
  haveI : Fact (N ≠ ⊥) := ⟨hN⟩
  haveI : Fintype (Kf K ⧸ Qf K N) := Fintype.ofFinite _
  set W := Wsp K χ₁ χ₂ N tys with hW
  have hmem : ∀ j, φ j ∈ W := fun j => mem_Wsp_iff.mpr ⟨hφ j, hφlev j, hφty j⟩

  set R := (ResZ K (repQ K N) (PL K)).domRestrict W with hR
  have hRinj : Function.Injective R := by
    intro x y hxy
    apply Subtype.ext
    rw [← sub_eq_zero]
    have h0 : ResZ K (repQ K N) (PL K) ((x : 𝔾 → ℂ) - y) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hxy
    exact eq_zero_of_ResZ_eq_zero K (W.sub_mem x.2 y.2) h0
  have hrange : LinearMap.range R = W.map (ResZ K (repQ K N) (PL K)) := by
    rw [hR, LinearMap.range_domRestrict]
  obtain ⟨hfin, hle⟩ := finite_and_finrank_map_ResZ_le (χ₁ := χ₁) (χ₂ := χ₂) (N := N) (tys := tys)
    (repQ K N) (PL K)
  haveI := hfin
  haveI : Module.Finite ℂ (LinearMap.range R) := by rw [hrange]; exact hfin
  let e : W ≃ₗ[ℂ] LinearMap.range R := LinearEquiv.ofInjective R hRinj
  haveI : Module.Finite ℂ W := Module.Finite.equiv e.symm
  have hWrank : finrank ℂ W ≤ Dbound K N tys := by
    rw [e.finrank_eq, hrange, Dbound, Nat.card_eq_fintype_card]
    exact hle

  have hli : LinearIndependent ℂ (fun j => (⟨φ j, hmem j⟩ : W)) := by
    apply LinearIndependent.of_comp W.subtype
    exact linearIndependent_of_orthonormal K φ hφc hφon
  calc n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
    _ ≤ finrank ℂ W := hli.fintype_card_le_finrank
    _ ≤ Dbound K N tys := hWrank

end Main
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.P2mK3AdmDim.coeffSpaceFamily"

end P2mK3AdmDim
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.P2mK3AdmDim.coeffSpaceFamily P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.P2mK3AdmDim"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.P2mK3AdmDim.coeffSpaceFamily P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.P2mK3AdmDim"

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (_hN : N ≠ ⊥) (tysK : AutomorphicForm.ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∃ D : ℕ, ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ)
      (n : ℕ) (φ : Fin n → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ j, AutomorphicForm.IsInducedSection (𝓞 K) K (AutomorphicForm.etaFst μ αm hαm s)
        (AutomorphicForm.etaSnd ν αm hαm s) (φ j))
      (_hφc : ∀ j, Continuous (φ j))
      (_hφlev : ∀ j (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K, φ j (g * u) = φ j g)
      (_hφty : ∀ j, φ j ∈ AutomorphicForm.archCutSubmodule K tysK)
      (_hφon : ∀ i j, ∫ k, φ i (k : AdelicGL2 (𝓞 K) K) * conj (φ j (k : AdelicGL2 (𝓞 K) K))
          ∂(AutomorphicForm.maximalCompactHaar K) = if i = j then 1 else 0),
      n ≤ D := by
  intro αm
  refine ⟨P2mK3AdmDim.Dbound K N tysK, ?_⟩
  intro hαm μ ν s n φ hφ hφc hφlev hφty hφon
  exact P2mK3AdmDim.main K N _hN tysK _ _ n φ hφ hφc hφlev hφty hφon

end S_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot (solution)
