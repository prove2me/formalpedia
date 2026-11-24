-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:21:27.730166+00:00
-- url     : https://prove2.me/theorems/207cf6c3-3178-4748-bc0a-173ce69761d7
-- title:
--   Symmetric Flag Basis Vectors Apply Centre
-- statement:
--   Definitions and structural lemmas for Symmetric Flag Basis Vectors Apply Centre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/SymmetricFlagBasisVectorsApplyCentre.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_e_cd4c86133218
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_f_95382bea84da
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_k_8a59f7856bba
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_m_92f5719d2794
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_n_ddfb24727e1c
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_order_e93fa31b6760
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_r_6b0f69a7b59a
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_rankComplement_9cb33f905537
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_t_ec1b9c4ed304
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_vertexCount_b44560ac9584
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_wittIndex_e86ea14fff7c
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_e_cd4c86133218
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_f_95382bea84da
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_k_8a59f7856bba
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_m_92f5719d2794
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_n_ddfb24727e1c
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_order_e93fa31b6760
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_r_6b0f69a7b59a
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_rankComplement_9cb33f905537
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_t_ec1b9c4ed304
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_vertexCount_b44560ac9584
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_wittIndex_e86ea14fff7c


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SA
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat
def ofHSpace {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) : HermSpace E S.V where
  B := S.hT.flip
  herm x y := S.herm.eq y x
  nondeg x h := S.nondeg.2 x h
@[simp] theorem ofHSpace_B {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (x y : S.V) : (ofHSpace S).B x y = S.hT y x := rfl
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}
def xPlus (F : FlagD H r) : Submodule K V := F.X ⊔ Submodule.span K {F.z}
abbrev latX (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := Λ ⊓ rs R F.X
def latU (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := latX F Λ ⊔ Submodule.span R {F.z}
def latUU (F F' : FlagD H r) (Λ : Submodule R V) : Submodule R V := latU F Λ ⊔ latU F' Λ
def latSat (F F' : FlagD H r) (Λ : Submodule R V) : Submodule R V := Λ ⊓ rs R (V0 F F')
abbrev satQuot (F F' : FlagD H r) (Λ : Submodule R V) : Type :=
  ↥(latSat F F' Λ) ⧸ (latUU F F' Λ).submoduleOf (latSat F F' Λ)
def IsTransv (F F' : FlagD H r) : Prop :=
  Module.finrank K (V0 F F') = 2 * r + 2 ∧ Disjoint (V0 F F') (wSp F F')
def norLift (F F' : FlagD H r) : Submodule K V := V0 F F' ⊓ perp H (xPlus F)
def IsComp (F F' : FlagD H r) (u : V) (a a' : K) : Prop := u - a • F.z - a' • F'.z ∈ F.X ⊔ F'.X
def IsSig (F F' : FlagD H r) (y y' : V) (a a' : K) : Prop :=
  y ∈ norLift F F' ∧ y' ∈ norLift F' F ∧ IsComp F F' (y - y') a a'
def IsCong (F F' : FlagD H r) (Λ : Submodule R V) (g : R) : Prop :=
  latX F' Λ ⊔ smulLat g Λ = latX F Λ ⊔ smulLat g Λ ∧ F'.z - F.z ∈ latX F Λ ⊔ smulLat g Λ
def redLat (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := (Λ ⊓ rs R (perp H F.X)) ⊔ rs R F.X
def redLat0 (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := redLat F Λ ⊓ rs R (perp H (xPlus F))
def IsPairMap (F F' F'' : FlagD H r) (Λ : Submodule R V) (g : R) (β : V ≃ₗ[K] V) : Prop :=
  F'.X.map (β : V →ₗ[K] V) = F''.X ∧ (perp H F'.X).map (β : V →ₗ[K] V) = perp H F''.X ∧
  (∀ x ∈ perp H F'.X, ∀ y ∈ perp H F'.X, H.B (β x) (β y) = H.B x y) ∧
  imLat β (redLat F' Λ) = redLat F'' Λ ∧ β F'.z - F''.z ∈ F''.X ∧
  ∀ l' ∈ Λ ⊓ rs R (perp H F'.X), ∀ l'' ∈ Λ ⊓ rs R (perp H F''.X), β l' - l'' ∈ F''.X →
    l'' - l' ∈ latX F Λ ⊔ smulLat g Λ
def fixSp (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) : Submodule K V where
  carrier := {x | x ∈ wSp F F' ∧ ∃ x'' ∈ wSp F F'', x - x'' ∈ F.X ∧ β x - x'' ∈ F''.X}
  zero_mem' := ⟨zero_mem _, 0, zero_mem _, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨hx, a, ha, h1, h2⟩ ⟨hy, b, hb, h3, h4⟩
    refine ⟨add_mem hx hy, a + b, add_mem ha hb, ?_, ?_⟩
    · rw [add_sub_add_comm]; exact add_mem h1 h3
    · rw [map_add, add_sub_add_comm]; exact add_mem h2 h4
  smul_mem' := by
    rintro c x ⟨hx, a, ha, h1, h2⟩
    refine ⟨Submodule.smul_mem _ c hx, c • a, Submodule.smul_mem _ c ha, ?_, ?_⟩
    · rw [← smul_sub]; exact Submodule.smul_mem _ c h1
    · rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ c h2
theorem B_eq_zero_comm {x y : V} : H.B x y = 0 ↔ H.B y x = 0 :=
  ⟨fun h => by rw [← H.herm, h, star_zero], fun h => by rw [← H.herm, h, star_zero]⟩
theorem perp_anti {S S' : Submodule K V} (h : S ≤ S') : perp H S' ≤ perp H S := fun y hy =>
  (mem_perp_iff H S y).2 fun x hx => (mem_perp_iff H S' y).1 hy x (h hx)
theorem perp_sup (S S' : Submodule K V) : perp H (S ⊔ S') = perp H S ⊓ perp H S' := by
  refine le_antisymm (le_inf (perp_anti le_sup_left) (perp_anti le_sup_right)) fun y hy => ?_
  refine (mem_perp_iff H _ y).2 fun x hx => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add, (mem_perp_iff H _ y).1 hy.1 a ha, (mem_perp_iff H _ y).1 hy.2 b hb, add_zero]
theorem mem_perp_span (s : Set V) (y : V) :
    y ∈ perp H (Submodule.span K s) ↔ ∀ x ∈ s, H.B y x = 0 := by
  rw [mem_perp_iff]
  refine ⟨fun h x hx => h x (Submodule.subset_span hx), fun h x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, ha, smul_zero]
theorem X_eq_span (F : FlagD H r) :
    F.X = Submodule.span K (Set.range fun a : Fin r => F.e a.castSucc) := by
  rw [FlagD.X, FlagD.Xa, ← Set.image_univ]
  congr 2
  ext b
  simp
theorem mem_perp_X (F : FlagD H r) (y : V) :
    y ∈ perp H F.X ↔ ∀ a : Fin r, H.B y (F.e a.castSucc) = 0 := by
  rw [X_eq_span, mem_perp_span, Set.forall_mem_range]
theorem X_le_perp (F : FlagD H r) : F.X ≤ perp H F.X := by
  intro x hx
  refine (mem_perp_X F x).2 fun a => B_eq_zero_comm.1 ?_
  exact (mem_perp_iff H _ _).1 ((mem_perp_X F _).2 fun b => F.iso a b) x hx
theorem xPlus_eq_span (F : FlagD H r) : xPlus F = Submodule.span K (Set.range F.e) := by
  rw [xPlus, X_eq_span, ← Submodule.span_union]
  congr 1
  ext v
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Fin.exists_fin_succ', FlagD.z, eq_comm]
theorem mem_perp_xPlus (F : FlagD H r) (y : V) :
    y ∈ perp H (xPlus F) ↔ y ∈ perp H F.X ∧ H.B y F.z = 0 := by
  rw [xPlus, perp_sup, Submodule.mem_inf, mem_perp_span]
  simp
omit [StarRing K] in

theorem mem_imLat (s : V ≃ₗ[K] V) (M : Submodule R V) (x : V) : x ∈ imLat s M ↔ ∃ y ∈ M, s y = x := Iff.rfl
theorem xPlus_sup (F F' : FlagD H r) : xPlus F ⊔ xPlus F' = V0 F F' := by
  rw [xPlus, xPlus, V0, Submodule.span_insert, sup_sup_sup_comm]
theorem jointSpan_comm (F F' : FlagD H r) : V0 F' F = V0 F F' := by
  rw [← xPlus_sup, ← xPlus_sup, sup_comm]
theorem wSp_comm (F F' : FlagD H r) : wSp F' F = wSp F F' := by rw [wSp, wSp, jointSpan_comm]
theorem wSp_eq (F F' : FlagD H r) : wSp F F' = perp H (xPlus F) ⊓ perp H (xPlus F') := by
  rw [wSp, ← xPlus_sup, perp_sup]
theorem IsTransv.symm {F F' : FlagD H r} (h : IsTransv F F') : IsTransv F' F := by
  rw [IsTransv, jointSpan_comm, wSp_comm]; exact h
theorem IsCong.refl (F : FlagD H r) (Λ : Submodule R V) (g : R) : IsCong F F Λ g := ⟨rfl, by simp⟩
theorem IsCong.symm {F F' : FlagD H r} {Λ : Submodule R V} {g : R} (h : IsCong F F' Λ g) : IsCong F' F Λ g :=
  ⟨h.1.symm, by rw [h.1, ← neg_sub]; exact neg_mem h.2⟩
theorem IsCong.trans {F F' F'' : FlagD H r} {Λ : Submodule R V} {g : R} (h : IsCong F F' Λ g)
    (k : IsCong F' F'' Λ g) : IsCong F F'' Λ g :=
  ⟨k.1.trans h.1, by rw [← sub_add_sub_cancel _ F'.z]; exact add_mem (h.1.le k.2) h.2⟩
section Pair
variable {F F' F'' : FlagD H r} {Λ : Submodule R V} {g : R} {β : V ≃ₗ[K] V}
theorem IsPairMap.mem_X_iff (h : IsPairMap F F' F'' Λ g β) (x : V) : β x ∈ F''.X ↔ x ∈ F'.X := by
  rw [← h.1]; simp
theorem IsPairMap.mem_perp_iff (h : IsPairMap F F' F'' Λ g β) (x : V) :
    β x ∈ perp H F''.X ↔ x ∈ perp H F'.X := by
  rw [← h.2.1]; simp
theorem IsPairMap.mem_redLat_iff (h : IsPairMap F F' F'' Λ g β) (x : V) :
    β x ∈ redLat F'' Λ ↔ x ∈ redLat F' Λ := by
  rw [← h.2.2.2.1, mem_imLat]
  exact ⟨fun ⟨y, hy, e⟩ => β.injective e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
theorem isPairMap_of_mem_iff (h1 : ∀ x, β x ∈ F''.X ↔ x ∈ F'.X)
    (h2 : ∀ x, β x ∈ perp H F''.X ↔ x ∈ perp H F'.X)
    (h3 : ∀ x ∈ perp H F'.X, ∀ y ∈ perp H F'.X, H.B (β x) (β y) = H.B x y)
    (h4 : ∀ x, β x ∈ redLat F'' Λ ↔ x ∈ redLat F' Λ) (h5 : β F'.z - F''.z ∈ F''.X)
    (h6 : ∀ l' ∈ Λ ⊓ rs R (perp H F'.X), ∀ l'' ∈ Λ ⊓ rs R (perp H F''.X), β l' - l'' ∈ F''.X →
      l'' - l' ∈ latX F Λ ⊔ smulLat g Λ) : IsPairMap F F' F'' Λ g β := by
  have k : ∀ {S S' : Submodule K V}, (∀ x, β x ∈ S' ↔ x ∈ S) → S.map (β : V →ₗ[K] V) = S' := by
    intro S S' hS
    ext y
    obtain ⟨x, rfl⟩ := β.surjective y
    rw [hS]; simp
  refine ⟨k h1, k h2, h3, ?_, h5, h6⟩
  ext y
  obtain ⟨x, rfl⟩ := β.surjective y
  rw [h4, mem_imLat]
  exact ⟨fun ⟨y, hy, e⟩ => β.injective e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
theorem IsPairMap.symm (h : IsPairMap F F' F'' Λ g β) : IsPairMap F F'' F' Λ g β.symm := by
  refine isPairMap_of_mem_iff (fun x => by rw [← h.mem_X_iff]; simp) (fun x => by rw [← h.mem_perp_iff]; simp)
    (fun x hx y hy => ?_) (fun x => by rw [← h.mem_redLat_iff]; simp) ?_ fun l hl l' hl' e => ?_
  · rw [← h.2.2.1 _ (by rw [← h.mem_perp_iff]; simpa using hx) _ (by rw [← h.mem_perp_iff]; simpa using hy)]
    simp
  · rw [← h.mem_X_iff, map_sub, β.apply_symm_apply, ← neg_sub]
    exact neg_mem h.2.2.2.2.1
  · rw [← h.mem_X_iff, map_sub, β.apply_symm_apply, ← neg_sub, neg_mem_iff] at e
    rw [← neg_sub]
    exact neg_mem (h.2.2.2.2.2 l' hl' l hl e)
end Pair
namespace FlagExample
open NumberField Formalism.BasicNotions.Examples₂
variable (E : Type) [Field E] [NumberField E] [StarRing E]
abbrev sp : HermSpace E (wittSpace E 2 1).V := ofHSpace (wittSpace E 2 1)
def vec (v : Fin 5 → ℤ) : (wittSpace E 2 1).V := (fun i => (v i : E) : Fin 5 → E)
def co (x : (wittSpace E 2 1).V) : Fin 5 → E := x
theorem sp_B (x y : (wittSpace E 2 1).V) : (sp E).B x y =
    -(star (co E y 0) * co E x 0) - star (co E y 1) * co E x 1 + star (co E y 2) * co E x 2 +
      star (co E y 3) * co E x 3 + star (co E y 4) * co E x 4 := by
  show ∑ i : Fin 5, star (co E y i) * sgn (wittSigns 2 1 i) * co E x i = _
  have h0 : wittSigns 2 1 (0 : Fin 5) = true := rfl
  have h1 : wittSigns 2 1 (1 : Fin 5) = true := rfl
  have h2 : wittSigns 2 1 (2 : Fin 5) = false := rfl
  have h3 : wittSigns 2 1 (3 : Fin 5) = false := rfl
  have h4 : wittSigns 2 1 (4 : Fin 5) = false := rfl
  rw [Fin.sum_univ_five, h0, h1, h2, h3, h4]
  simp only [sgn, if_true, Bool.false_eq_true, if_false]
  ring
theorem sp_B_vec (v w : Fin 5 → ℤ) : (sp E).B (vec E v) (vec E w) =
    ((-(w 0 * v 0) - w 1 * v 1 + w 2 * v 2 + w 3 * v 3 + w 4 * v 4 : ℤ) : E) := by
  rw [sp_B]; simp [co, vec]
def fl (m s : ℤ) (h1 : m * m = m) (h2 : s * s = m) : FlagD (sp E) 1 where
  e := ![vec E ![1 + 2 * m, 0, 1, 2 * s, 2 * m], vec E ![0, 1 + 2 * m, 0, 2 * s, -2 * m]]
  T := 1
  indep := by
    rw [linearIndependent_unique_iff]
    intro h
    have := congrFun h (2 : Fin 5)
    have h0 : ((1 : ℤ) : E) = 0 := this
    simp at h0
  iso := by
    intro b c
    rw [Subsingleton.elim b 0, Subsingleton.elim c 0]
    refine (sp_B_vec E _ _).trans (Int.cast_eq_zero.2 ?_)
    simp; linarith
  zperp := by
    intro b
    rw [Subsingleton.elim b 0]
    refine (sp_B_vec E _ _).trans (Int.cast_eq_zero.2 ?_)
    simp; linarith
  zz := by
    refine (sp_B_vec E _ _).trans (Eq.trans (congrArg _ (?_ : _ = (-1 : ℤ))) (by simp))
    simp; linarith
  hT := one_ne_zero
abbrev flZero : FlagD (sp E) 1 := fl E 0 0 rfl rfl
abbrev flPos : FlagD (sp E) 1 := fl E 1 1 rfl rfl
abbrev flNeg : FlagD (sp E) 1 := fl E 1 (-1) rfl rfl
variable {m s : ℤ} (h1 : m * m = m) (h2 : s * s = m)
theorem fl_X : (fl E m s h1 h2).X = Submodule.span E {vec E ![1 + 2 * m, 0, 1, 2 * s, 2 * m]} := by
  rw [X_eq_span, Set.range_unique]; rfl
theorem symmetricFlagBasisVectors_apply_centre : (fl E m s h1 h2).z = vec E ![0, 1 + 2 * m, 0, 2 * s, -2 * m] := rfl
def flip : (wittSpace E 2 1).V ≃ₗ[E] (wittSpace E 2 1).V :=
  LinearEquiv.piCongrRight (R := E) (φ := fun _ : Fin 5 => E) (ψ := fun _ : Fin 5 => E)
    fun i => if i = 3 then LinearEquiv.neg E else LinearEquiv.refl E E
theorem X_ne : (flPos E).X ≠ (flNeg E).X := by
  intro h
  have hm : vec E ![1 + 2 * 1, 0, 1, 2 * 1, 2 * 1] ∈ (flNeg E).X := by
    rw [← h, fl_X]; exact Submodule.mem_span_singleton_self _
  have h0 := (mem_perp_X (flNeg E) _).1 (X_le_perp _ hm) 0
  have h1 := (sp_B_vec E _ _).symm.trans h0
  simp at h1
example : ¬ IsPairMap (flZero E) (flPos E) (flNeg E) (wittSpace E 2 1).L0 ((2 : ℕ) : 𝓞 E)
    (LinearEquiv.refl E _) := fun h => X_ne E (by simpa using h.1)
example : vec E ![2, 0, 2, 1, 1] ∈ wSp (flZero E) (flPos E) ∧
    vec E ![2, 0, 2, 1, 1] ∉ fixSp (flZero E) (flPos E) (flNeg E) (flip E) := by
  constructor
  · rw [wSp_eq, Submodule.mem_inf, xPlus_eq_span, xPlus_eq_span, mem_perp_span, mem_perp_span,
      Set.forall_mem_range, Set.forall_mem_range]
    constructor <;> intro a <;> fin_cases a <;> refine (sp_B_vec E _ _).trans ?_ <;> simp
  · rintro ⟨-, y, hy, h, -⟩
    rw [fl_X, Submodule.mem_span_singleton] at h
    obtain ⟨t, ht⟩ := h
    rw [wSp_eq] at hy
    have h1 := ((mem_perp_xPlus _ _).1 hy.2).2
    rw [← sub_sub_cancel (vec E ![2, 0, 2, 1, 1]) y, ← ht, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, symmetricFlagBasisVectors_apply_centre, sp_B_vec, sp_B_vec] at h1
    simp at h1
example : IsComp (flZero E) (flPos E) ((flPos E).z - (flZero E).z) (-1) 1 := by simp [IsComp]
end FlagExample
end GlobalTheory.SA
end


