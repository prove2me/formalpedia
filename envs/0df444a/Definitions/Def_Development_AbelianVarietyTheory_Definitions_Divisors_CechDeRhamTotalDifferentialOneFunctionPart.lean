-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:48.349345+00:00
-- url     : https://prove2.me/theorems/2c6114ee-d81a-4b8a-bc9e-d34aa4f3f27c
-- title:
--   Cech De Rham Total Differential One Function Part
-- statement:
--   Definitions and structural lemmas for Cech De Rham Total Differential One Function Part, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamTotalDifferentialOneFunctionPart.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Theorems.Thm_GlobalTheory_CatCoh_commAlgFunctorCocyclesOne_eq_ker
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_dOne
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_wedge
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_oneFormMap_comp_oneFormMap
import Theorems.Thm_GlobalTheory_CechDR_dOne_smul
import Theorems.Thm_GlobalTheory_CechDR_dTwo_wedge
import Theorems.Thm_GlobalTheory_CechDR_wedge_smul_left
import Theorems.Thm_GlobalTheory_CechDR_wedge_smul_right
import Theorems.Thm_GlobalTheory_CechDR_wedge_swap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory KaehlerDifferential
namespace GlobalTheory.CechDR
open CatCoh
universe v u v' u' v'' u''
section Complex
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
theorem semiHom_mp {T T' : C} (φ : T ⟶ T') : SemiHom (RingHom.id R) (mp F φ : F.obj T →+* F.obj T') := by
  intro r b
  simp
def p1 {T T' : C} (φ : T ⟶ T') : Ω[F.obj T⁄R] →ₗ[R] Ω[F.obj T'⁄R] := (semiHom_mp F φ).m1
def pOm (j : ℕ) {T T' : C} (φ : T ⟶ T') : Om R (F.obj T) j →ₗ[R] Om R (F.obj T') j :=
  (semiHom_mp F φ).mOm j
section
variable {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'')
theorem p1_D (b : F.obj T) : p1 F φ (D R _ b) = D R _ (mp F φ b) := by
  unfold p1
  exact (semiHom_mp F φ).m1_D b
theorem oneFormsMapOfFunctorMorphism_smul (b : F.obj T) (ω : Ω[F.obj T⁄R]) : p1 F φ (b • ω) = mp F φ b • p1 F φ ω := by
  unfold p1
  exact (semiHom_mp F φ).oneFormMap_smul_semilinear b ω
theorem oneFormsMapOfFunctorMorphism_comp (ω : Ω[F.obj T⁄R]) : p1 F (φ ≫ ψ) ω = p1 F ψ (p1 F φ ω) := by
  unfold p1
  exact ((semiHom_mp F φ).oneFormMap_comp_oneFormMap (semiHom_mp F ψ) (semiHom_mp F (φ ≫ ψ))
    (fun b ↦ (mp_comp F φ ψ b).symm) ω).symm
theorem pOm_dOne (ω : Ω[F.obj T⁄R]) : pOm F 2 φ (dOne R _ ω) = dOne R _ (p1 F φ ω) := by
  unfold pOm p1
  exact (semiHom_mp F φ).mOm_dOne ω
theorem pOm_wedge (a b : Ω[F.obj T⁄R]) :
    pOm F 2 φ (wedge R _ a b) = wedge R _ (p1 F φ a) (p1 F φ b) := by
  unfold pOm p1
  exact (semiHom_mp F φ).mOm_wedge a b
end
abbrev C3 := ∀ (T T' T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T'''
abbrev A0 := ∀ T : C, Ω[F.obj T⁄R]
abbrev A1 := ∀ (T T' : C) (_ : T ⟶ T'), Ω[F.obj T'⁄R]
abbrev A2 := ∀ (T T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), Ω[F.obj T''⁄R]
abbrev W0 (j : ℕ) := ∀ T : C, Om R (F.obj T) j
abbrev W1 (j : ℕ) := ∀ (T T' : C) (_ : T ⟶ T'), Om R (F.obj T') j
abbrev Tot0 := C0 F
abbrev Tot1 := C1 F × A0 F
abbrev Tot2 := C2 F × A1 F × W0 F 2
abbrev Tot3 := C3 F × A2 F × W1 F 2 × W0 F 3
def dTot0 : Tot0 F →ₗ[R] Tot1 F where
  toFun g := (d0 F g, fun T ↦ D R _ (g T))
  map_add' g g' := Prod.ext (map_add _ _ _) (funext fun T ↦ by simp)
  map_smul' r g := Prod.ext (map_smul _ _ _) (funext fun T ↦ by simp)
def dTot1 : Tot1 F →ₗ[R] Tot2 F where
  toFun c := (d1 F c.1, fun T T' φ ↦ c.2 T' - p1 F φ (c.2 T) - D R _ (c.1 T T' φ),
    fun T ↦ dOne R _ (c.2 T))
  map_add' c c' := Prod.ext (map_add _ _ _) (Prod.ext (by funext T T' φ; simp; abel)
    (funext fun T ↦ by simp))
  map_smul' r c := Prod.ext (map_smul _ _ _) (Prod.ext (by funext T T' φ; simp [smul_sub])
    (funext fun T ↦ by simp))
def dTot2 : Tot2 F →ₗ[R] Tot3 F where
  toFun c := (fun T T' T'' T''' φ ψ χ ↦ c.1 T' T'' T''' ψ χ - c.1 T T'' T''' (φ ≫ ψ) χ +
      c.1 T T' T''' φ (ψ ≫ χ) - mp F χ (c.1 T T' T'' φ ψ),
    fun T T' T'' φ ψ ↦ p1 F ψ (c.2.1 T T' φ) - c.2.1 T T'' (φ ≫ ψ) + c.2.1 T' T'' ψ +
      D R _ (c.1 T T' T'' φ ψ),
    fun T T' φ ↦ c.2.2 T' - pOm F 2 φ (c.2.2 T) - dOne R _ (c.2.1 T T' φ),
    fun T ↦ dTwo R _ (c.2.2 T))
  map_add' c c' := Prod.ext (by funext T T' T'' T''' φ ψ χ; simp; abel)
    (Prod.ext (by funext T T' T'' φ ψ; simp; abel) (Prod.ext (by funext T T' φ; simp; abel)
    (funext fun T ↦ by simp)))
  map_smul' r c := Prod.ext (by funext T T' T'' T''' φ ψ χ; simp [smul_sub])
    (Prod.ext (by funext T T' T'' φ ψ; simp [smul_sub]) (Prod.ext (by funext T T' φ; simp [smul_sub])
    (funext fun T ↦ by simp)))
section
variable {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'')
theorem dTot0_f (g : Tot0 F) : (dTot0 F g).1 T T' φ = g T' - mp F φ (g T) := rfl
theorem dTot0_ω (g : Tot0 F) (T : C) : (dTot0 F g).2 T = D R _ (g T) := rfl
theorem cechDeRhamTotalDifferentialOne_functionPart (c : Tot1 F) :
    (dTot1 F c).1 T T' T'' φ ψ = mp F ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ := rfl
theorem dTot1_a (c : Tot1 F) :
    (dTot1 F c).2.1 T T' φ = c.2 T' - p1 F φ (c.2 T) - D R _ (c.1 T T' φ) := rfl
theorem dTot1_η (c : Tot1 F) (T : C) : (dTot1 F c).2.2 T = dOne R _ (c.2 T) := rfl
end
variable {F} in

theorem Tot1.ext {c c' : Tot1 F} (h1 : ∀ T T' φ, c.1 T T' φ = c'.1 T T' φ) (h2 : ∀ T, c.2 T = c'.2 T) :
    c = c' := by
  refine Prod.ext ?_ ?_
  · funext T T' φ
    exact h1 T T' φ
  · funext T
    exact h2 T
variable {F} in

theorem Tot2.ext {c c' : Tot2 F} (h1 : ∀ T T' T'' φ ψ, c.1 T T' T'' φ ψ = c'.1 T T' T'' φ ψ)
    (h2 : ∀ T T' φ, c.2.1 T T' φ = c'.2.1 T T' φ) (h3 : ∀ T, c.2.2 T = c'.2.2 T) : c = c' := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext T T' T'' φ ψ
    exact h1 T T' T'' φ ψ
  · funext T T' φ
    exact h2 T T' φ
  · funext T
    exact h3 T
def cechDeRhamTotalCocyclesOne : Submodule R (Tot1 F) := LinearMap.ker (dTot1 F)
def cechDeRhamTotalCocyclesTwo : Submodule R (Tot2 F) := LinearMap.ker (dTot2 F)
variable {F}
theorem mem_cechDeRhamTotalCocyclesOne_iff {c : Tot1 F} : c ∈ cechDeRhamTotalCocyclesOne F ↔ c.1 ∈ Z1 F ∧
    (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), c.2 T' = p1 F φ (c.2 T) + D R _ (c.1 T T' φ)) ∧
    ∀ T, dOne R _ (c.2 T) = 0 := by
  rw [cechDeRhamTotalCocyclesOne, LinearMap.mem_ker, commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker]
  constructor
  · intro h
    refine ⟨congrArg Prod.fst h, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
    · have e : (dTot1 F c).2.1 T T' φ = 0 := congrFun (congrFun (congrFun (congrArg (fun x ↦ x.2.1) h) T) T') φ
      rw [dTot1_a, sub_sub, sub_eq_zero] at e
      exact e
    · have e : (dTot1 F c).2.2 T = 0 := congrFun (congrArg (fun x ↦ x.2.2) h) T
      rw [dTot1_η] at e
      exact e
  · rintro ⟨h1, h2, h3⟩
    refine Prod.ext h1 (Prod.ext ?_ ?_)
    · funext T T' φ
      show (dTot1 F c).2.1 T T' φ = 0
      rw [dTot1_a, h2 φ]
      abel
    · funext T
      exact h3 T
theorem mem_cechDeRhamTotalCocyclesTwo_iff {c : Tot2 F} : c ∈ cechDeRhamTotalCocyclesTwo F ↔ c.1 ∈ Z2 F ∧
    (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), c.2.1 T T'' (φ ≫ ψ) =
      p1 F ψ (c.2.1 T T' φ) + c.2.1 T' T'' ψ + D R _ (c.1 T T' T'' φ ψ)) ∧
    (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), c.2.2 T' = pOm F 2 φ (c.2.2 T) + dOne R _ (c.2.1 T T' φ)) ∧
    ∀ T, dTwo R _ (c.2.2 T) = 0 := by
  rw [cechDeRhamTotalCocyclesTwo, LinearMap.mem_ker]
  constructor
  · intro h
    refine ⟨?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
    · intro T T' T'' T''' φ ψ χ
      have e : c.1 T' T'' T''' ψ χ - c.1 T T'' T''' (φ ≫ ψ) χ + c.1 T T' T''' φ (ψ ≫ χ) -
          mp F χ (c.1 T T' T'' φ ψ) = 0 :=
        congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun
          (congrArg Prod.fst h) T) T') T'') T''') φ) ψ) χ
      linear_combination -e
    · have e : p1 F ψ (c.2.1 T T' φ) - c.2.1 T T'' (φ ≫ ψ) + c.2.1 T' T'' ψ +
          D R _ (c.1 T T' T'' φ ψ) = 0 :=
        congrFun (congrFun (congrFun (congrFun (congrFun (congrArg (fun x ↦ x.2.1) h) T) T') T'') φ) ψ
      have e' : c.2.1 T T'' (φ ≫ ψ) - (p1 F ψ (c.2.1 T T' φ) + c.2.1 T' T'' ψ +
          D R _ (c.1 T T' T'' φ ψ)) = -(p1 F ψ (c.2.1 T T' φ) - c.2.1 T T'' (φ ≫ ψ) + c.2.1 T' T'' ψ +
          D R _ (c.1 T T' T'' φ ψ)) := by abel
      rw [e, neg_zero, sub_eq_zero] at e'
      exact e'
    · have e : c.2.2 T' - pOm F 2 φ (c.2.2 T) - dOne R _ (c.2.1 T T' φ) = 0 :=
        congrFun (congrFun (congrFun (congrArg (fun x ↦ x.2.2.1) h) T) T') φ
      rw [sub_sub, sub_eq_zero] at e
      exact e
    · exact congrFun (congrArg (fun x ↦ x.2.2.2) h) T
  · rintro ⟨h1, h2, h3, h4⟩
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext T T' T'' T''' φ ψ χ
      show c.1 T' T'' T''' ψ χ - c.1 T T'' T''' (φ ≫ ψ) χ + c.1 T T' T''' φ (ψ ≫ χ) -
          mp F χ (c.1 T T' T'' φ ψ) = 0
      have e := h1 φ ψ χ
      linear_combination -e
    · funext T T' T'' φ ψ
      show p1 F ψ (c.2.1 T T' φ) - c.2.1 T T'' (φ ≫ ψ) + c.2.1 T' T'' ψ +
          D R _ (c.1 T T' T'' φ ψ) = 0
      rw [h2 φ ψ]
      abel
    · funext T T' φ
      show c.2.2 T' - pOm F 2 φ (c.2.2 T) - dOne R _ (c.2.1 T T' φ) = 0
      rw [h3 φ]
      abel
    · funext T
      exact h4 T
section
variable {T T' T'' T''' : C}
theorem cechDeRhamTotalCocyclesOne.comp (c : cechDeRhamTotalCocyclesOne F) (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    c.1.1 T T'' (φ ≫ ψ) = mp F ψ (c.1.1 T T' φ) + c.1.1 T' T'' ψ := Z1.comp ⟨c.1.1, (mem_cechDeRhamTotalCocyclesOne_iff.1 c.2).1⟩ φ ψ
theorem cechDeRhamTotalCocyclesOne.conn (c : cechDeRhamTotalCocyclesOne F) (φ : T ⟶ T') : c.1.2 T' = p1 F φ (c.1.2 T) + D R _ (c.1.1 T T' φ) := (mem_cechDeRhamTotalCocyclesOne_iff.1 c.2).2.1 φ
theorem cechDeRhamTotalCocyclesOne.closed (c : cechDeRhamTotalCocyclesOne F) (T : C) : dOne R _ (c.1.2 T) = 0 := (mem_cechDeRhamTotalCocyclesOne_iff.1 c.2).2.2 T
theorem cechDeRhamTotalCocyclesTwo.comp (c : cechDeRhamTotalCocyclesTwo F) (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''') :
    mp F χ (c.1.1 T T' T'' φ ψ) + c.1.1 T T'' T''' (φ ≫ ψ) χ =
      c.1.1 T T' T''' φ (ψ ≫ χ) + c.1.1 T' T'' T''' ψ χ := by
  have h := (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1
  exact h φ ψ χ
theorem cechDeRhamTotalCocyclesTwo.closed (c : cechDeRhamTotalCocyclesTwo F) (T : C) : dTwo R _ (c.1.2.2 T) = 0 := (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).2.2.2 T
end
variable (F)
theorem dTot0_mem (g : Tot0 F) : dTot0 F g ∈ cechDeRhamTotalCocyclesOne F := by
  rw [mem_cechDeRhamTotalCocyclesOne_iff]
  refine ⟨commAlgFunctorCoboundaryZero_mem_cocyclesOne F g, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · rw [dTot0_ω, dTot0_ω, dTot0_f, p1_D, map_sub]
    abel
  · rw [dTot0_ω]
    exact dOne_D _
theorem dTot1_mem (c : Tot1 F) : dTot1 F c ∈ cechDeRhamTotalCocyclesTwo F := by
  rw [mem_cechDeRhamTotalCocyclesTwo_iff]
  refine ⟨differential_one_mem_scaled_lattice F c.1, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · simp only [dTot1_a, cechDeRhamTotalDifferentialOne_functionPart, oneFormsMapOfFunctorMorphism_comp, map_sub, map_add, p1_D]
    abel
  · simp only [dTot1_η, dTot1_a, map_sub, pOm_dOne, dOne_D]
    abel
  · rw [dTot1_η]
    exact dTwo_dOne _
def Hyp1 : Type _ := cechDeRhamTotalCocyclesOne F ⧸ LinearMap.range ((dTot0 F).codRestrict (cechDeRhamTotalCocyclesOne F) (dTot0_mem F))
def Hyp2 : Type _ := cechDeRhamTotalCocyclesTwo F ⧸ LinearMap.range ((dTot1 F).codRestrict (cechDeRhamTotalCocyclesTwo F) (dTot1_mem F))
instance : AddCommGroup (Hyp1 F) := inferInstanceAs (AddCommGroup (_ ⧸ LinearMap.range _))
instance : Module R (Hyp1 F) := inferInstanceAs (Module R (_ ⧸ LinearMap.range _))
instance : AddCommGroup (Hyp2 F) := inferInstanceAs (AddCommGroup (_ ⧸ LinearMap.range _))
instance : Module R (Hyp2 F) := inferInstanceAs (Module R (_ ⧸ LinearMap.range _))
def Hyp1.mk : cechDeRhamTotalCocyclesOne F →ₗ[R] Hyp1 F := Submodule.mkQ _
def Hyp2.mk : cechDeRhamTotalCocyclesTwo F →ₗ[R] Hyp2 F := Submodule.mkQ _
variable {F}
theorem Hyp1.mk_eq_zero {c : cechDeRhamTotalCocyclesOne F} : Hyp1.mk F c = 0 ↔ ∃ g, dTot0 F g = c.1 := by
  show (Submodule.Quotient.mk c : cechDeRhamTotalCocyclesOne F ⧸ _) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, congrArg Subtype.val hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
theorem Hyp2.mk_eq_zero {c : cechDeRhamTotalCocyclesTwo F} : Hyp2.mk F c = 0 ↔ ∃ e, dTot1 F e = c.1 := by
  show (Submodule.Quotient.mk c : cechDeRhamTotalCocyclesTwo F ⧸ _) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, congrArg Subtype.val he⟩
  · rintro ⟨e, he⟩
    exact ⟨e, Subtype.ext he⟩
variable (F)
def cupTot : Tot1 F →ₗ[R] Tot1 F →ₗ[R] Tot2 F :=
  LinearMap.mk₂ R
    (fun a b ↦ (fun T T' T'' φ ψ ↦ mp F ψ (a.1 T T' φ) * b.1 T' T'' ψ,
      fun T T' φ ↦ a.1 T T' φ • b.2 T' - b.1 T T' φ • p1 F φ (a.2 T),
      fun T ↦ wedge R _ (a.2 T) (b.2 T)))
    (fun a a' b ↦ Tot2.ext (by intros; simp [add_mul]) (by intros; simp [add_smul]; abel)
      (by intros; simp))
    (fun r a b ↦ Tot2.ext (by intros; simp) (by intros; simp [smul_sub, smul_comm r])
      (by intros; simp [wedge_smul_left]))
    (fun a b b' ↦ Tot2.ext (by intros; simp [mul_add]) (by intros; simp [add_smul]; abel)
      (by intros; simp))
    (fun r a b ↦ Tot2.ext (by intros; simp) (by intros; simp [smul_sub, smul_comm r])
      (by intros; simp [wedge_smul_right]))
section
variable {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (a b : Tot1 F)
theorem cupTot_apply : (cupTot F a b).1 T T' T'' φ ψ = mp F ψ (a.1 T T' φ) * b.1 T' T'' ψ := rfl
theorem cupTot_a : (cupTot F a b).2.1 T T' φ = a.1 T T' φ • b.2 T' - b.1 T T' φ • p1 F φ (a.2 T) := rfl
theorem cupTot_η (T : C) : (cupTot F a b).2.2 T = wedge R _ (a.2 T) (b.2 T) := rfl
end
theorem cupTot_mem (a b : cechDeRhamTotalCocyclesOne F) : cupTot F a.1 b.1 ∈ cechDeRhamTotalCocyclesTwo F := by
  rw [mem_cechDeRhamTotalCocyclesTwo_iff]
  refine ⟨?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · intro T T' T'' T''' φ ψ χ
    simp only [cupTot_apply, cechDeRhamTotalCocyclesOne.comp a, cechDeRhamTotalCocyclesOne.comp b, map_mul, map_add, mp_comp]
    ring
  · simp only [cupTot_a, cupTot_apply]
    rw [cechDeRhamTotalCocyclesOne.comp a φ ψ, cechDeRhamTotalCocyclesOne.comp b φ ψ, cechDeRhamTotalCocyclesOne.conn b ψ, cechDeRhamTotalCocyclesOne.conn a φ]
    simp only [map_add, map_sub, oneFormsMapOfFunctorMorphism_smul, oneFormsMapOfFunctorMorphism_comp, p1_D, Derivation.leibniz]
    module
  · simp only [cupTot_η, cupTot_a, map_sub, dOne_smul, cechDeRhamTotalCocyclesOne.closed b, ← pOm_dOne, cechDeRhamTotalCocyclesOne.closed a,
      map_zero, smul_zero, add_zero, pOm_wedge]
    rw [cechDeRhamTotalCocyclesOne.conn a φ, cechDeRhamTotalCocyclesOne.conn b φ]
    simp only [map_add, LinearMap.add_apply]
    rw [wedge_swap (D R _ (b.1.1 T T' φ)) (p1 F φ (a.1.2 T))]
    abel
  · rw [cupTot_η]
    exact dTwo_wedge (cechDeRhamTotalCocyclesOne.closed a T) (cechDeRhamTotalCocyclesOne.closed b T)
def cupZZ : cechDeRhamTotalCocyclesOne F →ₗ[R] cechDeRhamTotalCocyclesOne F →ₗ[R] cechDeRhamTotalCocyclesTwo F :=
  LinearMap.mk₂ R (fun a b ↦ ⟨cupTot F a.1 b.1, cupTot_mem F a b⟩)
    (fun a a' b ↦ Subtype.ext (by simp)) (fun r a b ↦ Subtype.ext (by simp))
    (fun a b b' ↦ Subtype.ext (by simp)) (fun r a b ↦ Subtype.ext (by simp))
theorem coe_cupZZ (a b : cechDeRhamTotalCocyclesOne F) : (cupZZ F a b).1 = cupTot F a.1 b.1 := rfl
def cupHyp : Hyp1 F →ₗ[R] Hyp1 F →ₗ[R] Hyp2 F :=
  LinearMap.liftQ₂ _ _ ((cupZZ F).compr₂ (Hyp2.mk F))
    (by
      rintro _ ⟨g, rfl⟩
      ext b
      refine Hyp2.mk_eq_zero.2 ⟨(fun T T' φ ↦ mp F φ (g T) * b.1.1 T T' φ, fun T ↦ g T • b.1.2 T), ?_⟩
      refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_
      · simp only [cechDeRhamTotalDifferentialOne_functionPart, coe_cupZZ, cupTot_apply, LinearMap.codRestrict_apply, dTot0_f, cechDeRhamTotalCocyclesOne.comp b,
          map_mul, map_sub, mp_comp]
        ring
      · simp only [dTot1_a, coe_cupZZ, cupTot_a, LinearMap.codRestrict_apply, dTot0_f, dTot0_ω,
          oneFormsMapOfFunctorMorphism_smul, p1_D, Derivation.leibniz]
        rw [cechDeRhamTotalCocyclesOne.conn b φ]
        module
      · simp only [dTot1_η, coe_cupZZ, cupTot_η, LinearMap.codRestrict_apply, dTot0_ω, dOne_smul,
          cechDeRhamTotalCocyclesOne.closed b, smul_zero, add_zero])
    (by
      rintro _ ⟨g, rfl⟩
      ext a
      refine Hyp2.mk_eq_zero.2 ⟨(fun T T' φ ↦ -(a.1.1 T T' φ * g T'), fun T ↦ -(g T • a.1.2 T)), ?_⟩
      refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_
      · simp only [cechDeRhamTotalDifferentialOne_functionPart, coe_cupZZ, cupTot_apply, LinearMap.codRestrict_apply, dTot0_f, cechDeRhamTotalCocyclesOne.comp a,
          map_mul, map_neg]
        ring
      · simp only [dTot1_a, coe_cupZZ, cupTot_a, LinearMap.codRestrict_apply, dTot0_f, dTot0_ω,
          oneFormsMapOfFunctorMorphism_smul, map_neg, Derivation.leibniz]
        rw [cechDeRhamTotalCocyclesOne.conn a φ]
        module
      · simp only [dTot1_η, coe_cupZZ, cupTot_η, LinearMap.codRestrict_apply, dTot0_ω, dOne_smul,
          map_neg, cechDeRhamTotalCocyclesOne.closed a, smul_zero, add_zero]
        exact (wedge_swap _ _).symm)
def cechDeRhamTotalCocyclesOne.fn : cechDeRhamTotalCocyclesOne F →ₗ[R] Z1 F where
  toFun c := ⟨c.1.1, (mem_cechDeRhamTotalCocyclesOne_iff.1 c.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def toO : Hyp1 F →ₗ[R] H1 F :=
  Submodule.mapQ _ _ (cechDeRhamTotalCocyclesOne.fn F) (by rintro _ ⟨g, rfl⟩; exact ⟨g, rfl⟩)
def Fil1 : Submodule R (Hyp1 F) := LinearMap.ker (toO F)
def Glob1 : Submodule R (A0 F) where
  carrier := {ω | ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ω T' = p1 F φ (ω T)}
  add_mem' {a b} ha hb T T' φ := by simp [ha φ, hb φ]
  zero_mem' T T' φ := by simp
  smul_mem' r a ha T T' φ := by simp [ha φ]
def Closed1 : Submodule R (Glob1 F) where
  carrier := {ω | ∀ T, dOne R _ (ω.1 T) = 0}
  add_mem' {a b} ha hb T := by simp [ha T, hb T]
  zero_mem' T := by simp
  smul_mem' r a ha T := by simp [ha T]
def formZZ : Closed1 F →ₗ[R] cechDeRhamTotalCocyclesOne F where
  toFun ω := ⟨(0, ω.1.1), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨zero_mem _, fun T T' φ ↦ by simpa using ω.1.2 φ, ω.2⟩⟩
  map_add' a b := Subtype.ext (Prod.ext (add_zero _).symm rfl)
  map_smul' r a := Subtype.ext (Prod.ext (smul_zero _).symm rfl)
def ofForm : Closed1 F →ₗ[R] Hyp1 F := Hyp1.mk F ∘ₗ formZZ F
end Complex
end GlobalTheory.CechDR


