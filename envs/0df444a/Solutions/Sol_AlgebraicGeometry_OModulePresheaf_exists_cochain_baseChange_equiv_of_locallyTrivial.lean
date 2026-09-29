-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_cochain_baseChange_equiv_of_locallyTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8217bbbc-48ba-5c1f-a936-5bca9708459f

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial.AlgebraicGeometry TensorProduct AlgebraicGeometry.Scheme.TwoAffineOpenCover"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom Spec Scheme Scheme.Hom.preimage_mono IsSeparated isAffineOpen_top isAffineHom_diagonal_iff Scheme.Modules.pullbackPushforwardAdjunction IsAffineOpen Scheme.Modules IsAffineHom OModulePresheaf OModulePresheaf.res_res OModulePresheaf.d_apply Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap OModulePresheaf.ofModules Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "res_res cochain d d_apply unit res res_refl obj res_comp ofModules"
namespace CechBaseChange
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

section EqRes
variable {R : Type u} [CommRing R] {Y : Scheme.{u}} {ρ : Y ⟶ Spec (.of R)} (G : OModulePresheaf ρ)

def eqRes {U U' : Y.Opens} (h : U = U') : G.obj U' ≃ₗ[R] G.obj U :=
  LinearEquiv.ofLinear (G.res h.le) (G.res h.ge)
    (by rw [← G.res_comp h.le h.ge]; exact G.res_refl U)
    (by rw [← G.res_comp h.ge h.le]; exact G.res_refl U')

theorem eqRes_apply {U U' : Y.Opens} (h : U = U') (x : G.obj U') : eqRes G h x = G.res h.le x := rfl

theorem res_res_eq_res_res {U V V' W : Y.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W) (h₃ : U ≤ V') (h₄ : V' ≤ W) (x : G.obj W) :
    G.res h₁ (G.res h₂ x) = G.res h₃ (G.res h₄ x) := by
  rw [G.res_res, G.res_res]

end EqRes

section Affine
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) (𝒰 : X.OrderedAffineCover)

theorem isAffineOpen_inf_of_isSeparated' [IsSeparated π] {U W : X.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : IsAffineOpen (U ⊓ W) := by
  haveI : IsAffineHom (pullback.diagonal π) := inferInstance
  exact isAffineHom_diagonal_iff.mp this ⊤ (isAffineOpen_top _) U (by simp) W (by simp) hU hW

theorem isAffineOpen_inter' [IsSeparated π] {i : ℕ} (s : 𝒰.Idx i) : IsAffineOpen (𝒰.inter s) := by
  suffices h : ∀ (n : ℕ) (t : Fin (n + 1) → 𝒰.ι), IsAffineOpen (⨅ j, 𝒰.U (t j)) from h i s.1
  intro n
  induction n with
  | zero =>
    intro t
    have h1 : (⨅ j : Fin 1, 𝒰.U (t j)) = 𝒰.U (t 0) :=
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)
    rw [h1]; exact 𝒰.isAffineOpen (t 0)
  | succ m ih =>
    intro t
    have hsplit : (⨅ j : Fin (m + 2), 𝒰.U (t j)) = 𝒰.U (t 0) ⊓ (⨅ j : Fin (m + 1), 𝒰.U (t j.succ)) :=
      le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
        (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
    rw [hsplit]
    exact isAffineOpen_inf_of_isSeparated' π (𝒰.isAffineOpen (t 0)) (ih (t ∘ Fin.succ))

end Affine

section Main

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) (M : X.Modules)
  (A : Type u) [CommRing A] [Algebra R A]

theorem unit_res {U U' : X.Opens} (h : U' ≤ U)
    (h' : (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ U' ≤ (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ U)
    (m : (OModulePresheaf.ofModules π M).obj U) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app U'
        (M.presheaf.map (homOfLE h).op m)
      = ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M).presheaf.map (homOfLE h').op
          (show (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
              ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj
              ((Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ U) from
            ((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app U m) := by
  have hn := ((Scheme.Modules.pullbackPushforwardAdjunction
    (Limits.pullback.fst π (specMap R A))).unit.app M).mapPresheaf.naturality (homOfLE h).op
  have hx := ConcreteCategory.congr_hom hn m
  refine hx.trans ?_
  have : ((TopologicalSpace.Opens.map (Limits.pullback.fst π (specMap R A)).base).map (homOfLE h)) = homOfLE h' :=
    Subsingleton.elim _ _
  show (((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M).presheaf.map
    ((TopologicalSpace.Opens.map (Limits.pullback.fst π (specMap R A)).base).map (homOfLE h)).op) _ = _
  rw [this]
  rfl

theorem tmul_eq_smul_one_tmul {N : Type u} [AddCommGroup N] [Module R N] (a : A) (n : N) :
    a ⊗ₜ[R] n = a • ((1 : A) ⊗ₜ[R] n) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable [IsSeparated π] (𝒰 : X.OrderedAffineCover)
  (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
    Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))

omit [IsSeparated π] in

def unitAt {i : ℕ} (s : 𝒰.Idx i) :
    (OModulePresheaf.ofModules π M).obj (𝒰.inter s) →+
      (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj ((𝒰.baseChange π A).inter s) :=
  ((OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res
      (𝒰.baseChange_inter_le π A s)).toAddMonoidHom.comp
    (((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app
      (𝒰.inter s)).hom

omit [IsSeparated π] in
theorem unitAt_apply {i : ℕ} (s : 𝒰.Idx i) (m : (OModulePresheaf.ofModules π M).obj (𝒰.inter s)) :
    unitAt π M A 𝒰 s m
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res (𝒰.baseChange_inter_le π A s)
          ((((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app
            (𝒰.inter s)).hom m) :=
  rfl

include htriv in
theorem exists_eSimplex {i : ℕ} (s : 𝒰.Idx i) :
    ∃ e : A ⊗[R] (OModulePresheaf.ofModules π M).obj (𝒰.inter s) ≃ₗ[A]
        (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj ((𝒰.baseChange π A).inter s),
      ∀ m, e ((1 : A) ⊗ₜ[R] m) = unitAt π M A 𝒰 s m := by
  obtain ⟨e, he⟩ := Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial π M htriv
    (𝒰.inter s) (isAffineOpen_inter' π 𝒰 s) A
  refine ⟨e.trans (eqRes (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)) (𝒰.baseChange_inter π A s)),
    fun m => ?_⟩
  exact congrArg ((OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res (𝒰.baseChange_inter_le π A s))
    (he m)

def eSimplex {i : ℕ} (s : 𝒰.Idx i) :
    A ⊗[R] (OModulePresheaf.ofModules π M).obj (𝒰.inter s) ≃ₗ[A]
      (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj ((𝒰.baseChange π A).inter s) :=
  (exists_eSimplex π M A 𝒰 htriv s).choose

theorem eSimplex_one_tmul {i : ℕ} (s : 𝒰.Idx i) (m : (OModulePresheaf.ofModules π M).obj (𝒰.inter s)) :
    eSimplex π M A 𝒰 htriv s ((1 : A) ⊗ₜ[R] m) = unitAt π M A 𝒰 s m :=
  (exists_eSimplex π M A 𝒰 htriv s).choose_spec m

theorem eSimplex_tmul {i : ℕ} (s : 𝒰.Idx i) (a : A) (m : (OModulePresheaf.ofModules π M).obj (𝒰.inter s)) :
    eSimplex π M A 𝒰 htriv s (a ⊗ₜ[R] m) = a • unitAt π M A 𝒰 s m := by
  rw [tmul_eq_smul_one_tmul (R := R) A a m, map_smul, eSimplex_one_tmul]

def E (i : ℕ) :
    A ⊗[R] (OModulePresheaf.ofModules π M).cochain 𝒰 i ≃ₗ[A]
      (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).cochain (𝒰.baseChange π A) i :=
  (TensorProduct.piRight R A A (fun s : 𝒰.Idx i => (OModulePresheaf.ofModules π M).obj (𝒰.inter s))).trans
    (LinearEquiv.piCongrRight fun s : 𝒰.Idx i => eSimplex π M A 𝒰 htriv s)

theorem E_tmul (i : ℕ) (a : A) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 i) (s : 𝒰.Idx i) :
    E π M A 𝒰 htriv i (a ⊗ₜ[R] c) s = a • unitAt π M A 𝒰 s (c s) := by
  change eSimplex π M A 𝒰 htriv s
      (TensorProduct.piRight R A A (fun s : 𝒰.Idx i => (OModulePresheaf.ofModules π M).obj (𝒰.inter s))
        (a ⊗ₜ[R] c) s) = _
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, eSimplex_tmul]

theorem E_one_tmul (i : ℕ) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 i) (s : 𝒰.Idx i) :
    E π M A 𝒰 htriv i ((1 : A) ⊗ₜ[R] c) s = unitAt π M A 𝒰 s (c s) := by
  rw [E_tmul, one_smul]

omit [IsSeparated π] in

theorem unitAt_res {i i' : ℕ} (s : 𝒰.Idx i) (t : 𝒰.Idx i') (h : 𝒰.inter t ≤ 𝒰.inter s)
    (hA : (𝒰.baseChange π A).inter t ≤ (𝒰.baseChange π A).inter s)
    (m : (OModulePresheaf.ofModules π M).obj (𝒰.inter s)) :
    unitAt π M A 𝒰 t ((OModulePresheaf.ofModules π M).res h m)
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res hA (unitAt π M A 𝒰 s m) := by
  rw [unitAt_apply, unitAt_apply, OModulePresheaf.res_res]
  have h' : (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter t ≤ (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter s :=
    Scheme.Hom.preimage_mono _ h
  have key := unit_res π M A h h' m

  have : (((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app
        (𝒰.inter t)).hom ((OModulePresheaf.ofModules π M).res h m)
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res h'
          ((((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app
              (𝒰.inter s)).hom m) := by
    exact key
  rw [this, OModulePresheaf.res_res]

theorem E_d_one_tmul (i : ℕ) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 i) :
    E π M A 𝒰 htriv (i + 1) ((1 : A) ⊗ₜ[R] (OModulePresheaf.ofModules π M).d 𝒰 i c)
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).d (𝒰.baseChange π A) i
          (E π M A 𝒰 htriv i ((1 : A) ⊗ₜ[R] c)) := by
  funext t
  rw [E_one_tmul, OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, E_one_tmul]
  congr 1

  exact unitAt_res π M A 𝒰 (𝒰.face t j) t (𝒰.inter_le_inter_face t j)
    ((𝒰.baseChange π A).inter_le_inter_face t j) (c (𝒰.face t j))

theorem E_d (i : ℕ) :
    (E π M A 𝒰 htriv (i + 1)).toLinearMap ∘ₗ ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).d (𝒰.baseChange π A) i
        ∘ₗ (E π M A 𝒰 htriv i).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a c =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.baseChange_tmul]
    rw [tmul_eq_smul_one_tmul (R := R) A a, tmul_eq_smul_one_tmul (R := R) A a c, map_smul, map_smul, map_smul,
      E_d_one_tmul]

end Main

end AlgebraicGeometry.OModulePresheaf.CechBaseChange

end

open AlgebraicGeometry.OModulePresheaf.CechBaseChange in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) [IsSeparated π]
    (𝒰 : X.OrderedAffineCover) (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (A : Type u) [CommRing A] [Algebra R A] :
    ∃ E : ∀ i : ℕ, A ⊗[R] (OModulePresheaf.ofModules π M).cochain 𝒰 i ≃ₗ[A]
        (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).cochain (𝒰.baseChange π A) i,
      (∀ i : ℕ, (E (i + 1)).toLinearMap ∘ₗ ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A
        = (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) i
          ∘ₗ (E i).toLinearMap) ∧
      (∀ (i : ℕ) (a : A) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 i) (s : 𝒰.Idx i),
        E i (a ⊗ₜ[R] c) s
          = a • (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).res
              (𝒰.baseChange_inter_le π A s)
              ((((Scheme.Modules.pullbackPushforwardAdjunction
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app
                (𝒰.inter s)).hom (c s))) :=
  ⟨E π M A 𝒰 htriv, E_d π M A 𝒰 htriv, E_tmul π M A 𝒰 htriv⟩

end S_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial (solution)
