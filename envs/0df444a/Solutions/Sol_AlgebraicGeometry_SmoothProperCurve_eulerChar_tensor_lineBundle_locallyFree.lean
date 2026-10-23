-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.eulerChar_tensor_lineBundle_locallyFree
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-22T17:19:48.099825+00:00
-- url     : https://prove2.me/submissions/773d211e-de1d-4f25-9402-0b8e901e5db0

import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_CurveDegreeTests
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_and_isQuasicoherent_of_isLocallyFreeOfRank
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry

-- The cochain equivalences below are adapted from the accepted proof
-- of OModulePresheaf.cechFinite_toOrderedAffineCover_iff, submission
-- 5c49132a-a2f5-591e-826a-bb5f108af925 (FLT repository, pinned source in scout.json).
namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) {c : X ⟶ Spec (.of R)}
variable (F : OModulePresheaf c)

namespace Scheme
namespace TwoAffineOpenCover

local notation "K" => 𝒱.toOrderedAffineCover

private def _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.idx0 (i : ULift.{u} (Fin 2)) : (K).Idx 0 := ⟨fun _ => i, fun a b h => absurd h (by omega)⟩


private def _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.idx01 : (K).Idx 1 :=
  ⟨fun j => ⟨j⟩, fun a b h => by
    change (⟨a⟩ : ULift.{u} (Fin 2)) < ⟨b⟩
    exact h⟩

theorem idx0_val (i : ULift.{u} (Fin 2)) (j : Fin 1) : (𝒱.idx0 i).1 j = i := rfl

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.eq_idx0 (s : (K).Idx 0) : s = 𝒱.idx0 (s.1 0) :=
  Subtype.ext (funext fun j => by fin_cases j; rfl)


def idxZeroEquiv : (K).Idx 0 ≃ ULift.{u} (Fin 2) where
  toFun s := s.1 0
  invFun := 𝒱.idx0
  left_inv s := (𝒱.eq_idx0 s).symm
  right_inv _ := rfl

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.eq_idx01 (s : (K).Idx 1) : s = 𝒱.idx01 := by
  apply Subtype.ext; funext j
  have hs := s.2
  have h01 : s.1 0 < s.1 1 := hs (by decide)

  have hlt : (s.1 0).down < (s.1 1).down := h01
  have h0 : (s.1 0).down = 0 := by omega
  have h1 : (s.1 1).down = 1 := by omega
  fin_cases j
  · exact ULift.ext _ _ h0
  · exact ULift.ext _ _ h1

scoped instance uniqueIdxOne : Unique ((K).Idx 1) where
  default := 𝒱.idx01
  uniq := 𝒱.eq_idx01

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.isEmpty_Idx_add_two (i : ℕ) : IsEmpty ((K).Idx (i + 2)) := by
  rw [Scheme.OrderedAffineCover.Idx, isEmpty_subtype]
  intro s hs
  have := Fintype.card_le_of_injective s hs.injective
  simp only [Fintype.card_fin] at this
  change i + 2 + 1 ≤ Fintype.card (ULift.{u} (Fin 2)) at this
  simp at this


private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.inter_idx0 (i : ULift.{u} (Fin 2)) : (K).inter (𝒱.idx0 i) = (K).U i :=
  le_antisymm (iInf_le _ 0) (le_iInf fun _ => le_rfl)

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.inter_idx01 : (K).inter 𝒱.idx01 = 𝒱.U0 ⊓ 𝒱.U1 :=
  le_antisymm (le_inf (iInf_le _ 0) (iInf_le _ 1))
    (le_iInf fun j => by fin_cases j <;> [exact inf_le_left; exact inf_le_right])

end Scheme.TwoAffineOpenCover

namespace OModulePresheaf

private def _root_.AlgebraicGeometry.OModulePresheaf.resEq {U U' : X.Opens} (h : U = U') : F.obj U' ≃ₗ[R] F.obj U where
  toLinearMap := F.res h.le
  invFun := F.res h.ge
  left_inv x := by
    show F.res h.ge (F.res h.le x) = x
    rw [F.res_res]; exact F.res_refl_apply _ x
  right_inv x := by
    show F.res h.le (F.res h.ge x) = x
    rw [F.res_res]; exact F.res_refl_apply _ x

theorem resEq_apply {U U' : X.Opens} (h : U = U') (x : F.obj U') : F.resEq h x = F.res h.le x := rfl

theorem res_resEq {U U' W : X.Opens} (h : U = U') (hW : W ≤ U) (x : F.obj U') :
    F.res hW (F.resEq h x) = F.res (hW.trans h.le) x := by
  rw [resEq_apply, F.res_res]

local notation "K" => 𝒱.toOrderedAffineCover

private def _root_.AlgebraicGeometry.OModulePresheaf.pick (p : F.obj 𝒱.U0 × F.obj 𝒱.U1) : ∀ i : ULift.{u} (Fin 2), F.obj ((K).U i)
  | ⟨⟨0, _⟩⟩ => p.1
  | ⟨⟨1, _⟩⟩ => p.2

theorem pick_zero (p : F.obj 𝒱.U0 × F.obj 𝒱.U1) : F.pick 𝒱 p ⟨0⟩ = p.1 := rfl
theorem pick_one (p : F.obj 𝒱.U0 × F.obj 𝒱.U1) : F.pick 𝒱 p ⟨1⟩ = p.2 := rfl

private theorem _root_.AlgebraicGeometry.OModulePresheaf.pick_add (p q : F.obj 𝒱.U0 × F.obj 𝒱.U1) (i : ULift.{u} (Fin 2)) :
    F.pick 𝒱 (p + q) i = F.pick 𝒱 p i + F.pick 𝒱 q i := by
  rcases i with ⟨⟨_ | _ | n, hn⟩⟩
  · rfl
  · rfl
  · omega

private theorem _root_.AlgebraicGeometry.OModulePresheaf.pick_smul (r : R) (p : F.obj 𝒱.U0 × F.obj 𝒱.U1) (i : ULift.{u} (Fin 2)) :
    F.pick 𝒱 (r • p) i = r • F.pick 𝒱 p i := by
  rcases i with ⟨⟨_ | _ | n, hn⟩⟩
  · rfl
  · rfl
  · omega


private def _root_.AlgebraicGeometry.OModulePresheaf.pickₗ (i : ULift.{u} (Fin 2)) : F.obj 𝒱.U0 × F.obj 𝒱.U1 →ₗ[R] F.obj ((K).U i) where
  toFun p := F.pick 𝒱 p i
  map_add' p q := F.pick_add 𝒱 p q i
  map_smul' r p := F.pick_smul 𝒱 r p i


private def _root_.AlgebraicGeometry.OModulePresheaf.cochainZeroTo : F.cochain K 0 →ₗ[R] F.obj 𝒱.U0 × F.obj 𝒱.U1 :=
  ((F.resEq (𝒱.inter_idx0 ⟨0⟩)).symm.toLinearMap.comp (LinearMap.proj (𝒱.idx0 ⟨0⟩))).prod
    ((F.resEq (𝒱.inter_idx0 ⟨1⟩)).symm.toLinearMap.comp (LinearMap.proj (𝒱.idx0 ⟨1⟩)))


private def _root_.AlgebraicGeometry.OModulePresheaf.cochainZeroOf : F.obj 𝒱.U0 × F.obj 𝒱.U1 →ₗ[R] F.cochain K 0 :=
  LinearMap.pi fun s => (F.res ((K).inter_le s 0)).comp (F.pickₗ 𝒱 (s.1 0))

theorem cochainZeroTo_apply (f : F.cochain K 0) :
    F.cochainZeroTo 𝒱 f
      = (F.res (𝒱.inter_idx0 ⟨0⟩).ge (f (𝒱.idx0 ⟨0⟩)), F.res (𝒱.inter_idx0 ⟨1⟩).ge (f (𝒱.idx0 ⟨1⟩))) :=
  rfl

theorem cochainZeroOf_apply (p : F.obj 𝒱.U0 × F.obj 𝒱.U1) (s : (K).Idx 0) :
    F.cochainZeroOf 𝒱 p s = F.res ((K).inter_le s 0) (F.pick 𝒱 p (s.1 0)) := rfl

private theorem _root_.AlgebraicGeometry.OModulePresheaf.cochainZeroTo_cochainZeroOf (p : F.obj 𝒱.U0 × F.obj 𝒱.U1) :
    F.cochainZeroTo 𝒱 (F.cochainZeroOf 𝒱 p) = p := by
  rw [cochainZeroTo_apply]
  refine Prod.ext ?_ ?_
  · show F.res _ (F.res _ (F.pick 𝒱 p ⟨0⟩)) = p.1
    rw [F.res_res, pick_zero]; exact F.res_refl_apply _ _
  · show F.res _ (F.res _ (F.pick 𝒱 p ⟨1⟩)) = p.2
    rw [F.res_res, pick_one]; exact F.res_refl_apply _ _

private theorem _root_.AlgebraicGeometry.OModulePresheaf.cochainZeroOf_cochainZeroTo (f : F.cochain K 0) :
    F.cochainZeroOf 𝒱 (F.cochainZeroTo 𝒱 f) = f := by
  funext s
  rw [cochainZeroOf_apply, cochainZeroTo_apply]
  obtain ⟨i, rfl⟩ : ∃ i, s = 𝒱.idx0 i := ⟨_, 𝒱.eq_idx0 s⟩
  rcases i with ⟨⟨_ | _ | n, hn⟩⟩
  · show F.res _ (F.res _ (f _)) = f _
    rw [F.res_res]; exact F.res_refl_apply _ _
  · show F.res _ (F.res _ (f _)) = f _
    rw [F.res_res]; exact F.res_refl_apply _ _
  · omega


private def _root_.AlgebraicGeometry.OModulePresheaf.cochainZeroEquiv : F.cochain K 0 ≃ₗ[R] F.obj 𝒱.U0 × F.obj 𝒱.U1 :=
  LinearEquiv.ofLinear (F.cochainZeroTo 𝒱) (F.cochainZeroOf 𝒱)
    (LinearMap.ext (F.cochainZeroTo_cochainZeroOf 𝒱)) (LinearMap.ext (F.cochainZeroOf_cochainZeroTo 𝒱))


private theorem _root_.AlgebraicGeometry.OModulePresheaf.finite_HSucc_succ (i : ℕ) : Module.Finite R (F.HSucc K (i + 1)) := by
  haveI := 𝒱.isEmpty_Idx_add_two i
  haveI : Subsingleton (F.cochain K (i + 1 + 1)) := inferInstance
  haveI : Subsingleton (F.HSucc K (i + 1)) := Quot.Subsingleton
  exact Module.Finite.of_finite

end OModulePresheaf

end AlgebraicGeometry

end

noncomputable section

namespace TwoChartCech

universe uR uK uC

variable {R : Type uR} [CommRing R]
variable {K0 K1 : Type uK} [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
variable {C0 C1 : Type uK} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem kerMap_bijective_of_bijective (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0)
    (ι1 : K1 →ₗ[R] C1) (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (h0 : Function.Bijective ι0)
    (h1 : Function.Injective ι1) : Function.Bijective (kerMap dK d ι0 ι1 comm) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply h0.1
    exact congrArg Subtype.val hxy
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := h0.2 y
    have hx : x ∈ LinearMap.ker dK := by
      rw [LinearMap.mem_ker] at hy ⊢
      apply h1
      rw [map_zero, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply, hy]
    exact ⟨⟨x, hx⟩, rfl⟩

theorem cokerMap_bijective_of_bijective (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0)
    (ι1 : K1 →ₗ[R] C1) (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (h0 : Function.Surjective ι0)
    (h1 : Function.Bijective ι1) : Function.Bijective (cokerMap dK d ι0 ι1 comm) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker] at hq
    change Submodule.Quotient.mk (ι1 y) = 0 at hq
    rw [Submodule.Quotient.mk_eq_zero] at hq ⊢
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hq
    obtain ⟨x, rfl⟩ := h0 c
    refine ⟨x, h1.1 ?_⟩
    rw [← hc, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply]
  · intro q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨y, rfl⟩ := h1.2 c
    exact ⟨Submodule.Quotient.mk y, rfl⟩

end TwoChartCech

namespace AlgebraicGeometry

universe u

open CategoryTheory Opposite

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) {c : X ⟶ Spec (.of R)}
variable (F : OModulePresheaf c)

namespace Scheme
namespace TwoAffineOpenCover

local notation "K" => 𝒱.toOrderedAffineCover

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.face_idx01_zero : (K).face 𝒱.idx01 0 = 𝒱.idx0 ⟨1⟩ :=
  Subtype.ext (funext fun j => by fin_cases j; rfl)

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.face_idx01_one : (K).face 𝒱.idx01 1 = 𝒱.idx0 ⟨0⟩ :=
  Subtype.ext (funext fun j => by fin_cases j; rfl)

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.inter_le_inf (s : (K).Idx 1) : (K).inter s ≤ 𝒱.U0 ⊓ 𝒱.U1 := by
  rw [𝒱.eq_idx01 s, 𝒱.inter_idx01]

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.inf_le_inter (s : (K).Idx 1) : 𝒱.U0 ⊓ 𝒱.U1 ≤ (K).inter s := by
  rw [𝒱.eq_idx01 s, 𝒱.inter_idx01]

end Scheme.TwoAffineOpenCover

namespace OModulePresheaf

local notation "K" => 𝒱.toOrderedAffineCover

private theorem _root_.AlgebraicGeometry.OModulePresheaf.res_congr_idx {i : ℕ} (co : F.cochain K i) {s s' : (K).Idx i} (e : s = s') {W : X.Opens}
    (p : W ≤ (K).inter s) (p' : W ≤ (K).inter s') : F.res p (co s) = F.res p' (co s') := by
  subst e; rfl


private def _root_.AlgebraicGeometry.OModulePresheaf.cochainOneTo : F.cochain K 1 →ₗ[R] F.obj (𝒱.U0 ⊓ 𝒱.U1) :=
  (F.res (𝒱.inf_le_inter 𝒱.idx01)).comp (LinearMap.proj 𝒱.idx01)


private def _root_.AlgebraicGeometry.OModulePresheaf.cochainOneOf : F.obj (𝒱.U0 ⊓ 𝒱.U1) →ₗ[R] F.cochain K 1 :=
  LinearMap.pi fun s => F.res (𝒱.inter_le_inf s)

theorem cochainOneTo_apply (co : F.cochain K 1) :
    F.cochainOneTo 𝒱 co = F.res (𝒱.inf_le_inter 𝒱.idx01) (co 𝒱.idx01) := rfl

theorem cochainOneOf_apply (x : F.obj (𝒱.U0 ⊓ 𝒱.U1)) (s : (K).Idx 1) :
    F.cochainOneOf 𝒱 x s = F.res (𝒱.inter_le_inf s) x := rfl

private theorem _root_.AlgebraicGeometry.OModulePresheaf.cochainOneTo_cochainOneOf (x : F.obj (𝒱.U0 ⊓ 𝒱.U1)) :
    F.cochainOneTo 𝒱 (F.cochainOneOf 𝒱 x) = x := by
  rw [cochainOneTo_apply, cochainOneOf_apply, F.res_res]
  exact F.res_refl_apply _ x

private theorem _root_.AlgebraicGeometry.OModulePresheaf.cochainOneOf_cochainOneTo (co : F.cochain K 1) :
    F.cochainOneOf 𝒱 (F.cochainOneTo 𝒱 co) = co := by
  funext s
  rw [cochainOneOf_apply, cochainOneTo_apply, F.res_res]
  have hs := 𝒱.eq_idx01 s
  subst hs
  exact F.res_refl_apply _ _


private def _root_.AlgebraicGeometry.OModulePresheaf.cochainOneEquiv : F.cochain K 1 ≃ₗ[R] F.obj (𝒱.U0 ⊓ 𝒱.U1) :=
  LinearEquiv.ofLinear (F.cochainOneTo 𝒱) (F.cochainOneOf 𝒱)
    (LinearMap.ext (F.cochainOneTo_cochainOneOf 𝒱)) (LinearMap.ext (F.cochainOneOf_cochainOneTo 𝒱))


private theorem _root_.AlgebraicGeometry.OModulePresheaf.cochainOneTo_d (co : F.cochain K 0) :
    F.cochainOneTo 𝒱 (F.d K 0 co) = (F.twoChartSections 𝒱).cechDiff (F.cochainZeroTo 𝒱 co) := by
  rw [cochainOneTo_apply, F.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, ← sub_eq_add_neg,
    map_sub]
  rw [TwoChartCech.Sections.cechDiff_apply, cochainZeroTo_apply]

  change F.res _ (F.res _ (co ((K).face 𝒱.idx01 0))) - F.res _ (F.res _ (co ((K).face 𝒱.idx01 1)))
    = F.res (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1) (F.res _ (co (𝒱.idx0 ⟨1⟩)))
      - F.res (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0) (F.res _ (co (𝒱.idx0 ⟨0⟩)))
  rw [F.res_res, F.res_res, F.res_res, F.res_res]
  rw [F.res_congr_idx 𝒱 co (𝒱.face_idx01_zero) _
      ((inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1).trans (𝒱.inter_idx0 ⟨1⟩).ge),
    F.res_congr_idx 𝒱 co (𝒱.face_idx01_one) _
      ((inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0).trans (𝒱.inter_idx0 ⟨0⟩).ge)]

private theorem _root_.AlgebraicGeometry.OModulePresheaf.cechDiff_comp_cochainZeroEquiv :
    (F.twoChartSections 𝒱).cechDiff ∘ₗ (F.cochainZeroEquiv 𝒱).toLinearMap
      = (F.cochainOneEquiv 𝒱).toLinearMap ∘ₗ F.d K 0 := by
  apply LinearMap.ext
  intro co
  exact (F.cochainOneTo_d 𝒱 co).symm


private def _root_.AlgebraicGeometry.OModulePresheaf.H0Equiv : F.H0 K ≃ₗ[R] (F.twoChartSections 𝒱).H0 :=
  LinearEquiv.ofBijective _
    (TwoChartCech.kerMap_bijective_of_bijective (F.d K 0) (F.twoChartSections 𝒱).cechDiff
      (F.cochainZeroEquiv 𝒱).toLinearMap (F.cochainOneEquiv 𝒱).toLinearMap
      (F.cechDiff_comp_cochainZeroEquiv 𝒱) (F.cochainZeroEquiv 𝒱).bijective
      (F.cochainOneEquiv 𝒱).injective)

private theorem _root_.AlgebraicGeometry.OModulePresheaf.d_one_eq_zero : F.d K 1 = 0 := by
  haveI := 𝒱.isEmpty_Idx_add_two 0
  apply LinearMap.ext
  intro co
  exact Subsingleton.elim _ _

private theorem _root_.AlgebraicGeometry.OModulePresheaf.ker_d_one_eq_top : LinearMap.ker (F.d K 1) = ⊤ := by
  rw [F.d_one_eq_zero 𝒱, LinearMap.ker_zero]


private def _root_.AlgebraicGeometry.OModulePresheaf.HSuccZeroEquivCoker : F.HSucc K 0 ≃ₗ[R] (F.cochain K 1 ⧸ LinearMap.range (F.d K 0)) :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofTop _ (F.ker_d_one_eq_top 𝒱)) (by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy
    · intro y hy
      refine ⟨⟨y, by rw [F.ker_d_one_eq_top 𝒱]; trivial⟩, hy, rfl⟩)


private def _root_.AlgebraicGeometry.OModulePresheaf.HSuccZeroEquiv : F.HSucc K 0 ≃ₗ[R] (F.twoChartSections 𝒱).H1 :=
  (F.HSuccZeroEquivCoker 𝒱).trans (LinearEquiv.ofBijective _
    (TwoChartCech.cokerMap_bijective_of_bijective (F.d K 0) (F.twoChartSections 𝒱).cechDiff
      (F.cochainZeroEquiv 𝒱).toLinearMap (F.cochainOneEquiv 𝒱).toLinearMap
      (F.cechDiff_comp_cochainZeroEquiv 𝒱) (F.cochainZeroEquiv 𝒱).surjective
      (F.cochainOneEquiv 𝒱).bijective))


theorem cechFinite_toOrderedAffineCover_iff' :
    F.CechFinite K ↔
      Module.Finite R (F.twoChartSections 𝒱).H0 ∧ Module.Finite R (F.twoChartSections 𝒱).H1 := by
  constructor
  · rintro ⟨h0, hS⟩
    exact ⟨Module.Finite.equiv (F.H0Equiv 𝒱), by
      haveI := hS 0; exact Module.Finite.equiv (F.HSuccZeroEquiv 𝒱)⟩
  · rintro ⟨h0, h1⟩
    refine ⟨Module.Finite.equiv (F.H0Equiv 𝒱).symm, fun i => ?_⟩
    cases i with
    | zero => exact Module.Finite.equiv (F.HSuccZeroEquiv 𝒱).symm
    | succ i => exact F.finite_HSucc_succ 𝒱 i

end OModulePresheaf

end AlgebraicGeometry

namespace AlgebraicGeometry.OModulePresheaf
universe u

lemma eulerChar_toOrderedAffineCover {R : Type u} [CommRing R] {X : Scheme.{u}}
    {c : X ⟶ Spec (.of R)} (F : OModulePresheaf c) (𝒱 : X.TwoAffineOpenCover) :
    F.eulerChar 𝒱.toOrderedAffineCover =
      (Module.finrank R (F.twoChartSections 𝒱).H0 : ℤ) -
        Module.finrank R (F.twoChartSections 𝒱).H1 := by
  have hc : Fintype.card 𝒱.toOrderedAffineCover.ι = 2 := by
    exact (Fintype.card_congr (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2)).trans (Fintype.card_fin 2)
  rw [eulerChar_def, hc]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul,
    pow_one, neg_one_mul, cechFinrank_zero, cechFinrank_succ]
  rw [(F.H0Equiv 𝒱).finrank_eq, (F.HSuccZeroEquiv 𝒱).finrank_eq]
  rfl

end AlgebraicGeometry.OModulePresheaf



set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TensorProduct
namespace PhilipponTensorEuler

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))

lemma euler_affHom [IsSeparated c] {F G : OModulePresheaf c}
    (f : OModulePresheaf.AffHom F G)
    (hf : ∀ U : X.affineOpens, Function.Bijective (f.app U))
    (𝒰 : X.OrderedAffineCover) : F.eulerChar 𝒰 = G.eulerChar 𝒰 := by
  obtain ⟨⟨e0⟩, hs⟩ := f.nonempty_H0_equiv_and_HSucc_equiv_of_bijective hf 𝒰
  have h : ∀ n, F.cechFinrank 𝒰 n = G.cechFinrank 𝒰 n := by
    intro n
    cases n with
    | zero => exact e0.finrank_eq
    | succ n => exact (hs n).some.finrank_eq
  unfold OModulePresheaf.eulerChar
  exact Finset.sum_congr rfl fun n _ => by rw [h n]

lemma euler_iso (𝒰 : X.TwoAffineOpenCover) {M N : X.Modules} (e : M ≅ N) :
    (OModulePresheaf.ofModules c M).eulerChar 𝒰.toOrderedAffineCover =
      (OModulePresheaf.ofModules c N).eulerChar 𝒰.toOrderedAffineCover := by
  rw [OModulePresheaf.eulerChar_toOrderedAffineCover,
    OModulePresheaf.eulerChar_toOrderedAffineCover]
  obtain ⟨𝒱, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso c c
      (Iso.refl X) (by simp) 𝒰 N M
      (e ≪≫ ((Scheme.Modules.pullbackId X).app N).symm)
  have h0' : 𝒱.U0 = 𝒰.U0 := by simpa using h0
  have h1' : 𝒱.U1 = 𝒰.U1 := by simpa using h1
  have hV : 𝒱 = 𝒰 := by cases 𝒱; cases 𝒰; simp_all
  subst 𝒱
  exact congrArg₂ (fun a b : ℕ => (a : ℤ) - b) e0.finrank_eq e1.finrank_eq

variable (M N : X.Modules)

-- The natural section map is the same tensor comparison used in the accepted
-- monoidalV2 cohomology proof, specialized to an arbitrary affine cover.
def tensorApp (U : X.Opens) :
    ((OModulePresheaf.ofModules c M).twist N).obj U →ₗ[R]
      (OModulePresheaf.ofModules c (M ⊗ N)).obj U where
  toFun t := TensorProduct.lift (Scheme.Modules.tensorSectionsBilin M N U) t
  map_add' s t := map_add _ s t
  map_smul' r t := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    change TensorProduct.lift (Scheme.Modules.tensorSectionsBilin M N U)
      (algebraMap R Γ(X, U) r • t) =
        algebraMap R Γ(X, U) r • TensorProduct.lift (Scheme.Modules.tensorSectionsBilin M N U) t
    exact LinearMap.map_smul _ _ _

lemma tensorApp_tmul (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) :
    tensorApp c M N U (x ⊗ₜ[Γ(X, U)] y) = Scheme.Modules.tensorSections x y := rfl

lemma tensorApp_res {U V : X.Opens} (h : U ≤ V)
    (t : ((OModulePresheaf.ofModules c M).twist N).obj V) :
    tensorApp c M N U (((OModulePresheaf.ofModules c M).twist N).res h t) =
      (OModulePresheaf.ofModules c (M ⊗ N)).res h (tensorApp c M N V t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [OModulePresheaf.twist_res_tmul, tensorApp_tmul, tensorApp_tmul]
    exact (Scheme.Modules.map_homOfLE_tensorSections h x y).symm
  | add t t' ht ht' => simp only [map_add, ht, ht']

def tensorAffHom : OModulePresheaf.AffHom
    ((OModulePresheaf.ofModules c M).twist N) (OModulePresheaf.ofModules c (M ⊗ N)) where
  app U := tensorApp c M N U
  app_smul U a t := map_smul (TensorProduct.lift (Scheme.Modules.tensorSectionsBilin M N U)) a t
  naturality h := LinearMap.ext (tensorApp_res c M N h)

lemma euler_twist_eq_tensor [IsSeparated c]
    (hM : (OModulePresheaf.ofModules c M).IsQuasicoherent)
    (hN : (OModulePresheaf.ofModules c N).IsQuasicoherent)
    (𝒰 : X.OrderedAffineCover) :
    ((OModulePresheaf.ofModules c M).twist N).eulerChar 𝒰 =
      (OModulePresheaf.ofModules c (M ⊗ N)).eulerChar 𝒰 := by
  exact euler_affHom c (tensorAffHom c M N)
    (fun U => Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2 c hM hN U) 𝒰

end PhilipponTensorEuler

end



set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace Polynomial
open PhilipponTensorEuler
namespace PhilipponVectorBundleEuler

lemma eval_one_sub_eval_zero (p : Polynomial ℚ) (hp : p.natDegree ≤ 1) :
    p.eval 1 - p.eval 0 = p.coeff 1 := by
  obtain ⟨a, b, rfl⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hp
  simp

lemma supported_top {R : Type u} [CommRing R] {X : Scheme.{u}}
    {c : X ⟶ Spec (.of R)} (F : OModulePresheaf c) : F.SupportedIn ⊤ := by
  intro U hU
  have hUe : (U.1 : Set X) = ∅ := by simpa [Closeds.coe_top, Set.inter_univ] using hU
  have hbot : U.1 = ⊥ := by ext x; simp [hUe]
  have hs : Subsingleton Γ(X, U.1) := by rw [hbot]; infer_instance
  refine ⟨fun x y => ?_⟩
  have h1 : (1 : Γ(X, U.1)) = 0 := Subsingleton.elim _ _
  rw [← one_smul Γ(X, U.1) x, ← one_smul Γ(X, U.1) y, h1, zero_smul, zero_smul]

lemma generic_rank (K : Type u) [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsIntegral C] (d : ℕ) (E : C.Modules)
    (hE : Scheme.Modules.IsLocallyFreeOfRank d E) :
    ∃ U : C.affineOpens, ∃ p : PrimeSpectrum Γ(C, U.1), p.asIdeal = ⊥ ∧
      Module.rankAtStalk (R := Γ(C, U.1)) ((OModulePresheaf.ofModules c E).obj U.1) p = d := by
  let x : C := Classical.choice inferInstance
  obtain ⟨V, hxV, e, he⟩ := hE.exists_basis x
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  obtain ⟨b, _⟩ := he U hUV
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI : IsDomain Γ(C, U) := IsIntegral.component_integral U
  let p : PrimeSpectrum Γ(C, U) := ⟨⊥, Ideal.bot_prime⟩
  refine ⟨⟨U,hU⟩, p, rfl, ?_⟩
  haveI : Module.Free Γ(C, U) Γ(E, U) := Module.Free.of_basis b
  change Module.rankAtStalk (R := Γ(C, U)) Γ(E, U) p = d
  rw [Module.rankAtStalk_eq_finrank_of_free]
  simpa using Module.finrank_eq_card_basis b

end PhilipponVectorBundleEuler

open PhilipponVectorBundleEuler

theorem solution
    (K : Type u) [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (𝒰 : C.TwoAffineOpenCover)
    (d : ℕ) (E : C.Modules)
    (hE : ∀ x : C, ∃ U : C.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj E ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin d))))
    (N : C.Modules) (hN : Scheme.Modules.IsInvertible N) :
    let χ : C.Modules → ℤ := fun M =>
      (Module.finrank K (𝒰.sectionsOf c M).H0 : ℤ) -
        Module.finrank K (𝒰.sectionsOf c M).H1
    χ (N ⊗ E) = (d : ℤ) * (χ N - χ (𝟙_ C.Modules)) + χ E := by
  let χ (M : C.Modules) := (OModulePresheaf.ofModules c M).eulerChar 𝒰.toOrderedAffineCover
  suffices hχ : χ (N ⊗ E) = (d : ℤ) * (χ N - χ (𝟙_ C.Modules)) + χ E by
    simpa only [χ, OModulePresheaf.eulerChar_toOrderedAffineCover,
      OModulePresheaf.ofModules_twoChartSections] using hχ
  have hEf : Scheme.Modules.IsLocallyFreeOfRank d E := ⟨hE⟩
  obtain ⟨hEc, hEq⟩ := OModulePresheaf.isCoherent_and_isQuasicoherent_of_isLocallyFreeOfRank c d E hEf
  let O : C.Modules := 𝟙_ C.Modules
  have hO := Scheme.Modules.isInvertible_unit C
  have hOc := OModulePresheaf.isCoherent_ofModules_of_locallyTrivial c O hO.exists_trivialization
  have hOq := OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial c O hO.exists_trivialization
  have hNq := OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial c N hN.exists_trivialization
  have hdim : topologicalKrullDim C ≤ 1 := SmoothOfRelativeDimension.topologicalKrullDim_le c 1
  have htop : topologicalKrullDim ((⊤ : Closeds C) : Set C) ≤ 1 :=
    (Topology.IsInducing.topologicalKrullDim_le (Topology.IsEmbedding.subtypeVal.isInducing)).trans hdim
  obtain ⟨q, hqdeg, hqχ⟩ := OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq
    c 𝒰.toOrderedAffineCover O hOc hOq ⊤ (supported_top _) 1 htop N hN.exists_trivialization
  have hq : ∀ m : ℕ, ((OModulePresheaf.ofModules c (N.tensorPow m)).eulerChar 𝒰.toOrderedAffineCover : ℚ) = q.eval (m : ℚ) := by
    intro m
    rw [← euler_iso c 𝒰 (λ_ (N.tensorPow m))]
    exact hqχ m
  obtain ⟨p, hpdeg, hpχ⟩ := OModulePresheaf.exists_polynomial_forall_eulerChar_twist_tensorPow_eq
    c 𝒰.toOrderedAffineCover (OModulePresheaf.ofModules c E) hEc hEq ⊤ (supported_top _) 1 htop N hN.exists_trivialization
  obtain ⟨U, z, hz, hrank⟩ := generic_rank K c d E hEf
  have hslope := OModulePresheaf.coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq
    c 𝒰.toOrderedAffineCover N hN.exists_trivialization 1 hdim q hq
    (OModulePresheaf.ofModules c E) hEc hEq p hpχ U z hz
  rw [hrank] at hslope
  have hp0 : p.eval 0 = (χ E : ℚ) := by
    have h := hpχ 0
    simp only [Scheme.Modules.tensorPow_zero] at h
    rw [euler_twist_eq_tensor c E O hEq hOq] at h
    rw [euler_iso c 𝒰 (ρ_ E)] at h
    simpa [χ] using h.symm
  have hp1 : p.eval 1 = (χ (N ⊗ E) : ℚ) := by
    have h := hpχ 1
    have hpowN : Scheme.Modules.IsInvertible (N.tensorPow 1) := by
      refine ⟨fun x => ?_⟩
      obtain ⟨U, hx, ⟨e⟩⟩ := hN.exists_trivialization x
      exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso (Scheme.Modules.tensorPowOneIso N) ≪≫ e⟩⟩
    have hpowq := OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial c (N.tensorPow 1)
      hpowN.exists_trivialization
    rw [euler_twist_eq_tensor c E (N.tensorPow 1) hEq hpowq] at h
    rw [euler_iso c 𝒰 ((Iso.refl E ⊗ᵢ Scheme.Modules.tensorPowOneIso N) ≪≫ (β_ E N))] at h
    simpa [χ] using h.symm
  have hq0 : q.eval 0 = (χ O : ℚ) := by simpa [χ, O] using (hq 0).symm
  have hq1 : q.eval 1 = (χ N : ℚ) := by
    have h := hq 1
    rw [euler_iso c 𝒰 (Scheme.Modules.tensorPowOneIso N)] at h
    simpa [χ] using h.symm
  have hs := eval_one_sub_eval_zero p hpdeg
  have ht := eval_one_sub_eval_zero q hqdeg
  rw [hp1,hp0] at hs
  rw [hq1,hq0] at ht
  exact_mod_cast (show (χ (N ⊗ E) : ℚ) = (d : ℚ) * ((χ N : ℚ) - (χ O : ℚ)) + (χ E : ℚ) by nlinarith)

end
