-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.FiniteBySections.exists_polynomial_coeff_pos_forall_eulerChar_tensorPow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/87bf65a2-4558-5c32-a921-170d1daae287

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_mul_pow_le_cechFinrank_zero_tensorPow
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_exists_polynomial_coeff_pos_forall_eulerChar_tensorPow_eq
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.SubQuot.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Filter"

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace P2mAmplePos

section Transfer

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

variable (F G : OModulePresheaf π) (K : V.OrderedAffineCover)
  (e : ∀ U : V.Opens, F.obj U →+ G.obj U)
  (hnat : ∀ (U U' : V.Opens) (h : U ≤ U') (x : F.obj U'), e U (F.res h x) = G.res h (e U' x))

def ec (i : ℕ) : F.cochain K i →+ G.cochain K i where
  toFun c s := e (K.inter s) (c s)
  map_zero' := funext fun s => by simp
  map_add' c c' := funext fun s => by simp

theorem ec_apply (i : ℕ) (c : F.cochain K i) (s : K.Idx i) : ec F G K e i c s = e (K.inter s) (c s) := rfl

include hnat in
theorem d_ec (i : ℕ) (c : F.cochain K i) : G.d K i (ec F G K e i c) = ec F G K e (i + 1) (F.d K i c) := by
  funext s
  rw [OModulePresheaf.d_apply, ec_apply, OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, ec_apply, hnat]

include hnat in

theorem subsingleton_HSucc_of_bijective (hbij : ∀ (i : ℕ) (s : K.Idx i), Function.Bijective (e (K.inter s)))
    (i : ℕ) [hG : Subsingleton (G.HSucc K i)] : Subsingleton (F.HSucc K i) := by
  rw [Submodule.Quotient.subsingleton_iff] at hG ⊢
  rw [eq_top_iff]
  rintro ⟨c, hc⟩ -
  rw [LinearMap.mem_ker] at hc

  have hc' : G.d K (i + 1) (ec F G K e (i + 1) c) = 0 := by
    rw [d_ec F G K e hnat, hc, map_zero]
  have hmem : (⟨ec F G K e (i + 1) c, LinearMap.mem_ker.mpr hc'⟩ : LinearMap.ker (G.d K (i + 1))) ∈
      (LinearMap.range (G.d K i)).comap (LinearMap.ker (G.d K (i + 1))).subtype := by
    rw [hG]; exact Submodule.mem_top
  rw [Submodule.mem_comap, LinearMap.mem_range] at hmem
  obtain ⟨b', hb'⟩ := hmem
  change G.d K i b' = ec F G K e (i + 1) c at hb'

  let b : F.cochain K i := fun s => (Equiv.ofBijective _ (hbij i s)).symm (b' s)
  have hb : ec F G K e i b = b' := funext fun s => Equiv.ofBijective_apply_symm_apply _ (hbij i s) (b' s)
  refine Submodule.mem_comap.mpr (LinearMap.mem_range.mpr ⟨b, ?_⟩)
  change F.d K i b = c
  have hinj : Function.Injective (ec F G K e (i + 1)) := by
    intro x y hxy
    funext s
    exact (hbij (i + 1) s).1 (congrFun hxy s)
  apply hinj
  rw [← d_ec F G K e hnat, hb, hb']

end Transfer

section Chi

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

theorem eulerChar_congr {M M' : X.Modules} (e : M ≅ M') (𝒦 : X.OrderedAffineCover) :
    (OModulePresheaf.ofModules f M).eulerChar 𝒦 = (OModulePresheaf.ofModules f M').eulerChar 𝒦 := by
  obtain ⟨⟨e0⟩, hS, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso f e 𝒦
  have h : ∀ i, (OModulePresheaf.ofModules f M).cechFinrank 𝒦 i = (OModulePresheaf.ofModules f M').cechFinrank 𝒦 i := by
    intro i
    cases i with
    | zero => exact e0.finrank_eq
    | succ j => obtain ⟨e⟩ := hS j; exact e.finrank_eq
  rw [OModulePresheaf.eulerChar_def, OModulePresheaf.eulerChar_def]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

theorem supportedIn_top (M : X.Modules) : (OModulePresheaf.ofModules f M).SupportedIn ⊤ := by
  intro V hV
  have hV' : ((V : X.Opens) : Set X) = ∅ := by simpa using hV
  have hbot : (V : X.Opens) = ⊥ := TopologicalSpace.Opens.ext (by simpa using hV')
  haveI : Subsingleton Γ(X, (V : X.Opens)) := by rw [hbot]; infer_instance
  exact Module.subsingleton Γ(X, (V : X.Opens)) _

theorem isInvertible_tensorPow {𝓛 : X.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    ∀ n : ℕ, Scheme.Modules.IsInvertible (𝓛.tensorPow n)
  | 0 => Scheme.Modules.isInvertible_unit X
  | n + 1 => (isInvertible_tensorPow h𝓛 n).tensor h𝓛

end Chi

section Alg

theorem coeff_pos_of_eventually_le (q : Polynomial ℚ) (d : ℕ) (hq : q.natDegree ≤ d) (c : ℚ) (hc : 0 < c)
    (m₀ : ℕ) (h : ∀ m : ℕ, m₀ ≤ m → c * (m : ℚ) ^ d ≤ q.eval (m : ℚ)) : 0 < q.coeff d := by
  by_contra hle'
  have hle : q.coeff d ≤ 0 := not_lt.mp hle'

  set r : Polynomial ℚ := Polynomial.C c * Polynomial.X ^ d - q with hr
  have hrm : ∀ m : ℕ, m₀ ≤ m → r.eval (m : ℚ) ≤ 0 := fun m hm => by
    have := h m hm
    simp only [hr, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    linarith
  have hcoeff : r.coeff d = c - q.coeff d := by
    simp [hr, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hcpos : 0 < r.coeff d := by rw [hcoeff]; linarith
  have hrdeg_le : r.natDegree ≤ d := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ hq)
    exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le d)
  have hrdeg : r.natDegree = d := le_antisymm hrdeg_le (Polynomial.le_natDegree_of_ne_zero hcpos.ne')
  have hlead : r.leadingCoeff = r.coeff d := by rw [Polynomial.leadingCoeff, hrdeg]
  rcases Nat.eq_zero_or_pos d with hd | hd
  ·
    subst hd
    have hr0 : r.eval (m₀ : ℚ) = r.coeff 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hrdeg, Polynomial.eval_C, Polynomial.coeff_C_zero]
    have := hrm m₀ le_rfl
    rw [hr0] at this
    exact absurd this (not_le.mpr hcpos)
  · have hdeg : 0 < r.degree := by
      have hr0 : r ≠ 0 := fun h0 => by rw [h0, Polynomial.coeff_zero] at hcpos; exact lt_irrefl _ hcpos
      rw [Polynomial.degree_eq_natDegree hr0, hrdeg]
      exact_mod_cast hd
    have ht : Tendsto (fun x : ℚ => r.eval x) atTop atTop :=
      Polynomial.tendsto_atTop_of_leadingCoeff_nonneg r hdeg (by rw [hlead]; exact hcpos.le)
    have ht' : Tendsto (fun m : ℕ => r.eval (m : ℚ)) atTop atTop := ht.comp tendsto_natCast_atTop_atTop
    obtain ⟨M, hM⟩ := (ht'.eventually_gt_atTop 0).exists_forall_of_atTop
    have h1 := hM (max M m₀) (le_max_left _ _)
    have h2 := hrm (max M m₀) (le_max_right _ _)
    exact absurd h2 (not_le.mpr h1)

end Alg

section Main

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

theorem isProper {𝓛 : X.Modules} {N : ℕ} (𝔓 : 𝓛.ProjPresentation f N) [IsFinite 𝔓.toProj] : IsProper f := by
  rw [← 𝔓.toProj_π]; infer_instance

theorem exists_forall_subsingleton_HSucc_std (𝓛 : X.Modules) {N : ℕ} (𝔓 : 𝓛.ProjPresentation f N)
    [IsFinite 𝔓.toProj] :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ i : ℕ,
      Subsingleton ((OModulePresheaf.ofModules f (𝓛.tensorPow m)).HSucc (ProjSpace.stdCoverPullback 𝔓.toProj) i) := by
  obtain ⟨m₀, hm₀⟩ := ProjSpace.exists_forall_subsingleton_HSucc_twist 𝔓.toProj f 𝔓.toProj_π
  refine ⟨m₀, fun m hm i => ?_⟩
  haveI := hm₀ m hm i
  obtain ⟨e, -, hnat, hbij⟩ := Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj 𝔓 m
  refine subsingleton_HSucc_of_bijective (OModulePresheaf.ofModules f (𝓛.tensorPow m))
    (ProjSpace.twist f 𝔓.toProj m) (ProjSpace.stdCoverPullback 𝔓.toProj)
    (fun U => (e U).toAddMonoidHom) (fun U U' h x => hnat U U' h x) (fun i s => ?_) i

  exact hbij _ (s.1 0).down ((ProjSpace.stdCoverPullback 𝔓.toProj).inter_le s 0)

theorem exists_forall_subsingleton_HSucc [IsIntegral X] (𝓛 : X.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    {N : ℕ} (𝔓 : 𝓛.ProjPresentation f N) [IsFinite 𝔓.toProj] (𝒦 : X.OrderedAffineCover) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ i : ℕ,
      Subsingleton ((OModulePresheaf.ofModules f (𝓛.tensorPow m)).HSucc 𝒦 i) := by
  haveI : IsProper f := isProper f 𝔓
  obtain ⟨m₀, hm₀⟩ := exists_forall_subsingleton_HSucc_std f 𝓛 𝔓
  refine ⟨m₀, fun m hm i => ?_⟩
  haveI := hm₀ m hm i
  obtain ⟨-, hS⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated f (𝓛.tensorPow m)
    (OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial f _ (isInvertible_tensorPow h𝓛 m).1)
    𝒦 (ProjSpace.stdCoverPullback 𝔓.toProj)
  obtain ⟨e⟩ := hS i
  exact e.toEquiv.subsingleton

theorem exists_forall_eulerChar_eq_cechFinrank_zero [IsIntegral X] (𝓛 : X.Modules)
    (h𝓛 : Scheme.Modules.IsInvertible 𝓛) {N : ℕ} (𝔓 : 𝓛.ProjPresentation f N) [IsFinite 𝔓.toProj]
    (𝒦 : X.OrderedAffineCover) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (OModulePresheaf.ofModules f (𝓛.tensorPow m)).eulerChar 𝒦 =
        (OModulePresheaf.ofModules f (𝓛.tensorPow m)).cechFinrank 𝒦 0 := by
  obtain ⟨m₀, hm₀⟩ := exists_forall_subsingleton_HSucc f 𝓛 h𝓛 𝔓 𝒦
  refine ⟨m₀, fun m hm => ?_⟩
  have hvan : ∀ i, (OModulePresheaf.ofModules f (𝓛.tensorPow m)).cechFinrank 𝒦 (i + 1) = 0 := fun i => by
    haveI := hm₀ m hm i
    rw [OModulePresheaf.cechFinrank_succ]
    exact Module.finrank_zero_of_subsingleton
  rw [OModulePresheaf.eulerChar_def]

  have hcard : 0 < Fintype.card 𝒦.ι := by
    rw [Fintype.card_pos_iff]
    by_contra hι
    rw [not_nonempty_iff] at hι
    have htop : (⊤ : X.Opens) = ⊥ := by
      rw [← 𝒦.iSup_eq_top]; exact iSup_of_empty _
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rw [htop] at hx
    exact hx
  rw [← Nat.sub_add_cancel hcard, Finset.sum_range_succ']
  simp only [hvan, Nat.cast_zero, mul_zero, Finset.sum_const_zero, zero_add, pow_zero, one_mul]

theorem main [IsIntegral X] (d : ℕ) (hd : topologicalKrullDim X = d)
    (𝓛 : X.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) {N : ℕ} (𝔓 : 𝓛.ProjPresentation f N)
    [hfin : IsFinite 𝔓.toProj] (𝒦 : X.OrderedAffineCover) :
    ∃ q : Polynomial ℚ, 0 < q.coeff d ∧
      ∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛.tensorPow m)).eulerChar 𝒦 : ℚ) = q.eval (m : ℚ) := by
  haveI : IsProper f := isProper f 𝔓

  have hunit := Scheme.Modules.isInvertible_unit X
  obtain ⟨q, hqdeg, hq⟩ :=
    OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq f 𝒦 (𝟙_ X.Modules)
      (OModulePresheaf.isCoherent_ofModules_of_locallyTrivial f _ hunit.1)
      (OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial f _ hunit.1)
      ⊤ (supportedIn_top f _) d ((topologicalKrullDim_subspace_le X _).trans hd.le) 𝓛 h𝓛.1
  have hq' : ∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛.tensorPow m)).eulerChar 𝒦 : ℚ) = q.eval (m : ℚ) := by
    intro m
    rw [← hq m, eulerChar_congr f (λ_ (𝓛.tensorPow m))]
  refine ⟨q, ?_, hq'⟩

  obtain ⟨c, hc, hlow⟩ :=
    Scheme.Modules.ProjPresentation.exists_forall_mul_pow_le_cechFinrank_zero_tensorPow (f := f) d hd.ge h𝓛 𝔓 hfin

  obtain ⟨m₀, hm₀⟩ := exists_forall_eulerChar_eq_cechFinrank_zero f 𝓛 h𝓛 𝔓 𝒦
  refine coeff_pos_of_eventually_le q d hqdeg c hc m₀ fun m hm => ?_
  rw [← hq' m, hm₀ m hm]
  exact_mod_cast hlow m 𝒦

end Main

end P2mAmplePos

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsIntegral X]
    (d : ℕ) (hd : topologicalKrullDim X = d)
    (𝓛 : X.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hfs : 𝓛.FiniteBySections f)
    (𝒦 : X.OrderedAffineCover) :
    ∃ q : Polynomial ℚ, 0 < q.coeff d ∧
      ∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛.tensorPow m)).eulerChar 𝒦 : ℚ) = q.eval (m : ℚ) := by
  obtain ⟨N, 𝔓, hfin⟩ := hfs
  haveI := hfin
  exact P2mAmplePos.main f d hd 𝓛 h𝓛 𝔓 𝒦

end
end S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_exists_polynomial_coeff_pos_forall_eulerChar_tensorPow_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_exists_polynomial_coeff_pos_forall_eulerChar_tensorPow_eq (solution)
