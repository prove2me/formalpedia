-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.degree_lt_of_forall_eulerChar_twist_tensorPow_eq_of_inter_iInter_support_zeroSchemeIdeal_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/5eabdb89-277f-55b1-8909-d50a0272ea4b

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Theorems.Thm_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_of_not_subset_support_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_degree_lt_of_forall_eulerChar_twist_tensorPow_eq_of_inter_iInter_support_zeroSchemeIdeal_eq_empty
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial TopologicalSpace"
open scoped TensorProduct

namespace P2mSecVanish

def ext (f : ℕ → ℚ) (Q : ℤ → ℚ) : ℤ → ℚ := fun m =>
  if 0 ≤ m then f m.toNat else f 0 - ∑ i ∈ Finset.range (-m).toNat, Q (-(i + 1 : ℕ))

theorem ext_natCast (f : ℕ → ℚ) (Q : ℤ → ℚ) (n : ℕ) : ext f Q n = f n := by
  simp [ext]

theorem ext_neg_succ (f : ℕ → ℚ) (Q : ℤ → ℚ) (j : ℕ) :
    ext f Q (-(j + 1 : ℕ)) = f 0 - ∑ i ∈ Finset.range (j + 1), Q (-(i + 1 : ℕ)) := by
  have h : ¬ (0 : ℤ) ≤ -(j + 1 : ℕ) := by omega
  simp only [ext, if_neg h, neg_neg, Int.toNat_natCast]

theorem fwdDiff_ext (f : ℕ → ℚ) (Q : ℤ → ℚ) (hf : ∀ n : ℕ, f (n + 1) - f n = Q n) (m : ℤ) :
    fwdDiff (1 : ℤ) (ext f Q) m = Q m := by
  rw [fwdDiff]
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    have : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, ext_natCast, ext_natCast]
    exact hf n
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = -(j + 1 : ℕ) := ⟨(-m - 1).toNat, by omega⟩
    cases j with
    | zero =>
      have h0 : (-((0 + 1 : ℕ) : ℤ) + 1) = ((0 : ℕ) : ℤ) := by norm_num
      rw [h0, ext_natCast, ext_neg_succ, Finset.sum_range_one]
      push_cast
      abel
    | succ j =>
      have h1 : (-((j + 1 + 1 : ℕ) : ℤ) + 1) = -((j + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [h1, ext_neg_succ, ext_neg_succ, Finset.sum_range_succ _ (j + 1)]
      push_cast
      ring

theorem poly_of_delta (f : ℕ → ℚ) (q : ℚ[X]) (e : ℕ) (hq : q.degree < e)
    (hf : ∀ n : ℕ, f (n + 1) - f n = q.eval (n : ℚ)) :
    ∃ p : ℚ[X], p.degree < (e + 1 : ℕ) ∧ ∀ n : ℕ, f n = p.eval (n : ℚ) := by
  set F : ℤ → ℚ := ext f (fun m => q.eval (m : ℚ)) with hF
  have hΔ : ∀ m : ℤ, fwdDiff (1 : ℤ) F m = q.eval (m : ℚ) := fun m => fwdDiff_ext f (fun m => q.eval (m : ℚ)) hf m
  have hvan : ∀ m : ℤ, (fwdDiff (1 : ℤ))^[e + 1] F m = 0 := by
    intro m
    rw [Function.iterate_succ_apply, show fwdDiff (1 : ℤ) F = fun m : ℤ => q.eval (m : ℚ) from funext hΔ]
    cases e with
    | zero =>
      have hq0 : q = 0 := by
        by_contra h
        rw [Nat.cast_zero] at hq
        exact Nat.not_lt_zero _ ((natDegree_lt_iff_degree_lt (n := 0) h).mpr hq)
      simp [hq0]
    | succ e =>
      refine (fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le
        (fun m : ℤ => q.eval (m : ℚ)) e).mpr ⟨q, ?_, fun _ => rfl⟩ m
      by_cases h : q = 0
      · simp [h]
      · exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt h).mpr hq)
  obtain ⟨p, hp, hpF⟩ := (fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le F e).mp hvan
  refine ⟨p, ?_, fun n => ?_⟩
  · by_cases h : p = 0
    · simp [h]
    · exact (natDegree_lt_iff_degree_lt h).mp (Nat.lt_succ_iff.mpr hp)
  · have := hpF n
    rw [hF, ext_natCast] at this
    exact_mod_cast this

section ZeroLoci

variable {V : Scheme.{u}} {L : V.Modules} {r : ℕ} (s : Fin r → (𝟙_ V.Modules ⟶ L))

def zl (J : Finset (Fin r)) : Set V := ⋂ i ∈ J, ((Scheme.Modules.zeroSchemeIdeal (s i)).support : Set V)

theorem zl_eq_inter_erase {J : Finset (Fin r)} {i : Fin r} (hi : i ∈ J) :
    zl s J = ((Scheme.Modules.zeroSchemeIdeal (s i)).support : Set V) ∩ zl s (J.erase i) := by
  classical
  conv_lhs => rw [← Finset.insert_erase hi]
  rw [zl, zl, Finset.set_biInter_insert]

theorem zl_empty : zl s ∅ = Set.univ := by
  simp [zl]

theorem zl_univ : zl s Finset.univ = ⋂ i, ((Scheme.Modules.zeroSchemeIdeal (s i)).support : Set V) := by
  simp [zl]

end ZeroLoci

section Toolkit

variable {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k))
variable (K : V.OrderedAffineCover) (L : V.Modules)
  (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))

noncomputable def chi (G : OModulePresheaf π) (n : ℕ) : ℤ := (G.twist (L.tensorPow n)).eulerChar K

include hL in
theorem locTriv_tensorPow (n : ℕ) : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj (L.tensorPow n) ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  suffices h : Scheme.Modules.IsInvertible (L.tensorPow n) from h.1
  induction n with
  | zero => exact Scheme.Modules.isInvertible_unit V
  | succ n ih => exact ih.tensor ⟨hL⟩

include hL in
theorem good_twist (G : OModulePresheaf π) (hc : G.IsCoherent) (hq : G.IsQuasicoherent) (n : ℕ) :
    (G.twist (L.tensorPow n)).IsCoherent ∧ (G.twist (L.tensorPow n)).IsQuasicoherent :=
  ⟨(G.isQuasicoherent_isCoherent_supportedIn_tensor (OModulePresheaf.ofModules π (L.tensorPow n))).2.1 hc
      (OModulePresheaf.isCoherent_ofModules_of_locallyTrivial π _ (locTriv_tensorPow L hL n)),
    (G.isQuasicoherent_isCoherent_supportedIn_tensor (OModulePresheaf.ofModules π (L.tensorPow n))).1 hq
      (OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial π _ (locTriv_tensorPow L hL n))⟩

include hL in
theorem cechFinite_twist [IsProper π] (G : OModulePresheaf π) (hc : G.IsCoherent) (hq : G.IsQuasicoherent) (n : ℕ) :
    (G.twist (L.tensorPow n)).CechFinite K :=
  (G.twist (L.tensorPow n)).cechFinite_of_isProper (good_twist π L hL G hc hq n).1 (good_twist π L hL G hc hq n).2 K

include hL in
theorem flat_sections (n : ℕ) (U : V.affineOpens) :
    Module.Flat Γ(V, U.1) ((OModulePresheaf.ofModules π (L.tensorPow n)).obj U.1) := by
  haveI := Scheme.Modules.projective_sections_of_locallyTrivial (L.tensorPow n) (locTriv_tensorPow L hL n) U
  show Module.Flat Γ(V, U.1) Γ(L.tensorPow n, U.1)
  exact Module.Flat.of_projective

include hL in

theorem chi_add [IsProper π] {G₁ G₂ G₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES G₁ G₂ G₃)
    (h₁c : G₁.IsCoherent) (h₁q : G₁.IsQuasicoherent) (h₂c : G₂.IsCoherent) (h₂q : G₂.IsQuasicoherent)
    (h₃c : G₃.IsCoherent) (h₃q : G₃.IsQuasicoherent) (n : ℕ) :
    chi π K L G₂ n = chi π K L G₁ n + chi π K L G₃ n := by
  obtain ⟨S', -⟩ := OModulePresheaf.exists_affSES_tensor_of_flat S (OModulePresheaf.ofModules π (L.tensorPow n))
    (flat_sections π L hL n)
  exact OModulePresheaf.eulerChar_eq_add_of_affSES S' K (cechFinite_twist π K L hL G₁ h₁c h₁q n)
    (cechFinite_twist π K L hL G₂ h₂c h₂q n) (cechFinite_twist π K L hL G₃ h₃c h₃q n)

theorem eulerChar_eq_zero_of_subsingleton [IsSeparated π] (G : OModulePresheaf π)
    (hG : ∀ U : V.affineOpens, Subsingleton (G.obj U.1)) : G.eulerChar K = 0 := by
  have hco : ∀ i, Subsingleton (G.cochain K i) := fun i => by
    haveI : ∀ t : K.Idx i, Subsingleton (G.obj (K.inter t)) := fun t => hG (K.affineInter π t)
    infer_instance
  have hcf : ∀ i, G.cechFinrank K i = 0 := by
    intro i
    cases i with
    | zero =>
      haveI := hco 0
      haveI : Subsingleton (G.H0 K) := inferInstance
      exact Module.finrank_zero_of_subsingleton
    | succ j =>
      haveI := hco (j + 1)
      haveI : Subsingleton (G.HSucc K j) := inferInstance
      exact Module.finrank_zero_of_subsingleton
  rw [OModulePresheaf.eulerChar_def]
  exact Finset.sum_eq_zero fun i _ => by rw [hcf i]; simp

theorem chi_eq_zero_of_subsingleton [IsSeparated π] (G : OModulePresheaf π)
    (hG : ∀ U : V.affineOpens, Subsingleton (G.obj U.1)) (n : ℕ) : chi π K L G n = 0 := by
  refine eulerChar_eq_zero_of_subsingleton π K _ fun U => ?_
  haveI := hG U
  show Subsingleton (G.obj U.1 ⊗[Γ(V, U.1)] Γ(L.tensorPow n, U.1))
  infer_instance

end Toolkit

section Inputs

variable {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k))
variable (K : V.OrderedAffineCover) (L : V.Modules)
  (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
  {r : ℕ} (s : Fin r → (𝟙_ V.Modules ⟶ L))

def P (J : Finset (Fin r)) (G : OModulePresheaf π) : Prop :=
  ∃ p : ℚ[X], p.degree < (J.card : ℕ) ∧ ∀ n : ℕ, (chi π K L G n : ℚ) = p.eval (n : ℚ)

def Q (Y : Closeds V) (G : OModulePresheaf π) : Prop :=
  ∀ J : Finset (Fin r), (Y : Set V) ∩ zl s J = ∅ → P π K L J G

theorem Q_zero [IsSeparated π] (Y : Closeds V) (G : OModulePresheaf π)
    (hG : ∀ U : V.affineOpens, Subsingleton (G.obj U.1)) : Q π K L s Y G := fun J _ =>
  ⟨0, by rw [degree_zero]; exact WithBot.bot_lt_coe _, fun n => by
    rw [chi_eq_zero_of_subsingleton π K L G hG n, eval_zero]; simp⟩

theorem Q_mono (Y Y' : Closeds V) (G : OModulePresheaf π) (h : Y' ≤ Y) (hQ : Q π K L s Y' G) : Q π K L s Y G :=
  fun J hJ => hQ J (Set.eq_empty_of_subset_empty (fun _ hx => hJ ▸ ⟨h hx.1, hx.2⟩))

include hL in
theorem Q_ext [IsProper π] (Y : Closeds V) (G₁ G₂ G₃ : OModulePresheaf π)
    (hS : Nonempty (OModulePresheaf.AffSES G₁ G₂ G₃))
    (h₁c : G₁.IsCoherent) (h₁q : G₁.IsQuasicoherent) (h₂c : G₂.IsCoherent) (h₂q : G₂.IsQuasicoherent)
    (h₃c : G₃.IsCoherent) (h₃q : G₃.IsQuasicoherent) :
    (Q π K L s Y G₁ → Q π K L s Y G₃ → Q π K L s Y G₂) ∧ (Q π K L s Y G₁ → Q π K L s Y G₂ → Q π K L s Y G₃) ∧
      (Q π K L s Y G₂ → Q π K L s Y G₃ → Q π K L s Y G₁) := by
  obtain ⟨S⟩ := hS
  have hadd := chi_add π K L hL S h₁c h₁q h₂c h₂q h₃c h₃q
  refine ⟨fun hQ₁ hQ₃ J hJ => ?_, fun hQ₁ hQ₂ J hJ => ?_, fun hQ₂ hQ₃ J hJ => ?_⟩
  · obtain ⟨p₁, hp₁, h₁⟩ := hQ₁ J hJ
    obtain ⟨p₃, hp₃, h₃⟩ := hQ₃ J hJ
    refine ⟨p₁ + p₃, (degree_add_le _ _).trans_lt (max_lt hp₁ hp₃), fun n => ?_⟩
    rw [hadd n, eval_add, ← h₁ n, ← h₃ n]; push_cast; ring
  · obtain ⟨p₁, hp₁, h₁⟩ := hQ₁ J hJ
    obtain ⟨p₂, hp₂, h₂⟩ := hQ₂ J hJ
    refine ⟨p₂ - p₁, (degree_sub_le _ _).trans_lt (max_lt hp₂ hp₁), fun n => ?_⟩
    rw [eval_sub, ← h₁ n, ← h₂ n, hadd n]; push_cast; ring
  · obtain ⟨p₂, hp₂, h₂⟩ := hQ₂ J hJ
    obtain ⟨p₃, hp₃, h₃⟩ := hQ₃ J hJ
    refine ⟨p₂ - p₃, (degree_sub_le _ _).trans_lt (max_lt hp₂ hp₃), fun n => ?_⟩
    rw [eval_sub, ← h₂ n, ← h₃ n, hadd n]; push_cast; ring

noncomputable abbrev OZ (Z₀ : Closeds V) : OModulePresheaf π :=
  OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι

include hL in

theorem hInt [IsProper π] (Z₀ : Closeds V) (hne : (Z₀ : Set V).Nonempty)
    (hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme)
    (ih : ∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' →
      Q π K L s Y' G) :
    Q π K L s Z₀ (OZ π Z₀) := by
  suffices H : ∀ (m : ℕ) (J : Finset (Fin r)), J.card ≤ m → (Z₀ : Set V) ∩ zl s J = ∅ → P π K L J (OZ π Z₀) from
    fun J hJ => H J.card J le_rfl hJ
  intro m
  induction m with
  | zero =>
    intro J hJm hJ
    have hJ0 : J = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hJm)
    rw [hJ0, zl_empty, Set.inter_univ] at hJ
    exact absurd hJ hne.ne_empty
  | succ m ihm =>
    intro J hJm hJ
    by_cases hvan : ∃ i ∈ J, (Z₀ : Set V) ⊆ ((Scheme.Modules.zeroSchemeIdeal (s i)).support : Set V)
    ·
      obtain ⟨i, hi, hsub⟩ := hvan
      have hJ' : (Z₀ : Set V) ∩ zl s (J.erase i) = ∅ := by
        rw [zl_eq_inter_erase s hi] at hJ
        rw [← hJ]
        ext x
        exact ⟨fun hx => ⟨hx.1, hsub hx.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩
      have hcard : (J.erase i).card ≤ m := by
        rw [Finset.card_erase_of_mem hi]; omega
      obtain ⟨p, hp, hχ⟩ := ihm (J.erase i) hcard hJ'
      refine ⟨p, hp.trans_le ?_, hχ⟩
      exact_mod_cast Finset.card_erase_le
    · push Not at hvan
      have hJne : J.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        rw [zl_empty, Set.inter_univ] at hJ
        exact hne.ne_empty hJ
      obtain ⟨i, hi⟩ := hJne

      obtain ⟨Y₁, G₁, hY₁, hY₁s, h₁c, h₁q, h₁s, hΔ⟩ :=
        OModulePresheaf.exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_of_not_subset_support_zeroSchemeIdeal
          π K L hL (s i) Z₀ hne hint (hvan i hi)
      have hJ' : (Y₁ : Set V) ∩ zl s (J.erase i) = ∅ := by
        rw [zl_eq_inter_erase s hi] at hJ
        refine Set.eq_empty_of_subset_empty fun x hx => ?_
        rw [← hJ]
        exact ⟨hY₁.le hx.1, hY₁s hx.1, hx.2⟩
      obtain ⟨p₁, hp₁, hχ₁⟩ := ih Y₁ hY₁ G₁ h₁c h₁q h₁s (J.erase i) hJ'
      have hcardJ : J.card = (J.erase i).card + 1 := by
        rw [Finset.card_erase_of_mem hi]
        have := Finset.card_pos.mpr ⟨i, hi⟩
        omega

      have hq : (p₁.comp (X + 1)).degree < ((J.erase i).card : ℕ) := by
        by_cases h1 : p₁ = 0
        · simp [h1]
        · have hn : p₁.natDegree < (J.erase i).card := (natDegree_lt_iff_degree_lt h1).mpr hp₁
          refine (degree_le_natDegree).trans_lt ?_
          have hc : (p₁.comp (X + 1)).natDegree ≤ p₁.natDegree := by
            refine natDegree_comp_le.trans ?_
            have : (X + 1 : ℚ[X]).natDegree = 1 := by simpa using natDegree_X_add_C (1 : ℚ)
            rw [this, mul_one]
          exact_mod_cast lt_of_le_of_lt hc hn
      obtain ⟨p, hp, hχ⟩ := poly_of_delta (fun n => (chi π K L (OZ π Z₀) n : ℚ)) _ _ hq fun n => by
        have := hΔ n
        rw [eval_comp, eval_add, eval_X, eval_one]
        have h1 := hχ₁ (n + 1)
        push_cast at h1
        rw [← h1]
        show (chi π K L (OZ π Z₀) (n + 1) : ℚ) - chi π K L (OZ π Z₀) n = _
        exact_mod_cast this
      exact ⟨p, by rw [hcardJ]; exact hp, hχ⟩

include hL in

theorem Q_all [IsProper π] :
    ∀ (Y : Closeds V) (G : OModulePresheaf π), G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y →
      Q π K L s Y G :=
  OModulePresheaf.forall_coherent_of_forall_integral π (Q π K L s)
    (fun Y G hG => Q_zero π K L s Y G hG) (fun Y Y' G h hQ => Q_mono π K L s Y Y' G h hQ)
    (fun Y G₁ G₂ G₃ hS h₁c h₁q h₂c h₂q h₃c h₃q => Q_ext π K L hL s Y G₁ G₂ G₃ hS h₁c h₁q h₂c h₂q h₃c h₃q)
    (fun Z₀ hne hint ih => hInt π K L hL s Z₀ hne hint ih)

include hL in
private theorem _root_.P2mSecVanish.card [IsProper π] (G : OModulePresheaf π) (hc : G.IsCoherent) (hq : G.IsQuasicoherent)
    (Y : Closeds V) (hY : G.SupportedIn Y)
    (hs : (Y : Set V) ∩ ⋂ i, ((Scheme.Modules.zeroSchemeIdeal (s i)).support : Set V) = ∅)
    (p : Polynomial ℚ) (hp : ∀ n : ℕ, ((G.twist (L.tensorPow n)).eulerChar K : ℚ) = p.eval (n : ℚ)) :
    p.degree < r := by
  have hJ : (Y : Set V) ∩ zl s Finset.univ = ∅ := by rw [zl_univ]; exact hs
  obtain ⟨p', hp', hχ⟩ := Q_all π K L hL s Y G hc hq hY Finset.univ hJ
  have hpp' : p = p' := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := Set.range (fun n : ℕ => (n : ℚ))) ?_
      (Set.infinite_range_of_injective Nat.cast_injective)
    rintro _ ⟨n, rfl⟩
    exact (hp n).symm.trans (hχ n)
  rw [hpp']
  simpa [Finset.card_univ, Fintype.card_fin] using hp'

p2m_export "P2mSecVanish" "card"
end Inputs

end P2mSecVanish

theorem solution
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
    (K : V.OrderedAffineCover) (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    {r : ℕ} (s : Fin r → (𝟙_ V.Modules ⟶ L))
    (G : OModulePresheaf π) (hc : G.IsCoherent) (hq : G.IsQuasicoherent)
    (Y : Closeds V) (hY : G.SupportedIn Y)
    (hs : (Y : Set V) ∩ ⋂ i, ((Scheme.Modules.zeroSchemeIdeal (s i)).support : Set V) = ∅)
    (p : Polynomial ℚ)
    (hp : ∀ n : ℕ, ((G.twist (L.tensorPow n)).eulerChar K : ℚ) = p.eval (n : ℚ)) :
    p.degree < r :=
  P2mSecVanish.card π K L hL s G hc hq Y hY hs p hp

end S_AlgebraicGeometry_OModulePresheaf_degree_lt_of_forall_eulerChar_twist_tensorPow_eq_of_inter_iInter_support_zeroSchemeIdeal_eq_empty
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_degree_lt_of_forall_eulerChar_twist_tensorPow_eq_of_inter_iInter_support_zeroSchemeIdeal_eq_empty (solution)
