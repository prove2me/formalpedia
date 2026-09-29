-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_polynomial_forall_eulerChar_twist_tensorPow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7bc37136-453b-546c-9430-fcefe5e84c90

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le
import Theorems.Thm_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq
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

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial TopologicalSpace"
open scoped TensorProduct

namespace P2mChiDatum

private def _root_.P2mChiDatum.ext (f : ℕ → ℚ) (Q : ℤ → ℚ) : ℤ → ℚ := fun m =>
  if 0 ≤ m then f m.toNat else f 0 - ∑ i ∈ Finset.range (-m).toNat, Q (-(i + 1 : ℕ))

p2m_export "P2mChiDatum" "ext"
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

section Dim

variable {V : Scheme.{u}}

theorem isIrreducible_of_isIntegral_subscheme (Z₀ : Closeds V)
    (hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme) :
    IsIrreducible (Z₀ : Set V) := by
  have h := (IrreducibleSpace.isIrreducible_univ
    (X := (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme)).image
      (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι
      (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.continuous.continuousOn
  rwa [Set.image_univ, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal] at h

theorem dim_lt_of_lt (Z₀ Y' : Closeds V) (hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme)
    (hY : Y' < Z₀) (e : ℕ) (hd : topologicalKrullDim Z₀ < (e + 1 : ℕ)) :
    topologicalKrullDim Y' < (e : ℕ) := by
  have hirr := isIrreducible_of_isIntegral_subscheme Z₀ hint
  have hne : (Y' : Set V) ≠ Z₀ := fun h => hY.ne (Closeds.ext h)
  have hstep : topologicalKrullDim (Y' : Set V) + 1 ≤ topologicalKrullDim (Z₀ : Set V) :=
    hirr.topologicalKrullDim_add_one_le_of_isClosed_of_ne Y'.isClosed hY.le hne
  have hd' : topologicalKrullDim (Z₀ : Set V) ≤ (e : ℕ) := by
    have : topologicalKrullDim (Z₀ : Set V) < (e : WithBot ℕ∞) + 1 := by exact_mod_cast hd
    exact ENat.WithBot.lt_add_one_iff.mp this
  exact ENat.WithBot.add_one_le_natCast_iff.mp (hstep.trans hd')

theorem dim_mono (Y Y' : Closeds V) (h : Y' ≤ Y) : topologicalKrullDim Y' ≤ topologicalKrullDim Y :=
  Topology.IsInducing.topologicalKrullDim_le (Topology.IsEmbedding.inclusion (show (Y' : Set V) ⊆ Y from h)).isInducing

theorem dim_nonneg (Y : Closeds V) (hY : (Y : Set V).Nonempty) : 0 ≤ topologicalKrullDim Y := by
  obtain ⟨y, hy⟩ := hY
  exact Order.krullDim_nonneg_iff.mpr
    ⟨⟨closure {(⟨y, hy⟩ : (Y : Set V))}, isIrreducible_singleton.closure, isClosed_closure⟩⟩

end Dim

section Skeleton

variable {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k))
variable (K : V.OrderedAffineCover) (L : V.Modules)

noncomputable def chi (G : OModulePresheaf π) (n : ℕ) : ℤ := (G.twist (L.tensorPow n)).eulerChar K

def Good (G : OModulePresheaf π) (Y : Closeds V) : Prop := G.IsCoherent ∧ G.IsQuasicoherent ∧ G.SupportedIn Y

def P (e : ℕ) (G : OModulePresheaf π) : Prop :=
  ∃ p : ℚ[X], p.degree < (e : ℕ) ∧ ∀ n : ℕ, (chi π K L G n : ℚ) = p.eval (n : ℚ)

def IH (Z₀ : Closeds V) : Prop :=
  ∀ Y' < Z₀, ∀ (G : OModulePresheaf π) (e' : ℕ), Good π G Y' → topologicalKrullDim Y' < (e' : ℕ) → P π K L e' G

noncomputable abbrev OZ (Z₀ : Closeds V) : OModulePresheaf π :=
  OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι

theorem skeleton
    (hDev : (∀ (Z₀ : Closeds V), (Z₀ : Set V).Nonempty →
        IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme →
        ∀ e : ℕ, topologicalKrullDim Z₀ < (e + 1 : ℕ) → IH π K L Z₀ → P π K L (e + 1) (OZ π Z₀)) →
      ∀ (Y : Closeds V) (G : OModulePresheaf π) (e : ℕ), Good π G Y → topologicalKrullDim Y < (e : ℕ) →
        P π K L e G)
    (hTwist : ∀ (Z₀ : Closeds V), (Z₀ : Set V).Nonempty →
        IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme →
        ∃ (Y₁ : Closeds V) (G₁ : OModulePresheaf π) (Y₂ : Closeds V) (G₂ : OModulePresheaf π),
          Y₁ < Z₀ ∧ Good π G₁ Y₁ ∧ Y₂ < Z₀ ∧ Good π G₂ Y₂ ∧
          ∀ n : ℕ, chi π K L (OZ π Z₀) (n + 1) - chi π K L (OZ π Z₀) n = chi π K L G₁ (n + 1) - chi π K L G₂ n) :
    ∀ (Y : Closeds V) (G : OModulePresheaf π) (e : ℕ), Good π G Y → topologicalKrullDim Y < (e : ℕ) →
      P π K L e G := by
  refine hDev fun Z₀ hne hint e hd ih => ?_
  obtain ⟨Y₁, G₁, Y₂, G₂, hY₁, hG₁, hY₂, hG₂, hΔ⟩ := hTwist Z₀ hne hint
  obtain ⟨p₁, hp₁, hχ₁⟩ := ih Y₁ hY₁ G₁ e hG₁ (dim_lt_of_lt Z₀ Y₁ hint hY₁ e hd)
  obtain ⟨p₂, hp₂, hχ₂⟩ := ih Y₂ hY₂ G₂ e hG₂ (dim_lt_of_lt Z₀ Y₂ hint hY₂ e hd)
  have hq : (p₁.comp (X + 1) - p₂).degree < (e : ℕ) := by
    refine (degree_sub_le _ _).trans_lt (max_lt ?_ hp₂)
    by_cases h1 : p₁ = 0
    · simp [h1]
    · have hn : p₁.natDegree < e := (natDegree_lt_iff_degree_lt h1).mpr hp₁
      refine (degree_le_natDegree).trans_lt ?_
      have hc : (p₁.comp (X + 1)).natDegree ≤ p₁.natDegree := by
        refine natDegree_comp_le.trans ?_
        have : (X + 1 : ℚ[X]).natDegree = 1 := by simpa using natDegree_X_add_C (1 : ℚ)
        rw [this, mul_one]
      exact_mod_cast lt_of_le_of_lt hc hn
  refine poly_of_delta (fun n => (chi π K L (OZ π Z₀) n : ℚ)) _ e hq fun n => ?_
  have := hΔ n
  rw [eval_sub, eval_comp, eval_add, eval_X, eval_one, ← hχ₂ n]
  have h1 := hχ₁ (n + 1)
  push_cast at h1
  rw [← h1]
  show (chi π K L (OZ π Z₀) (n + 1) : ℚ) - chi π K L (OZ π Z₀) n = _
  exact_mod_cast this

end Skeleton

section Inputs

variable {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k))
variable (K : V.OrderedAffineCover) (L : V.Modules)
  (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))

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
    haveI : ∀ s : K.Idx i, Subsingleton (G.obj (K.inter s)) := fun s => hG (K.affineInter π s)
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

def Q (Y : Closeds V) (G : OModulePresheaf π) : Prop :=
  ∀ e : ℕ, topologicalKrullDim Y < (e : ℕ) → P π K L e G

theorem Q_zero [IsSeparated π] (Y : Closeds V) (G : OModulePresheaf π)
    (hG : ∀ U : V.affineOpens, Subsingleton (G.obj U.1)) : Q π K L Y G := fun e _ =>
  ⟨0, by rw [degree_zero]; exact WithBot.bot_lt_coe _, fun n => by
    rw [chi_eq_zero_of_subsingleton π K L G hG n, eval_zero]; simp⟩

theorem Q_mono (Y Y' : Closeds V) (G : OModulePresheaf π) (h : Y' ≤ Y) (hQ : Q π K L Y' G) : Q π K L Y G :=
  fun e he => hQ e ((dim_mono Y Y' h).trans_lt he)

include hL in
theorem Q_ext [IsProper π] (Y : Closeds V) (G₁ G₂ G₃ : OModulePresheaf π)
    (hS : Nonempty (OModulePresheaf.AffSES G₁ G₂ G₃))
    (h₁c : G₁.IsCoherent) (h₁q : G₁.IsQuasicoherent) (h₂c : G₂.IsCoherent) (h₂q : G₂.IsQuasicoherent)
    (h₃c : G₃.IsCoherent) (h₃q : G₃.IsQuasicoherent) :
    (Q π K L Y G₁ → Q π K L Y G₃ → Q π K L Y G₂) ∧ (Q π K L Y G₁ → Q π K L Y G₂ → Q π K L Y G₃) ∧
      (Q π K L Y G₂ → Q π K L Y G₃ → Q π K L Y G₁) := by
  obtain ⟨S⟩ := hS
  have hadd := chi_add π K L hL S h₁c h₁q h₂c h₂q h₃c h₃q
  refine ⟨fun hQ₁ hQ₃ e he => ?_, fun hQ₁ hQ₂ e he => ?_, fun hQ₂ hQ₃ e he => ?_⟩
  · obtain ⟨p₁, hp₁, h₁⟩ := hQ₁ e he
    obtain ⟨p₃, hp₃, h₃⟩ := hQ₃ e he
    refine ⟨p₁ + p₃, (degree_add_le _ _).trans_lt (max_lt hp₁ hp₃), fun n => ?_⟩
    rw [hadd n, eval_add, ← h₁ n, ← h₃ n]; push_cast; ring
  · obtain ⟨p₁, hp₁, h₁⟩ := hQ₁ e he
    obtain ⟨p₂, hp₂, h₂⟩ := hQ₂ e he
    refine ⟨p₂ - p₁, (degree_sub_le _ _).trans_lt (max_lt hp₂ hp₁), fun n => ?_⟩
    rw [eval_sub, ← h₁ n, ← h₂ n, hadd n]; push_cast; ring
  · obtain ⟨p₂, hp₂, h₂⟩ := hQ₂ e he
    obtain ⟨p₃, hp₃, h₃⟩ := hQ₃ e he
    refine ⟨p₂ - p₃, (degree_sub_le _ _).trans_lt (max_lt hp₂ hp₃), fun n => ?_⟩
    rw [eval_sub, ← h₂ n, ← h₃ n, hadd n]; push_cast; ring

include hL in

theorem hDev [IsProper π]
    (hstep : ∀ (Z₀ : Closeds V), (Z₀ : Set V).Nonempty →
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme →
      ∀ e : ℕ, topologicalKrullDim Z₀ < (e + 1 : ℕ) → IH π K L Z₀ → P π K L (e + 1) (OZ π Z₀)) :
    ∀ (Y : Closeds V) (G : OModulePresheaf π) (e : ℕ), Good π G Y → topologicalKrullDim Y < (e : ℕ) →
      P π K L e G := by
  have main := OModulePresheaf.forall_coherent_of_forall_integral π (Q π K L)
    (fun Y G hG => Q_zero π K L Y G hG) (fun Y Y' G h hQ => Q_mono π K L Y Y' G h hQ)
    (fun Y G₁ G₂ G₃ hS h₁c h₁q h₂c h₂q h₃c h₃q => Q_ext π K L hL Y G₁ G₂ G₃ hS h₁c h₁q h₂c h₂q h₃c h₃q)
    (fun Z₀ hne hint ih e he => by
      cases e with
      | zero =>
        exact absurd (lt_of_le_of_lt (dim_nonneg Z₀ hne) (by exact_mod_cast he)) (lt_irrefl _)
      | succ e =>
        exact hstep Z₀ hne hint e he fun Y' hY' G e' hG hd => ih Y' hY' G hG.1 hG.2.1 hG.2.2 e' hd)
  exact fun Y G e hG hd => main Y G hG.1 hG.2.1 hG.2.2 e hd

include hL in

theorem hTwist [IsProper π] (Z₀ : Closeds V) (hne : (Z₀ : Set V).Nonempty)
    (hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme) :
    ∃ (Y₁ : Closeds V) (G₁ : OModulePresheaf π) (Y₂ : Closeds V) (G₂ : OModulePresheaf π),
      Y₁ < Z₀ ∧ Good π G₁ Y₁ ∧ Y₂ < Z₀ ∧ Good π G₂ Y₂ ∧
      ∀ n : ℕ, chi π K L (OZ π Z₀) (n + 1) - chi π K L (OZ π Z₀) n = chi π K L G₁ (n + 1) - chi π K L G₂ n := by
  obtain ⟨Y₁, Y₂, G₁, G₂, hY₁, hY₂, h₁c, h₁q, h₁s, h₂c, h₂q, h₂s, hΔ⟩ :=
    OModulePresheaf.exists_eulerChar_twist_pushforwardUnit_succ_sub_eq π K L hL Z₀ hne hint
  exact ⟨Y₁, G₁, Y₂, G₂, hY₁, ⟨h₁c, h₁q, h₁s⟩, hY₂, ⟨h₂c, h₂q, h₂s⟩, hΔ⟩

include hL in
theorem card [IsProper π] (G : OModulePresheaf π)
    (hc : G.IsCoherent) (hq : G.IsQuasicoherent)
    (Y : TopologicalSpace.Closeds V) (hY : G.SupportedIn Y)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ d) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ d ∧
      ∀ n : ℕ, ((G.twist (L.tensorPow n)).eulerChar K : ℚ) = p.eval (n : ℚ) := by
  have hd' : topologicalKrullDim Y < (d + 1 : ℕ) := by
    push_cast
    exact ENat.WithBot.lt_add_one_iff.mpr hd
  obtain ⟨p, hp, hχ⟩ := skeleton π K L (hDev π K L hL) (hTwist π K L hL) Y G (d + 1) ⟨hc, hq, hY⟩ hd'
  refine ⟨p, ?_, hχ⟩
  by_cases h : p = 0
  · simp [h]
  · exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt h).mpr hp)

end Inputs

end P2mChiDatum

theorem solution
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
    (K : V.OrderedAffineCover) (G : OModulePresheaf π)
    (hc : G.IsCoherent) (hq : G.IsQuasicoherent)
    (Y : TopologicalSpace.Closeds V) (hY : G.SupportedIn Y)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ d ∧
      ∀ n : ℕ, ((G.twist (L.tensorPow n)).eulerChar K : ℚ) = p.eval (n : ℚ) :=
  P2mChiDatum.card π K L hL G hc hq Y hY d hd

end S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq (solution)
