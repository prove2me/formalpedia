-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/61c850b6-1b92-5a1d-af6c-65718ed24c06

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial TopologicalSpace Opposite"
open scoped TensorProduct

namespace P2mLead

open AlgebraicGeometry.OModulePresheaf

section GenericRank

variable {B : Type u} [CommRing B]

theorem rankAtStalk_eq_zero_of_forall_exists_smul_eq_zero {M : Type u} [AddCommGroup M] [Module B M]
    (𝔭 : PrimeSpectrum B) (h : ∀ m : M, ∃ a : B, a ∉ 𝔭.asIdeal ∧ a • m = 0) :
    Module.rankAtStalk (R := B) M 𝔭 = 0 := by
  unfold Module.rankAtStalk
  haveI : Subsingleton (LocalizedModule 𝔭.asIdeal.primeCompl M) := by
    refine ⟨fun x y => ?_⟩
    have hx : ∀ z : LocalizedModule 𝔭.asIdeal.primeCompl M, z = 0 := by
      intro z
      induction z using LocalizedModule.induction_on with
      | h m s =>
        obtain ⟨a, ha, ham⟩ := h m
        rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
        exact ⟨⟨a, ha⟩, by rw [Submonoid.smul_def, Submonoid.smul_def, smul_zero, smul_zero, smul_comm, ham, smul_zero]⟩
    rw [hx x, hx y]
  exact Module.finrank_zero_of_subsingleton

variable [IsDomain B]

noncomputable def genRank (M : Type u) [AddCommGroup M] [Module B M] : ℕ :=
  Module.finrank (FractionRing B) (FractionRing B ⊗[B] M)

omit [IsDomain B] in
theorem finrank_localization_congr {S T : Submonoid B} (h : S = T) (M : Type u) [AddCommGroup M] [Module B M] :
    Module.finrank (Localization S) (Localization S ⊗[B] M) =
      Module.finrank (Localization T) (Localization T ⊗[B] M) := by
  subst h; rfl

theorem rankAtStalk_eq_genRank (𝔭 : PrimeSpectrum B) (h𝔭 : 𝔭.asIdeal = ⊥) (M : Type u) [AddCommGroup M]
    [Module B M] : Module.rankAtStalk (R := B) M 𝔭 = genRank (B := B) M := by
  rw [Module.rankAtStalk_eq_finrank_tensorProduct]
  obtain ⟨I, hI⟩ := 𝔭
  simp only at h𝔭
  subst h𝔭
  exact finrank_localization_congr Ideal.primeCompl_bot M

theorem genRank_add {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module B M₁] [AddCommGroup M₂] [Module B M₂]
    [AddCommGroup M₃] [Module B M₃] [Module.Finite B M₂]
    (f : M₁ →ₗ[B] M₂) (g : M₂ →ₗ[B] M₃) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) : genRank (B := B) M₂ = genRank (B := B) M₁ + genRank (B := B) M₃ := by
  haveI : Module.Flat B (FractionRing B) := IsLocalization.flat (FractionRing B) (nonZeroDivisors B)
  have hf' : Function.Injective (f.baseChange (FractionRing B)) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hg' : Function.Surjective (g.baseChange (FractionRing B)) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective (FractionRing B) hg
  have hex : Function.Exact (f.baseChange (FractionRing B)) (g.baseChange (FractionRing B)) := by
    have := Module.Flat.lTensor_exact (FractionRing B) hfg
    intro y
    have hy := this y
    simp only [LinearMap.baseChange_eq_ltensor, Set.mem_range] at hy ⊢
    exact hy
  have h1 := LinearMap.finrank_range_add_finrank_ker (g.baseChange (FractionRing B))
  rw [LinearMap.range_eq_top.mpr hg', finrank_top, LinearMap.exact_iff.mp hex,
    LinearMap.finrank_range_of_inj hf'] at h1
  unfold genRank
  omega

end GenericRank

section Dim

variable {V : Scheme.{u}}

theorem dim_top_le (d : ℕ) (hd : topologicalKrullDim V ≤ d) : topologicalKrullDim ((⊤ : Closeds V) : Set V) ≤ d :=
  (Topology.IsInducing.topologicalKrullDim_le (Topology.IsEmbedding.subtypeVal.isInducing)).trans hd

theorem dim_nonneg (Y : Closeds V) (hY : (Y : Set V).Nonempty) : 0 ≤ topologicalKrullDim Y := by
  obtain ⟨y, hy⟩ := hY
  exact Order.krullDim_nonneg_iff.mpr
    ⟨⟨closure {(⟨y, hy⟩ : (Y : Set V))}, isIrreducible_singleton.closure, isClosed_closure⟩⟩

theorem withBot_aux (D : WithBot ℕ∞) (hD : 0 ≤ D) (d : ℕ) (h : D + 1 ≤ (d : WithBot ℕ∞)) :
    1 ≤ d ∧ D ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by
  induction D using WithBot.recBotCoe with
  | bot => exact absurd (le_bot_iff.mp hD) (by simp)
  | coe m =>
    have h' : m + 1 ≤ (d : ℕ∞) := by
      have : ((m + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      exact_mod_cast this
    induction m using ENat.recTopCoe with
    | top => simp at h'
    | coe n =>
      have hn : n + 1 ≤ d := by exact_mod_cast h'
      refine ⟨by omega, ?_⟩
      have hn' : n ≤ d - 1 := by omega
      have : (n : ℕ∞) ≤ ((d - 1 : ℕ) : ℕ∞) := (ENat.coe_le_coe).mpr hn'
      exact (WithBot.coe_le_coe).mpr this

theorem dim_lt_of_ne_top [IrreducibleSpace V] (Z₀ : Closeds V) (hne : (Z₀ : Set V).Nonempty) (hZ : Z₀ ≠ ⊤)
    (d : ℕ) (hd : topologicalKrullDim V ≤ d) :
    1 ≤ d ∧ topologicalKrullDim (Z₀ : Set V) ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by
  have hneU : (Z₀ : Set V) ≠ Set.univ := fun h => hZ (Closeds.ext (by simpa using h))
  have hstep : topologicalKrullDim (Z₀ : Set V) + 1 ≤ topologicalKrullDim (Set.univ : Set V) :=
    (IrreducibleSpace.isIrreducible_univ V).topologicalKrullDim_add_one_le_of_isClosed_of_ne Z₀.isClosed
      (Set.subset_univ _) hneU
  have huniv : topologicalKrullDim (Set.univ : Set V) ≤ d :=
    (Topology.IsInducing.topologicalKrullDim_le (Topology.IsEmbedding.subtypeVal.isInducing)).trans hd
  exact withBot_aux _ (dim_nonneg Z₀ hne) d (hstep.trans huniv)

end Dim

section Twist

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

theorem supportedIn_top (G : OModulePresheaf π) : G.SupportedIn ⊤ := by
  intro U hU
  have hUe : (U.1 : Set V) = ∅ := by simpa [Closeds.coe_top, Set.inter_univ] using hU
  have hbot : U.1 = ⊥ := by ext x; simp [hUe]
  have hs : Subsingleton Γ(V, U.1) := by rw [hbot]; infer_instance
  refine ⟨fun x y => ?_⟩
  have h1 : (1 : Γ(V, U.1)) = 0 := Subsingleton.elim _ _
  rw [← one_smul Γ(V, U.1) x, ← one_smul Γ(V, U.1) y, h1, zero_smul, zero_smul]

theorem poly_eq_of_eval_eq (p p' : ℚ[X]) (h : ∀ n : ℕ, p.eval (n : ℚ) = p'.eval (n : ℚ)) : p = p' :=
  Polynomial.eq_of_infinite_eval_eq p p'
    ((Set.infinite_range_of_injective Nat.cast_injective).mono (by rintro _ ⟨m, rfl⟩; exact h m))

end Twist

section DatumRank

variable {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k))
variable (U₀ : V.affineOpens) (𝔭 : PrimeSpectrum Γ(V, U₀.1))

noncomputable def rk (G : OModulePresheaf π) : ℕ := Module.rankAtStalk (R := Γ(V, U₀.1)) (G.obj U₀.1) 𝔭

include 𝔭 in

theorem nonempty_chart : Nonempty U₀.1 := by
  by_contra h
  have hbot : U₀.1 = ⊥ := by
    ext x
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => h ⟨⟨x, hx⟩⟩
  have hs : Subsingleton Γ(V, U₀.1) := by rw [hbot]; infer_instance
  exact 𝔭.2.ne_top (Subsingleton.elim _ _)

theorem rk_eq_zero_of_subsingleton (G : OModulePresheaf π) (hG : ∀ U : V.affineOpens, Subsingleton (G.obj U.1)) :
    rk π U₀ 𝔭 G = 0 := by
  haveI := hG U₀
  unfold rk
  rw [Module.rankAtStalk_eq_zero_of_subsingleton]
  rfl

variable [IsIntegral V] (h𝔭 : 𝔭.asIdeal = ⊥)

include h𝔭 in

theorem rk_add {G₁ G₂ G₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES G₁ G₂ G₃) (h₂c : G₂.IsCoherent) :
    rk π U₀ 𝔭 G₂ = rk π U₀ 𝔭 G₁ + rk π U₀ 𝔭 G₃ := by
  haveI := nonempty_chart U₀ 𝔭
  haveI : Module.Finite Γ(V, U₀.1) (G₂.obj U₀.1) := h₂c U₀
  unfold rk
  rw [rankAtStalk_eq_genRank 𝔭 h𝔭, rankAtStalk_eq_genRank 𝔭 h𝔭, rankAtStalk_eq_genRank 𝔭 h𝔭]
  have hex : Function.Exact (S.inc.appSections U₀) (S.proj.appSections U₀) := by
    have h : Function.Exact (S.inc.app U₀) (S.proj.app U₀) := LinearMap.exact_iff.mpr (S.exact U₀).symm
    exact h
  exact genRank_add (S.inc.appSections U₀) (S.proj.appSections U₀) (S.injective U₀) (S.surjective U₀) hex

include h𝔭 in

theorem rk_eq_zero_of_supportedIn (G : OModulePresheaf π) (hq : G.IsQuasicoherent) (Y : Closeds V)
    (hY : G.SupportedIn Y) (x : V) (hxU : x ∈ U₀.1) (hxY : x ∉ Y) : rk π U₀ 𝔭 G = 0 := by
  haveI := nonempty_chart U₀ 𝔭

  obtain ⟨a, hale, hxa⟩ := U₀.2.exists_basicOpen_le (V := U₀.1 ⊓ Y.compl) ⟨x, ⟨hxU, hxY⟩⟩ hxU
  have hdisj : ((V.basicOpen a : V.Opens) : Set V) ∩ Y = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false, not_and]
    intro hz hzY
    exact ((hale hz).2) hzY
  have hsub : Subsingleton (G.obj (V.basicOpen a)) := hY ⟨V.basicOpen a, U₀.2.basicOpen a⟩ hdisj
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hxa
    exact hxa
  refine rankAtStalk_eq_zero_of_forall_exists_smul_eq_zero 𝔭 fun m => ?_
  obtain ⟨n, hn⟩ := (hq U₀ a).2 m (Subsingleton.elim _ _)
  refine ⟨a ^ n, ?_, hn⟩
  rw [h𝔭]
  exact pow_ne_zero n ha0

end DatumRank

section TopCase

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V)

noncomputable def actApp (U : V.affineOpens) : (unit π).obj U.1 →ₗ[R] (pushforwardUnit π ι).obj U.1 where
  toFun a := show Γ(Z, ι ⁻¹ᵁ U.1) from ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a
  map_add' a b := map_add _ a b
  map_smul' r a := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U.1
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (ι ≫ π) (ι ⁻¹ᵁ U.1)
    show ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (algebraMap R Γ(V, U.1) r * (show Γ(V, U.1) from a)) =
      algebraMap R Γ(Z, ι ⁻¹ᵁ U.1) r * ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (show Γ(V, U.1) from a)
    rw [map_mul, OModulePresheaf.appLE_algebraMap]

theorem actApp_apply (U : V.affineOpens) (a : Γ(V, U.1)) :
    actApp π ι U (show (unit π).obj U.1 from a) =
      (show (pushforwardUnit π ι).obj U.1 from ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a) := rfl

noncomputable def actHom : AffHom (unit π) (pushforwardUnit π ι) where
  app U := actApp π ι U
  app_smul U a x := by
    show ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (a * (show Γ(V, U.1) from x)) =
      ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a * ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (show Γ(V, U.1) from x)
    exact map_mul _ a _
  naturality {U U'} h := by
    refine LinearMap.ext fun a => ?_
    show ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl ((V.presheaf.map (homOfLE h).op) a) =
      Z.presheaf.map (homOfLE ((Opens.map ι.base).monotone h)).op (ι.appLE U'.1 (ι ⁻¹ᵁ U'.1) le_rfl a)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem actHom_app (U : V.affineOpens) : (actHom π ι).app U = actApp π ι U := rfl

theorem actHom_bijective [IsReduced V] (U : V.affineOpens) :
    Function.Bijective ((actHom π (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds V)).subschemeι).app U) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds V) with hI
  have hIbot : I = ⊥ := by rw [hI, Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]
  have heq : ∀ a : Γ(V, U.1), (actHom π I.subschemeι).app U a = I.subschemeι.app U.1 a := fun a => by
    show I.subschemeι.appLE U.1 _ le_rfl a = _
    rw [Scheme.Hom.appLE_eq_app]
  constructor
  · intro a b hab
    rw [heq, heq] at hab
    have hker : RingHom.ker (I.subschemeι.app U.1).hom = ⊥ := by
      rw [Scheme.IdealSheafData.ker_subschemeι_app I U, hIbot]; rfl
    exact (RingHom.injective_iff_ker_eq_bot _).mpr hker hab
  · intro y
    obtain ⟨a, ha⟩ := I.subschemeι_app_surjective U y
    exact ⟨a, (heq a).trans ha⟩

variable (G : OModulePresheaf π)

noncomputable def appT {F F' : OModulePresheaf π} (φ : AffHom F F') (U : V.affineOpens) :
    (F.tensor G).obj U.1 →ₗ[R] (F'.tensor G).obj U.1 where
  toFun t := show (F'.tensor G).obj U.1 from
    (φ.appSections U).rTensor (G.obj U.1) (show F.obj U.1 ⊗[Γ(V, U.1)] G.obj U.1 from t)
  map_add' s t := map_add ((φ.appSections U).rTensor (G.obj U.1)) s t
  map_smul' r t := map_smul ((φ.appSections U).rTensor (G.obj U.1))
    ((Scheme.TwoAffineOpenCover.algebraOfHom π U.1).algebraMap r) t

noncomputable def rTensorAffHom {F F' : OModulePresheaf π} (φ : AffHom F F') : AffHom (F.tensor G) (F'.tensor G) where
  app U := appT π G φ U
  app_smul U a t := map_smul ((φ.appSections U).rTensor (G.obj U.1)) a t
  naturality {U U'} h := by
    refine LinearMap.ext fun t => ?_
    show (φ.appSections U).rTensor (G.obj U.1) (F.tensorResₛₗ G h t) =
      F'.tensorResₛₗ G h ((φ.appSections U').rTensor (G.obj U'.1) t)
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      rw [tensorResₛₗ_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, tensorResₛₗ_tmul,
        AffHom.appSections_apply, AffHom.appSections_apply, φ.naturality_apply h]
    | add s t hs ht => simp only [map_add, hs, ht]

theorem rTensorAffHom_bijective {F F' : OModulePresheaf π} (φ : AffHom F F') (U : V.affineOpens)
    (hφ : Function.Bijective (φ.app U)) : Function.Bijective ((rTensorAffHom π G φ).app U) := by
  let e : F.obj U.1 ≃ₗ[Γ(V, U.1)] F'.obj U.1 := LinearEquiv.ofBijective (φ.appSections U) hφ
  have key : ∀ t : F.obj U.1 ⊗[Γ(V, U.1)] G.obj U.1,
      (φ.appSections U).rTensor (G.obj U.1) t = LinearEquiv.rTensor (G.obj U.1) e t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => rw [LinearMap.rTensor_tmul, LinearEquiv.rTensor_tmul]; rfl
    | add s t hs ht => simp only [map_add, hs, ht]
  constructor
  · intro s t hst
    exact (LinearEquiv.rTensor (G.obj U.1) e).injective (by rw [← key, ← key]; exact hst)
  · intro y
    obtain ⟨t, ht⟩ := (LinearEquiv.rTensor (G.obj U.1) e).surjective y
    exact ⟨t, (key t).trans ht⟩

variable (N : V.Modules)

noncomputable def lidApp (U : V.affineOpens) : ((unit π).twist N).obj U.1 →ₗ[R] (ofModules π N).obj U.1 where
  toFun t := show Γ(N, U.1) from TensorProduct.lid Γ(V, U.1) Γ(N, U.1) (show Γ(V, U.1) ⊗[Γ(V, U.1)] Γ(N, U.1) from t)
  map_add' s t := map_add _ s t
  map_smul' r t := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U.1
    show TensorProduct.lid Γ(V, U.1) Γ(N, U.1) (algebraMap R Γ(V, U.1) r • (show Γ(V, U.1) ⊗[Γ(V, U.1)] Γ(N, U.1) from t))
      = algebraMap R Γ(V, U.1) r • TensorProduct.lid Γ(V, U.1) Γ(N, U.1) _
    exact map_smul _ _ _

theorem lidApp_tmul (U : V.affineOpens) (a : Γ(V, U.1)) (n : Γ(N, U.1)) :
    lidApp π N U (show ((unit π).twist N).obj U.1 from a ⊗ₜ[Γ(V, U.1)] n) = (show Γ(N, U.1) from a • n) := rfl

noncomputable def lidHom : AffHom ((unit π).twist N) (ofModules π N) where
  app U := lidApp π N U
  app_smul U a t := map_smul (TensorProduct.lid Γ(V, U.1) Γ(N, U.1)) a _
  naturality {U U'} h := by
    refine LinearMap.ext fun t => ?_
    show lidApp π N U (((unit π).twist N).res h t) = (ofModules π N).res h (lidApp π N U' t)
    induction t using TensorProduct.induction_on with
    | zero =>
      refine (congrArg (lidApp π N U) (map_zero _)).trans ?_
      refine (map_zero _).trans ?_
      exact ((congrArg ((ofModules π N).res h) (map_zero _)).trans (map_zero _)).symm
    | tmul a n => exact ((ofModules π N).res_smul h a n).symm
    | add s t hs ht =>
      refine (congrArg (lidApp π N U) (map_add _ s t)).trans ?_
      refine (map_add _ _ _).trans ?_
      refine (congrArg₂ (· + ·) hs ht).trans ?_
      exact ((congrArg ((ofModules π N).res h) (map_add _ s t)).trans (map_add _ _ _)).symm

theorem lidHom_bijective (U : V.affineOpens) : Function.Bijective ((lidHom π N).app U) :=
  (TensorProduct.lid Γ(V, U.1) Γ(N, U.1)).bijective

theorem eulerChar_top_twist_eq [IsSeparated π] [IsReduced V] (K : V.OrderedAffineCover) :
    ((pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds V)).subschemeι).twist N).eulerChar K =
      (ofModules π N).eulerChar K := by
  set ι := (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds V)).subschemeι
  have h1 := AffHom.nonempty_H0_equiv_and_HSucc_equiv_of_bijective (rTensorAffHom π (ofModules π N) (actHom π ι))
    (fun U => rTensorAffHom_bijective π (ofModules π N) (actHom π ι) U (actHom_bijective π U)) K
  have h2 := AffHom.nonempty_H0_equiv_and_HSucc_equiv_of_bijective (lidHom π N) (lidHom_bijective π N) K
  have hcf : ∀ i, ((pushforwardUnit π ι).twist N).cechFinrank K i = (ofModules π N).cechFinrank K i := by
    intro i
    cases i with
    | zero =>
      obtain ⟨e1⟩ := h1.1
      obtain ⟨e2⟩ := h2.1
      exact (e1.symm.trans e2).finrank_eq
    | succ j =>
      obtain ⟨e1⟩ := h1.2 j
      obtain ⟨e2⟩ := h2.2 j
      exact (e1.symm.trans e2).finrank_eq
  rw [eulerChar_def, eulerChar_def]
  exact Finset.sum_congr rfl fun i _ => by rw [hcf i]

theorem rankAtStalk_top [IsReduced V] (U₀ : V.affineOpens) [Nontrivial Γ(V, U₀.1)] (𝔭 : PrimeSpectrum Γ(V, U₀.1)) :
    Module.rankAtStalk (R := Γ(V, U₀.1))
      ((pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds V)).subschemeι).obj U₀.1) 𝔭 = 1 := by
  set ι := (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds V)).subschemeι
  let e : Γ(V, U₀.1) ≃ₗ[Γ(V, U₀.1)] (pushforwardUnit π ι).obj U₀.1 :=
    LinearEquiv.ofBijective ((actHom π ι).appSections U₀) (actHom_bijective π U₀)
  have h := Module.rankAtStalk_eq_of_equiv e
  have h1 : Module.rankAtStalk (R := Γ(V, U₀.1)) Γ(V, U₀.1) = 1 := Module.rankAtStalk_self
  rw [← h, h1]
  rfl

end TopCase

section Main

variable {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π] [IsIntegral V]
variable (K : V.OrderedAffineCover) (L : V.Modules)
  (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
  (d : ℕ) (hd : topologicalKrullDim V ≤ d)
  (q : ℚ[X]) (hq : ∀ m : ℕ, ((ofModules π (L.tensorPow m)).eulerChar K : ℚ) = q.eval (m : ℚ))
  (U₀ : V.affineOpens) (𝔭 : PrimeSpectrum Γ(V, U₀.1)) (h𝔭 : 𝔭.asIdeal = ⊥)

def Q (_Y : Closeds V) (G : OModulePresheaf π) : Prop :=
  ∀ p : ℚ[X], (∀ m : ℕ, (chi π K L G m : ℚ) = p.eval (m : ℚ)) → p.coeff d = (rk π U₀ 𝔭 G : ℚ) * q.coeff d

omit [IsIntegral V] in
include hL hd in

theorem exists_poly (G : OModulePresheaf π) (hc : G.IsCoherent) (hqc : G.IsQuasicoherent) :
    ∃ p : ℚ[X], p.natDegree ≤ d ∧ ∀ m : ℕ, (chi π K L G m : ℚ) = p.eval (m : ℚ) :=
  exists_polynomial_forall_eulerChar_twist_tensorPow_eq π K G hc hqc ⊤ (supportedIn_top π G) d (dim_top_le d hd) L hL

omit [IsIntegral V] in
theorem Q_zero (Y : Closeds V) (G : OModulePresheaf π) (hG : ∀ U : V.affineOpens, Subsingleton (G.obj U.1)) :
    Q π K L d q U₀ 𝔭 Y G := by
  intro p hp
  have hp0 : p = 0 := poly_eq_of_eval_eq p 0 fun n => by
    rw [← hp n, chi_eq_zero_of_subsingleton π K L G hG n, eval_zero, Int.cast_zero]
  rw [hp0, coeff_zero, rk_eq_zero_of_subsingleton π U₀ 𝔭 G hG, Nat.cast_zero, zero_mul]

omit [IsProper π] [IsIntegral V] in
theorem Q_mono (Y Y' : Closeds V) (G : OModulePresheaf π) (_h : Y' ≤ Y) (hQ : Q π K L d q U₀ 𝔭 Y' G) :
    Q π K L d q U₀ 𝔭 Y G := hQ

include hL hd h𝔭 in
theorem Q_ext (Y : Closeds V) (G₁ G₂ G₃ : OModulePresheaf π) (hS : Nonempty (OModulePresheaf.AffSES G₁ G₂ G₃))
    (h₁c : G₁.IsCoherent) (h₁q : G₁.IsQuasicoherent) (h₂c : G₂.IsCoherent) (h₂q : G₂.IsQuasicoherent)
    (h₃c : G₃.IsCoherent) (h₃q : G₃.IsQuasicoherent) :
    (Q π K L d q U₀ 𝔭 Y G₁ → Q π K L d q U₀ 𝔭 Y G₃ → Q π K L d q U₀ 𝔭 Y G₂) ∧
      (Q π K L d q U₀ 𝔭 Y G₁ → Q π K L d q U₀ 𝔭 Y G₂ → Q π K L d q U₀ 𝔭 Y G₃) ∧
      (Q π K L d q U₀ 𝔭 Y G₂ → Q π K L d q U₀ 𝔭 Y G₃ → Q π K L d q U₀ 𝔭 Y G₁) := by
  obtain ⟨S⟩ := hS
  have hadd := chi_add π K L hL S h₁c h₁q h₂c h₂q h₃c h₃q
  have hrk : (rk π U₀ 𝔭 G₂ : ℚ) = rk π U₀ 𝔭 G₁ + rk π U₀ 𝔭 G₃ := by
    rw [rk_add π U₀ 𝔭 h𝔭 S h₂c]; push_cast; ring
  obtain ⟨p₁, -, hp₁⟩ := exists_poly π K L hL d hd G₁ h₁c h₁q
  obtain ⟨p₂, -, hp₂⟩ := exists_poly π K L hL d hd G₂ h₂c h₂q
  obtain ⟨p₃, -, hp₃⟩ := exists_poly π K L hL d hd G₃ h₃c h₃q
  have hsum : p₂ = p₁ + p₃ := poly_eq_of_eval_eq p₂ (p₁ + p₃) fun n => by
    rw [eval_add, ← hp₁ n, ← hp₂ n, ← hp₃ n, hadd n]; push_cast; ring
  refine ⟨fun hQ₁ hQ₃ p hp => ?_, fun hQ₁ hQ₂ p hp => ?_, fun hQ₂ hQ₃ p hp => ?_⟩
  · have hpp : p = p₂ := poly_eq_of_eval_eq p p₂ fun n => by rw [← hp n, hp₂ n]
    rw [hpp, hsum, coeff_add, hQ₁ p₁ hp₁, hQ₃ p₃ hp₃, hrk]; ring
  · have hpp : p = p₃ := poly_eq_of_eval_eq p p₃ fun n => by rw [← hp n, hp₃ n]
    have h2 := hQ₂ p₂ hp₂
    rw [hsum, coeff_add, hQ₁ p₁ hp₁, hrk] at h2
    rw [hpp]
    linear_combination h2
  · have hpp : p = p₁ := poly_eq_of_eval_eq p p₁ fun n => by rw [← hp n, hp₁ n]
    have h2 := hQ₂ p₂ hp₂
    rw [hsum, coeff_add, hQ₃ p₃ hp₃, hrk] at h2
    rw [hpp]
    linear_combination h2

include hL hd hq h𝔭 in

theorem Q_int (Z₀ : Closeds V) (hne : (Z₀ : Set V).Nonempty)
    (_hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme) :
    Q π K L d q U₀ 𝔭 Z₀ (OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι) := by
  haveI := nonempty_chart U₀ 𝔭
  set ι := (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι with hι
  obtain ⟨hOc, hOq, hOs⟩ := isCoherent_isQuasicoherent_supportedIn_pushforwardUnit π ι
  have hOs' : (pushforwardUnit π ι).SupportedIn Z₀ := by
    have hrange : (⟨Set.range ι.base, ι.isClosedEmbedding.isClosed_range⟩ : Closeds V) = Z₀ := by
      apply Closeds.ext
      simp only [Closeds.coe_mk]
      rw [hι, Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    intro U hU
    refine hOs U ?_
    rw [hrange]
    exact hU
  by_cases hZ : Z₀ = ⊤
  ·
    subst hZ
    intro p hp
    have hpq : p = q := poly_eq_of_eval_eq p q fun n => by
      rw [← hp n, ← hq n]
      exact congrArg (fun z : ℤ => (z : ℚ)) (eulerChar_top_twist_eq π (L.tensorPow n) K)
    rw [hpq]
    unfold rk
    rw [rankAtStalk_top π U₀ 𝔭, Nat.cast_one, one_mul]
  ·
    obtain ⟨hd1, hdim⟩ := dim_lt_of_ne_top Z₀ hne hZ d hd
    obtain ⟨p₀, hp₀, hχ₀⟩ := exists_polynomial_forall_eulerChar_twist_tensorPow_eq π K (pushforwardUnit π ι) hOc hOq
      Z₀ hOs' (d - 1) hdim L hL
    intro p hp
    have hpp : p = p₀ := poly_eq_of_eval_eq p p₀ fun n => by rw [← hp n, ← hχ₀ n]; rfl

    obtain ⟨x, hxU, hxZ⟩ : ∃ x : V, x ∈ U₀.1 ∧ x ∉ Z₀ := by
      have hZc : ((Z₀ : Set V)ᶜ).Nonempty := by
        rw [Set.nonempty_compl]
        exact fun h => hZ (Closeds.ext (by simpa using h))
      obtain ⟨u⟩ := (inferInstance : Nonempty U₀.1)
      obtain ⟨x, hxU, hxZ⟩ := nonempty_preirreducible_inter U₀.1.isOpen Z₀.isClosed.isOpen_compl ⟨u.1, u.2⟩ hZc
      exact ⟨x, hxU, hxZ⟩
    rw [hpp, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      rk_eq_zero_of_supportedIn π U₀ 𝔭 h𝔭 (pushforwardUnit π ι) hOq Z₀ hOs' x hxU hxZ, Nat.cast_zero, zero_mul]

include hL hd hq h𝔭 in

theorem card (F : OModulePresheaf π) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent) (p : ℚ[X])
    (hp : ∀ m : ℕ, ((F.twist (L.tensorPow m)).eulerChar K : ℚ) = p.eval (m : ℚ)) :
    p.coeff d = (Module.rankAtStalk (R := Γ(V, U₀.1)) (F.obj U₀.1) 𝔭 : ℚ) * q.coeff d := by
  have main := forall_coherent_of_forall_integral π (Q π K L d q U₀ 𝔭)
    (fun Y G hG => Q_zero π K L d q U₀ 𝔭 Y G hG) (fun Y Y' G h hQ => Q_mono π K L d q U₀ 𝔭 Y Y' G h hQ)
    (fun Y G₁ G₂ G₃ hS h₁c h₁q h₂c h₂q h₃c h₃q => Q_ext π K L hL d hd q U₀ 𝔭 h𝔭 Y G₁ G₂ G₃ hS h₁c h₁q h₂c h₂q h₃c h₃q)
    (fun Z₀ hne hint _ => Q_int π K L hL d hd q hq U₀ 𝔭 h𝔭 Z₀ hne hint)
    ⊤ F hc hqc (supportedIn_top π F)
  exact main p hp

end Main

end P2mLead

theorem solution
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π] [IsIntegral V]
    (K : V.OrderedAffineCover) (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (d : ℕ) (hd : topologicalKrullDim V ≤ d)
    (q : Polynomial ℚ)
    (hq : ∀ m : ℕ, ((OModulePresheaf.ofModules π (L.tensorPow m)).eulerChar K : ℚ) = q.eval (m : ℚ))
    (F : OModulePresheaf π) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (p : Polynomial ℚ)
    (hp : ∀ m : ℕ, ((F.twist (L.tensorPow m)).eulerChar K : ℚ) = p.eval (m : ℚ))
    (U₀ : V.affineOpens) (𝔭 : PrimeSpectrum Γ(V, U₀.1)) (h𝔭 : 𝔭.asIdeal = ⊥) :
    p.coeff d = (Module.rankAtStalk (R := Γ(V, U₀.1)) (F.obj U₀.1) 𝔭 : ℚ) * q.coeff d :=
  P2mLead.card π K L hL d hd q hq U₀ 𝔭 h𝔭 F hc hqc p hp

end S_AlgebraicGeometry_OModulePresheaf_coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq (solution)
