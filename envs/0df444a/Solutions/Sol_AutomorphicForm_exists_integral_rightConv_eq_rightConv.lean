-- Prove2me | solution 1 for AutomorphicForm.exists_integral_rightConv_eq_rightConv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/616c7c39-b53a-5ebb-9cc7-9a837da60deb

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_integral_rightConv_eq_rightConv
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped BigOperators Pointwise Topology

noncomputable section

namespace Ws1
namespace TestFnPacket

section Generic

variable {H G G' W : Type*} [Group H] [Group G] [Group G'] [AddCommGroup W] [Module ℂ W]

theorem comp_mem_typeSubmodule_of_map {ι : H →* G} {ι' : H →* G'} {ρ : Representation ℂ H W} (θ : G' → G)
    (hθ : ∀ (x : G') (k : H), θ (x * ι' k) = θ x * ι k) {f : G → ℂ} (hf : f ∈ typeSubmodule ι ρ) :
    (fun x => f (θ x)) ∈ typeSubmodule ι' ρ := by
  refine Submodule.span_induction (p := fun f _ => (fun x => f (θ x)) ∈ typeSubmodule ι' ρ) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    have hS : IsRightEquivariant ι' ρ ((LinearMap.funLeft ℂ ℂ θ) ∘ₗ T) := by
      intro k v' x
      show T (ρ k v') (θ x) = T v' (θ (x * ι' k))
      rw [hT k v' (θ x), hθ]
    exact mem_typeSubmodule_of_isRightEquivariant hS v
  · exact (typeSubmodule ι' ρ).zero_mem
  · exact fun _ _ _ _ hu hw => (typeSubmodule ι' ρ).add_mem hu hw
  · exact fun c _ _ hu => (typeSubmodule ι' ρ).smul_mem c hu

omit [Group G] [Group G'] in

theorem comp_mem_iSup_of_forall {I : Type*} (θ : G' → G) (p : I → Submodule ℂ (G → ℂ)) (q : I → Submodule ℂ (G' → ℂ))
    (h : ∀ i, ∀ f ∈ p i, (fun x => f (θ x)) ∈ q i) {f : G → ℂ} (hf : f ∈ ⨆ i, p i) :
    (fun x => f (θ x)) ∈ ⨆ i, q i := by
  refine Submodule.iSup_induction _ (motive := fun f => (fun x => f (θ x)) ∈ ⨆ i, q i) hf ?_ ?_ ?_
  · intro i f hfi
    exact Submodule.mem_iSup_of_mem i (h i f hfi)
  · exact Submodule.zero_mem _
  · intro a b ha hb
    exact Submodule.add_mem _ ha hb

end Generic

variable (F : Type) [Field F] [NumberField F]

theorem eq_of_glArch_eq_of_glFin_eq {a b : AdelicGL2 (𝓞 F) F}
    (h1 : glArch (𝓞 F) F a = glArch (𝓞 F) F b) (h2 : glFin (𝓞 F) F a = glFin (𝓞 F) F b) : a = b := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have e1 := congrArg
    (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h1
  have e2 := congrArg
    (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h2
  simp only [glArch_apply, glFin_apply] at e1 e2
  exact Prod.ext e1 e2

theorem commute_of_glArch_eq_one_of_glFin_eq_one {g k : AdelicGL2 (𝓞 F) F}
    (hg : glArch (𝓞 F) F g = 1) (hk : glFin (𝓞 F) F k = 1) : Commute g k := by
  show g * k = k * g
  apply eq_of_glArch_eq_of_glFin_eq F
  · rw [map_mul, map_mul, hg, one_mul, mul_one]
  · rw [map_mul, map_mul, hk, one_mul, mul_one]

theorem adelicArchGLIncl_archRowIsometryInclAt₀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    adelicArchGLIncl F (archRowIsometryInclAt₀ F w k) = rowIsometryInclAt₀ F w k := rfl

theorem glFin_eq_one_of_mem_iSup_range {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) : glFin (𝓞 F) F k = 1 := by
  refine Subgroup.iSup_induction _ (C := fun k => glFin (𝓞 F) F k = 1) hk ?_ (map_one _) ?_
  · rintro w k ⟨k', rfl⟩
    exact glFin_rowIsometryInclAt₀ F w k'
  · intro a b ha hb
    rw [map_mul, ha, hb, mul_one]

theorem finEmbed_glFin_of_glArch_eq_one {u : AdelicGL2 (𝓞 F) F} (hu : glArch (𝓞 F) F u = 1) :
    AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F u) = u :=
  eq_of_glArch_eq_of_glFin_eq F (by rw [AdelicDock.glArch_finEmbed, hu]) (AdelicDock.glFin_finEmbed _ _ _)

theorem continuous_finEmbed : Continuous (AdelicDock.finEmbed (𝓞 F) F) := by
  have hmat : Continuous (fun m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F) => AdelicDock.finMat (𝓞 F) F m) := by
    refine continuous_matrix fun i j => ?_
    exact continuous_const.prodMk (continuous_apply_apply i j)
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact hmat.comp Units.continuous_val
  · have : (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
        ((↑(AdelicDock.finEmbed (𝓞 F) F g)⁻¹ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))
        = fun g => AdelicDock.finMat (𝓞 F) F ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix _ _ _) := by
      funext g
      rw [← map_inv]
      rfl
    rw [this]
    exact hmat.comp Units.continuous_coe_inv

theorem comp_mem_archFactorCut_of_mem_archCut (tys : ArchTypeFamily F) (c d : AdelicGL2 (𝓞 F) F)
    (hd : glArch (𝓞 F) F d = 1) {h : AdelicGL2 (𝓞 F) F → ℂ} (hh : h ∈ archCutSubmodule F tys) :
    (fun x => h (c * adelicArchGLIncl F x * d)) ∈ archFactorCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hh
  refine (Submodule.mem_iInf _).mpr fun w => ?_
  refine comp_mem_iSup_of_forall (fun x => c * adelicArchGLIncl F x * d)
    (fun i => archTypeSubmoduleAt F w (tys.rep w i)) (fun i => archFactorTypeSubmoduleAt F w (tys.rep w i))
    (fun i f hf => ?_) (hh w)
  refine comp_mem_typeSubmodule_of_map _ (fun x k => ?_) hf
  rw [map_mul, adelicArchGLIncl_archRowIsometryInclAt₀, mul_assoc, mul_assoc,
    ← (commute_of_glArch_eq_one_of_glFin_eq_one F hd (glFin_rowIsometryInclAt₀ F w k)).eq, ← mul_assoc, ← mul_assoc]

theorem comp_mem_archFactorDualCut_of_mem_archDualCut (tys : ArchTypeFamily F) (c d : AdelicGL2 (𝓞 F) F)
    (hd : glArch (𝓞 F) F d = 1) {h : AdelicGL2 (𝓞 F) F → ℂ} (hh : h ∈ archDualCutSubmodule F tys) :
    (fun x => h (c * adelicArchGLIncl F x * d)) ∈ archFactorDualCutSubmodule F tys := by
  rw [mem_archDualCutSubmodule_iff] at hh
  refine (Submodule.mem_iInf _).mpr fun w => ?_
  refine comp_mem_iSup_of_forall (fun x => c * adelicArchGLIncl F x * d)
    (fun i => archDualTypeSubmoduleAt F w (tys.rep w i)) (fun i => archFactorDualTypeSubmoduleAt F w (tys.rep w i))
    (fun i f hf => ?_) (hh w)
  refine comp_mem_typeSubmodule_of_map _ (fun x k => ?_) hf
  rw [map_mul, adelicArchGLIncl_archRowIsometryInclAt₀, mul_assoc, mul_assoc,
    ← (commute_of_glArch_eq_one_of_glFin_eq_one F hd (glFin_rowIsometryInclAt₀ F w k)).eq, ← mul_assoc, ← mul_assoc]

theorem isArchFactorBiFinite_of_isArchBiFinite {tys : ArchTypeFamily F} {f : AdelicGL2 (𝓞 F) F → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hf : ∀ g, f g = fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) (hbf : IsArchBiFinite F tys f)
    {b₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hb₀ : ff b₀ ≠ 0) : IsArchFactorBiFinite F tys fa := by
  set e : AdelicGL2 (𝓞 F) F := AdelicDock.finEmbed (𝓞 F) F b₀ with he
  have hea : glArch (𝓞 F) F e = 1 := AdelicDock.glArch_finEmbed _ _ _
  have hef : glFin (𝓞 F) F e = b₀ := AdelicDock.glFin_finEmbed _ _ _
  constructor
  ·
    have h1 := comp_mem_archFactorCut_of_mem_archCut F tys e⁻¹ 1 (map_one _) hbf.1
    have hfun : (fun x : GL (Fin 2) (InfiniteAdeleRing F) => fa x⁻¹)
        = (ff b₀)⁻¹ • fun x => (fun z => f z⁻¹) (e⁻¹ * adelicArchGLIncl F x * 1) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, mul_one, mul_inv_rev, inv_inv]
      rw [hf, map_mul, map_mul, map_inv, map_inv, glArch_adelicArchGLIncl, glFin_adelicArchGLIncl, hea, hef,
        mul_one, inv_one, one_mul, mul_comm (fa _) (ff b₀), inv_mul_cancel_left₀ hb₀]
    rw [hfun]
    exact Submodule.smul_mem _ _ h1
  ·
    have h2 := comp_mem_archFactorDualCut_of_mem_archDualCut F tys 1 e hea hbf.2
    have hfun : fa = (ff b₀)⁻¹ • fun x => f (1 * adelicArchGLIncl F x * e) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, one_mul]
      rw [hf, map_mul, map_mul, glArch_adelicArchGLIncl, glFin_adelicArchGLIncl, hea, hef, mul_one, one_mul,
        mul_comm (fa _) (ff b₀), inv_mul_cancel_left₀ hb₀]
    rw [hfun]
    exact Submodule.smul_mem _ _ h2

theorem isFactorizableTestFn_comp_mul_left_of_mem_finiteAdelic
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) (tys : ArchTypeFamily F)
    (hbf : IsArchBiFinite F tys f) {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F) :
    IsFactorizableTestFn F (fun y => f (g * y)) ∧ IsArchBiFinite F tys (fun y => f (g * y)) ∧
    IsFactorizableTestFn F (fun y => f (y * g)) ∧ IsArchBiFinite F tys (fun y => f (y * g)) := by
  obtain ⟨fa, ff, hfaT, hffT, hfeq⟩ := hf
  have hga : glArch (𝓞 F) F g = 1 := hg
  have hL : ∀ y, f (g * y) = fa (glArch (𝓞 F) F y) * (fun b => ff (glFin (𝓞 F) F g * b)) (glFin (𝓞 F) F y) := by
    intro y
    rw [hfeq, map_mul, map_mul, hga, one_mul]
  have hR : ∀ y, f (y * g) = fa (glArch (𝓞 F) F y) * (fun b => ff (b * glFin (𝓞 F) F g)) (glFin (𝓞 F) F y) := by
    intro y
    rw [hfeq, map_mul, map_mul, hga, mul_one]
  have hffL : IsFinTestFactor F (fun b => ff (glFin (𝓞 F) F g * b)) :=
    ⟨hffT.1.comp_continuous (continuous_const.mul continuous_id),
      hffT.2.comp_homeomorph (Homeomorph.mulLeft (glFin (𝓞 F) F g))⟩
  have hffR : IsFinTestFactor F (fun b => ff (b * glFin (𝓞 F) F g)) :=
    ⟨hffT.1.comp_continuous (continuous_id.mul continuous_const),
      hffT.2.comp_homeomorph (Homeomorph.mulRight (glFin (𝓞 F) F g))⟩
  by_cases hff : ∃ b₀, ff b₀ ≠ 0
  · obtain ⟨b₀, hb₀⟩ := hff
    have hfa : IsArchFactorBiFinite F tys fa := isArchFactorBiFinite_of_isArchBiFinite F hfeq hbf hb₀
    exact ⟨⟨fa, _, hfaT, hffL, hL⟩,
      IsArchBiFinite.of_factorization F (ff := fun b => ff (glFin (𝓞 F) F g * b)) hL hfa,
      ⟨fa, _, hfaT, hffR, hR⟩,
      IsArchBiFinite.of_factorization F (ff := fun b => ff (b * glFin (𝓞 F) F g)) hR hfa⟩
  · push Not at hff
    have h0L : (fun y => f (g * y)) = 0 := funext fun y => by rw [Pi.zero_apply, hfeq, hff, mul_zero]
    have h0R : (fun y => f (y * g)) = 0 := funext fun y => by rw [Pi.zero_apply, hfeq, hff, mul_zero]
    exact ⟨⟨fa, _, hfaT, hffL, hL⟩, h0L ▸ isArchBiFinite_zero F tys, ⟨fa, _, hfaT, hffR, hR⟩,
      h0R ▸ isArchBiFinite_zero F tys⟩

def sandwich (A B : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) where
  toFun m := fun p q => ∑ k : Fin 2, ∑ l : Fin 2,
    InfiniteAdeleRing.ringEquiv_mixedSpace F (A p k) * m k l * InfiniteAdeleRing.ringEquiv_mixedSpace F (B l q)
  map_add' m m' := by
    funext p q
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' r m := by
    funext p q
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, mul_smul_comm, smul_mul_assoc]

omit [NumberField F] in
theorem archEntries_mul_mul (A x B : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F (A * x * B) = sandwich F (A : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) B (archEntries F x) := by
  funext p q
  simp only [archEntries_apply, sandwich, LinearMap.coe_mk, AddHom.coe_mk, Units.val_mul, Matrix.mul_apply,
    Finset.sum_mul, map_sum, map_mul]
  rw [Finset.sum_comm]

open scoped Classical in
theorem isFactorizableTestFn_sum_mul_translate_of_mem_iSup_range
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) {n : ℕ} (c : Fin n → ℂ)
    (a b : Fin n → AdelicGL2 (𝓞 F) F)
    (ha : ∀ i, a i ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range)
    (hb : ∀ i, b i ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) :
    IsFactorizableTestFn F (fun y => ∑ i, c i * f (a i * y * b i)) := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfaΦ⟩, hfaS⟩, hffT, hfeq⟩ := hf
  have ha1 : ∀ i, glFin (𝓞 F) F (a i) = 1 := fun i => glFin_eq_one_of_mem_iSup_range F (ha i)
  have hb1 : ∀ i, glFin (𝓞 F) F (b i) = 1 := fun i => glFin_eq_one_of_mem_iSup_range F (hb i)
  have hfeq' : ∀ y, (∑ i, c i * f (a i * y * b i))
      = (fun x => ∑ i, c i * fa (glArch (𝓞 F) F (a i) * x * glArch (𝓞 F) F (b i))) (glArch (𝓞 F) F y)
        * ff (glFin (𝓞 F) F y) := by
    intro y
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfeq, map_mul, map_mul, map_mul, map_mul, ha1, hb1, one_mul, mul_one]
    ring
  refine ⟨fun x => ∑ i, c i * fa (glArch (𝓞 F) F (a i) * x * glArch (𝓞 F) F (b i)), ff,
    ⟨⟨fun m => ∑ i, c i * Φ ((sandwich F (glArch (𝓞 F) F (a i) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
      (glArch (𝓞 F) F (b i))).toContinuousLinearMap m), ?_, fun x => ?_⟩, ?_⟩, hffT, hfeq'⟩
  · exact ContDiff.sum fun i _ => contDiff_const.mul (hΦ.comp (ContinuousLinearMap.contDiff _))
  · simp only [LinearMap.coe_toContinuousLinearMap']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfaΦ, archEntries_mul_mul]
  ·
    refine HasCompactSupport.intro
      (isCompact_iUnion fun i : Fin n => hfaS.image
        (show Continuous (fun z : GL (Fin 2) (InfiniteAdeleRing F) =>
            (glArch (𝓞 F) F (a i))⁻¹ * z * (glArch (𝓞 F) F (b i))⁻¹) from
          (continuous_const.mul continuous_id).mul continuous_const)) fun x hx => ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    have hz : fa (glArch (𝓞 F) F (a i) * x * glArch (𝓞 F) F (b i)) = 0 := by
      by_contra hne
      apply hx
      refine Set.mem_iUnion.mpr ⟨i, glArch (𝓞 F) F (a i) * x * glArch (𝓞 F) F (b i),
        subset_tsupport _ (Function.mem_support.mpr hne), ?_⟩
      simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel_right]
    rw [hz, mul_zero]

theorem isFactorizableTestFn_subgroup_biAverage
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F) [MeasurableSpace U] [BorelSpace U]
    (μ : Measure U) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) (tys : ArchTypeFamily F)
    (hbf : IsArchBiFinite F tys f) :
    IsFactorizableTestFn F (fun y => ∫ u, ∫ u', f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * y * (u' : AdelicGL2 (𝓞 F) F)) ∂μ ∂μ) ∧
    IsArchBiFinite F tys (fun y => ∫ u, ∫ u', f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * y * (u' : AdelicGL2 (𝓞 F) F)) ∂μ ∂μ) ∧
    ∀ (x : AdelicGL2 (𝓞 F) F), ∀ u ∈ U,
      (fun y => ∫ u, ∫ u', f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * y * (u' : AdelicGL2 (𝓞 F) F)) ∂μ ∂μ) (u * x) =
        (fun y => ∫ u, ∫ u', f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * y * (u' : AdelicGL2 (𝓞 F) F)) ∂μ ∂μ) x ∧
      (fun y => ∫ u, ∫ u', f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * y * (u' : AdelicGL2 (𝓞 F) F)) ∂μ ∂μ) (x * u) =
        (fun y => ∫ u, ∫ u', f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * y * (u' : AdelicGL2 (𝓞 F) F)) ∂μ ∂μ) x := by
  obtain ⟨fa, ff, hfaT, hffT, hfeq⟩ := hf
  have hUa : ∀ u ∈ U, glArch (𝓞 F) F u = 1 := fun u hu => by rw [hUO] at hu; exact hu.2

  set G : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ := fun b =>
    ∫ u, ∫ u', ff ((glFin (𝓞 F) F (u : AdelicGL2 (𝓞 F) F))⁻¹ * b * glFin (𝓞 F) F (u' : AdelicGL2 (𝓞 F) F)) ∂μ ∂μ
    with hG
  have hint : ∀ (y : AdelicGL2 (𝓞 F) F) (u u' : U),
      f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * y * (u' : AdelicGL2 (𝓞 F) F))
        = fa (glArch (𝓞 F) F y) * ff ((glFin (𝓞 F) F (u : AdelicGL2 (𝓞 F) F))⁻¹ * glFin (𝓞 F) F y
            * glFin (𝓞 F) F (u' : AdelicGL2 (𝓞 F) F)) := by
    intro y u u'
    rw [hfeq, map_mul, map_mul, map_inv, hUa _ u.2, hUa _ u'.2, inv_one, one_mul, mul_one, map_mul, map_mul, map_inv]
  have hAvg : ∀ y, (∫ u, ∫ u', f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * y * (u' : AdelicGL2 (𝓞 F) F)) ∂μ ∂μ)
      = fa (glArch (𝓞 F) F y) * G (glFin (𝓞 F) F y) := by
    intro y
    simp only [hG, hint, integral_const_mul]

  set Uf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) with hUf
  have hUfc : IsCompact Uf := hU.image (continuous_glFin (𝓞 F) F)
  have hUf_mem : ∀ u : U, glFin (𝓞 F) F (u : AdelicGL2 (𝓞 F) F) ∈ Uf := fun u => ⟨u, u.2, rfl⟩
  have hUf_one : (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) ∈ Uf := ⟨1, U.one_mem, map_one _⟩
  have hUf_eq : Uf = (AdelicDock.finEmbed (𝓞 F) F) ⁻¹' (O : Set (AdelicGL2 (𝓞 F) F)) := by
    ext b
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : u ∈ O ⊓ finiteAdelicGL2Subgroup F := hUO ▸ hu
      show AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F u) ∈ (O : Set (AdelicGL2 (𝓞 F) F))
      rw [finEmbed_glFin_of_glArch_eq_one F hu'.2]
      exact hu'.1
    · intro hb
      refine ⟨AdelicDock.finEmbed (𝓞 F) F b, ?_, AdelicDock.glFin_finEmbed _ _ b⟩
      rw [hUO]
      exact ⟨hb, AdelicDock.glArch_finEmbed _ _ b⟩
  have hUfo : IsOpen Uf := by
    rw [hUf_eq]
    exact hO.preimage (continuous_finEmbed F)

  have hG_mul : ∀ (b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)), ∀ v ∈ Uf, G (b * v) = G b := by
    rintro b _ ⟨u₀, hu₀, rfl⟩
    simp only [hG]
    congr 1
    funext u
    have h := integral_mul_left_eq_self (μ := μ)
      (fun u' : U => ff ((glFin (𝓞 F) F (u : AdelicGL2 (𝓞 F) F))⁻¹ * b * glFin (𝓞 F) F (u' : AdelicGL2 (𝓞 F) F)))
      ⟨u₀, hu₀⟩
    simp only [Subgroup.coe_mul, map_mul, ← mul_assoc] at h ⊢
    exact h
  have hGT : IsFinTestFactor F G := by
    constructor
    · rw [IsLocallyConstant.iff_exists_open]
      intro b
      refine ⟨(fun b' => b⁻¹ * b') ⁻¹' Uf, hUfo.preimage (continuous_const.mul continuous_id), ?_, fun b' hb' => ?_⟩
      · show b⁻¹ * b ∈ Uf
        rw [inv_mul_cancel]
        exact hUf_one
      · rw [show b' = b * (b⁻¹ * b') by rw [mul_inv_cancel_left]]
        exact hG_mul b _ hb'
    · refine HasCompactSupport.intro ((hUfc.mul hffT.2).mul hUfc) fun b hb => ?_
      have hz : ∀ u u' : U, ff ((glFin (𝓞 F) F (u : AdelicGL2 (𝓞 F) F))⁻¹ * b
          * glFin (𝓞 F) F (u' : AdelicGL2 (𝓞 F) F)) = 0 := by
        intro u u'
        by_contra hne
        apply hb
        refine ⟨glFin (𝓞 F) F (u : AdelicGL2 (𝓞 F) F) * ((glFin (𝓞 F) F (u : AdelicGL2 (𝓞 F) F))⁻¹ * b
            * glFin (𝓞 F) F (u' : AdelicGL2 (𝓞 F) F)),
          Set.mul_mem_mul (hUf_mem u) (subset_tsupport _ (Function.mem_support.mpr hne)),
          (glFin (𝓞 F) F (u' : AdelicGL2 (𝓞 F) F))⁻¹, ?_, ?_⟩
        · rw [← map_inv]
          exact ⟨(u' : AdelicGL2 (𝓞 F) F)⁻¹, U.inv_mem u'.2, rfl⟩
        · simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel_right]
      show G b = 0
      simp only [hG, hz, integral_zero]
  refine ⟨⟨fa, G, hfaT, hGT, hAvg⟩, ?_, fun x u hu => ⟨?_, ?_⟩⟩
  ·
    by_cases hff : ∃ b₀, ff b₀ ≠ 0
    · obtain ⟨b₀, hb₀⟩ := hff
      exact IsArchBiFinite.of_factorization F hAvg (isArchFactorBiFinite_of_isArchBiFinite F hfeq hbf hb₀)
    · push Not at hff
      have h0 : (fun y => ∫ u, ∫ u', f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * y * (u' : AdelicGL2 (𝓞 F) F)) ∂μ ∂μ) = 0 := by
        funext y
        rw [hAvg y, Pi.zero_apply]
        simp only [hG, hff, integral_zero, mul_zero]
      rw [h0]
      exact isArchBiFinite_zero F tys
  ·
    have h := integral_mul_left_eq_self (μ := μ)
      (fun v : U => ∫ v', f ((v : AdelicGL2 (𝓞 F) F)⁻¹ * x * (v' : AdelicGL2 (𝓞 F) F)) ∂μ) (⟨u, hu⟩⁻¹)
    show (∫ v, ∫ v', f ((v : AdelicGL2 (𝓞 F) F)⁻¹ * (u * x) * (v' : AdelicGL2 (𝓞 F) F)) ∂μ ∂μ)
      = ∫ v, ∫ v', f ((v : AdelicGL2 (𝓞 F) F)⁻¹ * x * (v' : AdelicGL2 (𝓞 F) F)) ∂μ ∂μ
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc] at h ⊢
    exact h
  ·
    show (∫ v, ∫ v', f ((v : AdelicGL2 (𝓞 F) F)⁻¹ * (x * u) * (v' : AdelicGL2 (𝓞 F) F)) ∂μ ∂μ)
      = ∫ v, ∫ v', f ((v : AdelicGL2 (𝓞 F) F)⁻¹ * x * (v' : AdelicGL2 (𝓞 F) F)) ∂μ ∂μ
    have hfun : (fun v : U => ∫ v', f ((v : AdelicGL2 (𝓞 F) F)⁻¹ * (x * u) * (v' : AdelicGL2 (𝓞 F) F)) ∂μ)
        = fun v : U => ∫ v', f ((v : AdelicGL2 (𝓞 F) F)⁻¹ * x * (v' : AdelicGL2 (𝓞 F) F)) ∂μ := by
      funext v
      have h := integral_mul_left_eq_self (μ := μ)
        (fun v' : U => f ((v : AdelicGL2 (𝓞 F) F)⁻¹ * x * (v' : AdelicGL2 (𝓞 F) F))) ⟨u, hu⟩
      simp only [Subgroup.coe_mul, mul_assoc] at h ⊢
      exact h
    rw [hfun]

end Ws1.TestFnPacket

end

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped BigOperators Pointwise

noncomputable section

namespace Ws1
namespace ConvClose

variable (F : Type) [Field F] [NumberField F]
variable (U : Subgroup (AdelicGL2 (𝓞 F) F))
variable [MeasurableSpace U] [BorelSpace U] (μ : Measure U) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in

theorem integral_rightConv_apply_mul_eq (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    {φ f : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (hf : Continuous f)
    (hfs : HasCompactSupport f) (x : AdelicGL2 (𝓞 F) F) :
    ∫ u, rightConv F φ f (x * (u : AdelicGL2 (𝓞 F) F)) ∂μ =
      rightConv F φ (fun y => ∫ u, f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * y) ∂μ) x := by
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  set μG := adelicGLHaar (Fin 2) (𝓞 F) F with hμG
  show (∫ u, (∫ z, φ (x * (u : AdelicGL2 (𝓞 F) F) * z) * f z ∂μG) ∂μ) =
    ∫ z, φ (x * z) * (∫ u, f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * z) ∂μ) ∂μG
  have h1 : ∀ u : U, (∫ z, φ (x * (u : AdelicGL2 (𝓞 F) F) * z) * f z ∂μG) =
      ∫ z, φ (x * z) * f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * z) ∂μG := fun u => by
    rw [← integral_mul_left_eq_self (fun z => φ (x * z) * f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * z))
      (u : AdelicGL2 (𝓞 F) F)]
    simp only [mul_assoc, inv_mul_cancel_left]
  simp_rw [h1, ← integral_const_mul]
  refine integral_integral_swap (μ := μ) (ν := μG)
    (f := fun (u : U) (z : AdelicGL2 (𝓞 F) F) => φ (x * z) * f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * z)) ?_
  have hcont : Continuous (Function.uncurry fun (u : U) (z : AdelicGL2 (𝓞 F) F) =>
      φ (x * z) * f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * z)) :=
    (hφ.comp (continuous_const.mul continuous_snd)).mul
      (hf.comp ((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd))
  have hsupp : HasCompactSupport (Function.uncurry fun (u : U) (z : AdelicGL2 (𝓞 F) F) =>
      φ (x * z) * f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * z)) := by
    refine HasCompactSupport.intro (isCompact_univ.prod (hU.mul hfs)) ?_
    rintro ⟨u, z⟩ huz
    simp only [Function.uncurry_apply_pair]
    have hz : z ∉ (U : Set (AdelicGL2 (𝓞 F) F)) * tsupport f := fun hz => huz ⟨Set.mem_univ _, hz⟩
    have : f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * z) = 0 := by
      by_contra hne
      exact hz ⟨u, u.2, (u : AdelicGL2 (𝓞 F) F)⁻¹ * z, subset_tsupport _ (Function.mem_support.mpr hne),
        mul_inv_cancel_left _ _⟩
    rw [this, mul_zero]
  exact hcont.integrable_of_hasCompactSupport hsupp

theorem rightConv_eq_rightConv_avg (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    {φ f : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ)
    (hφ : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (x * u) = φ x) (hf : Continuous f) (hfs : HasCompactSupport f) :
    rightConv F φ f = rightConv F φ (fun y => ∫ u, f (y * (u : AdelicGL2 (𝓞 F) F)) ∂μ) := by
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  set μG := adelicGLHaar (Fin 2) (𝓞 F) F with hμG
  funext x
  show (∫ z, φ (x * z) * f z ∂μG) = ∫ z, φ (x * z) * (∫ u, f (z * (u : AdelicGL2 (𝓞 F) F)) ∂μ) ∂μG

  have h1 : ∀ u : U, (∫ z, φ (x * z) * f z ∂μG) = ∫ z, φ (x * z) * f (z * (u : AdelicGL2 (𝓞 F) F)) ∂μG := by
    intro u
    rw [← integral_mul_right_eq_self (fun z => φ (x * z) * f (z * (u : AdelicGL2 (𝓞 F) F)))
      (u : AdelicGL2 (𝓞 F) F)⁻¹]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [mul_assoc, inv_mul_cancel, mul_one]
    rw [← mul_assoc, hφ _ _ (U.inv_mem u.2)]
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap (μ := μG) (ν := μ)
    (f := fun (z : AdelicGL2 (𝓞 F) F) (u : U) => φ (x * z) * f (z * (u : AdelicGL2 (𝓞 F) F))) ?_]
  · simp_rw [← h1]
    simp
  have hcont : Continuous (Function.uncurry fun (z : AdelicGL2 (𝓞 F) F) (u : U) =>
      φ (x * z) * f (z * (u : AdelicGL2 (𝓞 F) F))) :=
    (hφc.comp (continuous_const.mul continuous_fst)).mul
      (hf.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))
  have hsupp : HasCompactSupport (Function.uncurry fun (z : AdelicGL2 (𝓞 F) F) (u : U) =>
      φ (x * z) * f (z * (u : AdelicGL2 (𝓞 F) F))) := by
    refine HasCompactSupport.intro ((hfs.mul hU).prod isCompact_univ) ?_
    rintro ⟨z, u⟩ huz
    simp only [Function.uncurry_apply_pair]
    have hz : z ∉ tsupport f * (U : Set (AdelicGL2 (𝓞 F) F)) := fun hz => huz ⟨hz, Set.mem_univ _⟩
    have : f (z * (u : AdelicGL2 (𝓞 F) F)) = 0 := by
      by_contra hne
      exact hz ⟨z * u, subset_tsupport _ (Function.mem_support.mpr hne), (u : AdelicGL2 (𝓞 F) F)⁻¹,
        U.inv_mem u.2, mul_inv_cancel_right _ _⟩
    rw [this, mul_zero]
  exact hcont.integrable_of_hasCompactSupport hsupp

omit [μ.IsHaarMeasure] in

theorem continuous_and_hasCompactSupport_rightAvg (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : Continuous f)
    (hfs : HasCompactSupport f) :
    Continuous (fun y => ∫ u, f (y * (u : AdelicGL2 (𝓞 F) F)) ∂μ) ∧
    HasCompactSupport (fun y => ∫ u, f (y * (u : AdelicGL2 (𝓞 F) F)) ∂μ) := by
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  constructor
  · obtain ⟨C, hC⟩ := (hfs.isCompact_range hf).isBounded.exists_norm_le
    refine continuous_of_dominated (bound := fun _ => C)
      (fun y => (hf.comp (continuous_const.mul continuous_subtype_val)).aestronglyMeasurable)
      (fun y => Filter.Eventually.of_forall fun u => hC _ (Set.mem_range_self _))
      (integrable_const C) (Filter.Eventually.of_forall fun u => hf.comp (continuous_id.mul continuous_const))
  · refine HasCompactSupport.intro (hfs.mul hU) fun y hy => ?_
    have hz : ∀ u : U, f (y * (u : AdelicGL2 (𝓞 F) F)) = 0 := by
      intro u
      by_contra hne
      exact hy ⟨y * u, subset_tsupport _ (Function.mem_support.mpr hne), (u : AdelicGL2 (𝓞 F) F)⁻¹,
        U.inv_mem u.2, mul_inv_cancel_right _ _⟩
    show (∫ u, f (y * (u : AdelicGL2 (𝓞 F) F)) ∂μ) = 0
    simp only [hz, integral_zero]

end Ws1.ConvClose

end

theorem solution
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    [MeasurableSpace U] [BorelSpace U] (μ : Measure U) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (tys : ArchTypeFamily F)
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hyc : Continuous y) (hyU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, y (x * u) = y x)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f) :
    ∃ f' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f' ∧ IsArchBiFinite F tys f' ∧
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, f' (u * x) = f' x ∧ f' (x * u) = f' x) ∧
      ∀ x : AdelicGL2 (𝓞 F) F, ∫ u, rightConv F y f (x * (u : AdelicGL2 (𝓞 F) F)) ∂μ = rightConv F y f' x := by
  obtain ⟨hfc, hfs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  obtain ⟨hgc, hgs⟩ := Ws1.ConvClose.continuous_and_hasCompactSupport_rightAvg F U μ hU hfc hfs
  obtain ⟨hT1, hT2, hT3⟩ :=
    Ws1.TestFnPacket.isFactorizableTestFn_subgroup_biAverage F U hU O hO hUO μ hf tys hbf
  refine ⟨_, hT1, hT2, hT3, fun x => ?_⟩

  rw [Ws1.ConvClose.rightConv_eq_rightConv_avg F U μ hU hyc hyU hfc hfs,
    Ws1.ConvClose.integral_rightConv_apply_mul_eq F U μ hU hyc hgc hgs x]

end S_AutomorphicForm_exists_integral_rightConv_eq_rightConv
end P2MW
export P2MW.S_AutomorphicForm_exists_integral_rightConv_eq_rightConv (solution)
