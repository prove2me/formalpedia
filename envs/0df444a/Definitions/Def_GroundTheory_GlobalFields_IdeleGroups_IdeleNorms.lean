-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
-- name    : GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:44.315813+00:00
-- url     : https://prove2.me/theorems/4843733e-4583-4859-a7f2-fc50af37a22c
-- title:
--   Idele Norms
-- statement:
--   Definitions and structural lemmas for Idele Norms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding


set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace IdeleGroup
variable {K}
@[simp] theorem adele_fst_mul_apply (a b : 𝔸[K]) (w : InfinitePlace K) :
    (a * b).1 w = a.1 w * b.1 w := rfl
@[simp] theorem adele_snd_mul_apply (a b : 𝔸[K]) (v : HeightOneSpectrum (𝓞 K)) :
    (a * b).2 v = a.2 v * b.2 v := rfl
@[simp] theorem adele_fst_one_apply (w : InfinitePlace K) : (1 : 𝔸[K]).1 w = 1 := rfl
@[simp] theorem adele_snd_one_apply (v : HeightOneSpectrum (𝓞 K)) : (1 : 𝔸[K]).2 v = 1 := rfl
theorem norm_eq_one_of_mul_eq_one {v : HeightOneSpectrum (𝓞 K)} {a b : v.adicCompletion K}
    (hab : a * b = 1) (ha : a ∈ v.adicCompletionIntegers K)
    (hb : b ∈ v.adicCompletionIntegers K) : ‖a‖ = 1 := by
  have ha' : ‖a‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 ha)
  have hb' : ‖b‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 hb)
  have h1 : ‖a‖ * ‖b‖ = 1 := by rw [← norm_mul, hab, norm_one]
  nlinarith [norm_nonneg a, norm_nonneg b]
theorem finite_mul_inv (x : IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    (x : 𝔸[K]).2 v * ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2 v = 1 := by
  have h : ((x : 𝔸[K]) * ((x⁻¹ : IdeleGroup K) : 𝔸[K])).2 v = 1 := by simp
  rwa [adele_snd_mul_apply] at h
theorem infinite_mul_inv (x : IdeleGroup K) (w : InfinitePlace K) :
    (x : 𝔸[K]).1 w * ((x⁻¹ : IdeleGroup K) : 𝔸[K]).1 w = 1 := by
  have h : ((x : 𝔸[K]) * ((x⁻¹ : IdeleGroup K) : 𝔸[K])).1 w = 1 := by simp
  rwa [adele_fst_mul_apply] at h
theorem finite_ne_zero (x : IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    (x : 𝔸[K]).2 v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (finite_mul_inv x v)
theorem infinite_ne_zero (x : IdeleGroup K) (w : InfinitePlace K) : (x : 𝔸[K]).1 w ≠ 0 :=
  left_ne_zero_of_mul_eq_one (infinite_mul_inv x w)
theorem eventually_norm_eq_one (x : IdeleGroup K) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖(x : 𝔸[K]).2 v‖ = 1 := by
  filter_upwards [(x : 𝔸[K]).2.2, ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2.2] with v h1 h2
  exact norm_eq_one_of_mul_eq_one (finite_mul_inv x v) h1 h2
theorem finite_mulSupport_norm (x : IdeleGroup K) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(x : 𝔸[K]).2 v‖).Finite :=
  Filter.eventually_cofinite.1 (eventually_norm_eq_one x)
def infiniteModule (x : IdeleGroup K) : ℝ :=
  ∏ w : InfinitePlace K, ‖(x : 𝔸[K]).1 w‖ ^ w.mult
def finiteModule (x : IdeleGroup K) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(x : 𝔸[K]).2 v‖
theorem infiniteModule_mul (x y : IdeleGroup K) :
    infiniteModule (x * y) = infiniteModule x * infiniteModule y := by
  simp only [infiniteModule, Units.val_mul, adele_fst_mul_apply, norm_mul, mul_pow,
    Finset.prod_mul_distrib]
theorem finiteModule_mul (x y : IdeleGroup K) :
    finiteModule (x * y) = finiteModule x * finiteModule y := by
  simp only [finiteModule, Units.val_mul, adele_snd_mul_apply, norm_mul]
  exact finprod_mul_distrib (finite_mulSupport_norm x) (finite_mulSupport_norm y)
theorem infiniteModule_pos (x : IdeleGroup K) : 0 < infiniteModule x :=
  Finset.prod_pos fun w _ ↦ pow_pos (norm_pos_iff.2 (infinite_ne_zero x w)) _
theorem finiteModule_pos (x : IdeleGroup K) : 0 < finiteModule x := by
  rw [finiteModule, finprod_eq_prod _ (finite_mulSupport_norm x)]
  exact Finset.prod_pos fun v _ ↦ norm_pos_iff.2 (finite_ne_zero x v)
variable (K) in

def ideleModule : IdeleGroup K →* {r : ℝ // 0 < r} where
  toFun x := ⟨infiniteModule x * finiteModule x, mul_pos (infiniteModule_pos x) (finiteModule_pos x)⟩
  map_one' := by
    ext
    simp [infiniteModule, finiteModule]
  map_mul' x y := by
    ext
    simp only [Positive.val_mul, infiniteModule_mul, finiteModule_mul]
    ring
theorem ideleModule_apply (x : IdeleGroup K) :
    (ideleModule K x : ℝ) = infiniteModule x * finiteModule x :=
  rfl
theorem infiniteModule_diagonal (k : Kˣ) :
    infiniteModule (diagonal K k) = ∏ w : InfinitePlace K, w (k : K) ^ w.mult := by
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  congr 1
  exact InfinitePlace.Completion.norm_coe (K := K) (v := w) _
theorem finiteModule_diagonal (k : Kˣ) :
    finiteModule (diagonal K k) = ∏ᶠ w : FinitePlace K, w (k : K) := by
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  simp only [FinitePlace.equivHeightOneSpectrum_symm_apply]
  rfl
theorem ideleModule_diagonal (k : Kˣ) : ideleModule K (diagonal K k) = 1 := by
  refine Subtype.ext ?_
  rw [ideleModule_apply, infiniteModule_diagonal, finiteModule_diagonal, Positive.val_one]
  exact prod_abs_eq_one k.ne_zero
variable (K) in

def normOneSubgroup : Subgroup (IdeleGroup K) := (ideleModule K).ker
variable (K) in

theorem range_diagonal_le_normOneSubgroup : (diagonal K).range ≤ normOneSubgroup K := by
  rintro _ ⟨k, rfl⟩
  exact ideleModule_diagonal k
end IdeleGroup
namespace IdeleClassGroup
def ideleModule : IdeleClassGroup K →* {r : ℝ // 0 < r} :=
  QuotientGroup.lift _ (IdeleGroup.ideleModule K) (IdeleGroup.range_diagonal_le_normOneSubgroup K)
def normOneSubgroup : Subgroup (IdeleClassGroup K) := (ideleModule K).ker
end IdeleClassGroup
end
end GroundTheory.Global


