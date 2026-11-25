-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleActionQuotient
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_IdeleActionQuotient
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:42:43.129977+00:00
-- url     : https://prove2.me/theorems/3226e2ea-4a86-4dad-b385-6367a6039b80
-- title:
--   Idele Action Quotient
-- statement:
--   Definitions and structural lemmas for Idele Action Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleActionQuotient.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_surjective
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_localIdeal_smul
import Theorems.Thm_GroundTheory_Global_coe_mem_localIdeal
import Theorems.Thm_GroundTheory_Global_eventually_coe_mem_localIdeal
import Theorems.Thm_GroundTheory_Global_exists_sub_mem_integralFiniteAdeles
import Theorems.Thm_GroundTheory_Global_mem_iff_forall_mem_localIdeal
import Theorems.Thm_GroundTheory_Global_mem_integralFiniteAdeles
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
set_option maxSynthPendingDepth 1
namespace GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
theorem exists_sub_mem_localIdeal {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (a : FiniteAdeleRing (𝓞 K) K) :
    ∃ k : K, ∀ v : HeightOneSpectrum (𝓞 K), a v - (k : v.adicCompletion K) ∈ localIdeal I v := by
  obtain ⟨d, hdI, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (coeToSubmodule_ne_bot.2 hI)
  obtain ⟨k', hk'⟩ := exists_sub_mem_integralFiniteAdeles
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) d⁻¹ * a)
  refine ⟨d * k', fun v ↦ ?_⟩
  have ht : ((d⁻¹ : K) : v.adicCompletion K) * a v - (k' : v.adicCompletion K) ∈
      v.adicCompletionIntegers K :=
    (mem_integralFiniteAdeles.1 hk') v
  have h1 : (d : v.adicCompletion K) * ((d⁻¹ : K) : v.adicCompletion K) = 1 := by
    rw [← adicCompletion.coe_mul, mul_inv_cancel₀ hd0, adicCompletion.coe_one]
  have h : a v - ((d * k' : K) : v.adicCompletion K) =
      (⟨_, ht⟩ : v.adicCompletionIntegers K) • (d : v.adicCompletion K) := by
    change _ = (((d⁻¹ : K) : v.adicCompletion K) * a v - (k' : v.adicCompletion K)) *
      (d : v.adicCompletion K)
    rw [adicCompletion.coe_mul]
    linear_combination -(a v) * h1
  rw [h]
  exact Submodule.smul_mem _ _ (coe_mem_localIdeal v hdI)
def dfinsuppOfFinite {ι : Type*} {β : ι → Type*} [∀ i, Zero (β i)] (f : ∀ i, β i)
    (hf : {i | f i ≠ 0}.Finite) : Π₀ i, β i :=
  ⟨f, Trunc.mk ⟨hf.toFinset.val, fun i ↦ by
    by_cases h : f i = 0
    · exact Or.inr h
    · left
      rw [Finset.mem_val]
      exact hf.mem_toFinset.2 h⟩⟩
@[simp]
theorem dfinsuppOfFinite_apply {ι : Type*} {β : ι → Type*} [∀ i, Zero (β i)] (f : ∀ i, β i)
    (hf : {i | f i ≠ 0}.Finite) (i : ι) : dfinsuppOfFinite f hf i = f i :=
  rfl
instance (v : HeightOneSpectrum (𝓞 K)) :
    IsScalarTower (𝓞 K) (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  adicCompletion.instIsScalarTower' (𝓞 K) K v
abbrev LocalQuotient (I : FractionalIdeal (𝓞 K)⁰ K) (v : HeightOneSpectrum (𝓞 K)) :=
  v.adicCompletion K ⧸ localIdeal I v
def toLocalQuotients {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    K →ₗ[𝓞 K] DirectSum (HeightOneSpectrum (𝓞 K)) (LocalQuotient I) where
  toFun x := dfinsuppOfFinite (fun v ↦ Submodule.Quotient.mk (x : v.adicCompletion K))
    (Filter.eventually_cofinite.1 ((eventually_coe_mem_localIdeal hI x).mono fun v hv ↦
      (Submodule.Quotient.mk_eq_zero _).2 hv))
  map_add' x y := by
    refine DFinsupp.ext fun v ↦ ?_
    rw [DirectSum.add_apply]
    change Submodule.Quotient.mk ((x + y : K) : v.adicCompletion K) =
      Submodule.Quotient.mk (x : v.adicCompletion K) + Submodule.Quotient.mk (y : v.adicCompletion K)
    rw [adicCompletion.coe_add, Submodule.Quotient.mk_add]
  map_smul' r x := by
    refine DFinsupp.ext fun v ↦ ?_
    rw [RingHom.id_apply, DirectSum.smul_apply]
    change Submodule.Quotient.mk ((r • x : K) : v.adicCompletion K) =
      r • Submodule.Quotient.mk (p := localIdeal I v) (x : v.adicCompletion K)
    rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, Algebra.smul_def (A := v.adicCompletion K),
      adicCompletion.coe_mul]
    rfl
theorem toLocalQuotients_apply {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (x : K)
    (v : HeightOneSpectrum (𝓞 K)) :
    toLocalQuotients hI x v = Submodule.Quotient.mk (x : v.adicCompletion K) :=
  rfl
theorem toLocalQuotients_eq_zero_iff {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) {x : K} :
    toLocalQuotients hI x = 0 ↔ x ∈ I := by
  rw [mem_iff_forall_mem_localIdeal hI, DFinsupp.ext_iff]
  simp only [toLocalQuotients_apply, DFinsupp.coe_zero, Pi.zero_apply,
    Submodule.Quotient.mk_eq_zero]
theorem toLocalQuotients_surjective {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    Function.Surjective (toLocalQuotients hI) := by
  classical
  intro f
  choose y hy using fun v ↦ Submodule.Quotient.mk_surjective _ (f v)
  let z : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K := fun v ↦ if f v = 0 then 0 else y v
  have hz : ∀ v, Submodule.Quotient.mk (p := localIdeal I v) (z v) = f v := by
    intro v
    by_cases h : f v = 0
    · simp only [z, h, if_true, Submodule.Quotient.mk_zero]
    · simp only [z, h, if_false, hy]
  have hfin : {v | f v ≠ 0}.Finite :=
    f.support.finite_toSet.subset fun v hv ↦ DFinsupp.mem_support_iff.2 hv
  let a : FiniteAdeleRing (𝓞 K) K := ⟨z, Filter.eventually_cofinite.2 (hfin.subset fun v hv h ↦
    hv (by simp only [z, h, if_true]; exact (v.adicCompletionIntegers K).zero_mem))⟩
  obtain ⟨k, hk⟩ := exists_sub_mem_localIdeal hI a
  refine ⟨k, DFinsupp.ext fun v ↦ ?_⟩
  rw [toLocalQuotients_apply, ← hz v]
  exact ((Submodule.Quotient.eq _).2 (hk v)).symm
def quotientToLocalQuotients {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    (K ⧸ (I : Submodule (𝓞 K) K)) →ₗ[𝓞 K] DirectSum (HeightOneSpectrum (𝓞 K)) (LocalQuotient I) where
  toFun q := Quotient.liftOn' q (toLocalQuotients hI) fun a b h ↦ by
    rw [Submodule.quotientRel_def] at h
    have h0 := (toLocalQuotients_eq_zero_iff hI).2 h
    calc toLocalQuotients hI a = toLocalQuotients hI (b + (a - b)) :=
          congrArg (toLocalQuotients hI) (by abel)
      _ = toLocalQuotients hI b + toLocalQuotients hI (a - b) := map_add _ _ _
      _ = toLocalQuotients hI b := by rw [h0, add_zero]
  map_add' := by
    rintro ⟨a⟩ ⟨b⟩
    exact map_add (toLocalQuotients hI) a b
  map_smul' := by
    rintro r ⟨a⟩
    exact map_smul (toLocalQuotients hI) r a
def quotientEquivLocalQuotients {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    (K ⧸ (I : Submodule (𝓞 K) K)) ≃ₗ[𝓞 K] DirectSum (HeightOneSpectrum (𝓞 K)) (LocalQuotient I) :=
  LinearEquiv.ofBijective (quotientToLocalQuotients hI) ⟨by
      rw [injective_iff_map_eq_zero]
      rintro ⟨a⟩ h
      have h' : toLocalQuotients hI a = 0 := h
      exact (Submodule.Quotient.mk_eq_zero _).2 ((toLocalQuotients_eq_zero_iff hI).1 h'), by
      intro y
      obtain ⟨x, rfl⟩ := toLocalQuotients_surjective hI y
      exact ⟨Submodule.Quotient.mk x, rfl⟩⟩
namespace IdeleGroup
local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ
def localMul (s : IdeleGroup K) (I : 𝓘) (v : HeightOneSpectrum (𝓞 K)) :
    LocalQuotient (I : FractionalIdeal (𝓞 K)⁰ K) v ≃ₗ[𝓞 K]
      LocalQuotient ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v :=
  (Submodule.Quotient.equiv (localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) v)
    (localIdeal ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v)
    ((finiteProj v s).mulLeftLinearEquiv (v.adicCompletionIntegers K) (v.adicCompletion K))
    (by
      rw [localIdeal_smul, Units.toLinearMap_mulLeftLinearEquiv, coe_finiteProj])).restrictScalars
    (𝓞 K)
def smulQuotient (s : IdeleGroup K) (I : 𝓘) :
    (K ⧸ ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) ≃ₗ[𝓞 K]
      K ⧸ (((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
  (quotientEquivLocalQuotients I.ne_zero).trans
    ((DFinsupp.mapRange.linearEquiv (localMul s I)).trans
      (quotientEquivLocalQuotients (s • I).ne_zero).symm)
end IdeleGroup
end
end GroundTheory.Global


