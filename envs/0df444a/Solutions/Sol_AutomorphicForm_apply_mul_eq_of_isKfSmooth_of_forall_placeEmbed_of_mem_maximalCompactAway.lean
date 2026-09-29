-- Prove2me | solution 1 for AutomorphicForm.apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/cf3937b7-5f74-522a-82f5-188ed8bd2d13

import Mathlib
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_exists_maximalCompactAway_subset_of_mem_nhds_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway

set_option autoImplicit false

noncomputable section

namespace RS22

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel
open AdelicDock FLT.SmoothVectors Topology

variable {K : Type} [Field K] [NumberField K]

def atPlace (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (v.adicCompletion K)) : AdelicGL2 (𝓞 K) K :=
  finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v g)

theorem placeEmbed_eq_atPlace (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (v.adicCompletion K)) :
    UnramifiedWhittaker.placeEmbed K v g = atPlace v g := rfl

theorem glArch_atPlace (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (v.adicCompletion K)) :
    glArch (𝓞 K) K (atPlace v g) = 1 := glArch_finEmbed _ _ _

theorem finComponent_atPlace_self (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (v.adicCompletion K)) :
    finComponent (𝓞 K) K v (glFin (𝓞 K) K (atPlace v g)) = g := by
  rw [atPlace, glFin_finEmbed, finComponent_localEmbed_self]

theorem finComponent_atPlace_of_ne (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (v.adicCompletion K))
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    finComponent (𝓞 K) K w (glFin (𝓞 K) K (atPlace v g)) = 1 := by
  rw [atPlace, glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]

theorem localEmbed_entries_integral (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (v.adicCompletion K))
    (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K)
    (i j : Fin 2) :
    ((localEmbed (𝓞 K) K v g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j ∈ integralFiniteAdeles (𝓞 K) K := by
  intro w
  rw [coe_localEmbed]
  by_cases hw : w = v
  · subst hw
    rw [localMat_apply_self]
    exact hg i j
  · rw [localMat_apply_of_ne _ _ _ _ i j hw, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem atPlace_mem (v : HeightOneSpectrum (𝓞 K)) {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K) :
    atPlace v (finComponent (𝓞 K) K v (glFin (𝓞 K) K k)) ∈ adelicMaximalCompact K := by
  set g := finComponent (𝓞 K) K v (glFin (𝓞 K) K k) with hgdef
  have hkf := mem_finiteIntegralGL2_iff.mp hk.1
  have hint : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K := by
    intro i j
    rw [hgdef, finComponent_apply]
    exact hkf.1 i j v
  have hint' : ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
      ∈ v.adicCompletionIntegers K := by
    intro i j
    rw [hgdef, ← map_inv, ← map_inv, finComponent_apply]
    exact (mem_finiteIntegralGL2_iff.mp ((adelicMaximalCompact K).inv_mem hk).1).1 i j v
  refine ⟨?_, fun w => ?_⟩
  · rw [atPlace, glFin_finEmbed, mem_finiteIntegralGL2_iff]
    refine ⟨localEmbed_entries_integral v g hint, ?_⟩
    intro i j
    rw [← map_inv]
    exact localEmbed_entries_integral v g⁻¹ hint' i j
  · rw [glArch_atPlace, map_one]
    exact isRowIsometry_one

theorem exists_map_eq_finComponent (v : HeightOneSpectrum (𝓞 K)) {k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ adelicMaximalCompact K) :
    ∃ kv : GL (Fin 2) (v.adicCompletionIntegers K),
      Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv =
        finComponent (𝓞 K) K v (glFin (𝓞 K) K k) := by
  have hkf := mem_finiteIntegralGL2_iff.mp hk.1
  set g := finComponent (𝓞 K) K v (glFin (𝓞 K) K k) with hg
  have hint : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K := by
    intro i j; rw [hg, finComponent_apply]; exact hkf.1 i j v
  have hint' : ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
      ∈ v.adicCompletionIntegers K := by
    intro i j
    rw [hg, ← map_inv, ← map_inv, finComponent_apply]
    exact (mem_finiteIntegralGL2_iff.mp ((adelicMaximalCompact K).inv_mem hk).1).1 i j v
  let M : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K) := Matrix.of fun i j => ⟨_, hint i j⟩
  let Minv : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K) := Matrix.of fun i j => ⟨_, hint' i j⟩
  have hinj : Function.Injective (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) :=
    Subtype.val_injective
  have hM : M.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by ext i j; rfl
  have hMinv : Minv.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
      ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by ext i j; rfl
  have h1 : M * Minv = 1 := by
    apply Matrix.map_injective hinj
    change (M * Minv).map (algebraMap _ _) = (1 : Matrix (Fin 2) (Fin 2) _).map (algebraMap _ _)
    rw [Matrix.map_mul, hM, hMinv, Matrix.map_one (algebraMap _ _) (map_zero _) (map_one _)]
    exact g.val_inv
  have h2 : Minv * M = 1 := by
    apply Matrix.map_injective hinj
    change (Minv * M).map (algebraMap _ _) = (1 : Matrix (Fin 2) (Fin 2) _).map (algebraMap _ _)
    rw [Matrix.map_mul, hM, hMinv, Matrix.map_one (algebraMap _ _) (map_zero _) (map_one _)]
    exact g.inv_val
  refine ⟨⟨M, Minv, h1, h2⟩, ?_⟩
  apply Units.ext
  exact hM

theorem exists_fixing_away (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : IsKfSmooth K φ) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ k ∈ maximalCompactAway K S₀, ∀ g : AdelicGL2 (𝓞 K) K,
      φ (g * k) = φ g := by
  have hopen : IsOpen ((MulAction.stabilizer (finiteAdelicGL2Subgroup K)
      (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 K) K) ℂ) :
        Subgroup (finiteAdelicGL2Subgroup K)) : Set (finiteAdelicGL2Subgroup K)) := hφ
  obtain ⟨O, hO, hOpre⟩ := isOpen_induced_iff.mp hopen
  have h1O : (1 : AdelicGL2 (𝓞 K) K) ∈ O := by
    have : (1 : finiteAdelicGL2Subgroup K) ∈ (Subtype.val ⁻¹' O : Set (finiteAdelicGL2Subgroup K)) := by
      rw [hOpre]; exact Subgroup.one_mem _
    exact this
  obtain ⟨S₀, hS₀⟩ := AutomorphicForm.exists_maximalCompactAway_subset_of_mem_nhds_one K O (hO.mem_nhds h1O)
  refine ⟨S₀, fun k hk g => ?_⟩
  have hka : glArch (𝓞 K) K k = 1 := (mem_maximalCompactAway_iff.mp hk).2.1
  have hkO : (⟨k, hka⟩ : finiteAdelicGL2Subgroup K) ∈
      (Subtype.val ⁻¹' O : Set (finiteAdelicGL2Subgroup K)) := hS₀ hk
  rw [hOpre] at hkO
  have hstab := MulAction.mem_stabilizer_iff.mp hkO
  have := congrArg (fun f => RightTranslationFn.toFun f g) hstab
  simp at this
  exact this

theorem exists_truncation_fixing (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hsph : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K))
      (g : AdelicGL2 (𝓞 K) K), φ (g * UnramifiedWhittaker.placeEmbed K v
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ g)
    (k : AdelicGL2 (𝓞 K) K) (hk : k ∈ adelicMaximalCompact K)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (hT : ∀ v ∈ T, v ∉ S) :
    ∃ m : AdelicGL2 (𝓞 K) K, m ∈ adelicMaximalCompact K ∧ glArch (𝓞 K) K m = 1 ∧
      (∀ v ∈ T, finComponent (𝓞 K) K v (glFin (𝓞 K) K m) = finComponent (𝓞 K) K v (glFin (𝓞 K) K k)) ∧
      (∀ v ∉ T, finComponent (𝓞 K) K v (glFin (𝓞 K) K m) = 1) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, φ (g * m) = φ g) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact ⟨1, one_mem _, map_one _, fun v hv => absurd hv (Finset.notMem_empty v),
      fun v _ => by rw [map_one, map_one], fun g => by rw [mul_one]⟩
  | insert u T hu ih =>
    obtain ⟨m, hmK, hma, hmon, hmoff, hmfix⟩ := ih (fun v hv => hT v (Finset.mem_insert_of_mem hv))
    have huS : u ∉ S := hT u (Finset.mem_insert_self u T)
    obtain ⟨ku, hku⟩ := exists_map_eq_finComponent u hk
    have hmemu : atPlace u (finComponent (𝓞 K) K u (glFin (𝓞 K) K k)) ∈ adelicMaximalCompact K :=
      atPlace_mem u hk
    refine ⟨m * atPlace u (finComponent (𝓞 K) K u (glFin (𝓞 K) K k)), mul_mem hmK hmemu, ?_, ?_, ?_, ?_⟩
    · rw [map_mul, hma, glArch_atPlace, one_mul]
    · intro v hv
      rw [map_mul, map_mul]
      rcases Finset.mem_insert.1 hv with rfl | hvT
      · rw [hmoff v hu, finComponent_atPlace_self, one_mul]
      · have hvu : v ≠ u := fun h => hu (h ▸ hvT)
        rw [hmon v hvT, finComponent_atPlace_of_ne _ _ hvu, mul_one]
    · intro v hv
      have hvu : v ≠ u := fun h => hv (h ▸ Finset.mem_insert_self u T)
      have hvT : v ∉ T := fun h => hv (Finset.mem_insert_of_mem h)
      rw [map_mul, map_mul, hmoff v hvT, finComponent_atPlace_of_ne _ _ hvu, one_mul]
    · intro g
      rw [← mul_assoc, ← hku, ← placeEmbed_eq_atPlace, hsph u huS ku (g * m), hmfix g]

theorem apply_mul_eq_of_mem_maximalCompactAway (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : IsKfSmooth K φ)
    (hsph : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K))
      (g : AdelicGL2 (𝓞 K) K), φ (g * UnramifiedWhittaker.placeEmbed K v
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ g) :
    ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, φ (g * k) = φ g := by
  classical
  obtain ⟨S₀, hS₀⟩ := exists_fixing_away φ hφ
  intro k hk g
  obtain ⟨hkK, hka, hkS⟩ := mem_maximalCompactAway_iff.mp hk
  obtain ⟨m, hmK, hma, hmon, hmoff, hmfix⟩ :=
    exists_truncation_fixing S φ hsph k hkK (S₀ \ S) (fun v hv => (Finset.mem_sdiff.mp hv).2)
  have hkm : k * m⁻¹ ∈ maximalCompactAway K S₀ := by
    rw [mem_maximalCompactAway_iff]
    refine ⟨mul_mem hkK (inv_mem hmK), by rw [map_mul, map_inv, hka, hma, inv_one, mul_one], fun v hv => ?_⟩
    rw [map_mul, map_inv, map_mul, map_inv]
    by_cases hvS : v ∈ S
    · have hvT : v ∉ S₀ \ S := fun h => (Finset.mem_sdiff.mp h).2 hvS
      rw [hkS v hvS, hmoff v hvT, inv_one, mul_one]
    · rw [hmon v (Finset.mem_sdiff.mpr ⟨hv, hvS⟩), mul_inv_cancel]
  calc φ (g * k) = φ (g * (k * m⁻¹) * m) := by rw [mul_assoc, inv_mul_cancel_right]
    _ = φ (g * (k * m⁻¹)) := hmfix _
    _ = φ g := hS₀ _ hkm g

end RS22

end

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : AdelicGL2 (𝓞 K) K → ℂ) (_hφ : IsKfSmooth K φ)
    (_hsph : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
        φ (g * UnramifiedWhittaker.placeEmbed K v
          (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ g) :
    ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, φ (g * k) = φ g := by
  exact RS22.apply_mul_eq_of_mem_maximalCompactAway K S φ _hφ _hsph

end S_AutomorphicForm_apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway
end P2MW
export P2MW.S_AutomorphicForm_apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway (solution)
