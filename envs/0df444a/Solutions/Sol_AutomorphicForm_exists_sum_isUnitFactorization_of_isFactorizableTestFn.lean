-- Prove2me | solution 1 for AutomorphicForm.exists_sum_isUnitFactorization_of_isFactorizableTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0bd7f81e-73dd-59a5-b015-c5030e7e3546

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_IsFinTestFactor_exists_isCompact_isOpen_forall_mul_eq
import Theorems.Thm_NumberField_AdelicLevel_exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one
import Theorems.Thm_AutomorphicForm_exists_continuous_hasCompactSupport_isUnitFactorization_and_union_of_isArchTestFactor_of_isLocalTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_sum_isUnitFactorization_of_isFactorizableTestFn

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm Filter Topology

noncomputable section

namespace KcSumUnitFact

section Local

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem mul_mem_localIntegralSet {g h : GL (Fin 2) (v.adicCompletion K)}
    (hg : g ∈ localIntegralSet K v) (hh : h ∈ localIntegralSet K v) :
    g * h ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet] at hg hh ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hg.1 i k) (hh.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hh.2 i k) (hg.2 k j)

theorem inv_mem_localIntegralSet {g : GL (Fin 2) (v.adicCompletion K)}
    (hg : g ∈ localIntegralSet K v) : g⁻¹ ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet] at hg ⊢
  rw [inv_inv]
  exact ⟨hg.2, hg.1⟩

theorem valued_mul_apply_le {A B : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)}
    {a : WithZero (Multiplicative ℤ)}
    (hA : ∀ i j, Valued.v (A i j) ≤ a) (hB : ∀ i j, Valued.v (B i j) ≤ 1) (i j : Fin 2) :
    Valued.v ((A * B) i j) ≤ a := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine Valuation.map_add_le _ ?_ ?_
  · rw [Valuation.map_mul]
    calc Valued.v (A i 0) * Valued.v (B 0 j) ≤ a * 1 := mul_le_mul' (hA _ _) (hB _ _)
      _ = a := mul_one a
  · rw [Valuation.map_mul]
    calc Valued.v (A i 1) * Valued.v (B 1 j) ≤ a * 1 := mul_le_mul' (hA _ _) (hB _ _)
      _ = a := mul_one a

theorem valued_mul_sub_one_apply_le {A B : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)}
    {a : WithZero (Multiplicative ℤ)}
    (hA : ∀ i j, Valued.v (A i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ a)
    (hB : ∀ i j, Valued.v (B i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ a)
    (hBi : ∀ i j, Valued.v (B i j) ≤ 1) (i j : Fin 2) :
    Valued.v ((A * B) i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ a := by
  have hmat : A * B - 1 = (A - 1) * B + (B - 1) := by
    rw [sub_mul, one_mul, sub_add_sub_cancel]
  have happ : (A * B) i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      ((A - 1) * B) i j + (B i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) := by
    have := congrFun (congrFun hmat i) j
    simpa only [Matrix.sub_apply, Matrix.add_apply] using this
  rw [happ]
  refine Valuation.map_add_le _ ?_ (hB i j)
  exact valued_mul_apply_le K v (fun i j => by rw [Matrix.sub_apply]; exact hA i j) hBi i j

theorem valued_le_one_of_mem_localIntegralSet {g : GL (Fin 2) (v.adicCompletion K)}
    (hg : g ∈ localIntegralSet K v) (i j : Fin 2) :
    Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((mem_localIntegralSet K v).1 hg |>.1 i j)

theorem valued_inv_le_one_of_mem_localIntegralSet {g : GL (Fin 2) (v.adicCompletion K)}
    (hg : g ∈ localIntegralSet K v) (i j : Fin 2) :
    Valued.v (((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
      ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((mem_localIntegralSet K v).1 hg |>.2 i j)

def localCong (n : ℕ) : Subgroup (GL (Fin 2) (v.adicCompletion K)) where
  carrier := {k | k ∈ localIntegralSet K v ∧
    ∀ i j : Fin 2,
      Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
          - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(n : ℤ)) ∧
      Valued.v (((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
          - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(n : ℤ))}
  one_mem' := by
    refine ⟨one_mem_localIntegralSet K v, fun i j => ⟨?_, ?_⟩⟩
    · rw [Units.val_one, sub_self, Valuation.map_zero]; exact zero_le'
    · rw [inv_one, Units.val_one, sub_self, Valuation.map_zero]; exact zero_le'
  mul_mem' := by
    intro a b ha hb
    refine ⟨mul_mem_localIntegralSet K v ha.1 hb.1, fun i j => ⟨?_, ?_⟩⟩
    · rw [Units.val_mul]
      exact valued_mul_sub_one_apply_le K v (fun i j => (ha.2 i j).1) (fun i j => (hb.2 i j).1)
        (valued_le_one_of_mem_localIntegralSet K v hb.1) i j
    · rw [mul_inv_rev, Units.val_mul]
      exact valued_mul_sub_one_apply_le K v (fun i j => (hb.2 i j).2) (fun i j => (ha.2 i j).2)
        (valued_inv_le_one_of_mem_localIntegralSet K v ha.1) i j
  inv_mem' := by
    intro a ha
    refine ⟨inv_mem_localIntegralSet K v ha.1, fun i j => ⟨(ha.2 i j).2, ?_⟩⟩
    rw [inv_inv]
    exact (ha.2 i j).1

theorem mem_localCong_iff (n : ℕ) (k : GL (Fin 2) (v.adicCompletion K)) :
    k ∈ localCong K v n ↔ k ∈ localIntegralSet K v ∧
    ∀ i j : Fin 2,
      Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
          - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(n : ℤ)) ∧
      Valued.v (((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
          - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(n : ℤ)) :=
  Iff.rfl

theorem localCong_le_localIntegralSet (n : ℕ) :
    (localCong K v n : Set (GL (Fin 2) (v.adicCompletion K))) ⊆ localIntegralSet K v :=
  fun _ hk => hk.1

theorem isOpen_setOf_valued_sub_le (n : ℕ) (c : v.adicCompletion K) :
    IsOpen {x : v.adicCompletion K | Valued.v (x - c) ≤ WithZero.exp (-(n : ℤ))} := by
  obtain ⟨t, ht, hvt⟩ := AdelicLevel.exists_valued_eq_exp_neg (K := K) v n
  rw [← hvt]
  exact (AdelicLevel.isOpen_setOf_valued_le v t ht).preimage (continuous_id.sub continuous_const)

theorem isOpen_localCong (n : ℕ) : IsOpen (localCong K v n : Set (GL (Fin 2) (v.adicCompletion K))) := by
  have hval : Continuous fun k : GL (Fin 2) (v.adicCompletion K) =>
      (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := Units.continuous_val
  have hinv : Continuous fun k : GL (Fin 2) (v.adicCompletion K) =>
      ((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    Units.continuous_coe_inv
  have h1 : IsOpen {k : GL (Fin 2) (v.adicCompletion K) | ∀ i j : Fin 2,
      Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
          - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(n : ℤ)) ∧
      Valued.v (((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
          - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(n : ℤ))} := by
    simp only [Set.setOf_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
    · exact (isOpen_setOf_valued_sub_le K v n _).preimage (hval.matrix_elem i j)
    · exact (isOpen_setOf_valued_sub_le K v n _).preimage (hinv.matrix_elem i j)
  exact (isOpen_localIntegralSet K v).inter h1

theorem isClosed_localCong (n : ℕ) : IsClosed (localCong K v n : Set (GL (Fin 2) (v.adicCompletion K))) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_localCong K v n)

end Local

section FiniteAdelic

variable (K : Type) [Field K] [NumberField K]

def congFin (T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) where
  carrier := {k | ∀ v : HeightOneSpectrum (𝓞 K),
    AdelicLevel.finComponent (𝓞 K) K v k ∈ localIntegralSet K v ∧
      (v ∈ T → AdelicLevel.finComponent (𝓞 K) K v k ∈ localCong K v n)}
  one_mem' := fun v => by
    simp only [map_one]
    exact ⟨one_mem_localIntegralSet K v, fun _ => (localCong K v n).one_mem⟩
  mul_mem' := by
    intro a b ha hb v
    simp only [map_mul]
    exact ⟨mul_mem_localIntegralSet K v (ha v).1 (hb v).1,
      fun hv => (localCong K v n).mul_mem ((ha v).2 hv) ((hb v).2 hv)⟩
  inv_mem' := by
    intro a ha v
    simp only [map_inv]
    exact ⟨inv_mem_localIntegralSet K v (ha v).1, fun hv => (localCong K v n).inv_mem ((ha v).2 hv)⟩

theorem mem_congFin_iff {T : Finset (HeightOneSpectrum (𝓞 K))} {n : ℕ}
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)} :
    k ∈ congFin K T n ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      AdelicLevel.finComponent (𝓞 K) K v k ∈ localIntegralSet K v ∧
        (v ∈ T → AdelicLevel.finComponent (𝓞 K) K v k ∈ localCong K v n) :=
  Iff.rfl

theorem coe_congFin (T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    (congFin K T n : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) =
      unitFinSet K ∩ ⋂ v ∈ T, AdelicLevel.finComponent (𝓞 K) K v ⁻¹'
        (localCong K v n : Set (GL (Fin 2) (v.adicCompletion K))) := by
  ext k
  simp only [SetLike.mem_coe, mem_congFin_iff, unitFinSet, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_iInter, Set.mem_preimage]
  exact ⟨fun h => ⟨fun v => (h v).1, fun v hv => (h v).2 hv⟩, fun h v => ⟨h.1 v, fun hv => h.2 v hv⟩⟩

theorem isOpen_congFin (T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    IsOpen (congFin K T n : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := by
  rw [coe_congFin]
  exact (isOpen_unitFinSet K).inter (isOpen_biInter_finset fun v _ =>
    (isOpen_localCong K v n).preimage (AdelicLevel.continuous_finComponent (𝓞 K) K v))

theorem exists_congFin_subset {U : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))}
    (hU : U ∈ 𝓝 (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ),
      (congFin K T n : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) ⊆ U := by
  have hV : AdelicLevel.glFin (𝓞 K) K ⁻¹' U ∈ 𝓝 (1 : GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
    (AdelicLevel.continuous_glFin (𝓞 K) K).continuousAt.preimage_mem_nhds (by rwa [map_one])
  obtain ⟨T, n, hTn⟩ :=
    NumberField.AdelicLevel.exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one K _ hV
  refine ⟨T, n, fun k hk => ?_⟩
  have hk' : k ∈ congFin K T n := hk
  set g : GL (Fin 2) (AdeleRing (𝓞 K) K) := AdelicDock.finEmbed (𝓞 K) K k with hg
  have hgk : AdelicLevel.glFin (𝓞 K) K g = k := AdelicDock.glFin_finEmbed (𝓞 K) K k
  have hmem : g ∈ AdelicLevel.glFin (𝓞 K) K ⁻¹' U := by
    refine hTn g (AdelicDock.glArch_finEmbed (𝓞 K) K k) (fun v i j => ⟨?_, ?_⟩) (fun v hv i j => ⟨?_, ?_⟩)
    · change (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K
      rw [hgk]
      exact ((mem_localIntegralSet K v).1 (hk' v).1).1 i j
    · change (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g⁻¹) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K
      rw [map_inv, hgk, map_inv]
      exact ((mem_localIntegralSet K v).1 (hk' v).1).2 i j
    · change Valued.v ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
          - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(n : ℤ))
      rw [hgk]
      exact (((hk' v).2 hv).2 i j).1
    · change Valued.v ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g⁻¹) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
          - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(n : ℤ))
      rw [map_inv, hgk, map_inv]
      exact (((hk' v).2 hv).2 i j).2
  simpa only [Set.mem_preimage, hgk] using hmem

theorem finite_setOf_finComponent_not_mem (r : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    {v : HeightOneSpectrum (𝓞 K) | AdelicLevel.finComponent (𝓞 K) K v r ∉ localIntegralSet K v}.Finite := by
  have hfin : ∀ x : FiniteAdeleRing (𝓞 K) K,
      {v : HeightOneSpectrum (𝓞 K) | x v ∉ v.adicCompletionIntegers K}.Finite := fun x =>
    Filter.eventually_cofinite.1 x.2
  refine ((Set.finite_iUnion fun i : Fin 2 => Set.finite_iUnion fun j : Fin 2 =>
    (hfin ((r : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j)).union
      (hfin (((r⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j)))).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq, mem_localIntegralSet, not_and_or, not_forall] at hv
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq]
  rcases hv with ⟨i, j, h⟩ | ⟨i, j, h⟩
  · exact ⟨i, j, Or.inl h⟩
  · refine ⟨i, j, Or.inr ?_⟩
    rw [← map_inv] at h
    exact h

end FiniteAdelic

section CosetFactor

variable (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)

def localWindow (v : HeightOneSpectrum (𝓞 K)) : Set (GL (Fin 2) (v.adicCompletion K)) :=
  {y | y ∈ localIntegralSet K v ∧ (v ∈ T → y ∈ localCong K v n)}

theorem isOpen_localWindow (v : HeightOneSpectrum (𝓞 K)) : IsOpen (localWindow K T n v) := by
  by_cases hv : v ∈ T
  · have : localWindow K T n v = (localCong K v n : Set (GL (Fin 2) (v.adicCompletion K))) := by
      ext y
      simp only [localWindow, Set.mem_setOf_eq, SetLike.mem_coe]
      exact ⟨fun h => h.2 hv, fun h => ⟨h.1, fun _ => h⟩⟩
    rw [this]; exact isOpen_localCong K v n
  · have : localWindow K T n v = localIntegralSet K v := by
      ext y
      simp only [localWindow, Set.mem_setOf_eq]
      exact ⟨fun h => h.1, fun h => ⟨h, fun h' => absurd h' hv⟩⟩
    rw [this]; exact isOpen_localIntegralSet K v

theorem isCompact_localWindow (v : HeightOneSpectrum (𝓞 K)) : IsCompact (localWindow K T n v) := by
  by_cases hv : v ∈ T
  · have : localWindow K T n v =
        localIntegralSet K v ∩ (localCong K v n : Set (GL (Fin 2) (v.adicCompletion K))) := by
      ext y
      simp only [localWindow, Set.mem_setOf_eq, Set.mem_inter_iff, SetLike.mem_coe]
      exact ⟨fun h => ⟨h.1, h.2 hv⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
    rw [this]; exact (isCompact_localIntegralSet K v).inter_right (isClosed_localCong K v n)
  · have : localWindow K T n v = localIntegralSet K v := by
      ext y
      simp only [localWindow, Set.mem_setOf_eq]
      exact ⟨fun h => h.1, fun h => ⟨h, fun h' => absurd h' hv⟩⟩
    rw [this]; exact isCompact_localIntegralSet K v

def cosetSet (r : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) (v : HeightOneSpectrum (𝓞 K)) :
    Set (GL (Fin 2) (v.adicCompletion K)) :=
  (fun x => (AdelicLevel.finComponent (𝓞 K) K v r)⁻¹ * x) ⁻¹' localWindow K T n v

theorem mem_cosetSet_iff {r : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)} {v : HeightOneSpectrum (𝓞 K)}
    {x : GL (Fin 2) (v.adicCompletion K)} :
    x ∈ cosetSet K T n r v ↔
      (AdelicLevel.finComponent (𝓞 K) K v r)⁻¹ * x ∈ localIntegralSet K v ∧
        (v ∈ T → (AdelicLevel.finComponent (𝓞 K) K v r)⁻¹ * x ∈ localCong K v n) :=
  Iff.rfl

theorem isOpen_cosetSet (r : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen (cosetSet K T n r v) :=
  (isOpen_localWindow K T n v).preimage (continuous_const_mul _)

theorem isCompact_cosetSet (r : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (cosetSet K T n r v) := by
  change IsCompact ((Homeomorph.mulLeft (AdelicLevel.finComponent (𝓞 K) K v r)⁻¹) ⁻¹' localWindow K T n v)
  exact (Homeomorph.isCompact_preimage _).2 (isCompact_localWindow K T n v)

def cosetFactor (r : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) (v : HeightOneSpectrum (𝓞 K)) :
    GL (Fin 2) (v.adicCompletion K) → ℂ :=
  (cosetSet K T n r v).indicator fun _ => (1 : ℂ)

theorem isLocalTestFn_cosetFactor (r : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    (v : HeightOneSpectrum (𝓞 K)) : IsLocalTestFn K v (cosetFactor K T n r v) :=
  ⟨isLocallyConstant_indicator_one (isOpen_cosetSet K T n r v) (isCompact_cosetSet K T n r v).isClosed,
    HasCompactSupport.intro (isCompact_cosetSet K T n r v) fun _ hx => by
      simp [cosetFactor, Set.indicator_of_notMem hx]⟩

open scoped Classical in

theorem prod_cosetFactor_eq (r : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    (Tr : Finset (HeightOneSpectrum (𝓞 K))) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (∏ v ∈ Tr, cosetFactor K T n r v (AdelicLevel.finComponent (𝓞 K) K v h)) =
      if ∀ v ∈ Tr, AdelicLevel.finComponent (𝓞 K) K v h ∈ cosetSet K T n r v then 1 else 0 := by
  split_ifs with hall
  · exact Finset.prod_eq_one fun v hv => by
      simp only [cosetFactor, Set.indicator_of_mem (hall v hv)]
  · push Not at hall
    obtain ⟨v, hv, hnot⟩ := hall
    exact Finset.prod_eq_zero hv (by simp only [cosetFactor, Set.indicator_of_notMem hnot])

end CosetFactor

section Main

variable (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]

theorem main (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : IsFactorizableTestFn K f) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (T : Fin n → Finset (HeightOneSpectrum (𝓞 K)))
      (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
      (fi : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
      (ffi : Fin n → GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
      (fSi : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
      (∀ i, S ⊆ T i) ∧
      (∀ i, Continuous (fi i) ∧ HasCompactSupport (fi i) ∧ IsUnitFactorization K (T i) (fi i) fa (ffi i) (fSi i)) ∧
      ∀ g, f g = ∑ i, c i * fi i g := by
  classical
  obtain ⟨fa, ff, hfa, hff, hf_eq⟩ := hf

  obtain ⟨U, -, hUo, hUinv⟩ := AutomorphicForm.IsFinTestFactor.exists_isCompact_isOpen_forall_mul_eq K ff hff
  obtain ⟨T, e, hTe⟩ := exists_congFin_subset K (hUo.mem_nhds U.one_mem)
  set Kf : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := congFin K T e with hKf_def
  have hKfU : ∀ k ∈ Kf, k ∈ U := fun k hk => hTe hk
  have hKo : IsOpen (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := isOpen_congFin K T e

  obtain ⟨t, ht⟩ := hff.2.isCompact.elim_finite_subcover
    (fun x : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      (fun h => x⁻¹ * h) ⁻¹' (Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))))
    (fun x => hKo.preimage (continuous_const_mul x⁻¹))
    (fun h _ => Set.mem_iUnion.2 ⟨h, by
      simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
      exact Kf.one_mem⟩)

  set Q : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) ⧸ Kf) :=
    t.image (QuotientGroup.mk : _ → GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) ⧸ Kf) with hQ_def
  set N : ℕ := Q.card with hN_def
  set eQ : ↥Q ≃ Fin N := Q.equivFin with heQ_def
  set rep : Fin N → GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) :=
    fun i => ((eQ.symm i : ↥Q) : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) ⧸ Kf).out with hrep_def
  have hrep_mk : ∀ i : Fin N,
      (QuotientGroup.mk (rep i) : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) ⧸ Kf) = (eQ.symm i : ↥Q) :=
    fun i => QuotientGroup.out_eq' _

  have hdecomp : ∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      ff h = ∑ i : Fin N, ff (rep i) * (if (rep i)⁻¹ * h ∈ Kf then 1 else 0) := by
    intro h
    have step1 : ∀ i : Fin N, ((rep i)⁻¹ * h ∈ Kf) ↔
        (((eQ.symm i : ↥Q) : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) ⧸ Kf) = QuotientGroup.mk h) := by
      intro i
      rw [← hrep_mk i, QuotientGroup.eq]
    have step2 : (∑ i : Fin N, ff (rep i) * (if (rep i)⁻¹ * h ∈ Kf then (1 : ℂ) else 0)) =
        ∑ i : Fin N, (if (((eQ.symm i : ↥Q) : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) ⧸ Kf) =
          QuotientGroup.mk h) then ff (((eQ.symm i : ↥Q) : _ ⧸ Kf).out) else 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_ite, mul_one, mul_zero]
      simp only [step1 i]
      rfl
    have step3 : (∑ i : Fin N, (if (((eQ.symm i : ↥Q) : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) ⧸ Kf) =
          QuotientGroup.mk h) then ff (((eQ.symm i : ↥Q) : _ ⧸ Kf).out) else 0)) =
        ∑ q ∈ Q, (if q = QuotientGroup.mk h then ff q.out else 0) := by
      rw [← Finset.sum_coe_sort Q]
      exact Fintype.sum_equiv eQ.symm _ _ fun _ => rfl
    rw [step2, step3, Finset.sum_ite_eq']
    split_ifs with hmem
    ·
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul Kf h
      rw [hk]
      exact (hUinv h k (hKfU k k.2)).symm
    ·
      by_contra hne
      have hsupp : h ∈ tsupport ff := subset_tsupport _ (Function.mem_support.2 (Ne.symm hne ∘ Eq.symm))
      have := ht hsupp
      simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
      obtain ⟨x, hx, hxh⟩ := this
      apply hmem
      have : (QuotientGroup.mk x : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) ⧸ Kf) = QuotientGroup.mk h :=
        QuotientGroup.eq.2 hxh
      rw [← this]
      exact Finset.mem_image_of_mem _ hx

  set bad : Fin N → Finset (HeightOneSpectrum (𝓞 K)) :=
    fun i => (finite_setOf_finComponent_not_mem K (rep i)).toFinset with hbad_def
  have hbad : ∀ i v, v ∉ bad i → AdelicLevel.finComponent (𝓞 K) K v (rep i) ∈ localIntegralSet K v := by
    intro i v hv
    by_contra hnot
    exact hv ((Set.Finite.mem_toFinset _).2 hnot)
  set Ti : Fin N → Finset (HeightOneSpectrum (𝓞 K)) := fun i => S ∪ T ∪ bad i with hTi_def
  have hS_Ti : ∀ i, S ⊆ Ti i := fun i =>
    (Finset.subset_union_left).trans (Finset.subset_union_left)
  have hT_Ti : ∀ i, T ⊆ Ti i := fun i =>
    (Finset.subset_union_right).trans (Finset.subset_union_left)
  have hbad_Ti : ∀ i, bad i ⊆ Ti i := fun i => Finset.subset_union_right
  set fS : Fin N → ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ :=
    fun i v => cosetFactor K T e (rep i) v with hfS_def
  have key : ∀ i : Fin N, ∃ (f₀ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
      (ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
      Continuous f₀ ∧ HasCompactSupport f₀ ∧ IsUnitFactorization K (Ti i) f₀ fa ff₀ (fS i) := by
    intro i
    obtain ⟨f₀, ff₀, h1, h2, h3, -⟩ :=
      AutomorphicForm.exists_continuous_hasCompactSupport_isUnitFactorization_and_union_of_isArchTestFactor_of_isLocalTestFn
        K (Ti i) fa hfa (fS i) (fun v _ => isLocalTestFn_cosetFactor K T e (rep i) v)
    exact ⟨f₀, ff₀, h1, h2, h3⟩
  choose f₀ ff₀ hcont hsupp hunit using key

  have hff₀ : ∀ (i : Fin N) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)),
      ff₀ i h = if (rep i)⁻¹ * h ∈ Kf then 1 else 0 := by
    intro i h
    obtain ⟨-, -, -, hprod, hzero, -⟩ := hunit i
    have hcoset : ∀ v, AdelicLevel.finComponent (𝓞 K) K v h ∈ cosetSet K T e (rep i) v ↔
        (AdelicLevel.finComponent (𝓞 K) K v ((rep i)⁻¹ * h) ∈ localIntegralSet K v ∧
          (v ∈ T → AdelicLevel.finComponent (𝓞 K) K v ((rep i)⁻¹ * h) ∈ localCong K v e)) := by
      intro v
      rw [mem_cosetSet_iff, map_mul, map_inv]
    by_cases hint : ∀ v ∉ Ti i, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v
    · rw [hprod h hint]
      change (∏ v ∈ Ti i, cosetFactor K T e (rep i) v (AdelicLevel.finComponent (𝓞 K) K v h)) = _
      rw [prod_cosetFactor_eq]
      have hiff : (∀ v ∈ Ti i, AdelicLevel.finComponent (𝓞 K) K v h ∈ cosetSet K T e (rep i) v) ↔
          (rep i)⁻¹ * h ∈ Kf := by
        rw [show ((rep i)⁻¹ * h ∈ Kf) = ((rep i)⁻¹ * h ∈ congFin K T e) from rfl, mem_congFin_iff]
        constructor
        · intro hall v
          by_cases hv : v ∈ Ti i
          · exact (hcoset v).1 (hall v hv)
          · refine ⟨?_, fun hvT => absurd (hT_Ti i hvT) hv⟩
            rw [map_mul, map_inv]
            exact mul_mem_localIntegralSet K v
              (inv_mem_localIntegralSet K v (hbad i v fun hb => hv (hbad_Ti i hb))) (hint v hv)
        · intro hall v _
          exact (hcoset v).2 (hall v)
      simp only [hiff]
    · push Not at hint
      obtain ⟨v, hv, hnot⟩ := hint
      rw [hzero h ⟨v, hv, hnot⟩]
      symm
      rw [ite_eq_right_iff]
      intro hmem
      exfalso
      apply hnot
      have h1 : AdelicLevel.finComponent (𝓞 K) K v ((rep i)⁻¹ * h) ∈ localIntegralSet K v :=
        ((mem_congFin_iff K).1 hmem v).1
      have h2 : AdelicLevel.finComponent (𝓞 K) K v (rep i) ∈ localIntegralSet K v :=
        hbad i v fun hb => hv (hbad_Ti i hb)
      have := mul_mem_localIntegralSet K v h2 h1
      rwa [← map_mul, mul_inv_cancel_left] at this

  refine ⟨N, fun i => ff (rep i), Ti, fa, f₀, ff₀, fS, hS_Ti, fun i => ⟨hcont i, hsupp i, hunit i⟩,
    fun g => ?_⟩
  have hfg : ∀ i, f₀ i g =
      fa (AdelicLevel.glArch (𝓞 K) K g) * ff₀ i (AdelicLevel.glFin (𝓞 K) K g) :=
    fun i => (hunit i).2.2.2.2.2 g
  rw [hf_eq g, hdecomp (AdelicLevel.glFin (𝓞 K) K g), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hfg i, hff₀ i]
  ring

end Main

end KcSumUnitFact

end

open NumberField IsDedekindDomain AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : IsFactorizableTestFn K f) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (T : Fin n → Finset (HeightOneSpectrum (𝓞 K)))
      (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
      (fi : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
      (ffi : Fin n → GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
      (fSi : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
      (∀ i, S ⊆ T i) ∧
      (∀ i, Continuous (fi i) ∧ HasCompactSupport (fi i) ∧ IsUnitFactorization K (T i) (fi i) fa (ffi i) (fSi i)) ∧
      ∀ g, f g = ∑ i, c i * fi i g :=
  KcSumUnitFact.main K S f hf

end S_AutomorphicForm_exists_sum_isUnitFactorization_of_isFactorizableTestFn
end P2MW
export P2MW.S_AutomorphicForm_exists_sum_isUnitFactorization_of_isFactorizableTestFn (solution)
