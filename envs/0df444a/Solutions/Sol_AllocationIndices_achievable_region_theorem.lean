-- Prove2me | solution 1 for AllocationIndices.achievable_region_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T03:26:18.775978+00:00
-- url     : https://prove2.me/submissions/77d772aa-2717-4b1e-9d6c-e3474d5138f4

import Mathlib
import Definitions.Def_AllocationIndices_Achievable

/-! cc500be5 AllocationIndices.achievable_region_theorem (Gittins–Glazebrook–Weber, Thm 5.5).

Route (LP duality, no Krein–Milman needed):
* `r_decomp`: for an AG output `(σ, y)`, `rᵢ = ∑ₖ A^{S_{k+1}}ᵢ yₖ` exactly (each `i = σ m` is
  picked once, at stage `m`; `A^{S_{k+1}}ᵢ = 0` for `k < m`).
* `y_nonpos`: `yₖ ≤ 0` below the top stage (the maximality at stage `k+1`).
* `weak_duality`: `r·x ≤ ∑ₖ yₖ b(S_{k+1}) = r·x^σ` for every `x ∈ P(A, b)`.
* `exists_AG`: AG has an output (top-down induction, swapping the stage maximiser into place).
* `subset_hull`: `P ⊆ conv{x^σ}` by strict separation + weak duality.
* then `X = P` (convexity of `X`), and `ext P ⊆ ext conv{x^σ} ⊆ {x^σ}`.
-/

set_option autoImplicit false

universe u

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem cc500be5_mem_lowSet {N : ℕ} (σ : Equiv.Perm (Fin N)) (t : ℕ) (i : Fin N) :
    i ∈ lowSet σ t ↔ ((σ.symm i : Fin N) : ℕ) < t := by
  unfold lowSet
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa using hj
  · intro h
    exact ⟨σ.symm i, h, by simp⟩

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem cc500be5_card_lowSet {N : ℕ} (σ : Equiv.Perm (Fin N)) (t : ℕ) (ht : t ≤ N) :
    (lowSet σ t).card = t := by
  unfold lowSet
  rw [Finset.card_image_of_injective _ σ.injective, Fin.card_filter_val_lt]
  omega

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem cc500be5_lowSet_N {N : ℕ} (σ : Equiv.Perm (Fin N)) : lowSet σ N = univ := by
  ext i
  simp only [cc500be5_mem_lowSet, Finset.mem_univ, iff_true]
  exact (σ.symm i).isLt

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem cc500be5_sum_univ_eq {N : ℕ} {Pol : Type u} (D : GCL1System N Pol)
    (S : Finset (Fin N)) (x : Fin N → ℝ) :
    ∑ i, D.A S i * x i = ∑ i ∈ S, D.A S i * x i := by
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro i _ hi
  rw [D.A_eq_zero S i hi, zero_mul]

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem cc500be5_r_decomp {N : ℕ} {Pol : Type u} (D : GCL1System N Pol) (r : Fin N → ℝ)
    (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ) (h : IsAdaptiveGreedy D.A r σ y) (i : Fin N) :
    r i = ∑ k : Fin N, D.A (lowSet σ ((k : ℕ) + 1)) i * y k := by
  obtain ⟨m, hm⟩ : ∃ m : Fin N, σ.symm i = m := ⟨_, rfl⟩
  have hσm : σ m = i := by rw [← hm, Equiv.apply_symm_apply]
  have hmem : i ∈ lowSet σ ((m : ℕ) + 1) := by
    rw [cc500be5_mem_lowSet, hm]; omega
  have hApos := D.A_pos _ i hmem
  have h2 := (h m).2
  rw [hσm, div_eq_iff hApos.ne'] at h2
  unfold greedyNumerator at h2
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun k : Fin N => m < k)]
  have h3 : ∑ k ∈ univ.filter (fun k : Fin N => ¬ m < k), D.A (lowSet σ ((k : ℕ) + 1)) i * y k
      = D.A (lowSet σ ((m : ℕ) + 1)) i * y m := by
    apply Finset.sum_eq_single_of_mem
    · simp
    · intro k hk hkm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hk
      have hlt : k < m := lt_of_le_of_ne hk hkm
      have hnot : i ∉ lowSet σ ((k : ℕ) + 1) := by
        rw [cc500be5_mem_lowSet, hm]
        have := Fin.lt_def.mp hlt
        omega
      rw [D.A_eq_zero _ i hnot, zero_mul]
  rw [h3]
  linarith

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem cc500be5_y_nonpos {N : ℕ} {Pol : Type u} (D : GCL1System N Pol) (r : Fin N → ℝ)
    (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ) (h : IsAdaptiveGreedy D.A r σ y) (k : Fin N)
    (hk : (k : ℕ) + 1 < N) : y k ≤ 0 := by
  obtain ⟨k', hk'⟩ : ∃ k' : Fin N, (k' : ℕ) = (k : ℕ) + 1 := ⟨⟨(k : ℕ) + 1, hk⟩, rfl⟩
  have hsplit : univ.filter (fun j : Fin N => k < j)
      = insert k' (univ.filter (fun j : Fin N => k' < j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def,
      Fin.ext_iff]
    omega
  have hnotmem : k' ∉ univ.filter (fun j : Fin N => k' < j) := by simp
  have hmem1 : σ k ∈ lowSet σ ((k' : ℕ) + 1) := by
    rw [cc500be5_mem_lowSet, Equiv.symm_apply_apply]; omega
  have hmem0 : σ k ∈ lowSet σ ((k : ℕ) + 1) := by
    rw [cc500be5_mem_lowSet, Equiv.symm_apply_apply]; omega
  have hA1 := D.A_pos _ _ hmem1
  have hA0 := D.A_pos _ _ hmem0
  have h1 := (h k').1 (σ k) hmem1
  rw [div_le_iff₀ hA1] at h1
  have h0 := (h k).2
  have hnum : greedyNumerator D.A r σ y k (σ k) =
      greedyNumerator D.A r σ y k' (σ k) - D.A (lowSet σ ((k' : ℕ) + 1)) (σ k) * y k' := by
    unfold greedyNumerator
    rw [hsplit, Finset.sum_insert hnotmem]
    ring
  rw [← h0]
  apply div_nonpos_of_nonpos_of_nonneg _ hA0.le
  rw [hnum]
  linarith

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem cc500be5_obj_eq {N : ℕ} {Pol : Type u} (D : GCL1System N Pol) (r : Fin N → ℝ)
    (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ) (h : IsAdaptiveGreedy D.A r σ y)
    (x : Fin N → ℝ) :
    linearObjective r x = ∑ k : Fin N, y k * ∑ i, D.A (lowSet σ ((k : ℕ) + 1)) i * x i := by
  unfold linearObjective
  calc ∑ i, r i * x i = ∑ i, ∑ k : Fin N, D.A (lowSet σ ((k : ℕ) + 1)) i * y k * x i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [cc500be5_r_decomp D r σ y h i, Finset.sum_mul]
    _ = ∑ k : Fin N, ∑ i, D.A (lowSet σ ((k : ℕ) + 1)) i * y k * x i := Finset.sum_comm
    _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem cc500be5_weak_duality {N : ℕ} {Pol : Type u} (D : GCL1System N Pol) (r : Fin N → ℝ)
    (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ) (h : IsAdaptiveGreedy D.A r σ y)
    (x : Fin N → ℝ) (hx : x ∈ achievablePolytope D.A D.b) :
    linearObjective r x ≤ linearObjective r (D.perf (D.permPolicy σ)) := by
  obtain ⟨_, hxS, hxU⟩ := hx
  rw [cc500be5_obj_eq D r σ y h x, cc500be5_obj_eq D r σ y h]
  apply Finset.sum_le_sum
  intro k _
  have hcard := cc500be5_card_lowSet σ ((k : ℕ) + 1) (by have := k.isLt; omega)
  have htight : ∑ i, D.A (lowSet σ ((k : ℕ) + 1)) i * D.perf (D.permPolicy σ) i
      = D.b (lowSet σ ((k : ℕ) + 1)) := by
    rw [cc500be5_sum_univ_eq D]
    exact D.law_perm σ _ (by rw [hcard])
  rw [htight]
  rcases Nat.lt_or_ge ((k : ℕ) + 1) N with hlt | hge
  · have hy := cc500be5_y_nonpos D r σ y h k hlt
    have hne : lowSet σ ((k : ℕ) + 1) ≠ univ := by
      intro heq
      have := congrArg Finset.card heq
      rw [hcard, Finset.card_univ, Fintype.card_fin] at this
      omega
    have hge' := hxS _ hne
    rw [cc500be5_sum_univ_eq D]
    exact mul_le_mul_of_nonpos_left hge' hy
  · have hN : (k : ℕ) + 1 = N := by have := k.isLt; omega
    rw [hN, cc500be5_lowSet_N, hxU]

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem cc500be5_lowSet_swap {N : ℕ} (σ : Equiv.Perm (Fin N)) (k l : Fin N) (t : ℕ)
    (hk : (k : ℕ) < t) (hl : (l : ℕ) < t) :
    lowSet (σ * Equiv.swap k l) t = lowSet σ t := by
  ext i
  rw [cc500be5_mem_lowSet, cc500be5_mem_lowSet]
  have hsymm : (σ * Equiv.swap k l).symm i = Equiv.swap k l (σ.symm i) := by
    rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
  rw [hsymm, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [h1]; exact ⟨fun _ => hk, fun _ => hl⟩
  · rw [h2]; exact ⟨fun _ => hl, fun _ => hk⟩
  · exact Iff.rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem cc500be5_gN_congr {N : ℕ} (A : Finset (Fin N) → Fin N → ℝ) (r : Fin N → ℝ)
    (σ σ' : Equiv.Perm (Fin N)) (y y' : Fin N → ℝ) (k i : Fin N)
    (hL : ∀ t : ℕ, (k : ℕ) + 1 ≤ t → lowSet σ' t = lowSet σ t)
    (hy : ∀ j : Fin N, k < j → y' j = y j) :
    greedyNumerator A r σ' y' k i = greedyNumerator A r σ y k i := by
  unfold greedyNumerator
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  rw [hL _ (by have := Fin.lt_def.mp hj; omega), hy j hj]

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem cc500be5_stage_congr {N : ℕ} (A : Finset (Fin N) → Fin N → ℝ) (r : Fin N → ℝ)
    (σ σ' : Equiv.Perm (Fin N)) (y y' : Fin N → ℝ) (k : Fin N)
    (hL : ∀ t : ℕ, (k : ℕ) + 1 ≤ t → lowSet σ' t = lowSet σ t)
    (hσ : σ' k = σ k) (hy : ∀ j : Fin N, k ≤ j → y' j = y j)
    (hst : (∀ i ∈ lowSet σ ((k : ℕ) + 1),
        greedyNumerator A r σ y k i / A (lowSet σ ((k : ℕ) + 1)) i ≤ y k) ∧
      greedyNumerator A r σ y k (σ k) / A (lowSet σ ((k : ℕ) + 1)) (σ k) = y k) :
    (∀ i ∈ lowSet σ' ((k : ℕ) + 1),
        greedyNumerator A r σ' y' k i / A (lowSet σ' ((k : ℕ) + 1)) i ≤ y' k) ∧
      greedyNumerator A r σ' y' k (σ' k) / A (lowSet σ' ((k : ℕ) + 1)) (σ' k) = y' k := by
  have hg : ∀ i, greedyNumerator A r σ' y' k i = greedyNumerator A r σ y k i :=
    fun i => cc500be5_gN_congr A r σ σ' y y' k i hL (fun j hj => hy j hj.le)
  rw [hL _ le_rfl, hσ, hy k le_rfl]
  simp only [hg]
  exact hst

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem cc500be5_exists_AG {N : ℕ} (A : Finset (Fin N) → Fin N → ℝ) (r : Fin N → ℝ) :
    ∃ (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ), IsAdaptiveGreedy A r σ y := by
  have key : ∀ m : ℕ, m ≤ N → ∃ (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ),
      ∀ k : Fin N, N ≤ (k : ℕ) + m →
      ((∀ i ∈ lowSet σ ((k : ℕ) + 1),
          greedyNumerator A r σ y k i / A (lowSet σ ((k : ℕ) + 1)) i ≤ y k) ∧
        greedyNumerator A r σ y k (σ k) / A (lowSet σ ((k : ℕ) + 1)) (σ k) = y k) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨1, 0, fun k hk => ?_⟩
      exact absurd hk (by have := k.isLt; omega)
    | succ m ih =>
      intro hm
      obtain ⟨σ, y, hσy⟩ := ih (by omega)
      obtain ⟨k, hkv⟩ : ∃ k : Fin N, (k : ℕ) = N - 1 - m := ⟨⟨N - 1 - m, by omega⟩, rfl⟩
      have hne : (lowSet σ ((k : ℕ) + 1)).Nonempty :=
        ⟨σ k, by rw [cc500be5_mem_lowSet, Equiv.symm_apply_apply]; omega⟩
      obtain ⟨istar, histar, hmax⟩ := Finset.exists_max_image (lowSet σ ((k : ℕ) + 1))
        (fun i => greedyNumerator A r σ y k i / A (lowSet σ ((k : ℕ) + 1)) i) hne
      obtain ⟨l, hl⟩ : ∃ l : Fin N, l = σ.symm istar := ⟨_, rfl⟩
      have hlk : (l : ℕ) < (k : ℕ) + 1 := by
        rw [cc500be5_mem_lowSet] at histar
        rw [hl]
        exact histar
      obtain ⟨σ', hσ'⟩ : ∃ σ' : Equiv.Perm (Fin N), σ' = σ * Equiv.swap k l := ⟨_, rfl⟩
      obtain ⟨y', hy'⟩ : ∃ y' : Fin N → ℝ, y' = Function.update y k
          (greedyNumerator A r σ y k istar / A (lowSet σ ((k : ℕ) + 1)) istar) := ⟨_, rfl⟩
      have hL : ∀ t : ℕ, (k : ℕ) + 1 ≤ t → lowSet σ' t = lowSet σ t := by
        intro t ht
        rw [hσ']
        exact cc500be5_lowSet_swap σ k l t (by omega) (by omega)
      have hσ'k : σ' k = istar := by
        rw [hσ', Equiv.Perm.mul_apply, Equiv.swap_apply_left, hl, Equiv.apply_symm_apply]
      refine ⟨σ', y', fun k' hk' => ?_⟩
      have hkk' : k ≤ k' := by rw [Fin.le_def]; omega
      rcases lt_or_eq_of_le hkk' with hlt | heq
      · -- a stage already fixed by the induction hypothesis
        have hltv := Fin.lt_def.mp hlt
        have hk'm : N ≤ (k' : ℕ) + m := by omega
        have hL' : ∀ t : ℕ, (k' : ℕ) + 1 ≤ t → lowSet σ' t = lowSet σ t :=
          fun t ht => hL t (by omega)
        have hσk' : σ' k' = σ k' := by
          rw [hσ', Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne]
          · exact hlt.ne'
          · intro h
            rw [h] at hltv
            omega
        have hyk' : ∀ j : Fin N, k' ≤ j → y' j = y j := by
          intro j hj
          rw [hy', Function.update_of_ne (lt_of_lt_of_le hlt hj).ne']
        exact cc500be5_stage_congr A r σ σ' y y' k' hL' hσk' hyk' (hσy k' hk'm)
      · -- the new stage
        subst heq
        have hg : ∀ i, greedyNumerator A r σ' y' k i = greedyNumerator A r σ y k i :=
          fun i => cc500be5_gN_congr A r σ σ' y y' k i hL
            (fun j hj => by rw [hy', Function.update_of_ne hj.ne'])
        have hyk : y' k = greedyNumerator A r σ y k istar / A (lowSet σ ((k : ℕ) + 1)) istar := by
          rw [hy', Function.update_self]
        rw [hL _ le_rfl]
        simp only [hg]
        rw [hyk, hσ'k]
        exact ⟨fun i hi => hmax i hi, rfl⟩
  obtain ⟨σ, y, h⟩ := key N le_rfl
  exact ⟨σ, y, fun k => h k (by omega)⟩

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem cc500be5_subset_hull {N : ℕ} {Pol : Type u} (D : GCL1System N Pol) :
    achievablePolytope D.A D.b ⊆
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin N) => D.perf (D.permPolicy σ)) := by
  intro z hz
  by_contra hzK
  have hfin : (Set.range fun σ : Equiv.Perm (Fin N) => D.perf (D.permPolicy σ)).Finite :=
    Set.finite_range _
  obtain ⟨f, u, hfK, hfz⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ _) (hfin.isClosed_convexHull ℝ) hzK
  obtain ⟨r, hr⟩ : ∃ r : Fin N → ℝ, ∀ i, r i = f (fun j => if i = j then 1 else 0) :=
    ⟨_, fun _ => rfl⟩
  have hf : ∀ x : Fin N → ℝ, f x = linearObjective r x := by
    intro x
    have := LinearMap.pi_apply_eq_sum_univ (f : (Fin N → ℝ) →ₗ[ℝ] ℝ) x
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this]
    unfold linearObjective
    apply Finset.sum_congr rfl
    intro i _
    rw [hr, mul_comm]
  obtain ⟨σ, y, hAG⟩ := cc500be5_exists_AG D.A r
  have h1 := cc500be5_weak_duality D r σ y hAG z hz
  have h2 : f (D.perf (D.permPolicy σ)) < u := hfK _ (subset_convexHull ℝ _ ⟨σ, rfl⟩)
  rw [hf] at h2 hfz
  linarith

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem solution {N : ℕ} {Pol : Type u} (D : GCL1System N Pol)
    (hconv : Convex ℝ (Set.range D.perf)) (r : Fin N → ℝ) :
    Set.range D.perf = achievablePolytope D.A D.b ∧
    (∀ x ∈ Set.extremePoints ℝ (achievablePolytope D.A D.b),
      ∃ σ : Equiv.Perm (Fin N), x = D.perf (D.permPolicy σ)) ∧
    (∃ (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ), IsAdaptiveGreedy D.A r σ y) ∧
    (∀ (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ), IsAdaptiveGreedy D.A r σ y →
      ∀ π, linearObjective r (D.perf π) ≤ linearObjective r (D.perf (D.permPolicy σ))) := by
  have hrange : Set.range D.perf ⊆ achievablePolytope D.A D.b := by
    rintro _ ⟨π, rfl⟩
    exact ⟨D.perf_nonneg π, fun S _ => D.law_ge π S, D.law_univ π⟩
  have hV : (Set.range fun σ : Equiv.Perm (Fin N) => D.perf (D.permPolicy σ)) ⊆
      Set.range D.perf := by
    rintro _ ⟨σ, rfl⟩
    exact ⟨_, rfl⟩
  have hK : convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin N) => D.perf (D.permPolicy σ)) ⊆
      Set.range D.perf :=
    convexHull_min hV hconv
  have hP := cc500be5_subset_hull D
  refine ⟨?_, ?_, cc500be5_exists_AG D.A r, ?_⟩
  · exact Set.Subset.antisymm hrange (hP.trans hK)
  · intro x hx
    have hxK : x ∈ convexHull ℝ
        (Set.range fun σ : Equiv.Perm (Fin N) => D.perf (D.permPolicy σ)) := hP hx.1
    have hext := inter_extremePoints_subset_extremePoints_of_subset (hK.trans hrange) ⟨hxK, hx⟩
    obtain ⟨σ, hσ⟩ := extremePoints_convexHull_subset hext
    exact ⟨σ, hσ.symm⟩
  · intro σ y hAG π
    exact cc500be5_weak_duality D r σ y hAG _ (hrange ⟨π, rfl⟩)
