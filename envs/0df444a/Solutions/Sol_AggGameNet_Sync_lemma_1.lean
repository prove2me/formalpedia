-- Prove2me | solution 1 for AggGameNet.Sync.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:40:11.441736+00:00
-- url     : https://prove2.me/submissions/4a4bbcfa-7e51-4413-99b1-505bd20389ed

import Mathlib
import Definitions.Def_AggGameNet_Sync_Setting
import Theorems.Thm_DistAvgNOOT_lemma_5

namespace AggGameNet.Sync.L1aux

/-- sample variance -/
noncomputable def sv {N : ℕ} (y : Fin N → ℝ) : ℝ := ∑ i, (y i - (∑ j, y j) / N) ^ 2

lemma sum_mulVec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hcol : ∀ j, ∑ i, A i j = 1)
    (y : Fin N → ℝ) : ∑ i, (A.mulVec y) i = ∑ j, y j := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_mul, hcol j, one_mul]

lemma sv_mulVec_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hnn : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j = 1) (hcol : ∀ j, ∑ i, A i j = 1) (y : Fin N → ℝ) :
    sv (A.mulVec y) ≤ sv y := by
  unfold sv
  rw [sum_mulVec A hcol y]
  set m := (∑ j, y j) / N
  have key : ∀ i, (A.mulVec y i - m) ^ 2 ≤ ∑ j, A i j * (y j - m) ^ 2 := by
    intro i
    set b : Fin N → ℝ := fun j => y j - m
    set μ := ∑ j, A i j * b j
    have hμ : A.mulVec y i - m = μ := by
      simp only [Matrix.mulVec, dotProduct, μ, b, mul_sub, Finset.sum_sub_distrib,
        ← Finset.sum_mul, hrow i, one_mul]
    have h0 : 0 ≤ ∑ j, A i j * (b j - μ) ^ 2 :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hnn i j) (sq_nonneg _))
    have e : ∑ j, A i j * (b j - μ) ^ 2 = ∑ j, A i j * b j ^ 2 - μ ^ 2 := by
      have : ∀ j, A i j * (b j - μ) ^ 2 = A i j * b j ^ 2 - 2 * μ * (A i j * b j) +
          μ ^ 2 * A i j := fun j => by ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hrow i]
      ring
    rw [hμ]
    simp only [b] at e h0
    linarith
  refine (Finset.sum_le_sum (fun i _ => key i)).trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_mul, hcol j, one_mul]

/-- the `j`-th column sequence of the transition matrices started at `s` -/
noncomputable def colSeq {N : ℕ} (W : ℕ → Matrix (Fin N) (Fin N) ℝ) (s : ℕ) (j : Fin N) :
    ℕ → Fin N → ℝ
  | 0 => Pi.single j 1
  | t + 1 => (Phi W s t).mulVec (Pi.single j 1)

end AggGameNet.Sync.L1aux

open AggGameNet.Sync AggGameNet.Sync.L1aux
open Filter
open scoped Topology

theorem solution {N : ℕ} (hN : 0 < N)
    (G : ℕ → SimpleGraph (Fin N)) (Q : ℕ) (h4 : Assumption4 G Q)
    (W : ℕ → Matrix (Fin N) (Fin N) ℝ) (δ : ℝ)
    (hδ : 0 < δ) (h5 : Assumption5 G W δ) :
    (∀ s, Tendsto (fun m => Phi W s m) atTop
      (𝓝 (Matrix.of (fun _ _ => (1 / (N : ℝ)))))) ∧
    ∀ s m i j,
      |Phi W s m i j - 1 / (N : ℝ)| ≤ theta N δ * beta N Q δ ^ m := by
  -- basic properties of the weights
  have hnn : ∀ t i j, 0 ≤ W t i j := by
    intro t i j
    by_cases hj : nbr G t i j
    · exact hδ.le.trans (((h5 t).1 i j).1 hj)
    · exact le_of_eq (((h5 t).1 i j).2 hj).symm
  have hrow : ∀ t i, ∑ j, W t i j = 1 := fun t i => (h5 t).2.1 i
  have hcol : ∀ t j, ∑ i, W t i j = 1 := fun t j => (h5 t).2.2 j
  have hdiag : ∀ t i, δ ≤ W t i i := fun t i => ((h5 t).1 i i).1 (Or.inl rfl)
  have hηW : ∀ t i j, 0 < W t i j → δ ≤ W t i j := by
    intro t i j hp
    by_cases hj : nbr G t i j
    · exact ((h5 t).1 i j).1 hj
    · exact absurd (((h5 t).1 i j).2 hj) hp.ne'
  have hδ1 : δ ≤ 1 := by
    have hle : W 0 ⟨0, hN⟩ ⟨0, hN⟩ ≤ ∑ j, W 0 ⟨0, hN⟩ j :=
      Finset.single_le_sum (f := fun j => W 0 ⟨0, hN⟩ j) (fun j _ => hnn 0 _ j)
        (Finset.mem_univ _)
    rw [hrow] at hle
    linarith [hdiag 0 ⟨0, hN⟩]
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set η := δ / (4 * (N : ℝ) ^ 2) with hηdef
  set c := δ / (2 * (N : ℝ) ^ 2) with hcdef
  have hη0 : 0 < η := by positivity
  have hηq : η ≤ 1 / 4 := by
    rw [hηdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hc : c = 2 * η := by rw [hcdef, hηdef]; field_simp; ring
  have hc1 : 0 ≤ 1 - c := by rw [hc]; linarith
  have hQ1 : 1 ≤ Q := h4.1
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ1
  -- the main bound
  have hmain : ∀ s m i j, |Phi W s m i j - 1 / (N : ℝ)| ≤ (1 - η) ^ (m / Q) := by
    intro s m i j
    -- the column sequence
    set X : ℕ → Fin N → ℝ := colSeq W s j with hXdef
    have hX0 : X 0 = Pi.single j 1 := rfl
    have hXs : ∀ t, X (t + 1) = (Phi W s t).mulVec (Pi.single j 1) := fun t => rfl
    set A : ℕ → Matrix (Fin N) (Fin N) ℝ := fun t => W (s + t) with hAdef
    have hX : ∀ t, X (t + 1) = (A t).mulVec (X t) := by
      intro t
      cases t with
      | zero => rw [hXs, hX0]; simp [Phi, hAdef]
      | succ t =>
        rw [hXs, hXs, Matrix.mulVec_mulVec]
        simp only [Phi, hAdef]
        congr 2
    -- monotonicity
    have hmono : ∀ t, sv (X (t + 1)) ≤ sv (X t) := by
      intro t
      rw [hX t]
      exact sv_mulVec_le (A t) (fun i j => hnn _ i j) (fun i => hrow _ i) (fun j => hcol _ j) _
    have hmono' : ∀ a b, a ≤ b → sv (X b) ≤ sv (X a) := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => exact le_rfl
      | succ b _ ih => exact (hmono b).trans ih
    -- window contraction
    have hwin : ∀ w, sv (X (Q * w + 1 + Q)) ≤ (1 - c) * sv (X (Q * w + 1)) := by
      intro w
      have hconn : (⨆ t ∈ Finset.Ico (Q * w + 1) (Q * w + 1 + Q),
          SimpleGraph.fromRel (fun i j : Fin N => 0 < A t i j)).Connected := by
        refine (h4.2 (s + Q * w)).mono ?_
        refine iSup₂_le (fun l hl => ?_)
        have hl' := Finset.mem_Icc.1 hl
        refine le_trans ?_ (le_iSup₂_of_le (Q * w + l) (by
          simp only [Finset.mem_Ico]; omega) le_rfl)
        intro a b hab
        rw [SimpleGraph.fromRel_adj]
        refine ⟨hab.ne, Or.inl ?_⟩
        have : δ ≤ W (l + (s + Q * w)) a b := ((h5 _).1 a b).1 (Or.inr hab)
        simp only [hAdef]
        rw [show s + (Q * w + l) = l + (s + Q * w) by ring]
        linarith
      have := DistAvgNOOT.lemma_5 A δ (fun t i j => hnn _ i j) (fun t i => hrow _ i)
        (fun t j => hcol _ j) (fun t i => lt_of_lt_of_le hδ (hdiag _ i))
        (fun t i j h => hηW _ i j h) (Q * w + 1) Q hconn X hX
      simpa [sv, hcdef] using this
    have hpow : ∀ w, sv (X (Q * w + 1)) ≤ (1 - c) ^ w * sv (X 1) := by
      intro w
      induction w with
      | zero => simp
      | succ w ih =>
        rw [show Q * (w + 1) + 1 = Q * w + 1 + Q by ring]
        refine (hwin w).trans ?_
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_left ih hc1]
    -- initial variance
    have hsum1 : ∀ t, ∑ i, X t i = 1 := by
      intro t
      induction t with
      | zero => simp [hX0]
      | succ t ih => rw [hX t, sum_mulVec _ (fun j => hcol _ j), ih]
    have hsv0 : sv (X 0) ≤ 1 := by
      unfold sv
      rw [hsum1 0, hX0]
      have e : ∀ i, ((Pi.single j (1 : ℝ) : Fin N → ℝ) i - 1 / N) ^ 2 =
          ((Pi.single j (1 : ℝ) : Fin N → ℝ) i) ^ 2 - 2 / N * (Pi.single j (1 : ℝ) : Fin N → ℝ) i
            + 1 / (N : ℝ) ^ 2 := by
        intro i; ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h1 : ∑ i, ((Pi.single j (1 : ℝ) : Fin N → ℝ) i) ^ 2 = 1 := by
        rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
        simp
      have h2 : ∑ i, (Pi.single j (1 : ℝ) : Fin N → ℝ) i = 1 := by
        rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
        simp
      rw [h1, h2]
      have : (N : ℝ) * (1 / (N : ℝ) ^ 2) = 1 / N := by field_simp
      rw [this]
      have : 0 < 1 / (N : ℝ) := by positivity
      have : 2 / (N : ℝ) * 1 = 2 * (1 / N) := by ring
      linarith
    -- entry bound
    set w := m / Q
    have hwm : Q * w ≤ m := Nat.mul_div_le m Q
    have hsvm : sv (X (m + 1)) ≤ (1 - c) ^ w := by
      have := hmono' (Q * w + 1) (m + 1) (by omega)
      have h2 := hpow w
      have h3 := (hmono 0).trans hsv0
      have h4 : (1 - c) ^ w * sv (X 1) ≤ (1 - c) ^ w :=
        by nlinarith [pow_nonneg hc1 w, show 0 ≤ sv (X 1) from
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)]
      linarith
    have hentry : (X (m + 1) i - 1 / N) ^ 2 ≤ sv (X (m + 1)) := by
      have h := hsum1 (m + 1)
      unfold sv
      rw [h]
      exact Finset.single_le_sum (f := fun i => (X (m + 1) i - 1 / N) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    have hXe : X (m + 1) i = Phi W s m i j := by
      rw [hXs]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hcη : (1 - c) ^ w ≤ ((1 - η) ^ w) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      apply pow_le_pow_left₀ hc1
      rw [hc]; nlinarith
    rw [← hXe]
    exact abs_le_of_sq_le_sq (by linarith) (pow_nonneg (by linarith) _)
  -- comparison with θ β ^ m
  have hb0 : 0 < 1 - η := by linarith
  have hb1 : 1 - η ≤ 1 := by linarith
  have hcmp : ∀ m, (1 - η) ^ (m / Q) ≤ theta N δ * beta N Q δ ^ m := by
    intro m
    unfold theta beta
    rw [← hηdef]
    rw [← Real.rpow_natCast ((1 - η) ^ ((1 : ℝ) / (Q : ℝ))) m, ← Real.rpow_mul hb0.le,
      ← Real.rpow_intCast, ← Real.rpow_add hb0, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_ge hb0 hb1
    have hq : ((m / Q : ℕ) : ℝ) + 1 ≥ (m : ℝ) / Q := by
      have h := Nat.lt_div_mul_add (a := m) (show 0 < Q by omega)
      rw [ge_iff_le, div_le_iff₀ hQpos]
      have : (m : ℝ) < ((m / Q : ℕ) : ℝ) * Q + Q := by exact_mod_cast h
      linarith
    push_cast
    have : 1 / (Q : ℝ) * m = (m : ℝ) / Q := by ring
    linarith
  have hbound : ∀ s m i j, |Phi W s m i j - 1 / (N : ℝ)| ≤ theta N δ * beta N Q δ ^ m :=
    fun s m i j => (hmain s m i j).trans (hcmp m)
  refine ⟨fun s => ?_, hbound⟩
  -- limit
  have hβ0 : 0 ≤ beta N Q δ := (Real.rpow_pos_of_pos hb0 _).le
  have hβ1 : beta N Q δ < 1 := by
    unfold beta
    rw [← hηdef]
    exact Real.rpow_lt_one hb0.le (by linarith) (by positivity)
  have hgeo : Tendsto (fun m => theta N δ * beta N Q δ ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).const_mul (theta N δ)
  refine tendsto_pi_nhds.2 (fun i => tendsto_pi_nhds.2 (fun j => ?_))
  show Tendsto (fun m => Phi W s m i j) atTop (𝓝 (1 / (N : ℝ)))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun m => by
    rw [Real.norm_eq_abs]; exact hbound s m i j) hgeo
