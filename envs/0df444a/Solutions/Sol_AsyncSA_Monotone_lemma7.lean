-- Prove2me | solution 1 for AsyncSA.Monotone.lemma7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T19:59:46.576542+00:00
-- url     : https://prove2.me/submissions/a84c7008-a1af-43ef-b16e-cdf2f6f8a5c6

import Mathlib
import Definitions.Def_AsyncSA_Monotone_Model

open AsyncSA.Monotone in
theorem solution {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (xstar : Fin n → ℝ) (r : ℝ)
    (h4 : Assumption4 alg.F xstar) (hr : 0 < r) (ω : Ω) (k tk t'k t''k : ℕ)
    (h18 : ∀ t, tk ≤ t →
      Lseq alg.F xstar r k ≤ alg.x t ω ∧ alg.x t ω ≤ Useq alg.F xstar r k)
    (hτ : ∀ t, t'k ≤ t → ∀ i j, tk ≤ alg.τ i j t ω)
    (X : Fin n → ℕ → ℝ)
    (hX0 : ∀ i, X i t'k = Useq alg.F xstar r k i)
    (hX : ∀ i t, t'k ≤ t →
      X i (t + 1) = (1 - alg.α i t ω) * X i t + alg.α i t ω * alg.F (Useq alg.F xstar r k) i)
    (hUF : Useq alg.F xstar r k ≠ alg.F (Useq alg.F xstar r k))
    (δ : ℝ)
    (hδ : IsLeast ((fun i => (Useq alg.F xstar r k i - alg.F (Useq alg.F xstar r k) i) / 4) ''
      {i | 0 < Useq alg.F xstar r k i - alg.F (Useq alg.F xstar r k) i}) δ)
    (ht'' : t'k ≤ t''k)
    (hprod : ∀ i, ∏ s ∈ Finset.Ico t'k t''k, (1 - alg.α i s ω) ≤ 1 / 4)
    (hW : ∀ t, t''k ≤ t → ∀ i,
      tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t'k t ≤ δ) :
    ∀ i, ∀ t, t''k ≤ t → alg.x t ω i ≤ Useq alg.F xstar r (k + 1) i := by
  intro i
  have htk : tk ≤ t'k := (hτ t'k le_rfl i i).trans (alg.τ_le i i t'k ω)
  have key : ∀ t, t'k ≤ t → alg.x t ω i ≤
      X i t + tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t'k t := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      have hW0 : tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t'k t'k = 0 := by
        cases t'k with
        | zero => rfl
        | succ m => simp [tailW]
      rw [hW0, add_zero, hX0]
      exact (h18 t'k htk).2 i
    | succ t ht ih =>
      have hWs : tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t'k (t + 1) =
          (1 - alg.α i t ω) * tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t'k t +
            alg.α i t ω * alg.w i t ω := by
        simp only [tailW, if_pos ht]
      rw [alg.update, hX i t ht, hWs]
      have hxi : alg.F (fun j => alg.x (alg.τ i j t ω) ω j) i ≤
          alg.F (Useq alg.F xstar r k) i :=
        h4.mono (fun j => (h18 _ (hτ t ht i j)).2 j) i
      obtain ⟨a0, a1⟩ := alg.α_mem i t ω
      nlinarith [mul_le_mul_of_nonneg_left ih (sub_nonneg.2 a1),
        mul_le_mul_of_nonneg_left hxi a0]
  have hcf : ∀ t, t'k ≤ t → X i t - alg.F (Useq alg.F xstar r k) i =
      (∏ s ∈ Finset.Ico t'k t, (1 - alg.α i s ω)) *
        (Useq alg.F xstar r k i - alg.F (Useq alg.F xstar r k) i) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => simp [hX0]
    | succ t ht ih =>
      rw [Finset.prod_Ico_succ_top ht, hX i t ht,
        show (1 - alg.α i t ω) * X i t + alg.α i t ω * alg.F (Useq alg.F xstar r k) i -
          alg.F (Useq alg.F xstar r k) i =
          (1 - alg.α i t ω) * (X i t - alg.F (Useq alg.F xstar r k) i) by ring, ih]
      ring
  have hP : ∀ t, t''k ≤ t → 0 ≤ ∏ s ∈ Finset.Ico t'k t, (1 - alg.α i s ω) ∧
      ∏ s ∈ Finset.Ico t'k t, (1 - alg.α i s ω) ≤ 1 / 4 := by
    intro t ht
    rw [← Finset.prod_Ico_consecutive _ ht'' ht]
    have h1 : 0 ≤ ∏ s ∈ Finset.Ico t'k t''k, (1 - alg.α i s ω) :=
      Finset.prod_nonneg (fun s _ => sub_nonneg.2 (alg.α_mem i s ω).2)
    have h2 : 0 ≤ ∏ s ∈ Finset.Ico t''k t, (1 - alg.α i s ω) :=
      Finset.prod_nonneg (fun s _ => sub_nonneg.2 (alg.α_mem i s ω).2)
    have h3 : ∏ s ∈ Finset.Ico t''k t, (1 - alg.α i s ω) ≤ 1 :=
      Finset.prod_le_one (fun s _ => sub_nonneg.2 (alg.α_mem i s ω).2)
        (fun s _ => by linarith [(alg.α_mem i s ω).1])
    refine ⟨mul_nonneg h1 h2, ?_⟩
    calc _ ≤ 1 / 4 * 1 := mul_le_mul (hprod i) h3 h2 (by norm_num)
      _ = 1 / 4 := by norm_num
  intro t ht
  have hx := key t (ht''.trans ht)
  have hw := hW t ht i
  have hc := hcf t (ht''.trans ht)
  obtain ⟨p0, p1⟩ := hP t ht
  have hU1 : Useq alg.F xstar r (k + 1) i =
      1 / 2 * (Useq alg.F xstar r k i + alg.F (Useq alg.F xstar r k) i) := by
    simp only [Useq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [hU1]
  by_cases hD : 0 < Useq alg.F xstar r k i - alg.F (Useq alg.F xstar r k) i
  · have hδle : δ ≤ (Useq alg.F xstar r k i - alg.F (Useq alg.F xstar r k) i) / 4 :=
      hδ.2 ⟨i, hD, rfl⟩
    have := mul_le_mul_of_nonneg_right p1 hD.le
    linarith
  · push Not at hD
    have := (h18 t (by omega)).2 i
    linarith
