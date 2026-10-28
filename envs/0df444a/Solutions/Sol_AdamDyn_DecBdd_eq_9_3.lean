-- Prove2me | solution 1 for AdamDyn.DecBdd.eq_9_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:44:39.462997+00:00
-- url     : https://prove2.me/submissions/de751de4-1664-48c3-9501-c8e7e8f552cd

import Mathlib
import Definitions.Def_AdamDyn_DecBdd_Algorithm
import Definitions.Def_AdamDyn_DecBdd_ProofQuantities

open AdamDyn.DecBdd in
theorem solution {d : ℕ} {Ξ : Type*} (gf : AdamDyn.ConstStep.E d → Ξ → AdamDyn.ConstStep.E d)
    (γ α β : ℕ → ℝ) (ε : ℝ) (x0 : AdamDyn.ConstStep.E d)
    (hβ : ∀ n, 0 ≤ β n ∧ β n ≤ 1) (hβ1 : β 1 < 1)
    (ξs : ℕ → Ξ) (n : ℕ) (hn : 1 ≤ n) (hβpos : 0 < β (n + 1)) (i : Fin d) :
    Real.sqrt (vHat β n (adamRun gf γ α β ε x0 ξs n) i)
        - Real.sqrt (vHat β (n + 1) (adamRun gf γ α β ε x0 ξs (n + 1)) i) ≤
      cCoef β n * Real.sqrt (vHat β (n + 1) (adamRun gf γ α β ε x0 ξs (n + 1)) i) := by
  have hstep : ∀ k j, (adamRun gf γ α β ε x0 ξs (k + 1)).2.2 j
      = β (k + 1) * (adamRun gf γ α β ε x0 ξs k).2.2 j
        + (1 - β (k + 1)) * (gf (adamRun gf γ α β ε x0 ξs k).1 (ξs (k + 1))) j ^ 2 := by
    intro k j; rfl
  have hv : ∀ k j, 0 ≤ (adamRun gf γ α β ε x0 ξs k).2.2 j := by
    intro k
    induction k with
    | zero => intro j; simp [adamRun]
    | succ k ih =>
      intro j
      rw [hstep]
      have h1 := hβ (k + 1)
      have := ih j
      have h2 : 0 ≤ (1 - β (k + 1)) := by linarith
      nlinarith [mul_nonneg h1.1 this,
        mul_nonneg h2 (sq_nonneg ((gf (adamRun gf γ α β ε x0 ξs k).1 (ξs (k + 1))) j))]
  have hbw : ∀ k, AdamDyn.DecConv.biasWeight β (k + 1)
      = β (k + 1) * AdamDyn.DecConv.biasWeight β k + (1 - β (k + 1)) := fun k => rfl
  have hr : ∀ k, 1 ≤ k → 0 < AdamDyn.DecConv.biasWeight β k ∧ AdamDyn.DecConv.biasWeight β k ≤ 1 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      rw [hbw]
      have : AdamDyn.DecConv.biasWeight β 0 = 0 := rfl
      rw [this]
      constructor <;> linarith [hβ 1]
    | succ k _ ih =>
      rw [hbw]
      have h1 := hβ (k + 1)
      obtain ⟨ih1, ih2⟩ := ih
      constructor
      · nlinarith
      · nlinarith
  obtain ⟨hr0, hr1⟩ := hr n hn
  set v := (adamRun gf γ α β ε x0 ξs n).2.2 i with hvdef
  set v' := (adamRun gf γ α β ε x0 ξs (n + 1)).2.2 i with hv'def
  set r := AdamDyn.DecConv.biasWeight β n with hrdef
  set r' := AdamDyn.DecConv.biasWeight β (n + 1) with hr'def
  set b := β (n + 1) with hbdef
  have hv0 : 0 ≤ v := hv n i
  have hv'0 : 0 ≤ v' := hv (n + 1) i
  have hr'eq : r' = b * r + (1 - b) := hbw n
  have hb1 : b ≤ 1 := (hβ (n + 1)).2
  have hr'0 : 0 < r' := by rw [hr'eq]; nlinarith
  have hvv : b * v ≤ v' := by
    rw [hv'def, hstep]
    have : 0 ≤ (1 - b) := by linarith
    have := sq_nonneg ((gf (adamRun gf γ α β ε x0 ξs n).1 (ξs (n + 1))) i)
    nlinarith
  have ex : vHat β n (adamRun gf γ α β ε x0 ξs n) i = v / r := rfl
  have ey : vHat β (n + 1) (adamRun gf γ α β ε x0 ξs (n + 1)) i = v' / r' := rfl
  rw [ex, ey]
  set s := Real.sqrt b with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hβpos
  have hs2 : s ^ 2 = b := Real.sq_sqrt hβpos.le
  have hs1 : s ≤ 1 := by rw [hsdef]; exact Real.sqrt_le_one.mpr hb1
  set c := cCoef β n with hcdef
  set u := (1 - b) * (1 - r) / (2 * r) with hudef
  have hu0 : 0 ≤ u := by
    rw [hudef]; apply div_nonneg _ (by linarith); nlinarith
  have hcs : c * s = 1 - s + u := by
    rw [hcdef, cCoef, ← hbdef, ← hsdef, hudef, ← hrdef]
    have h1s : (1 : ℝ) + s ≠ 0 := by linarith
    have e1 : (1 - b) / s * (1 / (1 + s) + (1 - r) / (2 * r)) * s
        = (1 - b) / (1 + s) + (1 - b) * (1 - r) / (2 * r) := by
      field_simp
    rw [e1]
    have e2 : (1 - b) / (1 + s) = 1 - s := by
      rw [div_eq_iff h1s, ← hs2]; ring
    rw [e2]
  have hc0 : 0 ≤ c := by
    have : 0 ≤ c * s := by rw [hcs]; linarith
    exact nonneg_of_mul_nonneg_left this hs0 |> fun h => by nlinarith
  -- key inequality: v / r ≤ (1 + c) ^ 2 * (v' / r')
  have hkey : v / r ≤ (1 + c) ^ 2 * (v' / r') := by
    have hA : (1 + c) * s = 1 + u := by linarith
    have hineq : r' ≤ (1 + u) ^ 2 * r := by
      rw [hr'eq]
      have : (1 + u) ^ 2 * r ≥ (1 + 2 * u) * r := by nlinarith [mul_nonneg (sq_nonneg u) hr0.le]
      have e : (1 + 2 * u) * r = r + (1 - b) * (1 - r) := by
        rw [hudef]; field_simp
      nlinarith
    rw [div_le_iff₀ hr0]
    have h3 : (1 + c) ^ 2 * (v' / r') * r ≥ (1 + c) ^ 2 * (b * v / r') * r := by
      have : b * v / r' ≤ v' / r' := div_le_div_of_nonneg_right hvv hr'0.le
      have h00 : 0 ≤ (1 + c) ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h00) hr0.le
    have h4 : (1 + c) ^ 2 * (b * v / r') * r = ((1 + u) ^ 2 * r) * v / r' := by
      have hcb : (1 + c) ^ 2 * b = (1 + u) ^ 2 := by rw [← hs2, ← hA]; ring
      calc (1 + c) ^ 2 * (b * v / r') * r = ((1 + c) ^ 2 * b) * r * v / r' := by ring
        _ = ((1 + u) ^ 2 * r) * v / r' := by rw [hcb]
    have h5 : ((1 + u) ^ 2 * r) * v / r' ≥ v := by
      rw [ge_iff_le, le_div_iff₀ hr'0]
      nlinarith [mul_le_mul_of_nonneg_left hineq hv0]
    linarith
  have hsq : Real.sqrt (v / r) ≤ (1 + c) * Real.sqrt (v' / r') := by
    calc Real.sqrt (v / r) ≤ Real.sqrt ((1 + c) ^ 2 * (v' / r')) := Real.sqrt_le_sqrt hkey
      _ = (1 + c) * Real.sqrt (v' / r') := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
  linarith
