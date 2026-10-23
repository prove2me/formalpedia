-- Prove2me | solution 1 for AccelVI.AVC.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:57:45.295984+00:00
-- url     : https://prove2.me/submissions/cc772dcc-494f-4102-9d26-a036b615aede

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

open Matrix

namespace AccelVI.AVC

set_option linter.unusedSectionVars false

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

lemma e4_L_nonneg (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ)
    (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol) (i j : S) :
    0 ≤ LPol M pol i j := by
  simp only [LPol, Matrix.of_apply, FoundationsML.ReinforcementLearning.InducedTransition]
  exact Finset.sum_nonneg fun a _ => mul_nonneg ((hpol i).1 a) ((hM.1 i a).1 j)

lemma e4_L_rowsum (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ)
    (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol) (i : S) :
    ∑ j, LPol M pol i j = 1 := by
  simp only [LPol, Matrix.of_apply, FoundationsML.ReinforcementLearning.InducedTransition]
  rw [Finset.sum_comm]
  calc ∑ a, ∑ j, pol i a * M.P i a j = ∑ a, pol i a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.mul_sum, (hM.1 i a).2, mul_one]
    _ = 1 := (hpol i).2

lemma e4_pow_stoch (P : Matrix S S ℝ) (h0 : ∀ i j, 0 ≤ P i j) (h1 : ∀ i, ∑ j, P i j = 1) (n : ℕ) :
    (∀ i j, 0 ≤ (P ^ n) i j) ∧ ∀ i, ∑ j, (P ^ n) i j = 1 := by
  induction n with
  | zero =>
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [Matrix.one_apply]
  | succ n ih =>
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (ih.1 i k) (h0 k j)
    · rw [pow_succ]
      simp_rw [Matrix.mul_apply]
      rw [Finset.sum_comm]
      calc ∑ k, ∑ j, (P ^ n) i k * P k j = ∑ k, (P ^ n) i k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← Finset.mul_sum, h1 k, mul_one]
        _ = 1 := ih.2 i

lemma e4_occ (M : MDP S A) (pol : S → A → ℝ) (s : S) (t : ℕ) (s' : S) :
    FoundationsML.ReinforcementLearning.OccupationDist pol M.P s t s' = (LPol M pol ^ t) s s' := by
  induction t generalizing s' with
  | zero =>
    simp only [FoundationsML.ReinforcementLearning.OccupationDist, pow_zero, Matrix.one_apply]
    by_cases h : s' = s
    · simp [h]
    · simp [h, Ne.symm h]
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp only [FoundationsML.ReinforcementLearning.OccupationDist]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ih]; rfl

lemma e4_fixed (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ)
    (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol) :
    valuePol M pol = Tpol M pol (valuePol M pol) := by
  have hL0 := e4_L_nonneg M hM pol hpol
  have hL1 := e4_L_rowsum M hM pol hpol
  have hlam0 := hM.2.1
  have hlam1 := hM.2.2
  set L := LPol M pol with hLdef
  set r := rPol M pol with hrdef
  have hval : ∀ s, valuePol M pol s = ∑' t : ℕ, M.lam ^ t * ((L ^ t) *ᵥ r) s := by
    intro s
    unfold valuePol FoundationsML.ReinforcementLearning.PolicyValue
    refine tsum_congr fun t => ?_
    congr 1
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [e4_occ]; rfl
  set C : ℝ := ∑ j, |r j| with hC
  have hbound : ∀ t s, |((L ^ t) *ᵥ r) s| ≤ C := by
    intro t s
    have := e4_pow_stoch L hL0 hL1 t
    simp only [Matrix.mulVec, dotProduct]
    calc |∑ j, (L ^ t) s j * r j| ≤ ∑ j, |(L ^ t) s j * r j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |r j| := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (this.1 s j)]
        have h1 : (L ^ t) s j ≤ 1 := by
          rw [← this.2 s]
          exact Finset.single_le_sum (f := fun j => (L ^ t) s j) (fun k _ => this.1 s k) (Finset.mem_univ j)
        exact mul_le_of_le_one_left (abs_nonneg _) h1
  have hsum : ∀ s, Summable fun t : ℕ => M.lam ^ t * ((L ^ t) *ᵥ r) s := by
    intro s
    refine Summable.of_norm_bounded (g := fun t : ℕ => C * M.lam ^ t) ?_ ?_
    · exact (summable_geometric_of_lt_one hlam0.le hlam1).mul_left _
    · intro t
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hlam0.le t), mul_comm]
      exact mul_le_mul_of_nonneg_right (hbound t s) (pow_nonneg hlam0.le t)
  funext i
  simp only [Tpol, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hrec : ∀ t : ℕ, M.lam ^ (t + 1) * ((L ^ (t + 1)) *ᵥ r) i =
      M.lam * ∑ j, L i j * (M.lam ^ t * ((L ^ t) *ᵥ r) j) := by
    intro t
    rw [pow_succ' M.lam t, pow_succ' L t, ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring_nf
  have hswap : ∑' t : ℕ, ∑ j, L i j * (M.lam ^ t * ((L ^ t) *ᵥ r) j) =
      ∑ j, L i j * valuePol M pol j := by
    rw [Summable.tsum_finsetSum (fun j _ => ((hsum j)).mul_left _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tsum_mul_left, hval j]
  rw [hval i, Summable.tsum_eq_zero_add (hsum i)]
  simp only [pow_zero, one_mul, Matrix.one_mulVec]
  rw [tsum_congr hrec, tsum_mul_left, hswap]
  simp only [Matrix.mulVec, dotProduct]
  rfl


lemma e4_theta (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    alphaAVC lam * lam * (1 + gammaAVC lam) = theta lam ∧
    alphaAVC lam * lam * gammaAVC lam = theta lam ^ 2 / 2 := by
  have hu2 : Real.sqrt (1 - lam) ^ 2 = 1 - lam := Real.sq_sqrt (by linarith)
  have hw2 : Real.sqrt (1 + lam) ^ 2 = 1 + lam := Real.sq_sqrt (by linarith)
  have hu : 0 < Real.sqrt (1 - lam) := Real.sqrt_pos.2 (by linarith)
  have hw : 0 < Real.sqrt (1 + lam) := Real.sqrt_pos.2 (by linarith)
  have hth : theta lam = 1 - Real.sqrt (1 - lam) / Real.sqrt (1 + lam) := by
    unfold theta kappa
    rw [one_div_div, Real.sqrt_div' _ (by linarith)]
  have hg : gammaAVC lam = (1 - Real.sqrt (1 - lam) * Real.sqrt (1 + lam)) / lam := by
    unfold gammaAVC
    rw [← Real.sqrt_mul (by linarith)]
    congr 3
    ring
  have ha : alphaAVC lam = 1 / Real.sqrt (1 + lam) ^ 2 := by
    unfold alphaAVC; rw [hw2]
  rw [hth, hg, ha]
  generalize Real.sqrt (1 - lam) = u at *
  generalize Real.sqrt (1 + lam) = w at *
  constructor
  · field_simp
    nlinarith [hu2, hw2]
  · field_simp
    nlinarith [hu2, hw2]


lemma e4_rec (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ)
    (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol) (v0 v1 : S → ℝ) (s : ℕ) :
    avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1 (s + 2) - valuePol M pol =
      theta M.lam • (1 + LPol M pol) *ᵥ (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1 (s + 1) - valuePol M pol)
      - (theta M.lam ^ 2 / 2) • (1 + LPol M pol) *ᵥ (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1 s - valuePol M pol) := by
  have hfix := e4_fixed M hM pol hpol
  obtain ⟨c1, c2⟩ := e4_theta M.lam hM.2.1 hM.2.2
  have hlam := hM.2.1
  have hα : 1 - alphaAVC M.lam = alphaAVC M.lam * M.lam := by
    unfold alphaAVC; field_simp; ring
  have hα' : alphaAVC M.lam * (1 + M.lam) = 1 := by
    unfold alphaAVC; field_simp
  show (let h := avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1 (s + 1) + gammaAVC M.lam • (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1 (s + 1) - avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1 s)
      h - alphaAVC M.lam • (h - Tpol M pol h)) - valuePol M pol = _
  generalize avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1 (s + 1) = a
  generalize avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1 s = b
  generalize alphaAVC M.lam = α at *
  generalize gammaAVC M.lam = γ at *
  generalize theta M.lam = θ at *
  funext i
  have e1 := congrFun hfix i
  simp only [Tpol, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 ⊢
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.add_mulVec,
    Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← c2]
  subst c1
  linear_combination ((1+γ)*a i - γ*b i) * hα + (-α) * e1 + (valuePol M pol i) * hα'


lemma e4_step (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ)
    (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol) (v0 v1 : S → ℝ) (n : ℕ) :
    xvec (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1) (n + 2) - xPi M pol =
      (Bpol M pol) *ᵥ (xvec (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1) (n + 1) - xPi M pol) := by
  have hr := e4_rec M hM pol hpol v0 v1 n
  generalize avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1 = v at *
  have h1 : xvec v (n + 1) - xPi M pol = Sum.elim (v (n + 1) - valuePol M pol) (v n - valuePol M pol) := by
    ext (i | i) <;> simp [xvec, xPi]
  have h2 : xvec v (n + 2) - xPi M pol = Sum.elim (v (n + 2) - valuePol M pol) (v (n + 1) - valuePol M pol) := by
    ext (i | i) <;> simp [xvec, xPi]
  rw [h1, h2, Bpol, Matrix.fromBlocks_mulVec]
  ext (i | i)
  · simp only [Sum.elim_inl, Function.comp_def, Pi.add_apply, Matrix.smul_mulVec, hr]
    simp [Pi.sub_apply, sub_eq_add_neg]
    rfl
  · simp [Function.comp_def]

lemma lemma_5_2_core (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ)
    (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol) (v0 v1 : S → ℝ) (s : ℕ) (hs : 1 ≤ s) :
    xvec (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1) s =
      xPi M pol + ((Bpol M pol) ^ (s - 1)).mulVec
        (xvec (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1) 1 - xPi M pol) := by
  have key : ∀ n : ℕ, xvec (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1) (n + 1) - xPi M pol =
      ((Bpol M pol) ^ n).mulVec
        (xvec (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1) 1 - xPi M pol) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [e4_step M hM pol hpol v0 v1 n, ih, Matrix.mulVec_mulVec, ← pow_succ']
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← key n]
  abel

end AccelVI.AVC

open AccelVI.AVC
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

theorem solution (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol)
    (v0 v1 : S → ℝ) (s : ℕ) (hs : 1 ≤ s) :
    xvec (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1) s =
      xPi M pol + ((Bpol M pol) ^ (s - 1)).mulVec
        (xvec (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1) 1 - xPi M pol) := by
  exact lemma_5_2_core M hM pol hpol v0 v1 s hs
