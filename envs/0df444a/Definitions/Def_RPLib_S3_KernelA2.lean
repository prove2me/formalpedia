-- Prove2me | Definitions.Def_RPLib_S3_KernelA2
-- name    : RPLib_S3_KernelA2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:53:17.25601+00:00
-- url     : https://prove2.me/theorems/df9d3bf7-09fc-4f6b-804d-b1c97fc47efa
-- title:
--   The Eichler-Selberg trace formula, kernel part A2: $\omega(\cdot, w)$ is a cusp form on $\Gamma_1(M)$
-- statement:
--   The Hecke kernel $\omega(z,w)$ transforms under $\Gamma_1(M)$ with weight $k$ in $z$ and decays at every cusp, so that for fixed $w$ it defines a cusp form $\omega(\cdot, w) \in S_k(\Gamma_1(M))$ when $k \ge 3$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib
import Definitions.Def_RPLib_S3_KernelA

/-!
# S3-Kernel, part A2: slash behaviour, cusp decay and `ω(·, w)` as a cusp form on `Γ₁(M)` (`k ≥ 3`)

* `Q_smul`: `Q(g; γ τ, w) j(γ, τ) = Q(g γ; τ, w)`; `omegaH_slash`, `omegaH_slash_Gamma1` (invariance under `Γ₁(M)`);
* decay: the 1-periodic majorant `Fsum n k z w = Σ_{det g = n} |Q(g; z, w)|^(-k)` (`Fsum_add_int`) satisfies
  `Fsum ≤ Cdecay n k w * y^(-1/4)` for `y ≥ 1` (`Fsum_le'`), so `isZeroAtImInfty_omegaH_slash` at every cusp;
* `omegaCF M k hn δ' hk w hv : CuspForm (Γ₁(M) in GL₂(ℝ)) k` (defeq `Diamond.S1 M k`), `coe_omegaCF`.
-/

open Filter Complex UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups Topology Manifold

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.Kernel

lemma Q_mobius (g A : Matrix (Fin 2) (Fin 2) ℤ) (z w : ℂ) (hd : (A 1 0 : ℂ) * z + (A 1 1 : ℂ) ≠ 0) :
    Q g (((A 0 0 : ℂ) * z + (A 0 1 : ℂ)) / ((A 1 0 : ℂ) * z + (A 1 1 : ℂ))) w *
      ((A 1 0 : ℂ) * z + (A 1 1 : ℂ)) = Q (g * A) z w := by
  calc Q g (((A 0 0 : ℂ) * z + (A 0 1 : ℂ)) / ((A 1 0 : ℂ) * z + (A 1 1 : ℂ))) w *
        ((A 1 0 : ℂ) * z + (A 1 1 : ℂ))
      = ((g 1 0 : ℂ) * w + g 0 0) * (((A 0 0 : ℂ) * z + (A 0 1 : ℂ)) /
          ((A 1 0 : ℂ) * z + (A 1 1 : ℂ)) * ((A 1 0 : ℂ) * z + (A 1 1 : ℂ))) +
        ((g 1 1 : ℂ) * w + g 0 1) * ((A 1 0 : ℂ) * z + (A 1 1 : ℂ)) := by unfold Q; ring
    _ = ((g 1 0 : ℂ) * w + g 0 0) * ((A 0 0 : ℂ) * z + (A 0 1 : ℂ)) +
        ((g 1 1 : ℂ) * w + g 0 1) * ((A 1 0 : ℂ) * z + (A 1 1 : ℂ)) := by rw [div_mul_cancel₀ _ hd]
    _ = Q (g * A) z w := by
        simp only [Q, Matrix.mul_apply, Fin.sum_univ_two]
        push_cast
        ring

lemma coe_smul_SL (γ : SL(2, ℤ)) (τ : ℍ) : ((γ • τ : ℍ) : ℂ) =
    (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) / (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp

lemma denom_SL (γ : SL(2, ℤ)) (τ : ℍ) : denom γ τ = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
  simp [ModularGroup.denom_apply]

/-- `Q(g; γ τ, w) j(γ, τ) = Q(g γ; τ, w)`. -/
lemma Q_smul (g : Matrix (Fin 2) (Fin 2) ℤ) (γ : SL(2, ℤ)) (τ : ℍ) (w : ℂ) :
    Q g ((γ • τ : ℍ) : ℂ) w * denom γ τ = Q (g * (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ w := by
  have hd := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
  rw [denom_SL] at hd ⊢
  rw [coe_smul_SL]
  exact Q_mobius g γ τ w hd

/-- `ω(·, w)` as a function on `ℍ`. -/
def omegaH (M k : ℕ) (n : ℤ) (δ' : ZMod M) (w : ℂ) : ℍ → ℂ := fun τ => omega M k n δ' τ w

lemma term_slash (g : Matrix (Fin 2) (Fin 2) ℤ) (γ : SL(2, ℤ)) (τ : ℍ) (w : ℂ) (k : ℕ) :
    (Q g ((γ • τ : ℍ) : ℂ) w ^ k)⁻¹ * denom γ τ ^ (-(k : ℤ)) =
      (Q (g * (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ w ^ k)⁻¹ := by
  rw [← Q_smul, mul_pow, mul_inv, zpow_neg, zpow_natCast]

theorem omegaH_slash (M k : ℕ) (n : ℤ) (δ' : ZMod M) (w : ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (omegaH M k n δ' w ∣[(k : ℤ)] γ) τ =
      ∑' g : DeltaSet M n δ', (Q (g.1 * (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ w ^ k)⁻¹ := by
  rw [SL_slash_apply]
  simp only [omegaH, omega]
  rw [← tsum_mul_right]
  congr 1
  funext g
  exact term_slash g.1 γ τ w k

lemma mul_inv_SL (A : Matrix (Fin 2) (Fin 2) ℤ) (γ : SL(2, ℤ)) :
    A * (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = A := by
  rw [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]

lemma mul_mem_DeltaSet {M : ℕ} {n : ℤ} {δ' : ZMod M} {g : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : g ∈ DeltaSet M n δ') {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 M) :
    g * (γ : Matrix (Fin 2) (Fin 2) ℤ) ∈ DeltaSet M n δ' := by
  obtain ⟨hdet, hc, ha⟩ := mem_DeltaSet.1 hg
  obtain ⟨h00, h11, h10⟩ := (Gamma1_mem M γ).1 hγ
  refine mem_DeltaSet.2 ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_mul, hdet, Matrix.SpecialLinearGroup.det_coe, mul_one]
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]; push_cast; rw [hc, h10]; ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]; push_cast; rw [ha, h00, h10]; ring

/-- Right multiplication by `γ ∈ Γ₁(M)` permutes `Δ^{(δ')}_n(M)`. -/
def deltaEquiv {M : ℕ} {n : ℤ} {δ' : ZMod M} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 M) :
    DeltaSet M n δ' ≃ DeltaSet M n δ' where
  toFun g := ⟨g.1 * (γ : Matrix (Fin 2) (Fin 2) ℤ), mul_mem_DeltaSet g.2 hγ⟩
  invFun g := ⟨g.1 * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), mul_mem_DeltaSet g.2 (inv_mem hγ)⟩
  left_inv g := Subtype.ext (mul_inv_SL g.1 γ)
  right_inv g := Subtype.ext (by
    have := mul_inv_SL g.1 γ⁻¹
    rwa [inv_inv] at this)

theorem omegaH_slash_Gamma1 (M k : ℕ) (n : ℤ) (δ' : ZMod M) (w : ℂ) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 M) :
    omegaH M k n δ' w ∣[(k : ℤ)] γ = omegaH M k n δ' w := by
  funext τ
  rw [omegaH_slash]
  simp only [omegaH, omega]
  exact (deltaEquiv hγ).tsum_eq (fun g : DeltaSet M n δ' => (Q g.1 τ w ^ k)⁻¹)


/-! ### Decay at every cusp -/

/-- The majorant `F(z) = Σ_{det g = n} |Q(g; z, w)|^{-k}`. -/
def Fsum (n : ℤ) (k : ℕ) (z w : ℂ) : ℝ := ∑' g : DetSet n, ‖(Q g.1 z w ^ k)⁻¹‖

/-- The right multiplication `g ↦ g γ` from `Δ^{(δ')}_n(M)` into `{det = n}`. -/
def mulRightDet {M : ℕ} {n : ℤ} {δ' : ZMod M} (γ : SL(2, ℤ)) (g : DeltaSet M n δ') : DetSet n :=
  ⟨g.1 * (γ : Matrix (Fin 2) (Fin 2) ℤ), by
    rw [Matrix.det_mul, (mem_DeltaSet.1 g.2).1, Matrix.SpecialLinearGroup.det_coe, mul_one]⟩

lemma mulRightDet_val {M : ℕ} {n : ℤ} {δ' : ZMod M} (γ : SL(2, ℤ)) (g : DeltaSet M n δ') :
    (mulRightDet γ g).1 = g.1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) := rfl

lemma mulRightDet_injective {M : ℕ} {n : ℤ} {δ' : ZMod M} (γ : SL(2, ℤ)) :
    Function.Injective (mulRightDet (M := M) (n := n) (δ' := δ') γ) := by
  intro g g' h
  apply Subtype.ext
  have h1 : g.1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) = g'.1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← mulRightDet_val, ← mulRightDet_val, h]
  calc g.1 = g.1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) :=
        (mul_inv_SL g.1 γ).symm
    _ = g'.1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by rw [h1]
    _ = g'.1 := mul_inv_SL g'.1 γ

theorem norm_omegaH_slash_le (M k : ℕ) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (hk : 3 ≤ k) {w : ℂ}
    (hv : 0 < w.im) (γ : SL(2, ℤ)) (τ : ℍ) :
    ‖(omegaH M k n δ' w ∣[(k : ℤ)] γ) τ‖ ≤ Fsum n k τ w := by
  rw [omegaH_slash]
  have hsum : Summable fun g : DetSet n => ‖(Q g.1 τ w ^ k)⁻¹‖ :=
    summable_norm_det hn hk τ.im_pos hv
  have hinj := mulRightDet_injective (M := M) (n := n) (δ' := δ') γ
  have h1 := hsum.comp_injective hinj
  simp only [Function.comp_def, mulRightDet_val] at h1
  have h2 := tsum_comp_le_tsum_of_inj hsum (fun _ => norm_nonneg _) hinj
  simp only [Function.comp_def, mulRightDet_val] at h2
  refine (norm_tsum_le_tsum_norm h1).trans ?_
  unfold Fsum
  exact h2

/-- `T^m = [[1, m], [0, 1]]`. -/
def Tm (m : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, m; 0, 1]

lemma det_Tm (m : ℤ) : (Tm m).det = 1 := by simp [Tm, Matrix.det_fin_two_of]

lemma Tm_mul_Tm (a b : ℤ) : Tm a * Tm b = Tm (a + b) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Tm, Matrix.mul_apply, Fin.sum_univ_two]; ring

lemma Tm_zero : Tm 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Tm]

lemma Q_add_int (g : Matrix (Fin 2) (Fin 2) ℤ) (m : ℤ) (z w : ℂ) :
    Q g (z + (m : ℂ)) w = Q (g * Tm m) z w := by
  simp only [Q, Tm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

lemma mul_Tm_mem {n : ℤ} (g : DetSet n) (m : ℤ) : (g.1 * Tm m).det = n := by
  rw [Matrix.det_mul, det_Tm, mul_one]; exact g.2

/-- `g ↦ g T^m` permutes `{det = n}`. -/
def shiftEquiv (n m : ℤ) : DetSet n ≃ DetSet n where
  toFun g := ⟨g.1 * Tm m, mul_Tm_mem g m⟩
  invFun g := ⟨g.1 * Tm (-m), mul_Tm_mem g (-m)⟩
  left_inv g := Subtype.ext (by
    change g.1 * Tm m * Tm (-m) = g.1
    rw [Matrix.mul_assoc, Tm_mul_Tm, add_neg_cancel, Tm_zero, Matrix.mul_one])
  right_inv g := Subtype.ext (by
    change g.1 * Tm (-m) * Tm m = g.1
    rw [Matrix.mul_assoc, Tm_mul_Tm, neg_add_cancel, Tm_zero, Matrix.mul_one])

theorem Fsum_add_int (n : ℤ) (k : ℕ) (z w : ℂ) (m : ℤ) : Fsum n k (z + (m : ℂ)) w = Fsum n k z w := by
  calc Fsum n k (z + (m : ℂ)) w
      = ∑' g : DetSet n, (fun g : DetSet n => ‖(Q g.1 z w ^ k)⁻¹‖) (shiftEquiv n m g) := by
        unfold Fsum
        congr 1
        funext g
        change ‖(Q g.1 (z + (m : ℂ)) w ^ k)⁻¹‖ = ‖(Q (g.1 * Tm m) z w ^ k)⁻¹‖
        rw [Q_add_int]
    _ = Fsum n k z w := by
        unfold Fsum
        exact (shiftEquiv n m).tsum_eq (fun g : DetSet n => ‖(Q g.1 z w ^ k)⁻¹‖)

/-- The exponent `(2k - 1)/4` of the lattice part of the decay bound. -/
def sk (k : ℕ) : ℝ := (2 * (k : ℝ) - 1) / 4

lemma one_lt_sk {k : ℕ} (hk : 3 ≤ k) : 1 < sk k := by
  have : (3 : ℝ) ≤ k := by exact_mod_cast hk
  unfold sk; linarith

/-- `b₁(w) = v² / (3 (1 + |w|²))`. -/
def b1 (w : ℂ) : ℝ := w.im ^ 2 / (3 * (1 + ‖w‖ ^ 2))

lemma b1_pos {w : ℂ} (hv : 0 < w.im) : 0 < b1 w := by unfold b1; positivity

lemma b1_mul_N_le {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 ≤ g.det) {z w : ℂ} (hv : 0 < w.im)
    (hre0 : 0 ≤ z.re) (hre1 : z.re ≤ 1) (him : 1 ≤ z.im) :
    b1 w * N g ≤ ‖Q g z w‖ ^ 2 := by
  have hy : 0 < z.im := by linarith
  have h1 := N_le_normSq_Q g hdet z w hy.le hv.le
  rw [← Complex.sq_norm] at h1
  have hz2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hz3 : 1 + ‖z‖ ^ 2 ≤ 3 * z.im ^ 2 := by
    rw [hz2]; nlinarith
  have hW : 0 ≤ (1 + ‖w‖ ^ 2) * ‖Q g z w‖ ^ 2 := by positivity
  have h2 : (z.im * w.im) ^ 2 * N g ≤ 3 * z.im ^ 2 * ((1 + ‖w‖ ^ 2) * ‖Q g z w‖ ^ 2) := by
    calc (z.im * w.im) ^ 2 * N g ≤ (1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2) * ‖Q g z w‖ ^ 2 := h1
      _ = (1 + ‖z‖ ^ 2) * ((1 + ‖w‖ ^ 2) * ‖Q g z w‖ ^ 2) := by ring
      _ ≤ 3 * z.im ^ 2 * ((1 + ‖w‖ ^ 2) * ‖Q g z w‖ ^ 2) := mul_le_mul_of_nonneg_right hz3 hW
  have hy2 : 0 < z.im ^ 2 := by positivity
  have h3 : w.im ^ 2 * N g ≤ 3 * ((1 + ‖w‖ ^ 2) * ‖Q g z w‖ ^ 2) := by
    refine le_of_mul_le_mul_left ?_ hy2
    calc z.im ^ 2 * (w.im ^ 2 * N g) = (z.im * w.im) ^ 2 * N g := by ring
      _ ≤ 3 * z.im ^ 2 * ((1 + ‖w‖ ^ 2) * ‖Q g z w‖ ^ 2) := h2
      _ = z.im ^ 2 * (3 * ((1 + ‖w‖ ^ 2) * ‖Q g z w‖ ^ 2)) := by ring
  have h3w : 0 < 3 * (1 + ‖w‖ ^ 2) := by positivity
  rw [b1, div_mul_eq_mul_div, div_le_iff₀ h3w]
  linarith

lemma term_decay {n : ℤ} (hn : 0 < n) (g : DetSet n) {k : ℕ} (hk : 3 ≤ k) {z w : ℂ} (hv : 0 < w.im)
    (hre0 : 0 ≤ z.re) (hre1 : z.re ≤ 1) (him : 1 ≤ z.im) :
    ‖(Q g.1 z w ^ k)⁻¹‖ ≤ (2 * (n : ℝ) * w.im * z.im) ^ (-(1 / 4 : ℝ)) * (b1 w * N g.1) ^ (-sk k) := by
  have hy : 0 < z.im := by linarith
  have hdet : 0 < g.1.det := by rw [g.2]; exact hn
  have hN := N_pos hdet
  have hb := b1_pos hv
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : 2 * (n : ℝ) * w.im * z.im ≤ ‖Q g.1 z w‖ ^ 2 := by
    have := two_det_le_normSq_Q g.1 z w
    rw [← Complex.sq_norm, g.2] at this
    linarith
  have hp2 : 0 < 2 * (n : ℝ) * w.im * z.im := by positivity
  have hS : 0 < ‖Q g.1 z w‖ ^ 2 := lt_of_lt_of_le hp2 h2
  have hbN := b1_mul_N_le hdet.le hv hre0 hre1 him (g := g.1)
  have hpb : 0 < b1 w * N g.1 := mul_pos hb hN
  have hQ0 : 0 ≤ ‖Q g.1 z w‖ := norm_nonneg _
  have e1 : (‖Q g.1 z w‖ ^ k)⁻¹ = ‖Q g.1 z w‖ ^ (-(k : ℝ)) := by
    rw [Real.rpow_neg hQ0, Real.rpow_natCast]
  have e2 : (‖Q g.1 z w‖ ^ 2) ^ (-(k : ℝ) / 2) = ‖Q g.1 z w‖ ^ (-(k : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hQ0]; congr 1; ring
  have e3 : (‖Q g.1 z w‖ ^ 2) ^ (-(k : ℝ) / 2) =
      (‖Q g.1 z w‖ ^ 2) ^ (-(1 / 4 : ℝ)) * (‖Q g.1 z w‖ ^ 2) ^ (-sk k) := by
    rw [← Real.rpow_add hS]; congr 1; unfold sk; ring
  have hsk : -sk k ≤ 0 := by have := one_lt_sk hk; linarith
  rw [norm_inv, norm_pow, e1, ← e2, e3]
  exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hp2 h2 (by norm_num))
    (Real.rpow_le_rpow_of_nonpos hpb hbN hsk) (by positivity) (by positivity)

/-- The decay constant `C(n, k, w)`. -/
def Cdecay (n : ℤ) (k : ℕ) (w : ℂ) : ℝ :=
  (2 * (n : ℝ) * w.im) ^ (-(1 / 4 : ℝ)) * ∑' g : DetSet n, (b1 w * N g.1) ^ (-sk k)

lemma summable_b1N {n : ℤ} (hn : 0 < n) {k : ℕ} (hk : 3 ≤ k) {w : ℂ} (hv : 0 < w.im) :
    Summable fun g : DetSet n => (b1 w * N g.1) ^ (-sk k) := by
  refine ((summable_N_rpow hn (one_lt_sk hk)).mul_left (b1 w ^ (-sk k))).congr (fun g => ?_)
  have hdet : 0 < g.1.det := by rw [g.2]; exact hn
  rw [Real.mul_rpow (b1_pos hv).le (N_pos hdet).le]

theorem Fsum_le {n : ℤ} (hn : 0 < n) {k : ℕ} (hk : 3 ≤ k) {z w : ℂ} (hv : 0 < w.im)
    (hre0 : 0 ≤ z.re) (hre1 : z.re ≤ 1) (him : 1 ≤ z.im) :
    Fsum n k z w ≤ Cdecay n k w * z.im ^ (-(1 / 4 : ℝ)) := by
  have hy : 0 < z.im := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hmaj := (summable_b1N hn hk hv).mul_left ((2 * (n : ℝ) * w.im * z.im) ^ (-(1 / 4 : ℝ)))
  calc Fsum n k z w ≤ ∑' g : DetSet n,
        (2 * (n : ℝ) * w.im * z.im) ^ (-(1 / 4 : ℝ)) * (b1 w * N g.1) ^ (-sk k) :=
        (summable_norm_det hn hk hy hv).tsum_le_tsum
          (fun g => term_decay hn g hk hv hre0 hre1 him) hmaj
    _ = (2 * (n : ℝ) * w.im * z.im) ^ (-(1 / 4 : ℝ)) * ∑' g : DetSet n, (b1 w * N g.1) ^ (-sk k) :=
        tsum_mul_left
    _ = Cdecay n k w * z.im ^ (-(1 / 4 : ℝ)) := by
        unfold Cdecay
        rw [Real.mul_rpow (by positivity) hy.le]
        ring

theorem Fsum_le' {n : ℤ} (hn : 0 < n) {k : ℕ} (hk : 3 ≤ k) {z w : ℂ} (hv : 0 < w.im)
    (him : 1 ≤ z.im) : Fsum n k z w ≤ Cdecay n k w * z.im ^ (-(1 / 4 : ℝ)) := by
  have e := Fsum_add_int n k (z - ((⌊z.re⌋ : ℤ) : ℂ)) w ⌊z.re⌋
  rw [sub_add_cancel] at e
  have hre : (z - ((⌊z.re⌋ : ℤ) : ℂ)).re = Int.fract z.re := by
    rw [Complex.sub_re, Complex.intCast_re]; rfl
  have him' : (z - ((⌊z.re⌋ : ℤ) : ℂ)).im = z.im := by
    rw [Complex.sub_im, Complex.intCast_im, sub_zero]
  rw [e]
  have := Fsum_le hn hk hv (z := z - ((⌊z.re⌋ : ℤ) : ℂ)) (by rw [hre]; exact Int.fract_nonneg _)
    (by rw [hre]; exact (Int.fract_lt_one _).le) (by rw [him']; exact him)
  rwa [him'] at this

theorem isZeroAtImInfty_omegaH_slash (M k : ℕ) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (hk : 3 ≤ k) {w : ℂ}
    (hv : 0 < w.im) (γ : SL(2, ℤ)) : IsZeroAtImInfty (omegaH M k n δ' w ∣[(k : ℤ)] γ) := by
  unfold IsZeroAtImInfty ZeroAtFilter
  refine squeeze_zero_norm' (a := fun τ : ℍ => Cdecay n k w * (τ : ℂ).im ^ (-(1 / 4 : ℝ))) ?_ ?_
  · rw [Filter.Eventually, atImInfty_mem]
    exact ⟨1, fun τ hτ => (norm_omegaH_slash_le M k hn δ' hk hv γ τ).trans (Fsum_le' hn hk hv hτ)⟩
  · have h1 : Tendsto (fun τ : ℍ => (τ : ℂ).im) atImInfty atTop := tendsto_comap
    have h2 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp h1).const_mul
      (Cdecay n k w)
    rw [mul_zero] at h2
    exact h2

/-! ### `ω(·, w)` as a cusp form on `Γ₁(M)` -/

theorem mdifferentiable_omegaH (M k : ℕ) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (hk : 3 ≤ k) {w : ℂ}
    (hv : 0 < w.im) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (omegaH M k n δ' w) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine (differentiableOn_omega M k hn δ' hk hv).congr (fun z hz => ?_)
  rw [Function.comp_apply, ofComplex_apply_of_im_pos hz]
  rfl

/-- `ω(·, w) ∈ S_k(Γ₁(M))` for `Im w > 0`, `n > 0`, `k ≥ 3`. -/
def omegaCF (M k : ℕ) [NeZero M] {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (hk : 3 ≤ k) (w : ℂ)
    (hv : 0 < w.im) : CuspForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) where
  toFun := omegaH M k n δ' w
  slash_action_eq' γ hγ := by
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    have := omegaH_slash_Gamma1 M k n δ' w hγ₀
    rw [SL_slash] at this
    exact this
  holo' := mdifferentiable_omegaH M k hn δ' hk hv
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    exact isZeroAtImInfty_omegaH_slash M k hn δ' hk hv γ

@[simp] lemma coe_omegaCF (M k : ℕ) [NeZero M] {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (hk : 3 ≤ k) (w : ℂ)
    (hv : 0 < w.im) : ⇑(omegaCF M k hn δ' hk w hv) = omegaH M k n δ' w := rfl

end RamanujanPetersson.Kernel


