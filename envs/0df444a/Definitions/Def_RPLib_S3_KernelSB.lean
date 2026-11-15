-- Prove2me | Definitions.Def_RPLib_S3_KernelSB
-- name    : RPLib_S3_KernelSB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:28:59.922203+00:00
-- url     : https://prove2.me/theorems/dec8a1d9-4453-4df3-9695-2a94afbce151
-- title:
--   The Eichler-Selberg trace formula in weight two: summability, automorphy and the reproducing identity of `ω_s`
-- statement:
--   Summability, automorphy and the reproducing identity of `ω_s`.
--
--   * `norm_termS_le`, `summable_omegaS` (`k/2 + s > 1`): absolute convergence of `ω_s`.
--   * `ratQ_smul`, `omegaSH_slash_Gamma1`: `ω_s(·, w)` is `Γ₁(M)`-invariant of weight `k`.
--   * `petersson_omegaS_eq_tsum`, `reproducing_abstractS`: unfolding and the Bergman step summed over representatives.
--   * **`reproducingS`** (`M ≥ 3`, `k ≥ 2`, `k/2 + s > 1`, `gcd(n, M) = 1`):
--     `(T_n ⟨δ⟩ f)(w) = n^(k-1) C_k(s)⁻¹ ⟪ω_s(·, -conj w), f⟫` with `ω_s` at `δ'' = unitOf M n * δ`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_KernelSA
import Definitions.Def_RPLib_S3_KernelC

/-!
# S3-ES-Wt2 (O2, part B): summability, automorphy and the reproducing identity of `ω_s`

* `norm_termS_le`, `summable_omegaS` (`k/2 + s > 1`): absolute convergence of `ω_s`.
* `ratQ_smul`, `omegaSH_slash_Gamma1`: `ω_s(·, w)` is `Γ₁(M)`-invariant of weight `k`.
* `petersson_omegaS_eq_tsum`, `reproducing_abstractS`: unfolding and the Bergman step summed over representatives.
* **`reproducingS`** (`M ≥ 3`, `k ≥ 2`, `k/2 + s > 1`, `gcd(n, M) = 1`):
  `(T_n ⟨δ⟩ f)(w) = n^(k-1) C_k(s)⁻¹ ⟪ω_s(·, -conj w), f⟫` with `ω_s` at `δ'' = unitOf M n * δ`.
-/

open Filter Complex UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups Topology Manifold ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KernelS

open RP.FundDomain RP.Petersson RamanujanPetersson.Diamond RamanujanPetersson.Hecke
  RamanujanPetersson.Kernel RamanujanPetersson.Bergman RamanujanPetersson.BergmanS
open RamanujanPetersson.HeckeAlgebra (heckeTn)

attribute [local instance] measurableConstSMul_pgl smulInvariantMeasure_pgl
  smulInvariantMeasure_subgroup

/-! ### (1) Absolute convergence -/

lemma ratQ_nonneg {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 ≤ g.det) {z w : ℂ} (hy : 0 ≤ z.im)
    (hv : 0 ≤ w.im) : 0 ≤ ratQ g z w := by
  have : (0 : ℝ) ≤ g.det := by exact_mod_cast hdet
  unfold ratQ; positivity

lemma norm_termS_le {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) (k : ℕ) {s : ℝ} (hσ : 0 ≤ (k : ℝ) / 2 + s) :
    ‖(Q g z w ^ k)⁻¹ * ((ratQ g z w ^ s : ℝ) : ℂ)‖ ≤
      ((g.det : ℝ) * z.im * w.im) ^ s * (B z w * N g) ^ (-((k : ℝ) / 2 + s)) := by
  have hQ := Q_ne_zero hdet hy hv
  have hq : 0 < ‖Q g z w‖ ^ 2 := by have := norm_pos_iff.mpr hQ; positivity
  have hX : 0 < (g.det : ℝ) * z.im * w.im := by
    have : (0 : ℝ) < g.det := by exact_mod_cast hdet
    positivity
  have hN := N_pos hdet
  have hB := B_pos hy hv
  have hBN : B z w * N g ≤ ‖Q g z w‖ ^ 2 := by
    rw [Complex.sq_norm, B, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have := N_le_normSq_Q g hdet.le z w hy.le hv.le
    linarith
  have hr : ratQ g z w = ((g.det : ℝ) * z.im * w.im) / ‖Q g z w‖ ^ 2 := rfl
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (ratQ_nonneg hdet.le hy.le hv.le) _), hr,
    Real.div_rpow hX.le hq.le, norm_inv, norm_pow]
  have hk2 : (‖Q g z w‖ ^ 2) ^ ((k : ℝ) / 2) = ‖Q g z w‖ ^ k := by
    rw [← Real.rpow_natCast (‖Q g z w‖) 2, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have hsplit : (‖Q g z w‖ ^ 2) ^ (-((k : ℝ) / 2 + s)) = ((‖Q g z w‖ ^ k) * (‖Q g z w‖ ^ 2) ^ s)⁻¹ := by
    rw [Real.rpow_neg hq.le, Real.rpow_add hq, hk2]
  calc (‖Q g z w‖ ^ k)⁻¹ * (((g.det : ℝ) * z.im * w.im) ^ s / (‖Q g z w‖ ^ 2) ^ s)
      = ((g.det : ℝ) * z.im * w.im) ^ s * (‖Q g z w‖ ^ 2) ^ (-((k : ℝ) / 2 + s)) := by
        rw [hsplit, mul_inv]; ring
    _ ≤ ((g.det : ℝ) * z.im * w.im) ^ s * (B z w * N g) ^ (-((k : ℝ) / 2 + s)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (mul_pos hB hN) hBN (by linarith))
          (Real.rpow_nonneg hX.le _)

theorem summable_norm_omegaS (M k : ℕ) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ}
    (hσ : 1 < (k : ℝ) / 2 + s) {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) :
    Summable fun g : DeltaSet M n δ' => ‖(Q g.1 z w ^ k)⁻¹ * ((ratQ g.1 z w ^ s : ℝ) : ℂ)‖ := by
  refine ((summable_N_rpow_delta M hn δ' hσ).mul_left
    (((n : ℝ) * z.im * w.im) ^ s * B z w ^ (-((k : ℝ) / 2 + s)))).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun g => ?_)
  have hd := (mem_DeltaSet.1 g.2).1
  have hpos : 0 < g.1.det := by rw [hd]; exact hn
  have := norm_termS_le hpos hy hv k (s := s) (by linarith)
  rw [hd, Real.mul_rpow (B_pos hy hv).le (N_pos hpos).le] at this
  exact this.trans_eq (by ring)

theorem summable_omegaS (M k : ℕ) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ}
    (hσ : 1 < (k : ℝ) / 2 + s) {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) :
    Summable fun g : DeltaSet M n δ' => (Q g.1 z w ^ k)⁻¹ * ((ratQ g.1 z w ^ s : ℝ) : ℂ) :=
  Summable.of_norm (summable_norm_omegaS M k hn δ' hσ hy hv)

/-! ### (2) Automorphy in `z` -/

/-- `ratQ g (γ τ) w = ratQ (g γ) τ w` for `γ ∈ SL₂(ℤ)`. -/
lemma ratQ_smul (g : Matrix (Fin 2) (Fin 2) ℤ) (γ : SL(2, ℤ)) (τ : ℍ) (w : ℂ) :
    ratQ g ((γ • τ : ℍ) : ℂ) w = ratQ (g * (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ w := by
  have hQ := Q_smul g γ τ w
  have hdet : (g * (γ : Matrix (Fin 2) (Fin 2) ℤ)).det = g.det := by
    rw [Matrix.det_mul]; simp
  have him : ((γ • τ : ℍ) : ℂ).im = (τ : ℂ).im / Complex.normSq (denom γ τ) :=
    ModularGroup.im_smul_eq_div_normSq γ τ
  unfold ratQ
  rw [hdet, ← hQ, norm_mul, mul_pow, him, Complex.normSq_eq_norm_sq]
  ring

/-- `ω_s(·, w)` as a function on `ℍ`. -/
def omegaSH (M k : ℕ) (n : ℤ) (δ' : ZMod M) (s : ℝ) (w : ℂ) : ℍ → ℂ := fun τ => omegaS M k n δ' s τ w

lemma termS_slash (g : Matrix (Fin 2) (Fin 2) ℤ) (γ : SL(2, ℤ)) (τ : ℍ) (w : ℂ) (k : ℕ) (s : ℝ) :
    (Q g ((γ • τ : ℍ) : ℂ) w ^ k)⁻¹ * ((ratQ g ((γ • τ : ℍ) : ℂ) w ^ s : ℝ) : ℂ) * denom γ τ ^ (-(k : ℤ)) =
      (Q (g * (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ w ^ k)⁻¹ *
        ((ratQ (g * (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ w ^ s : ℝ) : ℂ) := by
  rw [← term_slash g γ τ w k, ratQ_smul]
  ring

theorem omegaSH_slash_Gamma1 (M k : ℕ) (n : ℤ) (δ' : ZMod M) (s : ℝ) (w : ℂ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma1 M) :
    omegaSH M k n δ' s w ∣[(k : ℤ)] γ = omegaSH M k n δ' s w := by
  funext τ
  rw [SL_slash_apply]
  simp only [omegaSH, omegaS]
  rw [← tsum_mul_right]
  simp_rw [termS_slash _ γ τ w k s]
  exact (deltaEquiv hγ).tsum_eq (fun g : DeltaSet M n δ' =>
    (Q g.1 τ w ^ k)⁻¹ * ((ratQ g.1 τ w ^ s : ℝ) : ℂ))

/-! ### (3) Unfolding and the reproducing identity -/

lemma term_unfoldS {M k : ℕ} (f : S1 M k) (s : ℝ) (g : Matrix (Fin 2) (Fin 2) ℤ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma1 M) (z : ℍ) (w : ℂ) :
    conj ((Q (g * (γ : Matrix (Fin 2) (Fin 2) ℤ)) z w ^ k)⁻¹) *
        ((ratQ (g * (γ : Matrix (Fin 2) (Fin 2) ℤ)) z w ^ s : ℝ) : ℂ) * f z * ((z.im : ℂ) ^ k) =
      conj ((Q g ((γ • z : ℍ) : ℂ) w ^ k)⁻¹) * ((ratQ g ((γ • z : ℍ) : ℂ) w ^ s : ℝ) : ℂ) *
        f (γ • z) * (((γ • z).im : ℂ) ^ k) := by
  have e := term_unfold f g hγ z w
  rw [ratQ_smul]
  linear_combination ((ratQ (g * (γ : Matrix (Fin 2) (Fin 2) ℤ)) z w ^ s : ℝ) : ℂ) * e

/-- Pointwise unfolding of the Petersson integrand. -/
theorem petersson_omegaS_eq_tsum {M k : ℕ} [NeZero M] {n : ℤ} (hn : 0 < n) {δ' : ZMod M} {s : ℝ}
    (hσ : 1 < (k : ℝ) / 2 + s) {I : Type*} [Fintype I] (α : I → Matrix (Fin 2) (Fin 2) ℤ)
    (hα : ∀ i, α i ∈ DeltaSet M n δ') (hbij : Function.Bijective (repMap α hα)) (f : S1 M k) (w z : ℍ) :
    petersson (k : ℤ) (omegaSH M k n δ' s (-conj (w : ℂ))) f z =
      ∑' γ : Gamma1 M, ∑ i, PhiAS k s (α i) f w ((γ : SL(2, ℤ)) • z) := by
  have hv : 0 < (-conj (w : ℂ)).im := by simpa using w.im_pos
  have hs : Summable fun g : DeltaSet M n δ' =>
      conj ((Q g.1 z (-conj (w : ℂ)) ^ k)⁻¹ * ((ratQ g.1 z (-conj (w : ℂ)) ^ s : ℝ) : ℂ)) *
        (f z * ((z.im : ℂ) ^ k)) :=
    (Complex.summable_conj.2 (summable_omegaS M k hn δ' hσ (z := (z : ℂ)) (w := -conj (w : ℂ))
      z.im_pos hv)).mul_right _
  have hs' : Summable fun p : Gamma1 M × I =>
      conj ((Q (Equiv.ofBijective (repMap α hα) hbij p).1 z (-conj (w : ℂ)) ^ k)⁻¹ *
        ((ratQ (Equiv.ofBijective (repMap α hα) hbij p).1 z (-conj (w : ℂ)) ^ s : ℝ) : ℂ)) *
        (f z * ((z.im : ℂ) ^ k)) :=
    ((Equiv.ofBijective (repMap α hα) hbij).summable_iff (f := fun g : DeltaSet M n δ' =>
      conj ((Q g.1 z (-conj (w : ℂ)) ^ k)⁻¹ * ((ratQ g.1 z (-conj (w : ℂ)) ^ s : ℝ) : ℂ)) *
        (f z * ((z.im : ℂ) ^ k)))).2 hs
  rw [petersson_nat, mul_assoc]
  simp only [omegaSH, omegaS]
  rw [Complex.conj_tsum, ← tsum_mul_right,
    ← (Equiv.ofBijective (repMap α hα) hbij).tsum_eq (fun g : DeltaSet M n δ' =>
      conj ((Q g.1 z (-conj (w : ℂ)) ^ k)⁻¹ * ((ratQ g.1 z (-conj (w : ℂ)) ^ s : ℝ) : ℂ)) *
        (f z * ((z.im : ℂ) ^ k))), hs'.tsum_prod]
  refine tsum_congr fun γ => ?_
  rw [tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := term_unfoldS (k := k) f s (α i) γ.2 z (-conj (w : ℂ))
  simp only [Equiv.ofBijective_apply, repMap, map_mul, Complex.conj_ofReal]
  rw [PhiAS]
  linear_combination e

/-- **Reproducing identity with abstract representatives** (Hecke-trick version). -/
theorem reproducing_abstractS {M k : ℕ} [NeZero M] (hM : 3 ≤ M) {n : ℤ} (hn : 0 < n) {δ' : ZMod M}
    (hk : 2 ≤ k) {s : ℝ} (hσ : 1 < (k : ℝ) / 2 + s) {I : Type*} [Fintype I]
    (α : I → Matrix (Fin 2) (Fin 2) ℤ) (hα : ∀ i, α i ∈ DeltaSet M n δ')
    (hbij : Function.Bijective (repMap α hα)) (f : S1 M k) (w : ℍ) :
    peterssonInner (Gamma1 M) k (omegaSH M k n δ' s (-conj (w : ℂ))) f =
      bergmanConstS k s * ∑ i, ((((α i 0 0 : ℂ) - (α i 1 0 : ℂ) * w) ^ k)⁻¹) * f (adjPt (α i) w) := by
  have hpos : ∀ i, 0 < (α i).det := fun i => by rw [(mem_DeltaSet.1 (hα i)).1]; exact hn
  have hint : Integrable (fun z => ∑ i, PhiAS k s (α i) f w z) :=
    integrable_finsetSum _ fun i _ => (integral_termS hk hσ f (hpos i) w).1
  rw [peterssonInner]
  simp_rw [petersson_omegaS_eq_tsum hn hσ α hα hbij f w]
  rw [integral_fdom_tsum hM hint,
    integral_finsetSum _ fun i _ => (integral_termS hk hσ f (hpos i) w).1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(integral_termS hk hσ f (hpos i) w).2]
  ring

/-- **The `s`-reproducing identity for `T_n ⟨δ⟩`** (`M ≥ 3`, `k ≥ 2`, `k/2 + s > 1`, `gcd(n, M) = 1`). -/
theorem reproducingS {M k : ℕ} [NeZero M] (hM : 3 ≤ M) (hk : 2 ≤ k) {s : ℝ} (hσ : 1 < (k : ℝ) / 2 + s)
    {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ) (f : S1 M k) (z : ℍ) :
    ((heckeTn (k : ℤ) n * diamond (k : ℤ) δ : Module.End ℂ (S1 M k)) f) z =
      (n : ℂ) ^ (k - 1) * (bergmanConstS k s)⁻¹ *
        peterssonInner (Gamma1 M) k
          (omegaSH M k n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s (-conj (z : ℂ))) f := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hs : 0 < (k : ℝ) - 1 + s := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hB := bergmanConstS_ne_zero hs
  rw [reproducing_abstractS hM hn' hk hσ (alphaHNF n (unitOf M n * δ)) (alphaHNF_mem hnM _)
      (repMap_HNF_bijective hn hnM _) f z, Module.End.mul_apply, ← cosetSum_eq (by omega) hn hnM δ f z,
      mul_assoc, inv_mul_cancel_left₀ hB]
  rfl

end RamanujanPetersson.KernelS


