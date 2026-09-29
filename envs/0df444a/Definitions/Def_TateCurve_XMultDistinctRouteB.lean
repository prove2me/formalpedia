-- Prove2me | Definitions.Def_TateCurve_XMultDistinctRouteB
-- name    : TateCurve_XMultDistinctRouteB
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/6b85dce0-e5bf-5222-b407-a1a88a87cb92
-- title:
--   Bézout cofactors, paired x-coefficients, and DiamondAux auxiliaries
-- statement:
--   Three families of objects are introduced, together with the identities they serve. First, for a Weierstrass curve $W$ over a field $F$, [`WeierstrassCurve.bezF`](../def/TateCurve_XMultDistinctRouteB.html#L16) and [`WeierstrassCurve.bezG`](../def/TateCurve_XMultDistinctRouteB.html#L27) are explicit polynomial expressions in $x$ — of degree two and three respectively — whose coefficients are the displayed integer polynomials in $b_2,b_4,b_6,b_8$ of $W$. They are the cofactors of a Bézout relation: `bezout_Φ_two_Ψ₂Sq` states $F(x)\,\Phi_2(x)+G(x)\,\Psi_2^2(x)=\Delta^2$ for all $x\in F$, whence a common root of $\Phi_2$ and $\Psi_2^2$ forces $\Delta^2=0$, and for an elliptic $W$ the polynomial $\Phi_2$ has no root in common with $\Psi_2^2$.
--
--   Second, over a complete nontrivially normed ultrametric field $K$ of characteristic zero with parameters $q,u,v$, [`TateCurve.xPairNum u v d`](../def/TateCurve_XMultDistinctRouteB.html#L119) is $d\,\bigl(\sum_{k<d}u^k v^{d-1-k}\bigr)\bigl(\sum_{j<d}(uv)^j\bigr)$ and [`TateCurve.xPairCoeff u v M`](../def/TateCurve_XMultDistinctRouteB.html#L123) is $\bigl(\sum_{d\mid M}\mathrm{xPairNum}(u,v,d)\,(uv)^{M-d}\bigr)/(uv)^M$. These are divided differences of the $q$-expansion coefficients: $\mathrm{xCoeff}(u,M)-\mathrm{xCoeff}(v,M)=-\bigl((u-v)(1-uv)\bigr)\mathrm{xPairCoeff}(u,v,M)$, which factors $\mathrm{pointX}(q,u)-\mathrm{pointX}(q,v)$ as $(u-v)(1-uv)$ times a unit-valued factor, and yields the $X$-fibre separation, torsion-order and parameter-class statements proved here.
--
--   Third, [`TateCurve.DiamondAux q u w`](../def/TateCurve_XMultDistinctRouteB.html#L798) is a proposition-valued structure whose fields record $w\neq 0$, $\lVert w\rVert=1$, and that each of $w$, $w^2$, $uw$, $uw^{-1}$ satisfies `OffLattice q`, i.e. is not of the form $q^{-n}$ for any $n\in\mathbb{Z}$. Such auxiliary parameters, constructed as $1+q^n$ for suitable $n$, drive the derivation of the duplication field of `SymAddHyps` from the symmetric sum and product identities.
--
--   **Relation to Mathlib.** The Weierstrass data $b_2,b_4,b_6,b_8$, $\Delta$, the division polynomials $\Psi_2^2$ and $\Phi_2$, and affine points are Mathlib's; `bezF`, `bezG`, `xPairNum`, `xPairCoeff` and `DiamondAux` are the project's own, as are the Tate curve `curve q` and its parametrisation `pointX`, `pointY`, for which Mathlib has no counterpart.
--
--   **Where it is used.** The $X$-fibre separation and the absence of intermediate torsion established from these objects give the explicit description of the $p$-torsion of a Tate curve in terms of the parameters $\zeta^i q^{j/p}$, which is what the analysis of the mod-$p$ representation of the Frey curve at primes of multiplicative reduction requires.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_TateCurve_XMultDistinctRouteB.lean

import Mathlib
import Definitions.Def_TateCurve_XMultAlignment
import Theorems.Thm_TateCurve_pointY_inv
import Theorems.Thm_TateCurve_pointY_zpow_mul
import Theorems.Thm_TateCurve_pointX_qExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WeierstrassCurve

section Bezout

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

def bezF (x : F) : F :=
  (8 * W.b₂ ^ 3 * W.b₆ - 8 * W.b₂ ^ 2 * W.b₄ ^ 2 + 16 * W.b₂ ^ 2 * W.b₈ -
      336 * W.b₂ * W.b₄ * W.b₆ + 288 * W.b₄ ^ 3 - 384 * W.b₄ * W.b₈ + 1296 * W.b₆ ^ 2) * x ^ 2 +
    (2 * W.b₂ ^ 4 * W.b₆ - 2 * W.b₂ ^ 3 * W.b₄ ^ 2 - 80 * W.b₂ ^ 2 * W.b₄ * W.b₆ +
      72 * W.b₂ * W.b₄ ^ 3 + 32 * W.b₂ * W.b₄ * W.b₈ + 360 * W.b₂ * W.b₆ ^ 2 -
      144 * W.b₄ ^ 2 * W.b₆ - 576 * W.b₆ * W.b₈) * x +
    (-W.b₂ ^ 4 * W.b₈ + 5 * W.b₂ ^ 3 * W.b₄ * W.b₆ - 4 * W.b₂ ^ 2 * W.b₄ ^ 3 +
      48 * W.b₂ ^ 2 * W.b₄ * W.b₈ + W.b₂ ^ 2 * W.b₆ ^ 2 - 204 * W.b₂ * W.b₄ ^ 2 * W.b₆ -
      176 * W.b₂ * W.b₆ * W.b₈ + 144 * W.b₄ ^ 4 - 384 * W.b₄ ^ 2 * W.b₈ +
      864 * W.b₄ * W.b₆ ^ 2 + 256 * W.b₈ ^ 2)

def bezG (x : F) : F :=
  (-2 * W.b₂ ^ 3 * W.b₆ + 2 * W.b₂ ^ 2 * W.b₄ ^ 2 - 4 * W.b₂ ^ 2 * W.b₈ +
      84 * W.b₂ * W.b₄ * W.b₆ - 72 * W.b₄ ^ 3 + 96 * W.b₄ * W.b₈ - 324 * W.b₆ ^ 2) * x ^ 3 +
    (W.b₂ ^ 3 * W.b₈ - W.b₂ ^ 2 * W.b₄ * W.b₆ - 32 * W.b₂ * W.b₄ * W.b₈ - 9 * W.b₂ * W.b₆ ^ 2 +
      36 * W.b₄ ^ 2 * W.b₆ + 144 * W.b₆ * W.b₈) * x ^ 2 +
    (2 * W.b₂ ^ 3 * W.b₄ * W.b₆ - 2 * W.b₂ ^ 2 * W.b₄ ^ 3 + 2 * W.b₂ ^ 2 * W.b₄ * W.b₈ +
      2 * W.b₂ ^ 2 * W.b₆ ^ 2 - 84 * W.b₂ * W.b₄ ^ 2 * W.b₆ + 8 * W.b₂ * W.b₆ * W.b₈ +
      72 * W.b₄ ^ 4 - 48 * W.b₄ ^ 2 * W.b₈ + 270 * W.b₄ * W.b₆ ^ 2 - 64 * W.b₈ ^ 2) * x +
    (-W.b₂ ^ 3 * W.b₄ * W.b₈ + 4 * W.b₂ ^ 3 * W.b₆ ^ 2 - 3 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ +
      7 * W.b₂ ^ 2 * W.b₆ * W.b₈ + 36 * W.b₂ * W.b₄ ^ 2 * W.b₈ - 162 * W.b₂ * W.b₄ * W.b₆ ^ 2 +
      16 * W.b₂ * W.b₈ ^ 2 + 108 * W.b₄ ^ 3 * W.b₆ - 432 * W.b₄ * W.b₆ * W.b₈ +
      729 * W.b₆ ^ 3)

theorem bezout_Φ_two_Ψ₂Sq (x : F) :
    W.bezF x * (W.Φ 2).eval x + W.bezG x * W.Ψ₂Sq.eval x = W.Δ ^ 2 := by
  rw [bezF, bezG, Affine.eval_Φ_two (W := W), Affine.eval_Ψ₂Sq (W := W)]
  simp only [Δ]
  linear_combination (-12 * W.b₂ ^ 2 * W.b₄ * W.b₈ - 4 * W.b₂ ^ 2 * W.b₆ ^ 2 +
    80 * W.b₂ * W.b₄ ^ 2 * W.b₆ + 32 * W.b₂ * W.b₆ * W.b₈ - 64 * W.b₄ ^ 4 +
    112 * W.b₄ ^ 2 * W.b₈ - 324 * W.b₄ * W.b₆ ^ 2 - 64 * W.b₈ ^ 2) * W.b_relation

theorem Δ_sq_eq_zero_of_eval_eq_zero {x : F} (hΦ : (W.Φ 2).eval x = 0)
    (hΨ : W.Ψ₂Sq.eval x = 0) : W.Δ ^ 2 = 0 := by
  rw [← W.bezout_Φ_two_Ψ₂Sq x, hΦ, hΨ, mul_zero, mul_zero, add_zero]

theorem not_eval_Φ_two_eq_zero [W.IsElliptic] {x : F} (hΨ : W.Ψ₂Sq.eval x = 0) :
    (W.Φ 2).eval x ≠ 0 := fun hΦ =>
  pow_ne_zero 2 W.isUnit_Δ.ne_zero <| W.Δ_sq_eq_zero_of_eval_eq_zero hΦ hΨ

end Bezout

end WeierstrassCurve

namespace TateCurve

section AnnulusTranslateExtra
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K}

theorem exists_zpow_mul_norm_Ioc (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hu0 : u ≠ 0) :
    ∃ n : ℤ, ‖q‖ < ‖q ^ n * u‖ ∧ ‖q ^ n * u‖ ≤ 1 := by
  have hq_pos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hu_pos : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
  have hq_ne : (‖q‖ : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hy : (1 : ℝ) < ‖q‖⁻¹ := one_lt_inv_iff₀.mpr ⟨hq_pos, hq⟩
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hu_pos hy
  have hqk_pos : (0 : ℝ) < ‖q‖ ^ (n + 1 : ℤ) := zpow_pos hq_pos _

  have hcancel : ∀ m : ℤ, ‖q‖⁻¹ ^ m * ‖q‖ ^ m = 1 := fun m => by
    rw [← mul_zpow, inv_mul_cancel₀ hq_ne, one_zpow]
  refine ⟨n + 1, ?_, ?_⟩
  ·
    have hkey : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n = ‖q‖ := by
      rw [zpow_add₀ hq_ne, zpow_one]
      calc ‖q‖ ^ n * ‖q‖ * ‖q‖⁻¹ ^ n
          = ‖q‖⁻¹ ^ n * (‖q‖ ^ n * ‖q‖) := mul_comm _ _
        _ = ‖q‖⁻¹ ^ n * ‖q‖ ^ n * ‖q‖ := (mul_assoc _ _ _).symm
        _ = 1 * ‖q‖ := by rw [hcancel n]
        _ = ‖q‖ := one_mul _
    have hlt : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n < ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ :=
      mul_lt_mul_of_pos_left hn1 hqk_pos
    rw [norm_mul, norm_zpow]
    calc ‖q‖ = ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n := hkey.symm
      _ < ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ := hlt
  ·
    have hkey : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) = 1 := by
      calc ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1)
          = ‖q‖⁻¹ ^ (n + 1) * ‖q‖ ^ (n + 1) := mul_comm _ _
        _ = 1 := hcancel (n + 1)
    have hle : ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ ≤ ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) :=
      mul_le_mul_of_nonneg_left hn2 hqk_pos.le
    rw [norm_mul, norm_zpow]
    calc ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ ≤ ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) := hle
      _ = 1 := hkey

end AnnulusTranslateExtra

end TateCurve

set_option linter.unusedSectionVars false

open WeierstrassCurve.Affine
open Polynomial
open IsUltrametricDist

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u v : K}

section Factorization

noncomputable def xPairNum (u v : K) (d : ℕ) : K :=
  (d : K) * (∑ k ∈ Finset.range d, u ^ k * v ^ (d - 1 - k)) *
    (∑ j ∈ Finset.range d, (u * v) ^ j)

noncomputable def xPairCoeff (u v : K) (M : ℕ) : K :=
  (∑ d ∈ M.divisors, xPairNum u v d * (u * v) ^ (M - d)) / (u * v) ^ M

lemma xfun_sub_xfun (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    xfun u - xfun v = (u - v) * (1 - u * v) * ((1 - u) ^ 2 * (1 - v) ^ 2)⁻¹ := by
  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have h1v : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
  rw [xfun, xfun]
  field_simp
  ring

lemma xDivTerm_sub_mul (hu0 : u ≠ 0) (hv0 : v ≠ 0) (d : ℕ) :
    (xDivTerm u d - xDivTerm v d) * (u * v) ^ d =
      -((u - v) * (1 - u * v)) * xPairNum u v d := by
  have hu' : u⁻¹ ^ d * (u * v) ^ d = v ^ d := by
    rw [← mul_pow, ← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
  have hv' : v⁻¹ ^ d * (u * v) ^ d = u ^ d := by
    rw [← mul_pow, mul_comm u v, ← mul_assoc, inv_mul_cancel₀ hv0, one_mul]
  have hS : (∑ k ∈ Finset.range d, u ^ k * v ^ (d - 1 - k)) * (u - v) = u ^ d - v ^ d :=
    geom_sum₂_mul u v d
  have hT : (∑ j ∈ Finset.range d, (u * v) ^ j) * (u * v - 1) = (u * v) ^ d - 1 :=
    geom_sum_mul (u * v) d
  have step1 : (xDivTerm u d - xDivTerm v d) * (u * v) ^ d =
      (d : K) * ((u ^ d - v ^ d) * ((u * v) ^ d - 1)) := by
    rw [xDivTerm, xDivTerm]
    linear_combination ((d : K)) * hu' - (d : K) * hv'
  rw [step1, xPairNum, ← hS, ← hT]
  ring

lemma xCoeff_sub_xCoeff (hu0 : u ≠ 0) (hv0 : v ≠ 0) {M : ℕ} (hM : M ≠ 0) :
    xCoeff u M - xCoeff v M = -((u - v) * (1 - u * v)) * xPairCoeff u v M := by
  have hB : ((u * v) ^ M : K) ≠ 0 := pow_ne_zero M (mul_ne_zero hu0 hv0)
  rw [xPairCoeff, ← mul_div_assoc, eq_div_iff hB, xCoeff, xCoeff, ← Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdM : d ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (Nat.mem_divisors.mp hd).1
  have hsplit : (u * v) ^ M = (u * v) ^ d * (u * v) ^ (M - d) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, ← mul_assoc, xDivTerm_sub_mul hu0 hv0 d, mul_assoc]

lemma norm_xPairNum_le (hu1 : ‖u‖ ≤ 1) (hv1 : ‖v‖ ≤ 1) (d : ℕ) : ‖xPairNum u v d‖ ≤ 1 := by
  have huv1 : ‖u * v‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ hu1 (norm_nonneg v) hv1
  have hS : ‖∑ k ∈ Finset.range d, u ^ k * v ^ (d - 1 - k)‖ ≤ 1 := by
    refine norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_mul, norm_pow, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg u) hu1) (pow_nonneg (norm_nonneg v) _)
      (pow_le_one₀ (norm_nonneg v) hv1)
  have hT : ‖∑ j ∈ Finset.range d, (u * v) ^ j‖ ≤ 1 := by
    refine norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) huv1
  calc ‖xPairNum u v d‖ = ‖(d : K)‖ * ‖∑ k ∈ Finset.range d, u ^ k * v ^ (d - 1 - k)‖ *
        ‖∑ j ∈ Finset.range d, (u * v) ^ j‖ := by
        rw [xPairNum, norm_mul, norm_mul]
    _ ≤ 1 * 1 * 1 :=
        mul_le_mul (mul_le_mul (norm_natCast_le_one K d) hS (norm_nonneg _) zero_le_one) hT
          (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

lemma norm_xPairCoeff_le (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : ‖u‖ ≤ 1) (hv1 : ‖v‖ ≤ 1) (M : ℕ) :
    ‖xPairCoeff u v M‖ ≤ (‖u * v‖⁻¹) ^ M := by
  have huv0 : ‖u * v‖ ≠ 0 := norm_ne_zero_iff.mpr (mul_ne_zero hu0 hv0)
  have huv1 : ‖u * v‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ hu1 (norm_nonneg v) hv1
  have hpos : (0 : ℝ) < ‖u * v‖ ^ M := pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm huv0)) M
  have hA : ‖∑ d ∈ M.divisors, xPairNum u v d * (u * v) ^ (M - d)‖ ≤ 1 := by
    refine norm_sum_le_of_forall_le_of_nonneg zero_le_one fun d _ => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (norm_xPairNum_le hu1 hv1 d) (pow_nonneg (norm_nonneg _) _)
      (pow_le_one₀ (norm_nonneg _) huv1)
  rw [xPairCoeff, norm_div, norm_pow, div_le_iff₀ hpos, inv_pow,
    inv_mul_cancel₀ (ne_of_gt hpos)]
  exact hA

lemma summable_xCoeff_mul_pow (hq : ‖q‖₊ < 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    Summable (fun N : ℕ => xCoeff u (N + 1) * q ^ (N + 1)) := by
  have hC1 : (1 : ℝ) ≤ growthBound u := one_le_growthBound u
  have hr : ‖q‖ * growthBound u < 1 := norm_mul_growthBound_lt_one hq hqu hqu'
  have hr0 : (0 : ℝ) ≤ ‖q‖ * growthBound u :=
    mul_nonneg (norm_nonneg q) (zero_le_one.trans hC1)
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun N => norm_nonneg _) (fun N => ?_)
    ((summable_geometric_of_lt_one hr0 hr).mul_left (‖q‖ * growthBound u))
  rw [norm_mul, norm_pow]
  have h1 : ‖xCoeff u (N + 1)‖ ≤ growthBound u ^ (N + 1) := by
    refine norm_sum_le_of_forall_le_of_nonneg
      (pow_nonneg (zero_le_one.trans hC1) _) fun d hd => ?_
    have hdM : d ≤ N + 1 := Nat.le_of_dvd (Nat.succ_pos N) (Nat.mem_divisors.mp hd).1
    exact (norm_xDivTerm_le u d).trans (pow_le_pow_right₀ hC1 hdM)
  calc ‖xCoeff u (N + 1)‖ * ‖q‖ ^ (N + 1)
      ≤ growthBound u ^ (N + 1) * ‖q‖ ^ (N + 1) :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg q) _)
    _ = (‖q‖ * growthBound u) ^ (N + 1) := by rw [← mul_pow]; ring_nf
    _ = (‖q‖ * growthBound u) * (‖q‖ * growthBound u) ^ N := by rw [pow_succ]; ring

lemma norm_tsum_xPairCoeff_le (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : ‖u‖ ≤ 1) (hv1 : ‖v‖ ≤ 1)
    (huv : ‖q‖ < ‖u * v‖) :
    ‖∑' N : ℕ, xPairCoeff u v (N + 1) * q ^ (N + 1)‖ ≤ ‖q‖ / ‖u * v‖ := by
  have huvpos : (0 : ℝ) < ‖u * v‖ := norm_pos_iff.mpr (mul_ne_zero hu0 hv0)
  have hr0 : (0 : ℝ) ≤ ‖q‖ / ‖u * v‖ := div_nonneg (norm_nonneg q) (norm_nonneg _)
  have hr1 : ‖q‖ / ‖u * v‖ ≤ 1 := le_of_lt ((div_lt_one huvpos).mpr huv)
  refine norm_tsum_le_of_forall_le_of_nonneg hr0 fun N => ?_
  rw [norm_mul, norm_pow]
  calc ‖xPairCoeff u v (N + 1)‖ * ‖q‖ ^ (N + 1)
      ≤ (‖u * v‖⁻¹) ^ (N + 1) * ‖q‖ ^ (N + 1) :=
        mul_le_mul_of_nonneg_right (norm_xPairCoeff_le hu0 hv0 hu1 hv1 (N + 1))
          (pow_nonneg (norm_nonneg q) _)
    _ = (‖q‖ / ‖u * v‖) ^ (N + 1) := by
        rw [← mul_pow]
        congr 1
        rw [div_eq_mul_inv, mul_comm]
    _ ≤ ‖q‖ / ‖u * v‖ := pow_le_of_le_one hr0 hr1 (Nat.succ_ne_zero N)

theorem pointX_sub_pointX_factor (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hu : OffLattice q u) (hv : OffLattice q v) (hu1 : ‖u‖ ≤ 1) (hv1 : ‖v‖ ≤ 1)
    (huv : ‖q‖ < ‖u * v‖) :
    pointX q u - pointX q v =
      (u - v) * (1 - u * v) *
        (((1 - u) ^ 2 * (1 - v) ^ 2)⁻¹ - ∑' N : ℕ, xPairCoeff u v (N + 1) * q ^ (N + 1)) := by

  have hqR : ‖q‖ < 1 := by exact_mod_cast hq
  have hunorm : ‖q‖ < ‖u‖ := lt_of_lt_of_le huv (by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg u) hv1)
  have hvnorm : ‖q‖ < ‖v‖ := lt_of_lt_of_le huv (by
    rw [norm_mul, mul_comm]
    exact mul_le_of_le_one_right (norm_nonneg v) hu1)
  have hqu : ‖q * u‖₊ < 1 := by
    have h : ‖q * u‖ < 1 := lt_of_le_of_lt
      (by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg q) hu1) hqR
    exact_mod_cast h
  have hqu' : ‖q * u⁻¹‖₊ < 1 := by
    have hupos : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
    have h : ‖q * u⁻¹‖ < 1 := by
      rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_one hupos]
      exact hunorm
    exact_mod_cast h
  have hqv : ‖q * v‖₊ < 1 := by
    have h : ‖q * v‖ < 1 := lt_of_le_of_lt
      (by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg q) hv1) hqR
    exact_mod_cast h
  have hqv' : ‖q * v⁻¹‖₊ < 1 := by
    have hvpos : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
    have h : ‖q * v⁻¹‖ < 1 := by
      rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_one hvpos]
      exact hvnorm
    exact_mod_cast h

  have hu1' : u ≠ 1 := by
    have := hu 0
    rwa [zpow_zero, one_mul] at this
  have hv1' : v ≠ 1 := by
    have := hv 0
    rwa [zpow_zero, one_mul] at this
  have hsum_u : Summable (fun N : ℕ => xCoeff u (N + 1) * q ^ (N + 1)) :=
    summable_xCoeff_mul_pow hq hqu hqu'
  have hsum_v : Summable (fun N : ℕ => xCoeff v (N + 1) * q ^ (N + 1)) :=
    summable_xCoeff_mul_pow hq hqv hqv'
  have hxfun : xfun u - xfun v = (u - v) * (1 - u * v) * ((1 - u) ^ 2 * (1 - v) ^ 2)⁻¹ :=
    xfun_sub_xfun hu1' hv1'
  have htails : (∑' N : ℕ, xCoeff u (N + 1) * q ^ (N + 1)) -
      (∑' N : ℕ, xCoeff v (N + 1) * q ^ (N + 1)) =
      -((u - v) * (1 - u * v)) * ∑' N : ℕ, xPairCoeff u v (N + 1) * q ^ (N + 1) := by
    rw [← Summable.tsum_sub hsum_u hsum_v, ← tsum_mul_left]
    refine tsum_congr fun N => ?_
    rw [← sub_mul, xCoeff_sub_xCoeff hu0 hv0 (Nat.succ_ne_zero N), mul_assoc]
  rw [pointX_qExpansion hq0 hq hu0 hu hqu hqu', pointX_qExpansion hq0 hq hv0 hv hqv hqv']
  calc (xfun u + ∑' N : ℕ, xCoeff u (N + 1) * q ^ (N + 1)) -
        (xfun v + ∑' N : ℕ, xCoeff v (N + 1) * q ^ (N + 1))
      = (xfun u - xfun v) + ((∑' N : ℕ, xCoeff u (N + 1) * q ^ (N + 1)) -
          (∑' N : ℕ, xCoeff v (N + 1) * q ^ (N + 1))) := by ring
    _ = (u - v) * (1 - u * v) * ((1 - u) ^ 2 * (1 - v) ^ 2)⁻¹ +
          (-((u - v) * (1 - u * v)) * ∑' N : ℕ, xPairCoeff u v (N + 1) * q ^ (N + 1)) := by
        rw [hxfun, htails]
    _ = (u - v) * (1 - u * v) *
          (((1 - u) ^ 2 * (1 - v) ^ 2)⁻¹ -
            ∑' N : ℕ, xPairCoeff u v (N + 1) * q ^ (N + 1)) := by ring

theorem eq_or_mul_eq_one_of_pointX_eq (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hu : OffLattice q u) (hv : OffLattice q v) (hu1 : ‖u‖ ≤ 1) (hv1 : ‖v‖ ≤ 1)
    (huv : ‖q‖ < ‖u * v‖) (hX : pointX q u = pointX q v) :
    u = v ∨ u * v = 1 := by
  have hu1' : u ≠ 1 := by
    have := hu 0
    rwa [zpow_zero, one_mul] at this
  have hv1' : v ≠ 1 := by
    have := hv 0
    rwa [zpow_zero, one_mul] at this
  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1')
  have h1v : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1')

  have hG : ((1 - u) ^ 2 * (1 - v) ^ 2)⁻¹ -
      (∑' N : ℕ, xPairCoeff u v (N + 1) * q ^ (N + 1)) ≠ 0 := by
    intro h0
    have hmain_ne : ((1 - u) ^ 2 * (1 - v) ^ 2 : K) ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 h1u) (pow_ne_zero 2 h1v)
    have h1u_le : ‖(1 : K) - u‖ ≤ 1 := by
      have h := nnnorm_add_le_max (1 : K) (-u)
      rw [nnnorm_neg, nnnorm_one, ← sub_eq_add_neg] at h
      have hu1'' : ‖u‖₊ ≤ 1 := by exact_mod_cast hu1
      have h2 : ‖(1 : K) - u‖₊ ≤ 1 := h.trans (max_le le_rfl hu1'')
      exact_mod_cast h2
    have h1v_le : ‖(1 : K) - v‖ ≤ 1 := by
      have h := nnnorm_add_le_max (1 : K) (-v)
      rw [nnnorm_neg, nnnorm_one, ← sub_eq_add_neg] at h
      have hv1'' : ‖v‖₊ ≤ 1 := by exact_mod_cast hv1
      have h2 : ‖(1 : K) - v‖₊ ≤ 1 := h.trans (max_le le_rfl hv1'')
      exact_mod_cast h2
    have hle : ‖((1 - u) ^ 2 * (1 - v) ^ 2 : K)‖ ≤ 1 := by
      rw [norm_mul, norm_pow, norm_pow]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) h1u_le)
        (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) h1v_le)
    have htail : ‖∑' N : ℕ, xPairCoeff u v (N + 1) * q ^ (N + 1)‖ ≤ ‖q‖ / ‖u * v‖ :=
      norm_tsum_xPairCoeff_le hu0 hv0 hu1 hv1 huv
    have hlt : ‖q‖ / ‖u * v‖ < 1 :=
      (div_lt_one (norm_pos_iff.mpr (mul_ne_zero hu0 hv0))).mpr huv
    have heq : (((1 - u) ^ 2 * (1 - v) ^ 2 : K))⁻¹ =
        ∑' N : ℕ, xPairCoeff u v (N + 1) * q ^ (N + 1) := sub_eq_zero.mp h0

    have hone : (1 : K) = ((1 - u) ^ 2 * (1 - v) ^ 2) *
        ∑' N : ℕ, xPairCoeff u v (N + 1) * q ^ (N + 1) := by
      rw [← heq, mul_inv_cancel₀ hmain_ne]
    have hnorm1 : (1 : ℝ) = ‖((1 - u) ^ 2 * (1 - v) ^ 2 : K)‖ *
        ‖∑' N : ℕ, xPairCoeff u v (N + 1) * q ^ (N + 1)‖ := by
      rw [← norm_mul, ← hone, norm_one]
    nlinarith [norm_nonneg ((1 - u) ^ 2 * (1 - v) ^ 2 : K),
      norm_nonneg (∑' N : ℕ, xPairCoeff u v (N + 1) * q ^ (N + 1))]

  have hfact := pointX_sub_pointX_factor hq0 hq hu0 hv0 hu hv hu1 hv1 huv
  rw [hX, sub_self] at hfact
  have h0 : (u - v) * (1 - u * v) = 0 := by
    rcases mul_eq_zero.mp hfact.symm with h | h
    · exact h
    · exact absurd h hG
  rcases mul_eq_zero.mp h0 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h).symm

end Factorization

section Fiber

private lemma pointX_q_mul_inv (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hu : OffLattice q u) :
    pointX q (q * u⁻¹) = pointX q u := by
  have h1 : q * u⁻¹ = q ^ (1 : ℤ) * u⁻¹ := by rw [zpow_one]
  rw [h1, pointX_zpow_mul hq0, pointX_inv hq0 hu0 hu]

theorem exists_zpow_of_pointX_eq_of_pow_lattice (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu : OffLattice q u) (hv : OffLattice q v)
    {p : ℕ} (hodd : Odd p) {su sv : ℤ} (hpu : u ^ p = q ^ su) (hpv : v ^ p = q ^ sv)
    (hX : pointX q u = pointX q v) :
    (∃ k : ℤ, v = q ^ k * u) ∨ (∃ k : ℤ, u * v = q ^ k) := by
  have hqR : ‖q‖ < 1 := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0

  obtain ⟨a, ha1, ha2⟩ := exists_zpow_mul_norm_Ioc hq0 hqR hu0
  obtain ⟨b, hb1, hb2⟩ := exists_zpow_mul_norm_Ioc hq0 hqR hv0
  set u₀ : K := q ^ a * u with hu₀def
  set v₀ : K := q ^ b * v with hv₀def
  have hu₀0 : u₀ ≠ 0 := mul_ne_zero (zpow_ne_zero a hq0) hu0
  have hv₀0 : v₀ ≠ 0 := mul_ne_zero (zpow_ne_zero b hq0) hv0
  have hu₀off : OffLattice q u₀ := hu.zpow_mul hq0 a
  have hv₀off : OffLattice q v₀ := hv.zpow_mul hq0 b
  have hXu₀ : pointX q u₀ = pointX q u := pointX_zpow_mul hq0 a
  have hXv₀ : pointX q v₀ = pointX q v := pointX_zpow_mul hq0 b
  have hX₀ : pointX q u₀ = pointX q v₀ := by rw [hXu₀, hXv₀]; exact hX

  set u₁ : K := q * u₀⁻¹ with hu₁def
  set v₁ : K := q * v₀⁻¹ with hv₁def
  have hu₁0 : u₁ ≠ 0 := mul_ne_zero hq0 (inv_ne_zero hu₀0)
  have hv₁0 : v₁ ≠ 0 := mul_ne_zero hq0 (inv_ne_zero hv₀0)
  have hu₁off : OffLattice q u₁ := (hu₀off.inv hq0).q_mul hq0
  have hv₁off : OffLattice q v₁ := (hv₀off.inv hq0).q_mul hq0
  have hXu₁ : pointX q u₁ = pointX q u₀ := pointX_q_mul_inv hq0 hu₀0 hu₀off
  have hXv₁ : pointX q v₁ = pointX q v₀ := pointX_q_mul_inv hq0 hv₀0 hv₀off

  have hu₀pos : (0 : ℝ) < ‖u₀‖ := norm_pos_iff.mpr hu₀0
  have hv₀pos : (0 : ℝ) < ‖v₀‖ := norm_pos_iff.mpr hv₀0
  have hu₁norm : ‖u₁‖ = ‖q‖ / ‖u₀‖ := by
    rw [hu₁def, norm_mul, norm_inv, div_eq_mul_inv]
  have hv₁norm : ‖v₁‖ = ‖q‖ / ‖v₀‖ := by
    rw [hv₁def, norm_mul, norm_inv, div_eq_mul_inv]
  have hu₁le : ‖u₁‖ ≤ 1 := by
    rw [hu₁norm]
    exact le_of_lt ((div_lt_one hu₀pos).mpr ha1)
  have hv₁le : ‖v₁‖ ≤ 1 := by
    rw [hv₁norm]
    exact le_of_lt ((div_lt_one hv₀pos).mpr hb1)

  have transfer_eq : ∀ k l : ℤ, q ^ k * u = q ^ l * v → ∃ m : ℤ, v = q ^ m * u := by
    intro k l hkl
    refine ⟨k - l, ?_⟩
    have h1 : v = q ^ (-l) * (q ^ k * u) := by
      rw [hkl, ← mul_assoc, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero, one_mul]
    rw [h1, ← mul_assoc, ← zpow_add₀ hq0, show -l + k = k - l by ring]
  have transfer_mul : ∀ k l m : ℤ, (q ^ k * u) * (q ^ l * v) = q ^ m →
      ∃ n : ℤ, u * v = q ^ n := by
    intro k l m hklm
    refine ⟨m - (k + l), ?_⟩
    have h1 : q ^ (k + l) * (u * v) = q ^ m := by
      rw [zpow_add₀ hq0, ← hklm]
      ring
    have h2 : u * v = q ^ (-(k + l)) * q ^ m := by
      rw [← h1, ← mul_assoc, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero, one_mul]
    rw [h2, ← zpow_add₀ hq0, show -(k + l) + m = m - (k + l) by ring]

  by_cases hP1 : ‖q‖ < ‖u₀ * v₀‖
  ·
    rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq hu₀0 hv₀0 hu₀off hv₀off ha2 hb2 hP1 hX₀ with
      h | h
    · refine Or.inl (transfer_eq a b ?_)
      rw [← hu₀def, ← hv₀def]
      exact h
    · refine Or.inr (transfer_mul a b 0 ?_)
      rw [← hu₀def, ← hv₀def, h, zpow_zero]
  by_cases hP4 : ‖q‖ < ‖u₁ * v₁‖
  ·
    have hX₁ : pointX q u₁ = pointX q v₁ := by rw [hXu₁, hXv₁]; exact hX₀
    rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq hu₁0 hv₁0 hu₁off hv₁off hu₁le hv₁le hP4 hX₁ with
      h | h
    ·
      refine Or.inl (transfer_eq a b ?_)
      have h0 : u₀ = v₀ := inv_injective (mul_left_cancel₀ hq0 h)
      rw [← hu₀def, ← hv₀def]
      exact h0
    ·
      refine Or.inr (transfer_mul a b 2 ?_)
      have hexp : u₀ * v₀ = q ^ (2 : ℤ) := by
        have h1 := congrArg (fun x => x * (u₀ * v₀)) h
        simp only [one_mul] at h1
        rw [show u₁ * v₁ * (u₀ * v₀) = (q * q) * ((u₀⁻¹ * u₀) * (v₀⁻¹ * v₀)) by
          rw [hu₁def, hv₁def]; ring] at h1
        rw [inv_mul_cancel₀ hu₀0, inv_mul_cancel₀ hv₀0, mul_one, mul_one] at h1
        rw [← h1, show (2 : ℤ) = 1 + 1 by norm_num, zpow_add₀ hq0, zpow_one]
      rw [← hu₀def, ← hv₀def]
      exact hexp
  by_cases hP2 : ‖q‖ < ‖u₀ * v₁‖
  ·
    have hX₂ : pointX q u₀ = pointX q v₁ := by rw [hXv₁]; exact hX₀
    rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq hu₀0 hv₁0 hu₀off hv₁off ha2 hv₁le hP2 hX₂ with
      h | h
    ·
      refine Or.inr (transfer_mul a b 1 ?_)
      have hexp : u₀ * v₀ = q := by
        rw [h, hv₁def, mul_assoc, inv_mul_cancel₀ hv₀0, mul_one]
      rw [← hu₀def, ← hv₀def, hexp, zpow_one]
    ·
      refine Or.inl (transfer_eq (a + 1) b ?_)
      have hexp : v₀ = q * u₀ := by
        have h1 := congrArg (fun x => x * v₀) h
        simp only [one_mul] at h1
        rw [show u₀ * v₁ * v₀ = (q * u₀) * (v₀⁻¹ * v₀) by rw [hv₁def]; ring] at h1
        rw [inv_mul_cancel₀ hv₀0, mul_one] at h1
        exact h1.symm
      have hqq : q * q ^ a = q ^ (a + 1) := by
        rw [add_comm a 1, zpow_add₀ hq0, zpow_one]
      have h0 : q ^ b * v = q ^ (a + 1) * u := by
        rw [← hv₀def, hexp, hu₀def, ← mul_assoc, hqq]
      exact h0.symm
  by_cases hP3 : ‖q‖ < ‖u₁ * v₀‖
  ·
    have hX₃ : pointX q u₁ = pointX q v₀ := by rw [hXu₁]; exact hX₀
    rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq hu₁0 hv₀0 hu₁off hv₀off hu₁le hb2 hP3 hX₃ with
      h | h
    ·
      refine Or.inr (transfer_mul a b 1 ?_)
      have hexp : u₀ * v₀ = q := by
        rw [← h, hu₁def, show u₀ * (q * u₀⁻¹) = q * (u₀ * u₀⁻¹) by ring,
          mul_inv_cancel₀ hu₀0, mul_one]
      rw [← hu₀def, ← hv₀def, hexp, zpow_one]
    ·
      refine Or.inl (transfer_eq a (b + 1) ?_)
      have hexp : u₀ = q * v₀ := by
        have h1 := congrArg (fun x => x * u₀) h
        simp only [one_mul] at h1
        rw [show u₁ * v₀ * u₀ = (q * v₀) * (u₀⁻¹ * u₀) by rw [hu₁def]; ring] at h1
        rw [inv_mul_cancel₀ hu₀0, mul_one] at h1
        exact h1.symm
      have hqq : q * q ^ b = q ^ (b + 1) := by
        rw [add_comm b 1, zpow_add₀ hq0, zpow_one]
      have h0 : q ^ a * u = q ^ (b + 1) * v := by
        rw [← hu₀def, hexp, hv₀def, ← mul_assoc, hqq]
      exact h0
  ·
    exfalso
    push_neg at hP1 hP2 hP3 hP4
    set A : ℝ := ‖u₀‖ with hA
    set B : ℝ := ‖v₀‖ with hB
    set Q : ℝ := ‖q‖ with hQ
    have hApos : (0 : ℝ) < A := hu₀pos
    have hBpos : (0 : ℝ) < B := hv₀pos
    have hQpos : (0 : ℝ) < Q := hqpos

    have hP1' : A * B ≤ Q := by
      have hnorm : ‖u₀ * v₀‖ = A * B := norm_mul _ _
      rw [← hnorm]; exact hP1
    have hP2' : A * (Q / B) ≤ Q := by
      have hnorm : ‖u₀ * v₁‖ = A * (Q / B) := by rw [norm_mul, hv₁norm]
      rw [← hnorm]; exact hP2
    have hP3' : (Q / A) * B ≤ Q := by
      have hnorm : ‖u₁ * v₀‖ = (Q / A) * B := by rw [norm_mul, hu₁norm]
      rw [← hnorm]; exact hP3
    have hP4' : (Q / A) * (Q / B) ≤ Q := by
      have hnorm : ‖u₁ * v₁‖ = (Q / A) * (Q / B) := by rw [norm_mul, hu₁norm, hv₁norm]
      rw [← hnorm]; exact hP4

    have h4 : Q * Q ≤ Q * (A * B) := by
      have h := hP4'
      rw [div_mul_div_comm, div_le_iff₀ (mul_pos hApos hBpos)] at h
      exact h
    have hQle : Q ≤ A * B := le_of_mul_le_mul_left h4 hQpos
    have hAB : A * B = Q := le_antisymm hP1' hQle
    have h2 : A * Q ≤ Q * B := by
      have h := hP2'
      rw [← mul_div_assoc, div_le_iff₀ hBpos] at h
      exact h
    have h3 : Q * B ≤ Q * A := by
      have h := hP3'
      rw [div_mul_eq_mul_div, div_le_iff₀ hApos] at h
      exact h
    have heqnorm : A = B := by nlinarith
    have hsq : A ^ 2 = Q := by nlinarith

    have hu₀pow : u₀ ^ p = q ^ (a * (p : ℤ) + su) := by
      rw [hu₀def, mul_pow, ← zpow_natCast (q ^ a) p, ← zpow_mul, hpu, ← zpow_add₀ hq0]
    have hnorm_pow : A ^ p = Q ^ (a * (p : ℤ) + su) := by
      have h := congrArg norm hu₀pow
      rw [norm_pow, norm_zpow] at h
      exact h
    have hexp : (a * (p : ℤ) + su) * 2 = ((p : ℕ) : ℤ) := by
      have hQ1 : Q ≠ 1 := ne_of_lt hqR
      have h1 : (Q ^ (a * (p : ℤ) + su)) ^ (2 : ℕ) = Q ^ ((p : ℕ) : ℤ) := by
        rw [← hnorm_pow, ← pow_mul, mul_comm p 2, pow_mul, hsq, zpow_natCast]
      have h2 : Q ^ ((a * (p : ℤ) + su) * 2) = Q ^ ((p : ℕ) : ℤ) := by
        rw [zpow_mul, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
        exact h1
      exact (zpow_right_inj₀ hQpos hQ1).mp h2
    rcases hodd with ⟨t, ht⟩
    omega

end Fiber

section TwoTorsion

lemma two_nsmul_point_ne_zero (hyps : SymAddHyps q) (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hu0 : u ≠ 0) (hu : OffLattice q u) (hu2 : OffLattice q (u ^ 2))
    (hns : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u)) :
    (2 : ℕ) • (Point.some (pointX q u) (pointY q u) hns : (curve q).toAffine.Point) ≠ 0 := by
  intro h2
  rw [two_nsmul] at h2
  by_cases hy : pointY q u = (curve q).toAffine.negY (pointX q u) (pointY q u)
  ·
    have hΨ : ((curve q).toAffine.Ψ₂Sq).eval (pointX q u) = 0 := by
      have hsq := WeierstrassCurve.Affine.sq_sub_negY_eq_eval_Ψ₂Sq
        (W := (curve q).toAffine) hns.left
      have h0 : pointY q u - (curve q).toAffine.negY (pointX q u) (pointY q u) = 0 :=
        sub_eq_zero.mpr hy
      rw [h0] at hsq
      simpa using hsq.symm
    have hΦ : (((curve q).toAffine.Φ 2)).eval (pointX q u) = 0 := by
      have hser : pointX q (u ^ 2) * ((curve q).toAffine.Ψ₂Sq).eval (pointX q u) =
          (((curve q).toAffine.Φ 2)).eval (pointX q u) := hyps.dbl u hu0 hu hu2
      rw [hΨ, mul_zero] at hser
      exact hser.symm
    have hΔ : (curve q).Δ ^ 2 = 0 :=
      WeierstrassCurve.Δ_sq_eq_zero_of_eval_eq_zero (W := curve q) hΦ hΨ
    exact pow_ne_zero 2 (Δ_ne_zero hq0 hq) hΔ
  · rw [Point.add_self_of_Y_ne hy] at h2
    exact Point.some_ne_zero _ h2

end TwoTorsion

section Consumers

theorem forall_nsmul_ne_zero_of_pow_lattice (hyps : SymAddHyps q) (hq0 : q ≠ 0)
    (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : OffLattice q u) {p : ℕ} {s : ℤ}
    (hpow : u ^ p = q ^ s) (hp : p.Prime) (hodd : Odd p)
    (hns : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u)) :
    ∀ m : ℕ, 2 ≤ m → m ≤ p - 1 →
      m • (Point.some (pointX q u) (pointY q u) hns : (curve q).toAffine.Point) ≠ 0 := by
  set P : (curve q).toAffine.Point := Point.some (pointX q u) (pointY q u) hns with hP
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases hodd with ⟨t, ht⟩
    omega
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm2 hmp hm0

    have hoffj : ∀ j : ℕ, 1 ≤ j → j ≤ p - 1 → OffLattice q (u ^ j) := fun j hj1 hj2 =>
      offLattice_pow_of_prime hq0 hu0 hu hpow hp (by omega) (by omega)
    rcases eq_or_lt_of_le hm2 with hm2' | hm3
    ·
      have hu2 : OffLattice q (u ^ 2) := hoffj 2 (by omega) (by omega)
      refine two_nsmul_point_ne_zero hyps hq0 hq hu0 hu hu2 hns ?_
      rw [hm2']
      rw [hP] at hm0
      exact hm0
    ·
      have htor' : ∀ m' : ℕ, 2 ≤ m' → m' ≤ m - 1 →
          m' • (Point.some (pointX q u) (pointY q u) hns : (curve q).toAffine.Point) ≠ 0 :=
        fun m' hm'2 hm'le => ih m' (by omega) hm'2 (by omega)
      have hoff' : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → OffLattice q (u ^ j) :=
        fun j hj1 hj2 => hoffj j hj1 (by omega)
      have halign := xOrZero_nsmul_of_forall_ne_zero hyps hq0 hu0 hoff' hns htor'
      obtain ⟨hne, hx⟩ := halign (m - 1) (by omega) le_rfl

      have hsucc : m • P = (m - 1) • P + P := by
        conv_lhs => rw [show m = (m - 1) + 1 by omega]
        exact succ_nsmul P (m - 1)
      have hneg : (m - 1) • P = -P := by
        have h0 : (m - 1) • P + P = 0 := by rw [← hsucc]; exact hm0
        exact eq_neg_of_add_eq_zero_left h0

      have hXcoin : pointX q (u ^ (m - 1)) = pointX q u := by
        have hx' := hx
        rw [← hP] at hx'
        rw [hneg, hP, Point.neg_some, Point.xOrZero_some] at hx'
        exact hx'.symm

      have hcast : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
      have hupow : (u ^ (m - 1)) ^ p = q ^ (s * ((m : ℤ) - 1)) := by
        rw [← pow_mul, mul_comm (m - 1) p, pow_mul, hpow, ← zpow_natCast (q ^ s) (m - 1),
          ← zpow_mul, hcast]
      have hoffm1 : OffLattice q (u ^ (m - 1)) := hoffj (m - 1) (by omega) (by omega)
      rcases exists_zpow_of_pointX_eq_of_pow_lattice hq0 hq (pow_ne_zero _ hu0) hu0 hoffm1 hu
        hodd hupow hpow hXcoin with ⟨k, hk⟩ | ⟨k, hk⟩
      ·
        have hm2off : OffLattice q (u ^ (m - 2)) := hoffj (m - 2) (by omega) (by omega)
        refine hm2off k ?_
        have hsplit : u ^ (m - 1) = u ^ (m - 2) * u := by
          conv_lhs => rw [show m - 1 = (m - 2) + 1 by omega]
          rw [pow_succ]
        have h1 : (q ^ k * u ^ (m - 2)) * u = 1 * u := by
          rw [one_mul, mul_assoc, ← hsplit, ← hk]
        exact mul_right_cancel₀ hu0 h1
      ·
        have hmoff : OffLattice q (u ^ m) := hoffj m (by omega) (by omega)
        refine hmoff (-k) ?_
        have hsplit : u ^ (m - 1) * u = u ^ m := by
          conv_rhs => rw [show m = (m - 1) + 1 by omega]
          rw [pow_succ]
        rw [← hsplit, hk, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero]

theorem nsmul_prime_eq_zero (hyps : SymAddHyps q) (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hu0 : u ≠ 0) (hu : OffLattice q u) {p : ℕ} {s : ℤ}
    (hpow : u ^ p = q ^ s) (hp : p.Prime) (hodd : Odd p)
    (hns : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u)) :
    p • (Point.some (pointX q u) (pointY q u) hns : (curve q).toAffine.Point) = 0 :=
  nsmul_prime_eq_zero_of_forall_ne_zero hyps hq0 hu0 hu hpow hp hodd hns
    (forall_nsmul_ne_zero_of_pow_lattice hyps hq0 hq hu0 hu hpow hp hodd hns)

theorem eq_zpow_mul_of_pointXY_eq (hyps : SymAddHyps q) (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu : OffLattice q u) (hv : OffLattice q v)
    {p : ℕ} {su sv : ℤ} (hpu : u ^ p = q ^ su) (hpv : v ^ p = q ^ sv)
    (hp : p.Prime) (hodd : Odd p)
    (hX : pointX q u = pointX q v) (hY : pointY q u = pointY q v) :
    ∃ k : ℤ, v = q ^ k * u := by
  rcases exists_zpow_of_pointX_eq_of_pow_lattice hq0 hq hu0 hv0 hu hv hodd hpu hpv hX with
    ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k, hk⟩
  ·
    exfalso
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      rcases hodd with ⟨t, ht⟩
      omega
    have hveq : v = q ^ k * u⁻¹ := by
      have h1 : u⁻¹ * (u * v) = u⁻¹ * q ^ k := by rw [hk]
      rw [← mul_assoc, inv_mul_cancel₀ hu0, one_mul] at h1
      rw [h1, mul_comm]

    have hXv : pointX q v = pointX q u := by
      rw [hveq, pointX_zpow_mul hq0, pointX_inv hq0 hu0 hu]
    have hYv : pointY q v = -pointY q u - pointX q u := by
      rw [hveq, pointY_zpow_mul hq0, pointY_inv hq0 hq hu0 hu]

    have hYneg : pointY q u = -pointY q u - pointX q u := by rw [← hYv, ← hY]

    have hyneg : pointY q u = (curve q).toAffine.negY (pointX q u) (pointY q u) := by
      show pointY q u = -pointY q u - (curve q).a₁ * pointX q u - (curve q).a₃
      rw [curve_a₁, curve_a₃]
      linear_combination hYneg

    have hu2 : OffLattice q (u ^ 2) :=
      offLattice_pow_of_prime hq0 hu0 hu hpu hp (by omega) (by omega)

    have hns : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u) :=
      nonsingular_point hq0 hq hu0 hu
    have hΨ : ((curve q).toAffine.Ψ₂Sq).eval (pointX q u) = 0 := by
      have hsq := WeierstrassCurve.Affine.sq_sub_negY_eq_eval_Ψ₂Sq
        (W := (curve q).toAffine) hns.left
      have h0 : pointY q u - (curve q).toAffine.negY (pointX q u) (pointY q u) = 0 :=
        sub_eq_zero.mpr hyneg
      rw [h0] at hsq
      simpa using hsq.symm
    have hΦ : (((curve q).toAffine.Φ 2)).eval (pointX q u) = 0 := by
      have hser : pointX q (u ^ 2) * ((curve q).toAffine.Ψ₂Sq).eval (pointX q u) =
          (((curve q).toAffine.Φ 2)).eval (pointX q u) := hyps.dbl u hu0 hu hu2
      rw [hΨ, mul_zero] at hser
      exact hser.symm
    have hΔ : (curve q).Δ ^ 2 = 0 :=
      WeierstrassCurve.Δ_sq_eq_zero_of_eval_eq_zero (W := curve q) hΦ hΨ
    exact pow_ne_zero 2 (Δ_ne_zero hq0 hq) hΔ

lemma pointXY_eq_of_zpow_mul (hq0 : q ≠ 0) (k : ℤ) :
    pointX q (q ^ k * u) = pointX q u ∧ pointY q (q ^ k * u) = pointY q u :=
  ⟨pointX_zpow_mul hq0 k, pointY_zpow_mul hq0 k⟩

end Consumers

end TateCurve

open Polynomial
open scoped NNReal

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u : K}

lemma symSumNum_self (z : K) : symSumNum q z z = ((curve q).Ψ₂Sq).eval z := by
  rw [WeierstrassCurve.Affine.eval_Ψ₂Sq, curve_b₂, curve_b₄, curve_b₆]
  simp only [symSumNum]; ring

lemma symProdNum_self (z : K) : symProdNum q z z = ((curve q).Φ 2).eval z := by
  rw [WeierstrassCurve.Affine.eval_Φ_two, curve_b₄, curve_b₆, curve_b₈]
  simp only [symProdNum]; ring

private lemma not_both_eval_eq_zero (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {z : K}
    (h1 : ((curve q).Ψ₂Sq).eval z = 0) (h2 : ((curve q).Φ 2).eval z = 0) : False := by
  haveI := isElliptic hq0 hq
  exact (curve q).not_eval_Φ_two_eq_zero h1 h2

private lemma quad_transfer (x y s t : K)
    (h3 : (s + t) * (x - y) ^ 2 = symSumNum q x y)
    (h4 : s * t * (x - y) ^ 2 = symProdNum q x y) :
    (symProdNum q s t * (((curve q).Ψ₂Sq).eval x) ^ 2
        - symSumNum q s t * (((curve q).Ψ₂Sq).eval x) * (((curve q).Φ 2).eval x)
        + (s - t) ^ 2 * (((curve q).Φ 2).eval x) ^ 2) * ((x - y) ^ 2) ^ 2 = 0 := by
  have hΨ : ((curve q).Ψ₂Sq).eval x = 4 * x ^ 3 + x ^ 2 + 4 * a₄ q * x + 4 * a₆ q := by
    rw [WeierstrassCurve.Affine.eval_Ψ₂Sq, curve_b₂, curve_b₄, curve_b₆]; ring
  have hΦ : ((curve q).Φ 2).eval x =
      x ^ 4 - 2 * a₄ q * x ^ 2 - 8 * a₆ q * x - a₆ q + a₄ q ^ 2 := by
    rw [WeierstrassCurve.Affine.eval_Φ_two, curve_b₄, curve_b₆, curve_b₈]; ring
  rw [hΨ, hΦ]
  simp only [symSumNum, symProdNum] at h3 h4 ⊢
  linear_combination
    ((x ^ 4 - 2 * a₄ q * x ^ 2 - 8 * a₆ q * x - a₆ q + a₄ q ^ 2) ^ 2 *
          ((s + t) * (x - y) ^ 2 +
            (2 * (x * y) * (x + y) + x * y + 2 * a₄ q * (x + y) + 4 * a₆ q))
        - 4 * a₆ q * (x - y) ^ 2 * (4 * x ^ 3 + x ^ 2 + 4 * a₄ q * x + 4 * a₆ q) ^ 2
        - 2 * (s * t * (x - y) ^ 2) * (4 * x ^ 3 + x ^ 2 + 4 * a₄ q * x + 4 * a₆ q) *
          (x ^ 4 - 2 * a₄ q * x ^ 2 - 8 * a₆ q * x - a₆ q + a₄ q ^ 2)
        - 2 * a₄ q * (x - y) ^ 2 * (4 * x ^ 3 + x ^ 2 + 4 * a₄ q * x + 4 * a₆ q) *
          (x ^ 4 - 2 * a₄ q * x ^ 2 - 8 * a₆ q * x - a₆ q + a₄ q ^ 2)) * h3
    + ((4 * x ^ 3 + x ^ 2 + 4 * a₄ q * x + 4 * a₆ q) ^ 2 *
          (s * t * (x - y) ^ 2 +
            ((x * y) ^ 2 - 2 * a₄ q * (x * y) - 4 * a₆ q * (x + y) - a₆ q + a₄ q ^ 2))
        - 2 * a₄ q * (x - y) ^ 2 * (4 * x ^ 3 + x ^ 2 + 4 * a₄ q * x + 4 * a₆ q) ^ 2
        - (2 * (2 * (x * y) * (x + y) + x * y + 2 * a₄ q * (x + y) + 4 * a₆ q) + (x - y) ^ 2) *
          (4 * x ^ 3 + x ^ 2 + 4 * a₄ q * x + 4 * a₆ q) *
          (x ^ 4 - 2 * a₄ q * x ^ 2 - 8 * a₆ q * x - a₆ q + a₄ q ^ 2)
        - 4 * (x - y) ^ 2 *
          (x ^ 4 - 2 * a₄ q * x ^ 2 - 8 * a₆ q * x - a₆ q + a₄ q ^ 2) ^ 2) * h4

section AuxiliarySupply

private structure DiamondAux (q u w : K) : Prop where
  ne_zero : w ≠ 0
  nnnorm_eq : ‖w‖₊ = 1
  offLattice : OffLattice q w
  offLattice_sq : OffLattice q (w ^ 2)
  offLattice_mul : OffLattice q (u * w)
  offLattice_div : OffLattice q (u * w⁻¹)

private lemma nnnorm_pow_lt_one (hq : ‖q‖₊ < 1) {n : ℕ} (hn : 1 ≤ n) : ‖q ^ n‖₊ < 1 := by
  rw [nnnorm_pow]
  exact pow_lt_one₀ zero_le hq (by omega)

private lemma nnnorm_one_add_pow (hq : ‖q‖₊ < 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖(1 : K) + q ^ n‖₊ = 1 := by
  have h : ((1 : K) + q ^ n) = 1 - (-(q ^ n)) := by ring
  rw [h]
  refine nnnorm_one_sub_of_lt_one ?_
  rw [nnnorm_neg]
  exact nnnorm_pow_lt_one hq hn

private lemma one_add_pow_ne_zero (hq : ‖q‖₊ < 1) {n : ℕ} (hn : 1 ≤ n) :
    (1 : K) + q ^ n ≠ 0 := by
  intro h0
  have := nnnorm_one_add_pow (q := q) hq hn
  rw [h0, nnnorm_zero] at this
  exact zero_ne_one this

private lemma one_add_pow_ne_one (hq0 : q ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    (1 : K) + q ^ n ≠ 1 := by
  intro h
  have hpow : q ^ n = 0 := by linear_combination h
  exact hq0 (pow_eq_zero_iff (by omega) |>.mp hpow)

private lemma offLattice_of_nnnorm_eq_one (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {w : K}
    (hw : ‖w‖₊ = 1) (hw1 : w ≠ 1) : OffLattice q w := by
  intro k hk
  have hnorm : ‖q‖₊ ^ k * ‖w‖₊ = 1 := by
    have := congrArg (‖·‖₊) hk
    simpa [nnnorm_mul, nnnorm_zpow] using this
  have hk0 : k = 0 := by
    have hq_pos : (0 : ℝ≥0) < ‖q‖₊ := by
      simpa [pos_iff_ne_zero, nnnorm_eq_zero] using hq0
    have : ‖q‖₊ ^ k = ‖q‖₊ ^ (0 : ℤ) := by
      rw [zpow_zero]
      rw [hw, mul_one] at hnorm
      exact hnorm
    exact zpow_right_injective₀ hq_pos (ne_of_lt hq) this
  rw [hk0, zpow_zero, one_mul] at hk
  exact hw1 hk

private lemma one_add_pow_injective (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {n m : ℕ}
    (h : (1 : K) + q ^ n = 1 + q ^ m) : n = m := by
  have hpow : q ^ n = q ^ m := by linear_combination h
  have hnorm : ‖q‖₊ ^ (n : ℤ) = ‖q‖₊ ^ (m : ℤ) := by
    rw [zpow_natCast, zpow_natCast, ← nnnorm_pow, ← nnnorm_pow, hpow]
  have hq_pos : (0 : ℝ≥0) < ‖q‖₊ := by
    simpa [pos_iff_ne_zero, nnnorm_eq_zero] using hq0
  have := zpow_right_injective₀ hq_pos (ne_of_lt hq) hnorm
  exact_mod_cast this

private lemma one_add_pow_mul_ne_one (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {n m : ℕ}
    (hn : 1 ≤ n) (hnm : n < m) : ((1 : K) + q ^ n) * (1 + q ^ m) ≠ 1 := by
  intro h
  have hmn : n + (m - n) = m := by omega
  have key : q ^ n * (1 + (q ^ (m - n) + q ^ m)) = 0 := by
    have expand : q ^ n * (1 + (q ^ (m - n) + q ^ m)) =
        q ^ n + (q ^ (n + (m - n)) + q ^ (n + m)) := by
      rw [pow_add, pow_add]; ring
    rw [expand, hmn]
    linear_combination h
  have h2 : (1 : K) + (q ^ (m - n) + q ^ m) = 0 := by
    rcases mul_eq_zero.mp key with h' | h'
    · exact absurd (pow_eq_zero_iff (by omega) |>.mp h') hq0
    · exact h'

  have hsmall : ‖q ^ (m - n) + q ^ m‖₊ < 1 := by
    refine lt_of_le_of_lt (IsUltrametricDist.nnnorm_add_le_max _ _) ?_
    exact max_lt (nnnorm_pow_lt_one hq (by omega)) (nnnorm_pow_lt_one hq (by omega))
  have hone : ‖(1 : K) + (q ^ (m - n) + q ^ m)‖₊ = 1 := by
    have h' : ((1 : K) + (q ^ (m - n) + q ^ m)) = 1 - (-(q ^ (m - n) + q ^ m)) := by ring
    rw [h']
    exact nnnorm_one_sub_of_lt_one (by rwa [nnnorm_neg])
  rw [h2, nnnorm_zero] at hone
  exact zero_ne_one hone

private lemma lattice_mul_unique (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h1 : ¬ OffLattice q (u * (1 + q ^ n))) (h2 : ¬ OffLattice q (u * (1 + q ^ m))) :
    n = m := by
  simp only [OffLattice, not_forall, not_not] at h1 h2
  obtain ⟨k, hk⟩ := h1
  obtain ⟨j, hj⟩ := h2
  have hcn := nnnorm_one_add_pow (q := q) hq hn
  have hcm := nnnorm_one_add_pow (q := q) hq hm
  have hq_pos : (0 : ℝ≥0) < ‖q‖₊ := by
    simpa [pos_iff_ne_zero, nnnorm_eq_zero] using hq0
  have hu_ne : ‖u‖₊ ≠ 0 := by simpa [nnnorm_eq_zero] using hu0
  have hnk : ‖q‖₊ ^ k * ‖u‖₊ = 1 := by
    have := congrArg (‖·‖₊) hk
    simpa [nnnorm_mul, nnnorm_zpow, hcn, mul_assoc] using this
  have hnj : ‖q‖₊ ^ j * ‖u‖₊ = 1 := by
    have := congrArg (‖·‖₊) hj
    simpa [nnnorm_mul, nnnorm_zpow, hcm, mul_assoc] using this
  have hkj : k = j := by
    have : ‖q‖₊ ^ k = ‖q‖₊ ^ j := by
      have := hnk.trans hnj.symm
      exact mul_right_cancel₀ hu_ne this
    exact zpow_right_injective₀ hq_pos (ne_of_lt hq) this
  rw [hkj] at hk
  have hcancel : (1 : K) + q ^ n = 1 + q ^ m := by
    have hqu : (q : K) ^ j * u ≠ 0 := mul_ne_zero (zpow_ne_zero _ hq0) hu0
    apply mul_left_cancel₀ hqu
    calc q ^ j * u * (1 + q ^ n) = q ^ j * (u * (1 + q ^ n)) := by ring
      _ = 1 := hk
      _ = q ^ j * (u * (1 + q ^ m)) := hj.symm
      _ = q ^ j * u * (1 + q ^ m) := by ring
  exact one_add_pow_injective hq0 hq hcancel

private lemma lattice_div_unique (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h1 : ¬ OffLattice q (u * (1 + q ^ n)⁻¹)) (h2 : ¬ OffLattice q (u * (1 + q ^ m)⁻¹)) :
    n = m := by
  simp only [OffLattice, not_forall, not_not] at h1 h2
  obtain ⟨k, hk⟩ := h1
  obtain ⟨j, hj⟩ := h2
  have hcn := nnnorm_one_add_pow (q := q) hq hn
  have hcm := nnnorm_one_add_pow (q := q) hq hm
  have hcn0 := one_add_pow_ne_zero (q := q) hq hn
  have hcm0 := one_add_pow_ne_zero (q := q) hq hm
  have hq_pos : (0 : ℝ≥0) < ‖q‖₊ := by
    simpa [pos_iff_ne_zero, nnnorm_eq_zero] using hq0
  have hu_ne : ‖u‖₊ ≠ 0 := by simpa [nnnorm_eq_zero] using hu0
  have hnk : ‖q‖₊ ^ k * ‖u‖₊ = 1 := by
    have := congrArg (‖·‖₊) hk
    simpa [nnnorm_mul, nnnorm_zpow, nnnorm_inv, hcn, mul_assoc] using this
  have hnj : ‖q‖₊ ^ j * ‖u‖₊ = 1 := by
    have := congrArg (‖·‖₊) hj
    simpa [nnnorm_mul, nnnorm_zpow, nnnorm_inv, hcm, mul_assoc] using this
  have hkj : k = j := by
    have : ‖q‖₊ ^ k = ‖q‖₊ ^ j := by
      have := hnk.trans hnj.symm
      exact mul_right_cancel₀ hu_ne this
    exact zpow_right_injective₀ hq_pos (ne_of_lt hq) this
  rw [hkj] at hk
  have hcancel : ((1 : K) + q ^ n)⁻¹ = (1 + q ^ m)⁻¹ := by
    have hqu : (q : K) ^ j * u ≠ 0 := mul_ne_zero (zpow_ne_zero _ hq0) hu0
    apply mul_left_cancel₀ hqu
    calc q ^ j * u * (1 + q ^ n)⁻¹ = q ^ j * (u * (1 + q ^ n)⁻¹) := by ring
      _ = 1 := hk
      _ = q ^ j * (u * (1 + q ^ m)⁻¹) := hj.symm
      _ = q ^ j * u * (1 + q ^ m)⁻¹ := by ring
  exact one_add_pow_injective hq0 hq (by
    have := congrArg (·⁻¹) hcancel
    simpa [inv_inv] using this)

private lemma pair_bad_unique (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {a m m' : ℕ}
    (ha : 1 ≤ a) (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (h1 : (1 : K) + q ^ a = -(1 + q ^ m) ∨ ((1 : K) + q ^ a) * (1 + q ^ m) = -1)
    (h2 : (1 : K) + q ^ a = -(1 + q ^ m') ∨ ((1 : K) + q ^ a) * (1 + q ^ m') = -1) :
    m = m' := by
  have ha0 := one_add_pow_ne_zero (q := q) hq ha
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  ·
    have hmm' : (1 : K) + q ^ m = 1 + q ^ m' := by
      have h12 := h1.symm.trans h2
      linear_combination -h12
    exact one_add_pow_injective hq0 hq hmm'
  ·
    by_contra hne
    have hprod : ((1 : K) + q ^ m) * (1 + q ^ m') = 1 := by
      have hmul : (-(1 + q ^ m) : K) * (1 + q ^ m') = -1 := by rw [← h1]; exact h2
      linear_combination -hmul
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact one_add_pow_mul_ne_one hq0 hq hm hlt hprod
    · exact one_add_pow_mul_ne_one hq0 hq hm' hlt (by linear_combination hprod)
  ·
    by_contra hne
    have hprod : ((1 : K) + q ^ m) * (1 + q ^ m') = 1 := by
      have hmul : (-(1 + q ^ m') : K) * (1 + q ^ m) = -1 := by rw [← h2]; exact h1
      linear_combination -hmul
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact one_add_pow_mul_ne_one hq0 hq hm hlt hprod
    · exact one_add_pow_mul_ne_one hq0 hq hm' hlt (by linear_combination hprod)
  ·
    have : (1 : K) + q ^ m = 1 + q ^ m' := by
      apply mul_left_cancel₀ ha0
      rw [h1, h2]
    exact one_add_pow_injective hq0 hq this

private lemma diamondAux_of_good (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {u : K} {n : ℕ} (hn : 1 ≤ n)
    (hneg : (1 : K) + q ^ n ≠ -1)
    (hmul : OffLattice q (u * (1 + q ^ n)))
    (hdiv : OffLattice q (u * (1 + q ^ n)⁻¹)) :
    DiamondAux q u (1 + q ^ n) := by
  have hw0 := one_add_pow_ne_zero (q := q) hq hn
  have hw1 := one_add_pow_ne_one (q := q) hq0 hn
  have hwn := nnnorm_one_add_pow (q := q) hq hn
  refine ⟨hw0, hwn, offLattice_of_nnnorm_eq_one hq0 hq hwn hw1, ?_, hmul, hdiv⟩

  refine offLattice_of_nnnorm_eq_one hq0 hq (by rw [nnnorm_pow, hwn, one_pow]) ?_
  intro hsq
  have hfact : (((1 : K) + q ^ n) - 1) * ((1 + q ^ n) + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfact with h' | h'
  · exact hw1 (by linear_combination h')
  · exact hneg (by linear_combination h')

private lemma exists_diamond_aux (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {u : K} (hu0 : u ≠ 0) :
    ∃ w₁ w₂ : K, DiamondAux q u w₁ ∧ DiamondAux q u w₂ ∧
      w₁ ^ 2 ≠ w₂ ^ 2 ∧ w₁ ^ 2 * w₂ ^ 2 ≠ 1 := by
  classical

  have pick₁ : ∃ n : ℕ, (1 ≤ n ∧ n ≤ 4) ∧ ((1 : K) + q ^ n ≠ -1) ∧
      OffLattice q (u * (1 + q ^ n)) ∧ OffLattice q (u * (1 + q ^ n)⁻¹) := by
    have hgood : ∃ n ∈ Finset.Icc 1 4, n ∉
        (((Finset.Icc 1 4).filter fun n => (1 : K) + q ^ n = -1) ∪
          ((Finset.Icc 1 4).filter fun n => ¬ OffLattice q (u * (1 + q ^ n))) ∪
          ((Finset.Icc 1 4).filter fun n => ¬ OffLattice q (u * (1 + q ^ n)⁻¹))) := by
      by_contra hall
      push_neg at hall
      have hsub : Finset.Icc 1 4 ⊆
          (((Finset.Icc 1 4).filter fun n => (1 : K) + q ^ n = -1) ∪
            ((Finset.Icc 1 4).filter fun n => ¬ OffLattice q (u * (1 + q ^ n))) ∪
            ((Finset.Icc 1 4).filter fun n => ¬ OffLattice q (u * (1 + q ^ n)⁻¹))) :=
        fun n hn => hall n hn
      have hcard := Finset.card_le_card hsub
      have hc₁ : ((Finset.Icc 1 4).filter fun n => (1 : K) + q ^ n = -1).card ≤ 1 :=
        Finset.card_le_one.mpr fun a ha b hb => by
          rw [Finset.mem_filter] at ha hb
          exact one_add_pow_injective hq0 hq (ha.2.trans hb.2.symm)
      have hc₂ : ((Finset.Icc 1 4).filter fun n =>
          ¬ OffLattice q (u * (1 + q ^ n))).card ≤ 1 :=
        Finset.card_le_one.mpr fun a ha b hb => by
          rw [Finset.mem_filter, Finset.mem_Icc] at ha hb
          exact lattice_mul_unique hq0 hq hu0 ha.1.1 hb.1.1 ha.2 hb.2
      have hc₃ : ((Finset.Icc 1 4).filter fun n =>
          ¬ OffLattice q (u * (1 + q ^ n)⁻¹)).card ≤ 1 :=
        Finset.card_le_one.mpr fun a ha b hb => by
          rw [Finset.mem_filter, Finset.mem_Icc] at ha hb
          exact lattice_div_unique hq0 hq hu0 ha.1.1 hb.1.1 ha.2 hb.2
      have hpair := Finset.card_union_le
        ((Finset.Icc 1 4).filter fun n => (1 : K) + q ^ n = -1)
        ((Finset.Icc 1 4).filter fun n => ¬ OffLattice q (u * (1 + q ^ n)))
      have htriple := Finset.card_union_le
        (((Finset.Icc 1 4).filter fun n => (1 : K) + q ^ n = -1) ∪
          ((Finset.Icc 1 4).filter fun n => ¬ OffLattice q (u * (1 + q ^ n))))
        ((Finset.Icc 1 4).filter fun n => ¬ OffLattice q (u * (1 + q ^ n)⁻¹))
      rw [Nat.card_Icc] at hcard
      omega
    obtain ⟨n, hnmem, hnot⟩ := hgood
    have hn := Finset.mem_Icc.mp hnmem
    simp only [Finset.mem_union, Finset.mem_filter, not_or, not_and, not_not] at hnot
    exact ⟨n, hn, hnot.1.1 hnmem, hnot.1.2 hnmem, hnot.2 hnmem⟩
  obtain ⟨n₁, hn₁, hg₁neg, hg₁mul, hg₁div⟩ := pick₁

  have pick₂ : ∃ m : ℕ, (n₁ + 1 ≤ m ∧ m ≤ n₁ + 5) ∧ ((1 : K) + q ^ m ≠ -1) ∧
      OffLattice q (u * (1 + q ^ m)) ∧ OffLattice q (u * (1 + q ^ m)⁻¹) ∧
      ¬((1 : K) + q ^ n₁ = -(1 + q ^ m) ∨ ((1 : K) + q ^ n₁) * (1 + q ^ m) = -1) := by
    have hgood : ∃ m ∈ Finset.Icc (n₁ + 1) (n₁ + 5), m ∉
        ((((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m => (1 : K) + q ^ m = -1) ∪
          ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m =>
            ¬ OffLattice q (u * (1 + q ^ m))) ∪
          ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m =>
            ¬ OffLattice q (u * (1 + q ^ m)⁻¹))) ∪
          ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m =>
            (1 : K) + q ^ n₁ = -(1 + q ^ m) ∨ ((1 : K) + q ^ n₁) * (1 + q ^ m) = -1)) := by
      by_contra hall
      push_neg at hall
      have hsub : Finset.Icc (n₁ + 1) (n₁ + 5) ⊆
          ((((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m => (1 : K) + q ^ m = -1) ∪
            ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m =>
              ¬ OffLattice q (u * (1 + q ^ m))) ∪
            ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m =>
              ¬ OffLattice q (u * (1 + q ^ m)⁻¹))) ∪
            ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m =>
              (1 : K) + q ^ n₁ = -(1 + q ^ m) ∨ ((1 : K) + q ^ n₁) * (1 + q ^ m) = -1)) :=
        fun m hm => hall m hm
      have hcard := Finset.card_le_card hsub
      have hc₁ : ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m =>
          (1 : K) + q ^ m = -1).card ≤ 1 :=
        Finset.card_le_one.mpr fun a ha b hb => by
          rw [Finset.mem_filter] at ha hb
          exact one_add_pow_injective hq0 hq (ha.2.trans hb.2.symm)
      have hc₂ : ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m =>
          ¬ OffLattice q (u * (1 + q ^ m))).card ≤ 1 :=
        Finset.card_le_one.mpr fun a ha b hb => by
          rw [Finset.mem_filter, Finset.mem_Icc] at ha hb
          exact lattice_mul_unique hq0 hq hu0 (by omega) (by omega) ha.2 hb.2
      have hc₃ : ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m =>
          ¬ OffLattice q (u * (1 + q ^ m)⁻¹)).card ≤ 1 :=
        Finset.card_le_one.mpr fun a ha b hb => by
          rw [Finset.mem_filter, Finset.mem_Icc] at ha hb
          exact lattice_div_unique hq0 hq hu0 (by omega) (by omega) ha.2 hb.2
      have hc₄ : ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m =>
          (1 : K) + q ^ n₁ = -(1 + q ^ m) ∨
            ((1 : K) + q ^ n₁) * (1 + q ^ m) = -1).card ≤ 1 :=
        Finset.card_le_one.mpr fun a ha b hb => by
          rw [Finset.mem_filter, Finset.mem_Icc] at ha hb
          exact pair_bad_unique hq0 hq hn₁.1 (by omega) (by omega) ha.2 hb.2
      have hpairc := Finset.card_union_le
        ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m => (1 : K) + q ^ m = -1)
        ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m => ¬ OffLattice q (u * (1 + q ^ m)))
      have htriple := Finset.card_union_le
        (((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m => (1 : K) + q ^ m = -1) ∪
          ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m =>
            ¬ OffLattice q (u * (1 + q ^ m))))
        ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m =>
          ¬ OffLattice q (u * (1 + q ^ m)⁻¹))
      have hquad := Finset.card_union_le
        ((((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m => (1 : K) + q ^ m = -1) ∪
          ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m =>
            ¬ OffLattice q (u * (1 + q ^ m)))) ∪
          ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m =>
            ¬ OffLattice q (u * (1 + q ^ m)⁻¹)))
        ((Finset.Icc (n₁ + 1) (n₁ + 5)).filter fun m =>
          (1 : K) + q ^ n₁ = -(1 + q ^ m) ∨ ((1 : K) + q ^ n₁) * (1 + q ^ m) = -1)
      rw [Nat.card_Icc] at hcard
      omega
    obtain ⟨m, hmmem, hnot⟩ := hgood
    have hm := Finset.mem_Icc.mp hmmem
    simp only [Finset.mem_union, Finset.mem_filter, not_or, not_and, not_not] at hnot
    refine ⟨m, hm, hnot.1.1.1 hmmem, hnot.1.1.2 hmmem, hnot.1.2 hmmem, ?_⟩
    intro hbad
    rcases hbad with hbad | hbad
    · exact (hnot.2 hmmem).1 hbad
    · exact (hnot.2 hmmem).2 hbad
  obtain ⟨n₂, hn₂, hg₂neg, hg₂mul, hg₂div, hpairgood⟩ := pick₂
  push_neg at hpairgood

  have hn₂1 : 1 ≤ n₂ := by omega
  have hne : n₁ ≠ n₂ := by omega
  refine ⟨1 + q ^ n₁, 1 + q ^ n₂,
    diamondAux_of_good hq0 hq hn₁.1 hg₁neg hg₁mul hg₁div,
    diamondAux_of_good hq0 hq hn₂1 hg₂neg hg₂mul hg₂div, ?_, ?_⟩
  ·
    intro hsq
    have hfact : (((1 : K) + q ^ n₁) - (1 + q ^ n₂)) * ((1 + q ^ n₁) + (1 + q ^ n₂)) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfact with h' | h'
    · exact hne (one_add_pow_injective hq0 hq (by linear_combination h'))
    · exact hpairgood.1 (by linear_combination h')
  ·
    intro hsq
    have hfact : (((1 : K) + q ^ n₁) * (1 + q ^ n₂) - 1) *
        ((1 + q ^ n₁) * (1 + q ^ n₂) + 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfact with h' | h'
    · have hone : ((1 : K) + q ^ n₁) * (1 + q ^ n₂) = 1 := by linear_combination h'
      exact one_add_pow_mul_ne_one hq0 hq hn₁.1 (by omega) hone
    · exact hpairgood.2 (by linear_combination h')

end AuxiliarySupply

private lemma diamond_branch (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hsum : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        symSumNum q (pointX q u) (pointX q v))
    (hprod : ∀ u v : K, AddParams q u v →
      pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 =
        symProdNum q (pointX q u) (pointX q v))
    {u w : K} (hu0 : u ≠ 0) (hu : OffLattice q u) (hu2 : OffLattice q (u ^ 2))
    (hw : DiamondAux q u w) :
    pointX q (u ^ 2) * ((curve q).Ψ₂Sq).eval (pointX q u) =
      ((curve q).Φ 2).eval (pointX q u) ∨
    ((curve q).Φ 2).eval (pointX q u) =
      pointX q (w ^ 2) * ((curve q).Ψ₂Sq).eval (pointX q u) := by
  have hw0 : w ≠ 0 := hw.ne_zero

  have hAPA : AddParams q u w :=
    ⟨hq0, hu0, hw0, hu, hw.offLattice, hw.offLattice_mul, hw.offLattice_div⟩
  have hmul0 : u * w ≠ 0 := mul_ne_zero hu0 hw0
  have hdiv0 : u * w⁻¹ ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hw0)
  have hBmul : (u * w) * (u * w⁻¹) = u ^ 2 := by
    field_simp
  have hBdiv : (u * w) * (u * w⁻¹)⁻¹ = w ^ 2 := by
    rw [mul_inv, inv_inv]
    field_simp
  have hAPB : AddParams q (u * w) (u * w⁻¹) := by
    refine ⟨hq0, hmul0, hdiv0, hw.offLattice_mul, hw.offLattice_div, ?_, ?_⟩
    · rw [hBmul]; exact hu2
    · rw [hBdiv]; exact hw.offLattice_sq

  have hA1 := hsum u w hAPA
  have hA2 := hprod u w hAPA
  have hB1 := hsum (u * w) (u * w⁻¹) hAPB
  have hB2 := hprod (u * w) (u * w⁻¹) hAPB
  rw [hBmul, hBdiv] at hB1 hB2
  set x := pointX q u with hxdef
  set y := pointX q w with hydef
  set s := pointX q (u * w) with hsdef
  set t := pointX q (u * w⁻¹) with htdef
  set D := pointX q (u ^ 2) with hDdef
  set E := pointX q (w ^ 2) with hEdef
  set Ψx := ((curve q).Ψ₂Sq).eval x with hΨdef
  set Φx := ((curve q).Φ 2).eval x with hΦdef

  have hxy : x ≠ y := by
    intro hxe
    have e1 : symSumNum q x y = 0 := by rw [← hA1, hxe]; ring
    have e2 : symProdNum q x y = 0 := by rw [← hA2, hxe]; ring
    rw [hxe] at e1 e2
    rw [symSumNum_self] at e1
    rw [symProdNum_self] at e2
    exact not_both_eval_eq_zero hq0 hq e1 e2

  have hst : s ≠ t := by
    intro hse
    have e1 : symSumNum q s t = 0 := by rw [← hB1, hse]; ring
    have e2 : symProdNum q s t = 0 := by rw [← hB2, hse]; ring
    rw [hse] at e1 e2
    rw [symSumNum_self] at e1
    rw [symProdNum_self] at e2
    exact not_both_eval_eq_zero hq0 hq e1 e2

  have hG : symProdNum q s t * Ψx ^ 2 - symSumNum q s t * Ψx * Φx + (s - t) ^ 2 * Φx ^ 2 = 0 := by
    have h := quad_transfer (q := q) x y s t hA1 hA2
    have hd2 : ((x - y) ^ 2) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (sub_ne_zero.mpr hxy))
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' hd2

  have hfact : (s - t) ^ 2 * ((Φx - D * Ψx) * (Φx - E * Ψx)) = 0 := by
    linear_combination hG - Ψx * Φx * hB1 + Ψx ^ 2 * hB2
  have hst2 : (s - t) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hst)
  have hsplit : (Φx - D * Ψx) * (Φx - E * Ψx) = 0 := by
    rcases mul_eq_zero.mp hfact with h' | h'
    · exact absurd h' hst2
    · exact h'
  rcases mul_eq_zero.mp hsplit with h' | h'
  · left; linear_combination -h'
  · right; linear_combination h'

theorem dbl_of_symAdd_sum_prod (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hsum : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        symSumNum q (pointX q u) (pointX q v))
    (hprod : ∀ u v : K, AddParams q u v →
      pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 =
        symProdNum q (pointX q u) (pointX q v)) :
    ∀ u : K, u ≠ 0 → OffLattice q u → OffLattice q (u ^ 2) →
      pointX q (u ^ 2) * ((curve q).Ψ₂Sq).eval (pointX q u) =
        ((curve q).Φ 2).eval (pointX q u) := by
  intro u hu0 hu hu2
  obtain ⟨w₁, w₂, haux₁, haux₂, hsqne, hsqprod⟩ := exists_diamond_aux hq0 hq (u := u) hu0

  rcases diamond_branch hq0 hq hsum hprod hu0 hu hu2 haux₁ with hdone | hbad₁
  · exact hdone
  rcases diamond_branch hq0 hq hsum hprod hu0 hu hu2 haux₂ with hdone | hbad₂
  · exact hdone

  have hw₁sq0 : w₁ ^ 2 ≠ 0 := pow_ne_zero _ haux₁.ne_zero
  have hw₂sq0 : w₂ ^ 2 ≠ 0 := pow_ne_zero _ haux₂.ne_zero
  have hEne : pointX q (w₁ ^ 2) ≠ pointX q (w₂ ^ 2) := by
    intro hEq
    have hnorm₁ : ‖w₁ ^ 2‖ ≤ 1 := by
      have : ‖w₁ ^ 2‖₊ = 1 := by rw [nnnorm_pow, haux₁.nnnorm_eq, one_pow]
      simp [← coe_nnnorm, this]
    have hnorm₂ : ‖w₂ ^ 2‖ ≤ 1 := by
      have : ‖w₂ ^ 2‖₊ = 1 := by rw [nnnorm_pow, haux₂.nnnorm_eq, one_pow]
      simp [← coe_nnnorm, this]
    have hnormprod : ‖q‖ < ‖w₁ ^ 2 * w₂ ^ 2‖ := by
      have h1 : ‖w₁ ^ 2 * w₂ ^ 2‖₊ = 1 := by
        rw [nnnorm_mul, nnnorm_pow, nnnorm_pow, haux₁.nnnorm_eq, haux₂.nnnorm_eq]
        simp
      have h2 : ‖w₁ ^ 2 * w₂ ^ 2‖ = 1 := by
        simpa [← coe_nnnorm] using congrArg (NNReal.toReal) h1
      rw [h2]
      exact_mod_cast hq
    rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq hw₁sq0 hw₂sq0
        haux₁.offLattice_sq haux₂.offLattice_sq hnorm₁ hnorm₂ hnormprod hEq with h | h
    · exact hsqne h
    · exact hsqprod h
  have hΨ0 : ((curve q).Ψ₂Sq).eval (pointX q u) = 0 := by
    have hkey : (pointX q (w₁ ^ 2) - pointX q (w₂ ^ 2)) *
        ((curve q).Ψ₂Sq).eval (pointX q u) = 0 := by
      linear_combination hbad₂ - hbad₁
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd (sub_eq_zero.mp h) hEne
    · exact h
  have hΦ0 : ((curve q).Φ 2).eval (pointX q u) = 0 := by
    rw [hbad₁, hΨ0, mul_zero]
  exact absurd hΦ0 (fun hΦ0 => not_both_eval_eq_zero hq0 hq hΨ0 hΦ0)

theorem symAddHyps_of_sum_prod (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hsum : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        symSumNum q (pointX q u) (pointX q v))
    (hprod : ∀ u v : K, AddParams q u v →
      pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 =
        symProdNum q (pointX q u) (pointX q v)) :
    SymAddHyps q :=
  ⟨hsum, hprod, dbl_of_symAdd_sum_prod hq0 hq hsum hprod⟩

end TateCurve

set_option linter.unusedSectionVars false

open Polynomial
open scoped NNReal

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u v : K}

theorem two_mul_pointY_add_pointX_sq (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : OffLattice q u) :
    (2 * pointY q u + pointX q u) ^ 2 =
      4 * pointX q u ^ 3 + pointX q u ^ 2 + 4 * a₄ q * pointX q u + 4 * a₆ q := by
  have h := equation_pointX_pointY hq0 hq hu0 hu
  linear_combination 4 * h

theorem two_mul_pointY_add_pointX_sq_eq_eval_Ψ₂Sq (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : OffLattice q u) :
    (2 * pointY q u + pointX q u) ^ 2 = ((curve q).Ψ₂Sq).eval (pointX q u) := by
  have hΨ : ((curve q).Ψ₂Sq).eval (pointX q u) =
      4 * pointX q u ^ 3 + pointX q u ^ 2 + 4 * a₄ q * pointX q u + 4 * a₆ q := by
    rw [WeierstrassCurve.Affine.eval_Ψ₂Sq, curve_b₂, curve_b₄, curve_b₆]; ring
  rw [hΨ]
  exact two_mul_pointY_add_pointX_sq hq0 hq hu0 hu

theorem symSumNum_sq_sub_quartic_mul_quartic (q x₁ x₂ : K) :
    symSumNum q x₁ x₂ ^ 2 -
        (4 * x₁ ^ 3 + x₁ ^ 2 + 4 * a₄ q * x₁ + 4 * a₆ q) *
          (4 * x₂ ^ 3 + x₂ ^ 2 + 4 * a₄ q * x₂ + 4 * a₆ q) =
      4 * (x₁ - x₂) ^ 2 * symProdNum q x₁ x₂ := by
  simp only [symSumNum, symProdNum]; ring

section PerPair

theorem symAdd_prod_of_sum_of_diff_sq (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hu0 : u ≠ 0) (hu : OffLattice q u) (hv0 : v ≠ 0) (hv : OffLattice q v)
    (hne : pointX q u ≠ pointX q v)
    (hsum : (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v))
    (hdiffsq : ((pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2) ^ 2 =
      ((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)) ^ 2) :
    pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 =
      symProdNum q (pointX q u) (pointX q v) := by
  have hQ1 := two_mul_pointY_add_pointX_sq hq0 hq hu0 hu
  have hQ2 := two_mul_pointY_add_pointX_sq hq0 hq hv0 hv
  have hsumsq : ((pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2) ^ 2 =
      symSumNum q (pointX q u) (pointX q v) ^ 2 := by rw [hsum]

  have key : (4 : K) * (pointX q u - pointX q v) ^ 2 *
      (pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 -
        symProdNum q (pointX q u) (pointX q v)) = 0 := by
    simp only [symSumNum] at hsumsq
    simp only [symProdNum]
    linear_combination hsumsq - hdiffsq
      - (2 * pointY q v + pointX q v) ^ 2 * hQ1
      - (4 * pointX q u ^ 3 + pointX q u ^ 2 + 4 * a₄ q * pointX q u + 4 * a₆ q) * hQ2

  have h4 : (4 : K) ≠ 0 := by norm_num
  have hΔ : (pointX q u - pointX q v) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hne)
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 (mul_ne_zero h4 hΔ)
  · exact sub_eq_zero.mp h0

theorem symAdd_prod_of_sum_of_diff (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hu0 : u ≠ 0) (hu : OffLattice q u) (hv0 : v ≠ 0) (hv : OffLattice q v)
    (hne : pointX q u ≠ pointX q v)
    (hsum : (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v))
    (hdiff : (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v))) :
    pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 =
      symProdNum q (pointX q u) (pointX q v) :=
  symAdd_prod_of_sum_of_diff_sq hq0 hq hu0 hu hv0 hv hne hsum (by rw [hdiff]; ring)

theorem symAdd_prod_of_sum_of_diff' (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hu0 : u ≠ 0) (hu : OffLattice q u) (hv0 : v ≠ 0) (hv : OffLattice q v)
    (hne : pointX q u ≠ pointX q v)
    (hsum : (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v))
    (hdiff : (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      (2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)) :
    pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 =
      symProdNum q (pointX q u) (pointX q v) :=
  symAdd_prod_of_sum_of_diff_sq hq0 hq hu0 hu hv0 hv hne hsum (by rw [hdiff])

end PerPair

section Forall

theorem symAdd_prod_of_sum_diff_forall (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hsum : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        symSumNum q (pointX q u) (pointX q v))
    (hdiff : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)))
    (hsep : ∀ u v : K, AddParams q u v →
      2 * pointY q u + pointX q u = 0 → 2 * pointY q v + pointX q v = 0 →
      pointX q u ≠ pointX q v) :
    ∀ u v : K, AddParams q u v →
      pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 =
        symProdNum q (pointX q u) (pointX q v) := by
  intro u v h
  by_cases hne : pointX q u = pointX q v
  ·

    exfalso
    have hS1 := hsum u v h
    have hQ1 := two_mul_pointY_add_pointX_sq hq0 hq h.u_ne_zero h.offLattice_u
    have hQ2 := two_mul_pointY_add_pointX_sq hq0 hq h.v_ne_zero h.offLattice_v
    have hzero : symSumNum q (pointX q u) (pointX q u) = 0 := by
      have h2 : (pointX q u - pointX q v) ^ 2 = 0 := by rw [hne]; ring
      calc symSumNum q (pointX q u) (pointX q u)
          = symSumNum q (pointX q u) (pointX q v) := by rw [hne]
        _ = (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 := hS1.symm
        _ = 0 := by rw [h2, mul_zero]
    have hpsiu : 2 * pointY q u + pointX q u = 0 := by
      have hsq : (2 * pointY q u + pointX q u) ^ 2 = 0 := by
        rw [hQ1]
        simp only [symSumNum] at hzero
        linear_combination hzero
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    have hpsiv : 2 * pointY q v + pointX q v = 0 := by
      have hsq : (2 * pointY q v + pointX q v) ^ 2 = 0 := by
        rw [hQ2, ← hne]
        simp only [symSumNum] at hzero
        linear_combination hzero
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    exact hsep u v h hpsiu hpsiv hne
  · exact symAdd_prod_of_sum_of_diff hq0 hq h.u_ne_zero h.offLattice_u h.v_ne_zero
      h.offLattice_v hne (hsum u v h) (hdiff u v h)

theorem symAddHyps_of_sum_diff (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hsum : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        symSumNum q (pointX q u) (pointX q v))
    (hdiff : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)))
    (hsep : ∀ u v : K, AddParams q u v →
      2 * pointY q u + pointX q u = 0 → 2 * pointY q v + pointX q v = 0 →
      pointX q u ≠ pointX q v) :
    SymAddHyps q :=
  symAddHyps_of_sum_prod hq0 hq hsum (symAdd_prod_of_sum_diff_forall hq0 hq hsum hdiff hsep)

theorem symAddHyps_of_sum_diff_of_ne (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hsum : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        symSumNum q (pointX q u) (pointX q v))
    (hdiff : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)))
    (hne : ∀ u v : K, AddParams q u v → pointX q u ≠ pointX q v) :
    SymAddHyps q :=
  symAddHyps_of_sum_diff hq0 hq hsum hdiff (fun u v h _ _ => hne u v h)

end Forall

end TateCurve


