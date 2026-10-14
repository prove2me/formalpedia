-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0475_parallel1
-- name    : PNT_ZeroFree_433_0475_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:13:38.169691+00:00
-- url     : https://prove2.me/theorems/feb81949-14d6-427d-b793-247a1744f5ef
-- title:
--   Zero-free region foundations: CubicDyadicDecay, HeathBrownIteration [0475_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicDyadicDecay
--   - OAI.NumberTheory.DirichletL.HeathBrownIteration
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicDyadicDecay.lean#L16-L325
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/HeathBrownIteration.lean#L14-L83

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_PNT_ZeroFree_433_0145
import Definitions.Def_PNT_ZeroFree_433_0152
import Definitions.Def_PNT_ZeroFree_433_0250_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicDyadicDecay.lean#L16-L325
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/HeathBrownIteration.lean#L14-L83
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicDyadicDecay
section
namespace OAI

namespace SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section

def decayConstant (α : ℝ) : ℝ :=
  (2 : ℝ)^α / ((2 : ℝ)^α - 1) + (1 - (2 : ℝ)^(α - 3))⁻¹

lemma dyadic_rpow (α : ℝ) (j : ℕ) :
    ((2 : ℝ)^j)^α = ((2 : ℝ)^α)^j := by
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm,
    Real.rpow_mul_natCast (by norm_num)]

lemma decay_le_low (t α : ℝ) (ht : 0 < t) (j : ℕ) :
    ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3 ≤ ((2 : ℝ)^α)^j := by
  rw [← dyadic_rpow]
  exact div_le_self (by positivity) (one_le_pow₀ (by
    have : 0 ≤ t * (2 : ℝ)^j := by positivity
    linarith))

lemma decay_le_high (t α : ℝ) (ht : 0 < t) (j : ℕ) :
    ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3 ≤
      t^(-3 : ℝ) * ((2 : ℝ)^(α - 3))^j := by
  have hk : 0 < (2 : ℝ)^j := by positivity
  calc
    _ ≤ ((2 : ℝ)^j)^α / (t * (2 : ℝ)^j)^3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) (by linarith) 3)
    _ = _ := by
      rw [← dyadic_rpow, Real.rpow_sub hk, Real.rpow_neg ht.le, mul_pow]
      simp only [Real.rpow_ofNat]
      try ring

lemma decay_summable (t α : ℝ) (ht : 0 < t) (hα : α < 3) :
    Summable (fun j : ℕ => ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) := by
  have hr : (2 : ℝ)^(α - 3) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact ((summable_geometric_of_lt_one (by positivity) hr).mul_left (t^(-3 : ℝ))).of_nonneg_of_le
    (fun j => by positivity) (decay_le_high t α ht)

lemma decayConstant_pos (α : ℝ) (hα : 0 < α) (hα3 : α < 3) :
    0 < decayConstant α := by
  have hq : 1 < (2 : ℝ)^α := Real.one_lt_rpow (by norm_num) hα
  have hr : (2 : ℝ)^(α - 3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  unfold decayConstant
  positivity

lemma geometric_prefix_le (q : ℝ) (hq : 1 < q) (k : ℕ) :
    (∑ j ∈ Finset.range k, q^j) ≤ q^k / (q - 1) := by
  rw [geom_sum_eq (ne_of_gt hq)]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

lemma decay_tail_le (t α : ℝ) (ht : 0 < t) (hα3 : α < 3) (k : ℕ) :
    (∑' j : ℕ, ((2 : ℝ)^(j+k))^α / (1 + t * (2 : ℝ)^(j+k))^3) ≤
      t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^k * (1 - (2 : ℝ)^(α-3))⁻¹ := by
  have hr0 : 0 ≤ (2 : ℝ)^(α-3) := by positivity
  have hr : (2 : ℝ)^(α-3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hs := summable_geometric_of_lt_one hr0 hr
  calc
    _ ≤ ∑' j : ℕ, t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^(j+k) := by
      apply (decay_summable t α ht hα3).comp_injective (add_left_injective k) |>.tsum_le_tsum
        (fun j => decay_le_high t α ht (j+k))
      exact (hs.comp_injective (add_left_injective k)).mul_left _
    _ = _ := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hr0 hr]
      try ring

theorem dyadic_decay_bound (t α : ℝ) (ht : 0 < t) (hα : 0 < α) (hα3 : α < 3) :
    (∑' j : ℕ, ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) ≤
      decayConstant α * t^(-α) := by
  have hq : 1 < (2 : ℝ)^α := Real.one_lt_rpow (by norm_num) hα
  have hr : (2 : ℝ)^(α-3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < (1 - (2 : ℝ)^(α-3))⁻¹ := inv_pos.mpr (by linarith)
  by_cases ht1 : 1 ≤ t
  · have hp : t^(-3 : ℝ) ≤ t^(-α) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    have hh := decay_tail_le t α ht hα3 0
    simp only [Nat.add_zero, pow_zero, mul_one] at hh
    apply hh.trans
    unfold decayConstant
    nlinarith [mul_nonneg (div_nonneg (by positivity : 0 ≤ (2 : ℝ)^α)
      (by linarith : 0 ≤ (2 : ℝ)^α - 1)) (by positivity : 0 ≤ t^(-α)),
      mul_le_mul_of_nonneg_right hp hden.le]
  · have hit : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr (le_of_not_ge ht1)
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hit (by norm_num : (1 : ℝ) < 2)
    let k := n+1
    have hk0 : 0 < (2 : ℝ)^k := by positivity
    have hk : t⁻¹ ≤ (2 : ℝ)^k := le_of_lt hn'
    have hk' : (2 : ℝ)^k ≤ 2*t⁻¹ := by
      dsimp [k]
      rw [pow_succ]
      nlinarith
    have hlow : (∑ j ∈ Finset.range k,
        ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) ≤
        (2 : ℝ)^α / ((2 : ℝ)^α - 1) * t^(-α) := by
      calc
        _ ≤ ∑ j ∈ Finset.range k, ((2 : ℝ)^α)^j :=
          Finset.sum_le_sum (fun j hj => decay_le_low t α ht j)
        _ ≤ ((2 : ℝ)^α)^k / ((2 : ℝ)^α - 1) := geometric_prefix_le _ hq k
        _ ≤ (2*t⁻¹)^α / ((2 : ℝ)^α - 1) := by
          rw [← dyadic_rpow]
          exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hk0.le hk' hα.le)
            (by linarith)
        _ = _ := by
          rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr ht.le),
            ← Real.rpow_neg_eq_inv_rpow]
          try ring
    have hhigh : t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^k ≤ t^(-α) := by
      rw [← dyadic_rpow]
      calc
        _ ≤ t^(-3 : ℝ) * (t⁻¹)^(α-3) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (inv_pos.mpr ht)
            hk (by linarith)) (by positivity)
        _ = _ := by
          rw [← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_add ht]
          congr 1
          try ring
    rw [← (decay_summable t α ht hα3).sum_add_tsum_nat_add k]
    have htail := (decay_tail_le t α ht hα3 k).trans
      (mul_le_mul_of_nonneg_right hhigh hden.le)
    unfold decayConstant
    nlinarith

theorem two_power_majorant (B : ℝ → ℝ) (C P Q t α β : ℝ)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (ht : 0 < t)
    (hα : 0 < α) (hα3 : α < 3) (hβ : 0 < β) (hβ3 : β < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ C * (P*K^α + Q*K^β)) :
    Summable (fun j : ℕ => B ((2 : ℝ)^j) / (1 + t*(2 : ℝ)^j)^3) ∧
    (∑' j : ℕ, B ((2 : ℝ)^j) / (1 + t*(2 : ℝ)^j)^3) ≤
      C * (P*decayConstant α*t^(-α) + Q*decayConstant β*t^(-β)) := by
  let f (γ : ℝ) (j : ℕ) := ((2 : ℝ)^j)^γ / (1+t*(2 : ℝ)^j)^3
  have hsα : Summable (f α) := decay_summable t α ht hα3
  have hsβ : Summable (f β) := decay_summable t β ht hβ3
  have hs : Summable (fun j => C*(P*f α j+Q*f β j)) :=
    ((hsα.mul_left P).add (hsβ.mul_left Q)).mul_left C
  have hle (j : ℕ) : B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3 ≤
      C*(P*f α j+Q*f β j) := by
    have hi := div_le_div_of_nonneg_right (hB ((2 : ℝ)^j)
      (one_le_pow₀ (by norm_num))) (by positivity : 0 ≤ (1+t*(2 : ℝ)^j)^3)
    dsimp [f]
    convert! hi using 1
    try ring
  have hsum := hs.of_nonneg_of_le
    (fun j => div_nonneg (hB0 _ (one_le_pow₀ (by norm_num))) (by positivity)) hle
  refine ⟨hsum, (hsum.tsum_le_tsum hle hs).trans ?_⟩
  rw [tsum_mul_left, (hsα.mul_left P).tsum_add (hsβ.mul_left Q), tsum_mul_left,
    tsum_mul_left]
  apply mul_le_mul_of_nonneg_left _ hC
  have h₁ := mul_le_mul_of_nonneg_left (dyadic_decay_bound t α ht hα hα3) hP
  have h₂ := mul_le_mul_of_nonneg_left (dyadic_decay_bound t β ht hβ hβ3) hQ
  dsimp [f] at *
  nlinarith

theorem sieve_growth_majorant (B : ℝ → ℝ) (A N t δ ξ : ℝ)
    (hA : 0 ≤ A) (hN : 0 < N) (ht : 0 < t)
    (hα : 0 < 1/3+δ) (hα3 : 1/3+δ < 3)
    (hβ : 0 < ξ+δ) (hβ3 : ξ+δ < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ A*(K*N)^δ*(N*K^(1/3 : ℝ)+K^ξ)) :
    Summable (fun j : ℕ => B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3) ∧
    (∑' j : ℕ, B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3) ≤
      A*N^δ * (N*decayConstant (1/3+δ)*t^(-(1/3+δ)) +
        decayConstant (ξ+δ)*t^(-(ξ+δ))) := by
  have hh := two_power_majorant B (A*N^δ) N 1 t (1/3+δ) (ξ+δ)
    (by positivity) hN.le (by norm_num) ht hα hα3 hβ hβ3 hB0
  simp only [one_mul] at hh
  apply hh
  intro K hK
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  apply (hB K hK).trans_eq
  rw [Real.mul_rpow hK0.le hN.le, Real.rpow_add hK0, Real.rpow_add hK0]
  try ring

lemma poisson_scale_identity (M N α : ℝ) (hM : 0 < M) (hN : 0 < N) :
    M/N * (M/N^2)^(-α) = M^(1-α) * N^(2*α-1) := by
  rw [Real.div_rpow hM.le (sq_nonneg N), Real.rpow_neg hM.le,
    Real.rpow_neg (sq_nonneg N), div_inv_eq_mul,
    ← Real.rpow_natCast_mul hN.le 2 α, Real.rpow_sub hM,
    Real.rpow_sub hN, Real.rpow_one, Real.rpow_one]
  norm_num
  try ring

lemma poisson_small_power_identity (M N δ β : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^δ * (M/N) * (M/N^2)^(-(β+δ)) =
      N^(3*δ)*M^(-δ)*M^(1-β)*N^(2*β-1) := by
  rw [mul_assoc, poisson_scale_identity M N (β+δ) hM hN]
  calc
    _ = M^(1-(β+δ)) * (N^δ*N^(2*(β+δ)-1)) := by ring
    _ = M^(-δ+(1-β)) * N^(3*δ+(2*β-1)) := by
      rw [← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> ring
    _ = _ := by rw [Real.rpow_add hM, Real.rpow_add hN]; ring

theorem sieve_poisson_bound (B : ℝ → ℝ) (A M N δ ξ : ℝ)
    (hA : 0 ≤ A) (hM : 0 < M) (hN : 0 < N)
    (hα : 0 < 1/3+δ) (hα3 : 1/3+δ < 3)
    (hβ : 0 < ξ+δ) (hβ3 : ξ+δ < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ A*(K*N)^δ*(N*K^(1/3 : ℝ)+K^ξ)) :
    (M/N) * (∑' j : ℕ, B ((2 : ℝ)^j) / (1+M*(2 : ℝ)^j/N^2)^3) ≤
      A*N^(3*δ)*M^(-δ) *
        (decayConstant (1/3+δ)*(M*N)^(2/3 : ℝ) +
          decayConstant (ξ+δ)*M^(1-ξ)*N^(2*ξ-1)) := by
  have ht : 0 < M/N^2 := by positivity
  have hh := (sieve_growth_majorant B A N (M/N^2) δ ξ hA hN ht
    hα hα3 hβ hβ3 hB0 hB).2
  have hden : (fun j : ℕ => B ((2 : ℝ)^j)/(1+(M/N^2)*(2 : ℝ)^j)^3) =
      (fun j : ℕ => B ((2 : ℝ)^j)/(1+M*(2 : ℝ)^j/N^2)^3) := by
    funext j
    congr 2
    try ring
  rw [hden] at hh
  apply (mul_le_mul_of_nonneg_left hh (div_pos hM hN).le).trans_eq
  have hid₁ := poisson_small_power_identity M N δ (1/3) hM hN
  have hid₂ := poisson_small_power_identity M N δ ξ hM hN
  have hmix : N * M^(1-(1/3 : ℝ)) * N^(2*(1/3 : ℝ)-1) =
      (M*N)^(2/3 : ℝ) := by
    norm_num
    rw [Real.mul_rpow hM.le hN.le]
    have hn' : N * N^(- (1/3 : ℝ)) = N^(2/3 : ℝ) := by
      calc
        _ = N^(1 : ℝ) * N^(-(1/3 : ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hN]; norm_num
    nlinarith [congrArg (fun x => M^(2/3 : ℝ)*x) hn']
  calc
    _ = A*N*decayConstant (1/3+δ)*(N^δ*(M/N)*(M/N^2)^(-(1/3+δ))) +
        A*decayConstant (ξ+δ)*(N^δ*(M/N)*(M/N^2)^(-(ξ+δ))) := by ring
    _ = _ := by
      rw [hid₁, hid₂]
      have he := congrArg (fun x => A*N^(3*δ)*M^(-δ)*decayConstant (1/3+δ)*x) hmix
      nlinarith [he]

lemma descent_factor_le_one (e d u v : ℝ) (he : 1 ≤ e) (hed : e ≤ d)
    (hv : v ≤ 0) (huv : u+v ≤ 0) : e^u*d^v ≤ 1 := by
  have hd : 1 ≤ d := he.trans hed
  by_cases hu : 0 ≤ u
  · calc
      _ ≤ d^u*d^v := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (by linarith) hed hu) (by positivity)
      _ = d^(u+v) := (Real.rpow_add (by linarith : 0 < d) u v).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hd huv
  · exact (mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos he (le_of_not_ge hu))
      (Real.rpow_le_one_of_one_le_of_nonpos hd hv) (by positivity) (by norm_num)).trans_eq
      (one_mul 1)

lemma monomial_descendant_le (M N e d u v : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hv : 0 ≤ v) (huv : 0 ≤ u+v) :
    (M/e)^u*(N/d)^v ≤ M^u*N^v := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  have hg := descent_factor_le_one e d (-u) (-v) he hed (by linarith) (by linarith)
  calc
    _ = (M^u*N^v)*(e^(-u)*d^(-v)) := by
      rw [Real.div_rpow hM.le he0.le, Real.div_rpow hN.le hd0.le,
        Real.rpow_neg he0.le, Real.rpow_neg hd0.le]
      try ring
    _ ≤ (M^u*N^v)*1 := mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := mul_one _

lemma mixed_monomial_identity (M N δ : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^(3*δ)*M^(-δ)*(M*N)^(2/3 : ℝ) =
      M^(2/3-δ)*N^(2/3+3*δ) := by
  rw [Real.mul_rpow hM.le hN.le]
  calc
    _ = (M^(-δ)*M^(2/3 : ℝ))*(N^(3*δ)*N^(2/3 : ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hM, ← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> ring

lemma secondary_monomial_identity (M N δ ξ : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^(3*δ)*M^(-δ)*M^(1-ξ)*N^(2*ξ-1) =
      M^(1-ξ-δ)*N^(2*ξ-1+3*δ) := by
  calc
    _ = (M^(-δ)*M^(1-ξ))*(N^(3*δ)*N^(2*ξ-1)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hM, ← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> ring

lemma mixed_descendant_le (M N e d δ : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 ≤ δ) :
    (N/d)^(3*δ)*(M/e)^(-δ)*((M/e)*(N/d))^(2/3 : ℝ) ≤
      N^(3*δ)*M^(-δ)*(M*N)^(2/3 : ℝ) := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  rw [mixed_monomial_identity (M/e) (N/d) δ (div_pos hM he0) (div_pos hN hd0),
    mixed_monomial_identity M N δ hM hN]
  exact monomial_descendant_le M N e d (2/3-δ) (2/3+3*δ) hM hN he hed
    (by linarith) (by linarith)

lemma secondary_descendant_le (M N e d δ ξ : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) :
    (N/d)^(3*δ)*(M/e)^(-δ)*(M/e)^(1-ξ)*(N/d)^(2*ξ-1) ≤
      N^(3*δ)*M^(-δ)*M^(1-ξ)*N^(2*ξ-1) := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  rw [secondary_monomial_identity (M/e) (N/d) δ ξ (div_pos hM he0) (div_pos hN hd0),
    secondary_monomial_identity M N δ ξ hM hN]
  exact monomial_descendant_le M N e d (1-ξ-δ) (2*ξ-1+3*δ) hM hN he hed
    (by linarith) (by linarith)

theorem poisson_envelope_descendant_le (M N e d δ ξ P Q : ℝ)
    (hM : 0 < M) (hN : 0 < N) (he : 1 ≤ e) (hed : e ≤ d)
    (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (N/d)^(3*δ)*(M/e)^(-δ) *
        (P*((M/e)*(N/d))^(2/3 : ℝ) + Q*(M/e)^(1-ξ)*(N/d)^(2*ξ-1)) ≤
      N^(3*δ)*M^(-δ) * (P*(M*N)^(2/3 : ℝ)+Q*M^(1-ξ)*N^(2*ξ-1)) := by
  have hm := mul_le_mul_of_nonneg_left (mixed_descendant_le M N e d δ hM hN he hed hδ) hP
  have hs := mul_le_mul_of_nonneg_left
    (secondary_descendant_le M N e d δ ξ hM hN he hed hδ hξ) hQ
  nlinarith [hm, hs]

end
end SevenEighths.CubicDyadicDecay

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.HeathBrownIteration
section
namespace OAI

namespace SevenEighths.HeathBrownIteration

noncomputable section

def step (x : ℝ) : ℝ := (6 * x - 4) / (3 * x - 1)

theorem step_sub (x : ℝ) (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 = 2 * (x - 4 / 3) / (3 * x - 1) := by
  have hd : 3 * x - 1 ≠ 0 := by linarith
  apply (eq_div_iff hd).mpr
  unfold step
  rw [sub_mul, div_mul_cancel₀ _ hd]
  ring

theorem step_gt {x : ℝ} (hx : (4 / 3 : ℝ) < x) :
    (4 / 3 : ℝ) < step x := by
  have h := step_sub x hx.le
  have hp : 0 < 2 * (x - 4 / 3) / (3 * x - 1) :=
    div_pos (mul_pos (by norm_num) (sub_pos.mpr hx)) (by linarith)
  linarith

theorem step_error_le {x : ℝ} (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 ≤ (2 / 3 : ℝ) * (x - 4 / 3) := by
  rw [step_sub x hx]
  apply (div_le_iff₀ (by linarith : 0 < 3 * x - 1)).mpr
  nlinarith [sq_nonneg (x - 4 / 3)]

theorem step_lt {x : ℝ} (hx : (4 / 3 : ℝ) < x) : step x < x := by
  have h := step_error_le hx.le
  linarith

def exponent : ℕ → ℝ
  | 0 => 2
  | n + 1 => step (exponent n)

theorem exponent_bounds (n : ℕ) :
    (4 / 3 : ℝ) < exponent n ∧ exponent n ≤ 2 := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih =>
    exact ⟨step_gt ih.1, (step_lt ih.1).le.trans ih.2⟩

theorem exponent_error_le (n : ℕ) :
    exponent n - 4 / 3 ≤ (2 / 3 : ℝ) ^ (n + 1) := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih =>
    calc
      exponent (n + 1) - 4 / 3 ≤ (2 / 3 : ℝ) * (exponent n - 4 / 3) :=
        step_error_le (exponent_bounds n).1.le
      _ ≤ (2 / 3 : ℝ) * (2 / 3 : ℝ) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (2 / 3 : ℝ) ^ (n + 1 + 1) := by rw [pow_succ]; ring

theorem exists_exponent_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, exponent n < 4 / 3 + ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 / 3 : ℝ) < 1)
  refine ⟨n, ?_⟩
  have hp : (2 / 3 : ℝ) ^ (n + 1) ≤ (2 / 3 : ℝ) ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (by norm_num) _) (by norm_num)
  have he := exponent_error_le n
  linarith

theorem finite_improvement {P : ℝ → Prop} (hstart : P 2)
    (himprove : ∀ x : ℝ, (4 / 3 : ℝ) < x → x ≤ 2 → P x → P (step x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, (4 / 3 : ℝ) < x ∧ x ≤ 2 ∧ x < 4 / 3 + ε ∧ P x := by
  have hp (n : ℕ) : P (exponent n) := by
    induction n with
    | zero => exact hstart
    | succ n ih => exact himprove _ (exponent_bounds n).1 (exponent_bounds n).2 ih
  obtain ⟨n, hn⟩ := exists_exponent_lt hε
  exact ⟨exponent n, (exponent_bounds n).1, (exponent_bounds n).2, hn, hp n⟩

end

end SevenEighths.HeathBrownIteration

end OAI

end


