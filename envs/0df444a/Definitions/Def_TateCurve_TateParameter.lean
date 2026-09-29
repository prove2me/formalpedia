-- Prove2me | Definitions.Def_TateCurve_TateParameter
-- name    : TateCurve_TateParameter
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/a732d95f-8d4c-51a6-b73d-735f6ad6ccc2
-- title:
--   The Tate parameter: inverting the j-invariant of Eq​
-- statement:
--   Throughout, $K$ is a nontrivially normed field whose norm is ultrametric and which is complete, and $E_q$ denotes the Weierstrass curve `curve q` with coefficients $(a_1,a_2,a_3,a_4,a_6)=(1,0,0,a_4(q),a_6(q))$, where $a_4(q)=-\sum_{n\ge 1}5n^3q^n/(1-q^n)$ and $a_6(q)=-\sum_{n\ge 1}b(n)q^n/(1-q^n)$ with $b(n)=(5n^3+7n^5)/12$. The first group of results records the non-archimedean size of the invariants of $E_q$ for $\lVert q\rVert<1$: $\lVert\Delta(E_q)-q\rVert\le\lVert q\rVert^2$, hence $\lVert\Delta(E_q)\rVert=\lVert q\rVert$ and $\Delta(E_q)\ne 0$ when $q\ne 0$, so $E_q$ is elliptic in Mathlib's sense; further $\lVert c_4(E_q)\rVert=1$, whence $\lVert j(E_q)\rVert=\lVert q\rVert^{-1}>1$. A second group supplies the Lipschitz machinery in the parameter: the ultrametric estimate $\lVert x^{n+1}-y^{n+1}\rVert\le\max(\lVert x\rVert,\lVert y\rVert)^n\lVert x-y\rVert$, an explicit formula for the difference of two terms of a $q$-series, the bounds $\lVert S(q_1)-S(q_2)\rVert\le\lVert q_1-q_2\rVert$ and $\lVert S(q_1)-S(q_2)-c_1(q_1-q_2)\rVert\le\max(\lVert q_1\rVert,\lVert q_2\rVert)\lVert q_1-q_2\rVert$ for the sums $S=\mathrm{coeffSum}\,c$, and the resulting estimates for $a_4$, $a_6$, $c_4$ and $\Delta$, notably $\lVert\Delta(E_{q_1})-\Delta(E_{q_2})-(q_1-q_2)\rVert\le\max(\lVert q_1\rVert,\lVert q_2\rVert)\lVert q_1-q_2\rVert$.
--
--   The definition proper is `jInversionStep j₀ q` $= c_4(E_q)^3/j_0 - (\Delta(E_q)-q)$. For $j_0\ne0$ its fixed points are exactly the $q$ with $c_4(E_q)^3=j_0\,\Delta(E_q)$; on the closed ball $\lVert q\rVert\le\lVert j_0\rVert^{-1}$ it preserves the norm $\lVert j_0\rVert^{-1}$ and is Lipschitz with constant $\lVert j_0\rVert^{-1}<1$. Banach's fixed point theorem then gives, for each $j_0$ with $\lVert j_0\rVert>1$, some $q\ne0$ with $\lVert q\rVert=\lVert j_0\rVert^{-1}$ and $c_4(E_q)^3=j_0\Delta(E_q)$; this algebraic identity is shown equivalent to $j(E_q)=j_0$, and such $q$ is unique among elements of norm $<1$. The final statements phrase this for an elliptic curve $E$ over $K$ with $\lVert j(E)\rVert>1$: there is a $q$ with $0<\lVert q\rVert<1$, $\lVert q\rVert=\lVert j(E)\rVert^{-1}$ and $j(E_q)=j(E)$. Only equality of $j$-invariants is asserted — no isomorphism of curves, and no uniformisation of points.
--
--   **Relation to Mathlib.** The curves, their $\Delta$, $c_4$, $j$ and the `IsElliptic` predicate are Mathlib's `WeierstrassCurve` notions, and the fixed point is obtained from Mathlib's `ContractingWith` theory; the Tate curve $E_q$ and its $q$-series coefficients are the project's own.
--
--   **Where it is used.** These results identify the $j$-invariant of a Tate curve with a prescribed non-integral $j_0$, the analytic input needed to recognise the Frey curve at a prime of multiplicative reduction as (a twist of) a Tate curve, and thereby to control its $\ell$-torsion Galois representation at such a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_TateCurve_TateParameter.lean

import Mathlib
import Definitions.Def_TateCurve_QSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist Filter

namespace TateCurve

section QSeriesExtras

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {q : K} [CompleteSpace K]

theorem nnnorm_Δ_sub_le (hq : ‖q‖₊ < 1) : ‖(curve q).Δ - q‖₊ ≤ ‖q‖₊ ^ 2 := by
  have ha₄ := nnnorm_a₄_le hq
  have ha₆ := nnnorm_a₆_le hq
  have ha₆q := nnnorm_a₆_add_le hq

  have hsplit : (curve q).Δ - q =
      -(a₆ q + q) + a₄ q ^ 2 + -(64 * a₄ q ^ 3) + -(432 * a₆ q ^ 2) + 72 * a₄ q * a₆ q := by
    rw [curve_Δ]; ring
  rw [hsplit]

  have hq_sq : ‖q‖₊ ^ 3 ≤ ‖q‖₊ ^ 2 := pow_le_pow_of_le_one zero_le hq.le (by norm_num)
  have h64 : ‖(64 : K)‖₊ ≤ 1 := by exact_mod_cast nnnorm_natCast_le_one K 64
  have h432 : ‖(432 : K)‖₊ ≤ 1 := by exact_mod_cast nnnorm_natCast_le_one K 432
  have h72 : ‖(72 : K)‖₊ ≤ 1 := by exact_mod_cast nnnorm_natCast_le_one K 72
  refine nnnorm_add_le_of_le (nnnorm_add_le_of_le (nnnorm_add_le_of_le (nnnorm_add_le_of_le
    ?_ ?_) ?_) ?_) ?_
  ·
    rw [nnnorm_neg]; exact ha₆q
  ·
    rw [nnnorm_pow]
    exact pow_le_pow_left' ha₄ 2
  ·
    rw [nnnorm_neg, nnnorm_mul, nnnorm_pow]
    calc ‖(64 : K)‖₊ * ‖a₄ q‖₊ ^ 3 ≤ 1 * ‖q‖₊ ^ 3 :=
          mul_le_mul' h64 (pow_le_pow_left' ha₄ 3)
      _ = ‖q‖₊ ^ 3 := one_mul _
      _ ≤ ‖q‖₊ ^ 2 := hq_sq
  ·
    rw [nnnorm_neg, nnnorm_mul, nnnorm_pow]
    calc ‖(432 : K)‖₊ * ‖a₆ q‖₊ ^ 2 ≤ 1 * ‖q‖₊ ^ 2 :=
          mul_le_mul' h432 (pow_le_pow_left' ha₆ 2)
      _ = ‖q‖₊ ^ 2 := one_mul _
  ·
    rw [nnnorm_mul, nnnorm_mul]
    calc ‖(72 : K)‖₊ * ‖a₄ q‖₊ * ‖a₆ q‖₊ ≤ 1 * ‖q‖₊ * ‖q‖₊ :=
          mul_le_mul' (mul_le_mul' h72 ha₄) ha₆
      _ = ‖q‖₊ ^ 2 := by ring

theorem nnnorm_Δ (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) : ‖(curve q).Δ‖₊ = ‖q‖₊ := by
  refine nnnorm_eq_of_nnnorm_sub_lt ((nnnorm_Δ_sub_le hq).trans_lt ?_)
  have hq0' : 0 < ‖q‖₊ := by simpa [pos_iff_ne_zero] using hq0
  calc ‖q‖₊ ^ 2 = ‖q‖₊ * ‖q‖₊ := pow_two ‖q‖₊
    _ < 1 * ‖q‖₊ := mul_lt_mul_of_pos_right hq hq0'
    _ = ‖q‖₊ := one_mul _

theorem Δ_ne_zero (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) : (curve q).Δ ≠ 0 := by
  intro h
  apply hq0
  have := nnnorm_Δ hq0 hq
  rw [h, nnnorm_zero] at this
  rw [← nnnorm_eq_zero, ← this]

theorem isElliptic (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) : (curve q).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (Δ_ne_zero hq0 hq)⟩

theorem nnnorm_c₄ (hq : ‖q‖₊ < 1) : ‖(curve q).c₄‖₊ = 1 := by
  have h : ‖(curve q).c₄ - 1‖₊ < 1 := by
    rw [curve_c₄]
    have : (1 : K) - 48 * a₄ q - 1 = -(48 * a₄ q) := by ring
    rw [this, nnnorm_neg, nnnorm_mul]
    calc ‖(48 : K)‖₊ * ‖a₄ q‖₊ ≤ 1 * ‖q‖₊ := by
          gcongr
          · exact_mod_cast nnnorm_natCast_le_one K 48
          · exact nnnorm_a₄_le hq
      _ = ‖q‖₊ := one_mul _
      _ < 1 := hq
  have := nnnorm_eq_of_nnnorm_sub_lt (a := (curve q).c₄) (b := (1 : K))
    (by rw [nnnorm_one]; exact h)
  rwa [nnnorm_one] at this

theorem nnnorm_j (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) :
    haveI := isElliptic hq0 hq
    ‖(curve q).j‖₊ = ‖q‖₊⁻¹ := by
  letI := isElliptic hq0 hq
  rw [WeierstrassCurve.j, nnnorm_mul, nnnorm_pow, nnnorm_c₄ hq, one_pow, mul_one]
  rw [Units.val_inv_eq_inv_val, nnnorm_inv, WeierstrassCurve.coe_Δ', nnnorm_Δ hq0 hq]

theorem one_lt_nnnorm_j (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) :
    haveI := isElliptic hq0 hq
    1 < ‖(curve q).j‖₊ := by
  rw [nnnorm_j hq0 hq]
  have hq0' : 0 < ‖q‖₊ := by simpa [pos_iff_ne_zero] using hq0
  exact (one_lt_inv₀ hq0').mpr hq

end QSeriesExtras

end TateCurve

open scoped NNReal

open IsUltrametricDist Filter

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

section PowSub

theorem nnnorm_pow_succ_sub_pow_succ_le (x y : K) (n : ℕ) :
    ‖x ^ (n + 1) - y ^ (n + 1)‖₊ ≤ (max ‖x‖₊ ‖y‖₊) ^ n * ‖x - y‖₊ := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hsplit : x ^ (k + 2) - y ^ (k + 2)
          = x * (x ^ (k + 1) - y ^ (k + 1)) + (x - y) * y ^ (k + 1) := by ring
      have h₁ : ‖x * (x ^ (k + 1) - y ^ (k + 1))‖₊
          ≤ (max ‖x‖₊ ‖y‖₊) ^ (k + 1) * ‖x - y‖₊ := by
        rw [nnnorm_mul]
        calc ‖x‖₊ * ‖x ^ (k + 1) - y ^ (k + 1)‖₊
            ≤ max ‖x‖₊ ‖y‖₊ * ((max ‖x‖₊ ‖y‖₊) ^ k * ‖x - y‖₊) :=
              mul_le_mul' (le_max_left _ _) ih
          _ = (max ‖x‖₊ ‖y‖₊) ^ (k + 1) * ‖x - y‖₊ := by ring
      have h₂ : ‖(x - y) * y ^ (k + 1)‖₊
          ≤ (max ‖x‖₊ ‖y‖₊) ^ (k + 1) * ‖x - y‖₊ := by
        rw [nnnorm_mul, nnnorm_pow]
        calc ‖x - y‖₊ * ‖y‖₊ ^ (k + 1)
            ≤ ‖x - y‖₊ * (max ‖x‖₊ ‖y‖₊) ^ (k + 1) :=
              mul_le_mul' le_rfl (pow_le_pow_left' (le_max_right _ _) _)
          _ = (max ‖x‖₊ ‖y‖₊) ^ (k + 1) * ‖x - y‖₊ := mul_comm _ _
      calc ‖x ^ (k + 1 + 1) - y ^ (k + 1 + 1)‖₊
          = ‖x * (x ^ (k + 1) - y ^ (k + 1)) + (x - y) * y ^ (k + 1)‖₊ := by rw [← hsplit]
        _ ≤ (max ‖x‖₊ ‖y‖₊) ^ (k + 1) * ‖x - y‖₊ := nnnorm_add_le_of_le h₁ h₂

end PowSub

section CoeffSumDiff

variable (c : ℕ → ℕ) {q₁ q₂ : K}

theorem term_sub_term (hq₁ : ‖q₁‖₊ < 1) (hq₂ : ‖q₂‖₊ < 1) {n : ℕ} (hn : n ≠ 0) :
    term c q₁ n - term c q₂ n
      = (c n : K) * ((q₁ ^ n - q₂ ^ n) / ((1 - q₁ ^ n) * (1 - q₂ ^ n))) := by
  have hq₁n : ‖q₁ ^ n‖₊ < 1 := by
    rw [nnnorm_pow]; exact pow_lt_one₀ zero_le hq₁ hn
  have hq₂n : ‖q₂ ^ n‖₊ < 1 := by
    rw [nnnorm_pow]; exact pow_lt_one₀ zero_le hq₂ hn
  have h₁ : (1 : K) - q₁ ^ n ≠ 0 := one_sub_ne_zero_of_lt_one hq₁n
  have h₂ : (1 : K) - q₂ ^ n ≠ 0 := one_sub_ne_zero_of_lt_one hq₂n
  simp only [term]
  field_simp
  ring

theorem nnnorm_term_sub_term_succ_le (hq₁ : ‖q₁‖₊ < 1) (hq₂ : ‖q₂‖₊ < 1) (m : ℕ) :
    ‖term c q₁ (m + 1) - term c q₂ (m + 1)‖₊
      ≤ (max ‖q₁‖₊ ‖q₂‖₊) ^ m * ‖q₁ - q₂‖₊ := by
  have hq₁n : ‖q₁ ^ (m + 1)‖₊ < 1 := by
    rw [nnnorm_pow]; exact pow_lt_one₀ zero_le hq₁ (Nat.succ_ne_zero m)
  have hq₂n : ‖q₂ ^ (m + 1)‖₊ < 1 := by
    rw [nnnorm_pow]; exact pow_lt_one₀ zero_le hq₂ (Nat.succ_ne_zero m)
  have hden : ‖(1 - q₁ ^ (m + 1)) * (1 - q₂ ^ (m + 1))‖₊ = 1 := by
    rw [nnnorm_mul, nnnorm_one_sub_of_lt_one hq₁n, nnnorm_one_sub_of_lt_one hq₂n, one_mul]
  rw [term_sub_term c hq₁ hq₂ (Nat.succ_ne_zero m)]
  rw [nnnorm_mul, nnnorm_div, hden, div_one]
  calc ‖(c (m + 1) : K)‖₊ * ‖q₁ ^ (m + 1) - q₂ ^ (m + 1)‖₊
      ≤ 1 * ((max ‖q₁‖₊ ‖q₂‖₊) ^ m * ‖q₁ - q₂‖₊) :=
        mul_le_mul' (nnnorm_natCast_le_one K (c (m + 1)))
          (nnnorm_pow_succ_sub_pow_succ_le q₁ q₂ m)
    _ = (max ‖q₁‖₊ ‖q₂‖₊) ^ m * ‖q₁ - q₂‖₊ := one_mul _

theorem nnnorm_term_sub_term_le (hq₁ : ‖q₁‖₊ < 1) (hq₂ : ‖q₂‖₊ < 1) (n : ℕ) :
    ‖term c q₁ n - term c q₂ n‖₊ ≤ ‖q₁ - q₂‖₊ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmax1 : (max ‖q₁‖₊ ‖q₂‖₊) ^ m ≤ 1 :=
    pow_le_one₀ zero_le (max_le hq₁.le hq₂.le)
  calc ‖term c q₁ (m + 1) - term c q₂ (m + 1)‖₊
      ≤ (max ‖q₁‖₊ ‖q₂‖₊) ^ m * ‖q₁ - q₂‖₊ := nnnorm_term_sub_term_succ_le c hq₁ hq₂ m
    _ ≤ 1 * ‖q₁ - q₂‖₊ := mul_le_mul' hmax1 le_rfl
    _ = ‖q₁ - q₂‖₊ := one_mul _

theorem nnnorm_term_sub_term_le_mul (hq₁ : ‖q₁‖₊ < 1) (hq₂ : ‖q₂‖₊ < 1) {n : ℕ} (hn : 2 ≤ n) :
    ‖term c q₁ n - term c q₂ n‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hmax : (max ‖q₁‖₊ ‖q₂‖₊) ^ m ≤ max ‖q₁‖₊ ‖q₂‖₊ := by
    calc (max ‖q₁‖₊ ‖q₂‖₊) ^ m ≤ (max ‖q₁‖₊ ‖q₂‖₊) ^ 1 :=
          pow_le_pow_of_le_one zero_le (max_le hq₁.le hq₂.le) hm
      _ = max ‖q₁‖₊ ‖q₂‖₊ := pow_one _
  calc ‖term c q₁ (m + 1) - term c q₂ (m + 1)‖₊
      ≤ (max ‖q₁‖₊ ‖q₂‖₊) ^ m * ‖q₁ - q₂‖₊ := nnnorm_term_sub_term_succ_le c hq₁ hq₂ m
    _ ≤ max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ := mul_le_mul' hmax le_rfl

variable [CompleteSpace K]

theorem summable_term_ite (hq : ‖q₁‖₊ < 1) :
    Summable fun n => if n = 1 then (0 : K) else term c q₁ n := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q₁) ?_)
  · rcases eq_or_ne n 1 with rfl | hn
    · have hif : (if (1 : ℕ) = 1 then (0 : K) else term c q₁ 1) = 0 := if_pos rfl
      rw [hif, norm_zero]
      positivity
    · rw [if_neg hn]
      exact_mod_cast nnnorm_term_le c hq n
  · exact_mod_cast hq

theorem nnnorm_coeffSum_sub_coeffSum_le (hq₁ : ‖q₁‖₊ < 1) (hq₂ : ‖q₂‖₊ < 1) :
    ‖coeffSum c q₁ - coeffSum c q₂‖₊ ≤ ‖q₁ - q₂‖₊ := by
  have hsum : coeffSum c q₁ - coeffSum c q₂ = ∑' n, (term c q₁ n - term c q₂ n) :=
    (((summable_term c hq₁).hasSum.sub (summable_term c hq₂).hasSum).tsum_eq).symm
  rw [hsum]
  exact nnnorm_tsum_le_of_forall_le fun n => nnnorm_term_sub_term_le c hq₁ hq₂ n

theorem nnnorm_coeffSum_sub_coeffSum_sub_le (hq₁ : ‖q₁‖₊ < 1) (hq₂ : ‖q₂‖₊ < 1) :
    ‖coeffSum c q₁ - coeffSum c q₂ - (c 1 : K) * (q₁ - q₂)‖₊
      ≤ max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ := by
  have hq₁M : ‖q₁‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ := le_max_left _ _
  have hq₂M : ‖q₂‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ := le_max_right _ _
  have h1q₁ : (1 : K) - q₁ ≠ 0 := one_sub_ne_zero_of_lt_one hq₁
  have h1q₂ : (1 : K) - q₂ ≠ 0 := one_sub_ne_zero_of_lt_one hq₂

  have hsplit₁ : coeffSum c q₁ = term c q₁ 1 + ∑' n, if n = 1 then (0 : K) else term c q₁ n :=
    (summable_term c hq₁).tsum_eq_add_tsum_ite 1
  have hsplit₂ : coeffSum c q₂ = term c q₂ 1 + ∑' n, if n = 1 then (0 : K) else term c q₂ n :=
    (summable_term c hq₂).tsum_eq_add_tsum_ite 1

  have htail : (∑' n, if n = 1 then (0 : K) else term c q₁ n)
        - (∑' n, if n = 1 then (0 : K) else term c q₂ n)
      = ∑' n, ((if n = 1 then (0 : K) else term c q₁ n)
        - (if n = 1 then (0 : K) else term c q₂ n)) :=
    (((summable_term_ite c hq₁).hasSum.sub (summable_term_ite c hq₂).hasSum).tsum_eq).symm
  have htail_le : ‖(∑' n, if n = 1 then (0 : K) else term c q₁ n)
        - (∑' n, if n = 1 then (0 : K) else term c q₂ n)‖₊
      ≤ max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ := by
    rw [htail]
    refine nnnorm_tsum_le_of_forall_le fun n => ?_
    rcases eq_or_ne n 1 with rfl | hn
    · simp
    rw [if_neg hn, if_neg hn]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    have h2n : 2 ≤ n := by omega
    exact nnnorm_term_sub_term_le_mul c hq₁ hq₂ h2n

  have hfac : ‖q₁ + q₂ - q₁ * q₂‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ := by
    have h1 : ‖q₁ + q₂‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ := nnnorm_add_le_of_le hq₁M hq₂M
    have h2 : ‖q₁ * q₂‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ := by
      rw [nnnorm_mul]
      calc ‖q₁‖₊ * ‖q₂‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ * 1 := mul_le_mul' hq₁M hq₂.le
        _ = max ‖q₁‖₊ ‖q₂‖₊ := mul_one _
    calc ‖q₁ + q₂ - q₁ * q₂‖₊ = ‖(q₁ + q₂) + -(q₁ * q₂)‖₊ := by rw [sub_eq_add_neg]
      _ ≤ max ‖q₁‖₊ ‖q₂‖₊ := nnnorm_add_le_of_le h1 (by rw [nnnorm_neg]; exact h2)
  have hlead : ‖(term c q₁ 1 - (c 1 : K) * q₁) - (term c q₂ 1 - (c 1 : K) * q₂)‖₊
      ≤ max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ := by
    have hkey : (term c q₁ 1 - (c 1 : K) * q₁) - (term c q₂ 1 - (c 1 : K) * q₂)
        = (c 1 : K) * ((q₁ - q₂) * (q₁ + q₂ - q₁ * q₂) / ((1 - q₁) * (1 - q₂))) := by
      rw [term_one, term_one]
      field_simp
      ring
    have hden : ‖(1 - q₁) * (1 - q₂)‖₊ = 1 := by
      rw [nnnorm_mul, nnnorm_one_sub_of_lt_one hq₁, nnnorm_one_sub_of_lt_one hq₂, one_mul]
    have hnum : ‖(q₁ - q₂) * (q₁ + q₂ - q₁ * q₂)‖₊ ≤ ‖q₁ - q₂‖₊ * max ‖q₁‖₊ ‖q₂‖₊ := by
      rw [nnnorm_mul]
      exact mul_le_mul' le_rfl hfac
    calc ‖(term c q₁ 1 - (c 1 : K) * q₁) - (term c q₂ 1 - (c 1 : K) * q₂)‖₊
        = ‖(c 1 : K)‖₊ * (‖(q₁ - q₂) * (q₁ + q₂ - q₁ * q₂)‖₊ / ‖(1 - q₁) * (1 - q₂)‖₊) := by
          rw [hkey, nnnorm_mul, nnnorm_div]
      _ = ‖(c 1 : K)‖₊ * ‖(q₁ - q₂) * (q₁ + q₂ - q₁ * q₂)‖₊ := by rw [hden, div_one]
      _ ≤ 1 * (‖q₁ - q₂‖₊ * max ‖q₁‖₊ ‖q₂‖₊) :=
          mul_le_mul' (nnnorm_natCast_le_one K (c 1)) hnum
      _ = max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ := by ring

  have hassemble : coeffSum c q₁ - coeffSum c q₂ - (c 1 : K) * (q₁ - q₂)
      = ((term c q₁ 1 - (c 1 : K) * q₁) - (term c q₂ 1 - (c 1 : K) * q₂))
        + ((∑' n, if n = 1 then (0 : K) else term c q₁ n)
          - (∑' n, if n = 1 then (0 : K) else term c q₂ n)) := by
    rw [hsplit₁, hsplit₂]; ring
  rw [hassemble]
  exact nnnorm_add_le_of_le hlead htail_le

end CoeffSumDiff

section CoefficientsDiff

variable [CompleteSpace K] {q₁ q₂ : K}

theorem nnnorm_a₄_sub_a₄_le (hq₁ : ‖q₁‖₊ < 1) (hq₂ : ‖q₂‖₊ < 1) :
    ‖a₄ q₁ - a₄ q₂‖₊ ≤ ‖q₁ - q₂‖₊ := by
  have h : a₄ q₁ - a₄ q₂
      = -(coeffSum (fun n => 5 * n ^ 3) q₁ - coeffSum (fun n => 5 * n ^ 3) q₂) := by
    rw [a₄, a₄]; ring
  rw [h, nnnorm_neg]
  exact nnnorm_coeffSum_sub_coeffSum_le _ hq₁ hq₂

theorem nnnorm_a₆_sub_a₆_le (hq₁ : ‖q₁‖₊ < 1) (hq₂ : ‖q₂‖₊ < 1) :
    ‖a₆ q₁ - a₆ q₂‖₊ ≤ ‖q₁ - q₂‖₊ := by
  have h : a₆ q₁ - a₆ q₂ = -(coeffSum b q₁ - coeffSum b q₂) := by
    rw [a₆, a₆]; ring
  rw [h, nnnorm_neg]
  exact nnnorm_coeffSum_sub_coeffSum_le _ hq₁ hq₂

theorem nnnorm_a₆_sub_a₆_add_le (hq₁ : ‖q₁‖₊ < 1) (hq₂ : ‖q₂‖₊ < 1) :
    ‖a₆ q₁ - a₆ q₂ + (q₁ - q₂)‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ := by
  have h := nnnorm_coeffSum_sub_coeffSum_sub_le (K := K) b hq₁ hq₂
  rw [b_one, Nat.cast_one, one_mul] at h
  have hkey : a₆ q₁ - a₆ q₂ + (q₁ - q₂)
      = -(coeffSum b q₁ - coeffSum b q₂ - (q₁ - q₂)) := by
    rw [a₆, a₆]; ring
  rw [hkey, nnnorm_neg]
  exact h

theorem nnnorm_c₄_sub_c₄_le (hq₁ : ‖q₁‖₊ < 1) (hq₂ : ‖q₂‖₊ < 1) :
    ‖(curve q₁).c₄ - (curve q₂).c₄‖₊ ≤ ‖q₁ - q₂‖₊ := by
  have hkey : (curve q₁).c₄ - (curve q₂).c₄ = -(48 * (a₄ q₁ - a₄ q₂)) := by
    rw [curve_c₄, curve_c₄]; ring
  rw [hkey, nnnorm_neg, nnnorm_mul]
  calc ‖(48 : K)‖₊ * ‖a₄ q₁ - a₄ q₂‖₊ ≤ 1 * ‖q₁ - q₂‖₊ := by
        gcongr
        · exact_mod_cast nnnorm_natCast_le_one K 48
        · exact nnnorm_a₄_sub_a₄_le hq₁ hq₂
    _ = ‖q₁ - q₂‖₊ := one_mul _

theorem nnnorm_Δ_sub_Δ_sub_le (hq₁ : ‖q₁‖₊ < 1) (hq₂ : ‖q₂‖₊ < 1) :
    ‖(curve q₁).Δ - (curve q₂).Δ - (q₁ - q₂)‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ := by
  have hM1 : max ‖q₁‖₊ ‖q₂‖₊ < 1 := max_lt hq₁ hq₂
  have ha₄₁ : ‖a₄ q₁‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ := (nnnorm_a₄_le hq₁).trans (le_max_left _ _)
  have ha₄₂ : ‖a₄ q₂‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ := (nnnorm_a₄_le hq₂).trans (le_max_right _ _)
  have ha₆₁ : ‖a₆ q₁‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ := (nnnorm_a₆_le hq₁).trans (le_max_left _ _)
  have ha₆₂ : ‖a₆ q₂‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ := (nnnorm_a₆_le hq₂).trans (le_max_right _ _)
  have hd₄ : ‖a₄ q₁ - a₄ q₂‖₊ ≤ ‖q₁ - q₂‖₊ := nnnorm_a₄_sub_a₄_le hq₁ hq₂
  have hd₆ : ‖a₆ q₁ - a₆ q₂‖₊ ≤ ‖q₁ - q₂‖₊ := nnnorm_a₆_sub_a₆_le hq₁ hq₂
  have hd₆' : ‖a₆ q₁ - a₆ q₂ + (q₁ - q₂)‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ :=
    nnnorm_a₆_sub_a₆_add_le hq₁ hq₂
  have hMM : max ‖q₁‖₊ ‖q₂‖₊ * max ‖q₁‖₊ ‖q₂‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ := by
    calc max ‖q₁‖₊ ‖q₂‖₊ * max ‖q₁‖₊ ‖q₂‖₊ ≤ 1 * max ‖q₁‖₊ ‖q₂‖₊ :=
          mul_le_mul' hM1.le le_rfl
      _ = max ‖q₁‖₊ ‖q₂‖₊ := one_mul _

  have hsplit : (curve q₁).Δ - (curve q₂).Δ - (q₁ - q₂)
      = -(a₆ q₁ - a₆ q₂ + (q₁ - q₂))
        + (a₄ q₁ - a₄ q₂) * (a₄ q₁ + a₄ q₂)
        + -(64 * ((a₄ q₁ - a₄ q₂) * (a₄ q₁ ^ 2 + a₄ q₁ * a₄ q₂ + a₄ q₂ ^ 2)))
        + -(432 * ((a₆ q₁ - a₆ q₂) * (a₆ q₁ + a₆ q₂)))
        + 72 * (a₄ q₁ * (a₆ q₁ - a₆ q₂) + a₆ q₂ * (a₄ q₁ - a₄ q₂)) := by
    rw [curve_Δ, curve_Δ]; ring
  rw [hsplit]
  have h64 : ‖(64 : K)‖₊ ≤ 1 := by exact_mod_cast nnnorm_natCast_le_one K 64
  have h432 : ‖(432 : K)‖₊ ≤ 1 := by exact_mod_cast nnnorm_natCast_le_one K 432
  have h72 : ‖(72 : K)‖₊ ≤ 1 := by exact_mod_cast nnnorm_natCast_le_one K 72
  refine nnnorm_add_le_of_le (nnnorm_add_le_of_le (nnnorm_add_le_of_le (nnnorm_add_le_of_le
    ?_ ?_) ?_) ?_) ?_
  ·
    rw [nnnorm_neg]; exact hd₆'
  ·
    rw [nnnorm_mul]
    calc ‖a₄ q₁ - a₄ q₂‖₊ * ‖a₄ q₁ + a₄ q₂‖₊
        ≤ ‖q₁ - q₂‖₊ * max ‖q₁‖₊ ‖q₂‖₊ :=
          mul_le_mul' hd₄ (nnnorm_add_le_of_le ha₄₁ ha₄₂)
      _ = max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ := mul_comm _ _
  ·
    rw [nnnorm_neg, nnnorm_mul, nnnorm_mul]
    have hquad : ‖a₄ q₁ ^ 2 + a₄ q₁ * a₄ q₂ + a₄ q₂ ^ 2‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ := by
      have h1 : ‖a₄ q₁ ^ 2‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ := by
        rw [nnnorm_pow, sq]
        exact (mul_le_mul' ha₄₁ ha₄₁).trans hMM
      have h2 : ‖a₄ q₁ * a₄ q₂‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ := by
        rw [nnnorm_mul]
        exact (mul_le_mul' ha₄₁ ha₄₂).trans hMM
      have h3 : ‖a₄ q₂ ^ 2‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ := by
        rw [nnnorm_pow, sq]
        exact (mul_le_mul' ha₄₂ ha₄₂).trans hMM
      exact nnnorm_add_le_of_le (nnnorm_add_le_of_le h1 h2) h3
    calc ‖(64 : K)‖₊ * (‖a₄ q₁ - a₄ q₂‖₊ * ‖a₄ q₁ ^ 2 + a₄ q₁ * a₄ q₂ + a₄ q₂ ^ 2‖₊)
        ≤ 1 * (‖q₁ - q₂‖₊ * max ‖q₁‖₊ ‖q₂‖₊) :=
          mul_le_mul' h64 (mul_le_mul' hd₄ hquad)
      _ = max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ := by ring
  ·
    rw [nnnorm_neg, nnnorm_mul, nnnorm_mul]
    calc ‖(432 : K)‖₊ * (‖a₆ q₁ - a₆ q₂‖₊ * ‖a₆ q₁ + a₆ q₂‖₊)
        ≤ 1 * (‖q₁ - q₂‖₊ * max ‖q₁‖₊ ‖q₂‖₊) :=
          mul_le_mul' h432 (mul_le_mul' hd₆ (nnnorm_add_le_of_le ha₆₁ ha₆₂))
      _ = max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ := by ring
  ·
    rw [nnnorm_mul]
    have hinner : ‖a₄ q₁ * (a₆ q₁ - a₆ q₂) + a₆ q₂ * (a₄ q₁ - a₄ q₂)‖₊
        ≤ max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ := by
      have h1 : ‖a₄ q₁ * (a₆ q₁ - a₆ q₂)‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ := by
        rw [nnnorm_mul]; exact mul_le_mul' ha₄₁ hd₆
      have h2 : ‖a₆ q₂ * (a₄ q₁ - a₄ q₂)‖₊ ≤ max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ := by
        rw [nnnorm_mul]; exact mul_le_mul' ha₆₂ hd₄
      exact nnnorm_add_le_of_le h1 h2
    calc ‖(72 : K)‖₊ * ‖a₄ q₁ * (a₆ q₁ - a₆ q₂) + a₆ q₂ * (a₄ q₁ - a₄ q₂)‖₊
        ≤ 1 * (max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊) := mul_le_mul' h72 hinner
      _ = max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ := one_mul _

end CoefficientsDiff

section TateParameter

variable [CompleteSpace K]

noncomputable def jInversionStep (j₀ q : K) : K :=
  (curve q).c₄ ^ 3 / j₀ - ((curve q).Δ - q)

theorem jInversionStep_eq_self_iff {j₀ q : K} (hj₀ : j₀ ≠ 0) :
    jInversionStep j₀ q = q ↔ (curve q).c₄ ^ 3 = j₀ * (curve q).Δ := by
  rw [jInversionStep]
  constructor
  · intro h
    have h2 : (curve q).c₄ ^ 3 / j₀ = (curve q).Δ := by linear_combination h
    rw [div_eq_iff hj₀] at h2
    linear_combination h2
  · intro h
    have h2 : (curve q).c₄ ^ 3 / j₀ = (curve q).Δ := by
      rw [div_eq_iff hj₀]; linear_combination h
    linear_combination h2

theorem nnnorm_jInversionStep {j₀ q : K} (hj : 1 < ‖j₀‖₊) (hq : ‖q‖₊ ≤ ‖j₀‖₊⁻¹) :
    ‖jInversionStep j₀ q‖₊ = ‖j₀‖₊⁻¹ := by
  have hpos : (0 : ℝ≥0) < ‖j₀‖₊ := lt_trans zero_lt_one hj
  have hρpos : (0 : ℝ≥0) < ‖j₀‖₊⁻¹ := by
    rw [inv_pos]; exact hpos
  have hρlt : ‖j₀‖₊⁻¹ < 1 := by
    have h := mul_lt_mul_of_pos_left hj (inv_pos.mpr hpos)
    rwa [mul_one, inv_mul_cancel₀ hpos.ne'] at h
  have hq1 : ‖q‖₊ < 1 := lt_of_le_of_lt hq hρlt

  have hmain : ‖(curve q).c₄ ^ 3 / j₀‖₊ = ‖j₀‖₊⁻¹ := by
    rw [nnnorm_div, nnnorm_pow, nnnorm_c₄ hq1, one_pow, one_div]

  have hcorr : ‖(curve q).Δ - q‖₊ < ‖j₀‖₊⁻¹ := by
    calc ‖(curve q).Δ - q‖₊ ≤ ‖q‖₊ ^ 2 := nnnorm_Δ_sub_le hq1
      _ ≤ ‖j₀‖₊⁻¹ ^ 2 := pow_le_pow_left' hq 2
      _ < ‖j₀‖₊⁻¹ := by
          calc ‖j₀‖₊⁻¹ ^ 2 = ‖j₀‖₊⁻¹ * ‖j₀‖₊⁻¹ := sq _
            _ < 1 * ‖j₀‖₊⁻¹ := mul_lt_mul_of_pos_right hρlt hρpos
            _ = ‖j₀‖₊⁻¹ := one_mul _

  rw [jInversionStep]
  rw [show (curve q).c₄ ^ 3 / j₀ - ((curve q).Δ - q)
      = (curve q).c₄ ^ 3 / j₀ - ((curve q).Δ - q) from rfl]
  refine nnnorm_eq_of_nnnorm_sub_lt ?_ |>.trans hmain
  rw [sub_sub_cancel_left, nnnorm_neg, hmain]
  exact hcorr

theorem nnnorm_jInversionStep_sub_le {j₀ q₁ q₂ : K} (hj : 1 < ‖j₀‖₊)
    (hq₁ : ‖q₁‖₊ < 1) (hq₂ : ‖q₂‖₊ < 1) :
    ‖jInversionStep j₀ q₁ - jInversionStep j₀ q₂‖₊
      ≤ max (max ‖q₁‖₊ ‖q₂‖₊) ‖j₀‖₊⁻¹ * ‖q₁ - q₂‖₊ := by
  have hpos : (0 : ℝ≥0) < ‖j₀‖₊ := lt_trans zero_lt_one hj
  have hc₄₁ : ‖(curve q₁).c₄‖₊ = 1 := nnnorm_c₄ hq₁
  have hc₄₂ : ‖(curve q₂).c₄‖₊ = 1 := nnnorm_c₄ hq₂

  have hsplit : jInversionStep j₀ q₁ - jInversionStep j₀ q₂
      = ((curve q₁).c₄ ^ 3 - (curve q₂).c₄ ^ 3) / j₀
        + -((curve q₁).Δ - (curve q₂).Δ - (q₁ - q₂)) := by
    rw [jInversionStep, jInversionStep]; ring
  rw [hsplit]
  refine nnnorm_add_le_of_le ?_ ?_
  ·

    have hcube : ‖(curve q₁).c₄ ^ 3 - (curve q₂).c₄ ^ 3‖₊ ≤ ‖q₁ - q₂‖₊ := by
      have hfactor : (curve q₁).c₄ ^ 3 - (curve q₂).c₄ ^ 3
          = ((curve q₁).c₄ - (curve q₂).c₄)
            * ((curve q₁).c₄ ^ 2 + (curve q₁).c₄ * (curve q₂).c₄ + (curve q₂).c₄ ^ 2) := by
        ring
      have hquad : ‖(curve q₁).c₄ ^ 2 + (curve q₁).c₄ * (curve q₂).c₄ + (curve q₂).c₄ ^ 2‖₊
          ≤ 1 := by
        have h1 : ‖(curve q₁).c₄ ^ 2‖₊ ≤ 1 := by rw [nnnorm_pow, hc₄₁, one_pow]
        have h2 : ‖(curve q₁).c₄ * (curve q₂).c₄‖₊ ≤ 1 := by
          rw [nnnorm_mul, hc₄₁, hc₄₂, one_mul]
        have h3 : ‖(curve q₂).c₄ ^ 2‖₊ ≤ 1 := by rw [nnnorm_pow, hc₄₂, one_pow]
        exact nnnorm_add_le_of_le (nnnorm_add_le_of_le h1 h2) h3
      calc ‖(curve q₁).c₄ ^ 3 - (curve q₂).c₄ ^ 3‖₊
          = ‖(curve q₁).c₄ - (curve q₂).c₄‖₊
            * ‖(curve q₁).c₄ ^ 2 + (curve q₁).c₄ * (curve q₂).c₄ + (curve q₂).c₄ ^ 2‖₊ := by
            rw [hfactor, nnnorm_mul]
        _ ≤ ‖q₁ - q₂‖₊ * 1 := mul_le_mul' (nnnorm_c₄_sub_c₄_le hq₁ hq₂) hquad
        _ = ‖q₁ - q₂‖₊ := mul_one _
    calc ‖((curve q₁).c₄ ^ 3 - (curve q₂).c₄ ^ 3) / j₀‖₊
        = ‖(curve q₁).c₄ ^ 3 - (curve q₂).c₄ ^ 3‖₊ * ‖j₀‖₊⁻¹ := by
          rw [nnnorm_div, div_eq_mul_inv]
      _ ≤ ‖q₁ - q₂‖₊ * ‖j₀‖₊⁻¹ := mul_le_mul' hcube le_rfl
      _ ≤ ‖q₁ - q₂‖₊ * max (max ‖q₁‖₊ ‖q₂‖₊) ‖j₀‖₊⁻¹ :=
          mul_le_mul' le_rfl (le_max_right _ _)
      _ = max (max ‖q₁‖₊ ‖q₂‖₊) ‖j₀‖₊⁻¹ * ‖q₁ - q₂‖₊ := mul_comm _ _
  ·
    rw [nnnorm_neg]
    calc ‖(curve q₁).Δ - (curve q₂).Δ - (q₁ - q₂)‖₊
        ≤ max ‖q₁‖₊ ‖q₂‖₊ * ‖q₁ - q₂‖₊ := nnnorm_Δ_sub_Δ_sub_le hq₁ hq₂
      _ ≤ max (max ‖q₁‖₊ ‖q₂‖₊) ‖j₀‖₊⁻¹ * ‖q₁ - q₂‖₊ :=
          mul_le_mul' (le_max_left _ _) le_rfl

theorem exists_tateParameter_c₄ (j₀ : K) (hj : 1 < ‖j₀‖₊) :
    ∃ q : K, q ≠ 0 ∧ ‖q‖₊ = ‖j₀‖₊⁻¹ ∧ (curve q).c₄ ^ 3 = j₀ * (curve q).Δ := by
  have hpos : (0 : ℝ≥0) < ‖j₀‖₊ := lt_trans zero_lt_one hj
  have hj₀0 : j₀ ≠ 0 := by
    intro h
    rw [h, nnnorm_zero] at hj
    exact (lt_irrefl _ (lt_trans zero_lt_one hj)).elim
  have hρpos : (0 : ℝ≥0) < ‖j₀‖₊⁻¹ := by rw [inv_pos]; exact hpos
  have hρlt : ‖j₀‖₊⁻¹ < 1 := by
    have h := mul_lt_mul_of_pos_left hj (inv_pos.mpr hpos)
    rwa [mul_one, inv_mul_cancel₀ hpos.ne'] at h

  set B : Set K := Metric.closedBall (0 : K) ((‖j₀‖₊⁻¹ : ℝ≥0) : ℝ) with hBdef
  have hmem : ∀ x : K, x ∈ B ↔ ‖x‖₊ ≤ ‖j₀‖₊⁻¹ := by
    intro x
    rw [hBdef, Metric.mem_closedBall, dist_zero_right, ← coe_nnnorm, NNReal.coe_le_coe]
  haveI : CompleteSpace B := Metric.isClosed_closedBall.completeSpace_coe
  have h0B : (0 : K) ∈ B := by
    rw [hBdef]
    exact Metric.mem_closedBall_self (NNReal.coe_nonneg _)
  haveI : Nonempty B := ⟨⟨0, h0B⟩⟩

  have hmaps : ∀ x : K, ‖x‖₊ ≤ ‖j₀‖₊⁻¹ → ‖jInversionStep j₀ x‖₊ ≤ ‖j₀‖₊⁻¹ := fun x hx =>
    le_of_eq (nnnorm_jInversionStep hj hx)
  let φ : B → B := fun z => ⟨jInversionStep j₀ (z : K), (hmem _).mpr (hmaps _ ((hmem _).mp z.2))⟩

  have hlip : LipschitzWith ‖j₀‖₊⁻¹ φ := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have hx : ‖(x : K)‖₊ ≤ ‖j₀‖₊⁻¹ := (hmem _).mp x.2
    have hy : ‖(y : K)‖₊ ≤ ‖j₀‖₊⁻¹ := (hmem _).mp y.2
    have hx1 : ‖(x : K)‖₊ < 1 := lt_of_le_of_lt hx hρlt
    have hy1 : ‖(y : K)‖₊ < 1 := lt_of_le_of_lt hy hρlt
    have key : ‖jInversionStep j₀ (x : K) - jInversionStep j₀ (y : K)‖₊
        ≤ ‖j₀‖₊⁻¹ * ‖(x : K) - (y : K)‖₊ := by
      refine (nnnorm_jInversionStep_sub_le hj hx1 hy1).trans ?_
      refine mul_le_mul' ?_ le_rfl
      exact max_le (max_le hx hy) le_rfl
    calc dist (φ x) (φ y)
        = ‖jInversionStep j₀ (x : K) - jInversionStep j₀ (y : K)‖ := by
          rw [show dist (φ x) (φ y)
              = dist (jInversionStep j₀ (x : K)) (jInversionStep j₀ (y : K)) from rfl,
            dist_eq_norm]
      _ ≤ ((‖j₀‖₊⁻¹ * ‖(x : K) - (y : K)‖₊ : ℝ≥0) : ℝ) := by
          rw [← coe_nnnorm]
          exact_mod_cast key
      _ = (‖j₀‖₊⁻¹ : ℝ≥0) * dist (x : K) (y : K) := by
          rw [NNReal.coe_mul, coe_nnnorm, dist_eq_norm]
      _ = (‖j₀‖₊⁻¹ : ℝ≥0) * dist x y := rfl
  have hcontract : ContractingWith ‖j₀‖₊⁻¹ φ := ⟨hρlt, hlip⟩

  obtain ⟨x, hfixB⟩ : ∃ y : B, φ y = y :=
    ⟨ContractingWith.fixedPoint φ hcontract, hcontract.fixedPoint_isFixedPt⟩
  have hfix : jInversionStep j₀ (x : K) = (x : K) := congrArg Subtype.val hfixB

  have hxnorm : ‖(x : K)‖₊ = ‖j₀‖₊⁻¹ := by
    rw [← hfix]
    exact nnnorm_jInversionStep hj ((hmem _).mp x.2)
  have hx0 : (x : K) ≠ 0 := by
    intro h
    rw [h, nnnorm_zero] at hxnorm
    exact hρpos.ne' hxnorm.symm
  exact ⟨(x : K), hx0, hxnorm, (jInversionStep_eq_self_iff hj₀0).mp hfix⟩

theorem tateParameter_unique {j₀ q₁ q₂ : K} (hj : 1 < ‖j₀‖₊)
    (hq₁ : ‖q₁‖₊ < 1) (hq₂ : ‖q₂‖₊ < 1)
    (h₁ : (curve q₁).c₄ ^ 3 = j₀ * (curve q₁).Δ)
    (h₂ : (curve q₂).c₄ ^ 3 = j₀ * (curve q₂).Δ) : q₁ = q₂ := by
  have hpos : (0 : ℝ≥0) < ‖j₀‖₊ := lt_trans zero_lt_one hj
  have hj₀0 : j₀ ≠ 0 := by
    intro h
    rw [h, nnnorm_zero] at hj
    exact (lt_irrefl _ (lt_trans zero_lt_one hj)).elim
  have hρlt : ‖j₀‖₊⁻¹ < 1 := by
    have h := mul_lt_mul_of_pos_left hj (inv_pos.mpr hpos)
    rwa [mul_one, inv_mul_cancel₀ hpos.ne'] at h
  by_contra hne
  have hd : (0 : ℝ≥0) < ‖q₁ - q₂‖₊ := by
    rw [pos_iff_ne_zero, ne_eq, nnnorm_eq_zero, sub_eq_zero]
    exact hne
  have hfix₁ : jInversionStep j₀ q₁ = q₁ := (jInversionStep_eq_self_iff hj₀0).mpr h₁
  have hfix₂ : jInversionStep j₀ q₂ = q₂ := (jInversionStep_eq_self_iff hj₀0).mpr h₂
  have hkey : ‖q₁ - q₂‖₊ ≤ max (max ‖q₁‖₊ ‖q₂‖₊) ‖j₀‖₊⁻¹ * ‖q₁ - q₂‖₊ := by
    conv_lhs => rw [← hfix₁, ← hfix₂]
    exact nnnorm_jInversionStep_sub_le hj hq₁ hq₂
  have hr : max (max ‖q₁‖₊ ‖q₂‖₊) ‖j₀‖₊⁻¹ < 1 := max_lt (max_lt hq₁ hq₂) hρlt
  have hlt : ‖q₁ - q₂‖₊ < ‖q₁ - q₂‖₊ := by
    calc ‖q₁ - q₂‖₊ ≤ max (max ‖q₁‖₊ ‖q₂‖₊) ‖j₀‖₊⁻¹ * ‖q₁ - q₂‖₊ := hkey
      _ < 1 * ‖q₁ - q₂‖₊ := mul_lt_mul_of_pos_right hr hd
      _ = ‖q₁ - q₂‖₊ := one_mul _
  exact lt_irrefl _ hlt

theorem curve_j_eq {q j₀ : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (h : (curve q).c₄ ^ 3 = j₀ * (curve q).Δ) :
    haveI := isElliptic hq0 hq
    (curve q).j = j₀ := by
  letI := isElliptic hq0 hq
  have hΔ0 : (curve q).Δ ≠ 0 := Δ_ne_zero hq0 hq
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', h,
    mul_comm j₀ ((curve q).Δ), ← mul_assoc, inv_mul_cancel₀ hΔ0, one_mul]

theorem c₄_pow_eq_of_curve_j_eq {q j₀ : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (h : (haveI := isElliptic hq0 hq; (curve q).j) = j₀) :
    (curve q).c₄ ^ 3 = j₀ * (curve q).Δ := by
  letI := isElliptic hq0 hq
  have hΔ0 : (curve q).Δ ≠ 0 := Δ_ne_zero hq0 hq
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ'] at h
  calc (curve q).c₄ ^ 3 = ((curve q).Δ * (curve q).Δ⁻¹) * (curve q).c₄ ^ 3 := by
        rw [mul_inv_cancel₀ hΔ0, one_mul]
    _ = (curve q).Δ * ((curve q).Δ⁻¹ * (curve q).c₄ ^ 3) := by ring
    _ = (curve q).Δ * j₀ := by rw [h]
    _ = j₀ * (curve q).Δ := mul_comm _ _

theorem exists_tateParameter (j₀ : K) (hj : 1 < ‖j₀‖₊) :
    ∃ q : K, ∃ (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1),
      ‖q‖₊ = ‖j₀‖₊⁻¹ ∧ (haveI := isElliptic hq0 hq; (curve q).j) = j₀ := by
  obtain ⟨q, hq0, hqnorm, halg⟩ := exists_tateParameter_c₄ j₀ hj
  have hpos : (0 : ℝ≥0) < ‖j₀‖₊ := lt_trans zero_lt_one hj
  have hρlt : ‖j₀‖₊⁻¹ < 1 := by
    have h := mul_lt_mul_of_pos_left hj (inv_pos.mpr hpos)
    rwa [mul_one, inv_mul_cancel₀ hpos.ne'] at h
  have hq : ‖q‖₊ < 1 := by rw [hqnorm]; exact hρlt
  exact ⟨q, hq0, hq, hqnorm, curve_j_eq hq0 hq halg⟩

theorem exists_tateParameter_of_isElliptic (E : WeierstrassCurve K) [E.IsElliptic]
    (hE : 1 < ‖E.j‖₊) :
    ∃ q : K, ∃ (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1),
      ‖q‖₊ = ‖E.j‖₊⁻¹ ∧ (haveI := isElliptic hq0 hq; (curve q).j) = E.j :=
  exists_tateParameter E.j hE

end TateParameter

end TateCurve


