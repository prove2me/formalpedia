-- Prove2me | Definitions.Def_MIPRE_Foundations_Pipeline_Margin
-- name    : MIPRE_Foundations_Pipeline_Margin
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T19:22:47.972815+00:00
-- url     : https://prove2.me/theorems/849ed237-28b5-419a-8287-4c514d5dca52
-- title:
--   The margin parameters ε₁ and ε₂ of the compression theorem, with the margin and repetition-exponent lemmas
-- statement:
--   Blueprint `lem:compress-margin` and `lem:compress-tau` (paper `recursive.tex`, proof of `thm:compression`): the arithmetic that lands each contrapositive soundness clause of the three stages strictly inside the gap handed to it. Write $x = \lambda n$, $(a_1,b_1)$ for the constants of introspection, $(a_2,b_2)$ for those of answer reduction, and $s$ for $\sigma$.
--
--   Definitions: `eps1 a b x`, the introspection margin, and `eps2 a₁ b₁ a₂ b₂ μ s x`, the answer-reduction margin,
--
--   $$\varepsilon_1(x) = (8\,a\,x^{a})^{-1/b}, \qquad \varepsilon_2 = \Big(\frac{\varepsilon_1(x)}{3\,s^{a_2}x^{\mu a_2}}\Big)^{1/b_2}.$$
--
--   The embedded lemmas, used by `GapCompression.ofPipeline`, are: $\varepsilon_1 > 0$ for $a \ge 1$, $x > 0$, and $\varepsilon_1 \le 1$ if also $b > 0$, $x \ge 1$ (`eps1_pos`, `eps1_le_one`); $\varepsilon_1^b = (8ax^a)^{-1}$ and $\varepsilon_1 = (8a)^{-1/b}x^{-a/b}$ (`eps1_rpow`, `eps1_eq`); `intro_margin`: $a(x^a\varepsilon_1^b + x^{-b}) < 1/2$ for $a \ge 1$, $b > 0$, $x \ge 1$ and $(4a)^{1/b} \le x$; `exists_mu`: for $a_1,a_2 \ge 1$, $b_2 > 0$ and naturals $K, C$ there are $\mu \ge C$ and $N$ with $s^{a_2}x^{-\mu b_2} < \varepsilon_1(x)/2$ for all $x \ge N$ and $1 \le s \le x^K$; $\varepsilon_2 > 0$ ($a_1 \ge 1$, $s,x > 0$), $\varepsilon_2 \le 1$ ($a_1,a_2 \ge 1$, $b_1,b_2 > 0$, $s,x \ge 1$) and $\varepsilon_2^{b_2} = \varepsilon_1/(3s^{a_2}x^{\mu a_2})$ ($a_1 \ge 1$, $b_2 > 0$, $s,x > 0$) (`eps2_pos`, `eps2_le_one`, `eps2_rpow`); `ar_margin`: given the margin claim's inequality, $s^{a_2}(x^{\mu a_2}\varepsilon_2^{b_2} + x^{-\mu b_2}) < \varepsilon_1$; `exists_eps2_lower`: there are $P, N$ with $x^{-P} \le \varepsilon_2$ for all $x \ge N$ and $1 \le s \le x^K$; `exists_tau`: for $c > 0$ and naturals $P,\beta$ there is $\tau$ with $\exp(-c\varepsilon^{13}k/(B+1)) \le 1/2$ for all $z \ge \tau$, $k \ge z^\tau$, $0 \le B \le z^\beta$ and $\varepsilon > 0$ with $z^{-P} \le \varepsilon$.
--
--   **Formalization Note** Everything is `Real.rpow` arithmetic with the natural parameters cast to `ℝ`; nothing depends on the verifiers. The witnesses are explicit: `exists_mu` gives $\mu = C + \lceil (Ka_2 + a_1/b_1 + 1)/b_2\rceil$, $N = \lceil 2(8a_1)^{1/b_1}\rceil + 2$; `exists_eps2_lower` gives $P = \lceil (1 + Ka_2 + \mu a_2 + (1+a_1)/b_1)/b_2\rceil$, $N = \lceil 8a_1\rceil + 3$; `exists_tau` gives $\tau = 13P + \beta + 1 + \lceil 2/c\rceil$. The thresholds are absorbed by $C_0$ in the `Compress` bundle.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pipeline/Margin.lean; blueprint lem:compress-margin; blueprint lem:compress-tau; paper recursive.tex, proof of thm:compression

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pipeline/Margin.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_AnswerReduction
import Definitions.Def_MIPRE_Foundations_Pipeline_Introspection
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition

/-!
# The parameter arithmetic of the compression theorem

Blueprint `lem:compress-margin` and `lem:compress-tau` (paper `recursive.tex`, the proof of
`thm:compression`; ledger nodes `1.5.3`, `1.5.5`): the four stages of `Compress` are chained
through a budget of margins, and these are the arithmetic facts about the imported constants
that make each application of a soundness clause, taken contrapositively, land strictly inside
the gap it is handed.

Write `x = λn`, `(a₁, b₁)` for the constants of introspection and `(a₂, b₂)` for those of
answer reduction (`a₁, a₂ ≥ 1`, `0 < b₁, b₂ ≤ 1`).

* `ε₁(x) = (8 a₁ x^{a₁})^{-1/b₁}` makes the introspection loss `δ₁(ε₁, n) < 1/2` once
  `x ≥ (4a₁)^{1/b₁}` (`intro_margin`): the first term of `δ₁` is exactly `1/8`, the second at
  most `1/4`.
* `ε₂ = (ε₁ / (3 σ^{a₂} x^{μ a₂}))^{1/b₂}` makes the first term of the answer-reduction loss
  `δ₂(ε₂, n)` exactly `ε₁/3`; the second, `σ^{a₂} x^{-μ b₂}`, is below `ε₁/2` for `μ` large
  (`exists_mu`, the margin claim): with `σ ≤ x^K`, any `μ b₂ ≥ K a₂ + a₁/b₁ + 1` works past a
  threshold on `x`. The paper fixes `μ = ⌈max{C_intro, (9a₁ + 2a₂ C_intro)/(b₁ b₂)}⌉` and
  `n ≥ 2`; the threshold here is absorbed by `C₀`.
* `1/ε₂` is bounded by a fixed power of `x` (`exists_eps2_lower`), so a universal repetition
  exponent `τ` brings the repetition bound `exp(-c ε₂^{13} k / (B + 1))` below `1/2` for any
  `k ≥ z^τ` and `B ≤ z^β`, `z = λn + 1`, for `n ≥ τ` (`exists_tau`).

Everything is real arithmetic with `Real.rpow`; nothing depends on the verifiers.
-/

namespace MIPRE.Pipeline

open Real

/-! ## The introspection margin -/

/-- `ε₁(x) = (8 a x^a)^{-1/b}`. -/
noncomputable def eps1 (a b x : ℝ) : ℝ := (8 * a * x ^ a) ^ (-(1 / b))

theorem eps1_pos {a b x : ℝ} (ha : 1 ≤ a) (hx : 0 < x) : 0 < eps1 a b x :=
  rpow_pos_of_pos (by positivity) _

theorem eps1_le_one {a b x : ℝ} (ha : 1 ≤ a) (hb : 0 < b) (hx : 1 ≤ x) : eps1 a b x ≤ 1 := by
  refine rpow_le_one_of_one_le_of_nonpos ?_ (by rw [neg_nonpos]; positivity)
  have : 1 ≤ x ^ a := one_le_rpow hx (by linarith)
  nlinarith

/-- `ε₁^b = (8 a x^a)⁻¹`. -/
theorem eps1_rpow {a b x : ℝ} (ha : 1 ≤ a) (hb : 0 < b) (hx : 0 < x) :
    eps1 a b x ^ b = (8 * a * x ^ a)⁻¹ := by
  rw [eps1, ← rpow_mul (by positivity), neg_mul, one_div, inv_mul_cancel₀ hb.ne', rpow_neg_one]

/-- `ε₁(x) = (8a)^{-1/b} · x^{-a/b}`. -/
theorem eps1_eq {a b x : ℝ} (ha : 1 ≤ a) (hx : 0 < x) :
    eps1 a b x = (8 * a) ^ (-(1 / b)) * x ^ (-(a / b)) := by
  rw [eps1, mul_rpow (by positivity) (rpow_nonneg hx.le _), ← rpow_mul hx.le]
  congr 2; ring

/-- **The introspection step lands below `1/2`**: `δ₁(ε₁, n) < 1/2` once `x = λn` is at least
`(4a)^{1/b}`. -/
theorem intro_margin {a b x : ℝ} (ha : 1 ≤ a) (hb : 0 < b) (hx : 1 ≤ x)
    (hx' : (4 * a) ^ (1 / b) ≤ x) :
    a * (x ^ a * eps1 a b x ^ b + x ^ (-b)) < 1 / 2 := by
  have hx0 : 0 < x := by linarith
  rw [eps1_rpow ha hb hx0]
  have h1 : x ^ a * (8 * a * x ^ a)⁻¹ = (8 * a)⁻¹ := by
    have : 0 < x ^ a := rpow_pos_of_pos hx0 a
    field_simp
  have h2 : 4 * a ≤ x ^ b := by
    have := rpow_le_rpow (by positivity) hx' hb.le
    rwa [← rpow_mul (by positivity), one_div, inv_mul_cancel₀ hb.ne', rpow_one] at this
  have h3 : a * x ^ (-b) ≤ 1 / 4 := by
    rw [rpow_neg hx0.le, ← div_eq_mul_inv, div_le_iff₀ (rpow_pos_of_pos hx0 b)]
    linarith
  have h4 : a * (8 * a)⁻¹ = 1 / 8 := by field_simp
  calc a * (x ^ a * (8 * a * x ^ a)⁻¹ + x ^ (-b)) = a * (8 * a)⁻¹ + a * x ^ (-b) := by
        rw [h1]; ring
    _ ≤ 1 / 8 + 1 / 4 := by rw [h4]; linarith
    _ < 1 / 2 := by norm_num

/-! ## The margin claim -/

/-- **The margin claim** (blueprint `lem:compress-margin`). Given the constants of introspection
and answer reduction, a bound `σ ≤ x^K` on the size parameter and a lower bound `C` wanted of
`μ`, there is a universal `μ ≥ C` and a threshold `N` such that for `x ≥ N`,
`σ^{a₂} x^{-μ b₂} < ε₁(x) / 2`. -/
theorem exists_mu {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂) (hb₂ : 0 < b₂)
    (K C : ℕ) :
    ∃ mu : ℕ, C ≤ mu ∧ ∃ N : ℕ, ∀ x : ℝ, (N : ℝ) ≤ x → ∀ s : ℝ, 1 ≤ s → s ≤ x ^ (K : ℝ) →
      s ^ a₂ * x ^ (-((mu : ℝ) * b₂)) < eps1 a₁ b₁ x / 2 := by
  refine ⟨C + ⌈(K * a₂ + a₁ / b₁ + 1) / b₂⌉₊, by omega, ⌈2 * (8 * a₁) ^ (1 / b₁)⌉₊ + 2,
    fun x hx s hs hsx => ?_⟩
  have hN : (2 * (8 * a₁) ^ (1 / b₁) : ℝ) + 2 ≤ x := by
    have := Nat.le_ceil (2 * (8 * a₁) ^ (1 / b₁))
    push_cast at hx; linarith
  have h8 : 0 < (8 * a₁) ^ (1 / b₁) := rpow_pos_of_pos (by positivity) _
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  -- the exponent of `x` on the left is at most `-(a₁/b₁) - 1`
  have hmu : K * a₂ + a₁ / b₁ + 1 ≤ ((C + ⌈(K * a₂ + a₁ / b₁ + 1) / b₂⌉₊ : ℕ) : ℝ) * b₂ := by
    have h := Nat.le_ceil ((K * a₂ + a₁ / b₁ + 1) / b₂)
    have hC : (0 : ℝ) ≤ C := by positivity
    push_cast
    rw [div_le_iff₀ hb₂] at h
    nlinarith
  have hs' : s ^ a₂ ≤ x ^ ((K : ℝ) * a₂) := by
    rw [rpow_mul hx0.le]
    exact rpow_le_rpow (by linarith) hsx (by linarith)
  have hleft : s ^ a₂ * x ^ (-(((C + ⌈(K * a₂ + a₁ / b₁ + 1) / b₂⌉₊ : ℕ) : ℝ) * b₂)) ≤
      x ^ (-(a₁ / b₁) - 1) := by
    calc s ^ a₂ * x ^ (-(((C + ⌈(K * a₂ + a₁ / b₁ + 1) / b₂⌉₊ : ℕ) : ℝ) * b₂))
        ≤ x ^ ((K : ℝ) * a₂) * x ^ (-(((C + ⌈(K * a₂ + a₁ / b₁ + 1) / b₂⌉₊ : ℕ) : ℝ) * b₂)) :=
          mul_le_mul_of_nonneg_right hs' (rpow_nonneg hx0.le _)
      _ = x ^ ((K : ℝ) * a₂ - ((C + ⌈(K * a₂ + a₁ / b₁ + 1) / b₂⌉₊ : ℕ) : ℝ) * b₂) := by
          rw [← rpow_add hx0]; ring_nf
      _ ≤ x ^ (-(a₁ / b₁) - 1) := rpow_le_rpow_of_exponent_le hx1 (by linarith)
  -- the right-hand side is `(8a₁)^{-1/b₁} x^{-a₁/b₁} / 2`
  rw [eps1_eq ha₁ hx0]
  refine hleft.trans_lt ?_
  rw [show -(a₁ / b₁) - 1 = -(a₁ / b₁) + (-1) by ring, rpow_add hx0, rpow_neg_one,
    rpow_neg (by positivity : (0:ℝ) ≤ 8 * a₁)]
  have hpos : 0 < x ^ (-(a₁ / b₁)) := rpow_pos_of_pos hx0 _
  have hx' : 2 * (8 * a₁) ^ (1 / b₁) < x := by linarith
  have key : x⁻¹ < ((8 * a₁) ^ (1 / b₁))⁻¹ / 2 := by
    have := one_div_lt_one_div_of_lt (by positivity : (0:ℝ) < 2 * (8 * a₁) ^ (1 / b₁)) hx'
    rw [one_div, one_div, mul_inv, mul_comm] at this
    rwa [div_eq_mul_inv]
  calc x ^ (-(a₁ / b₁)) * x⁻¹ < x ^ (-(a₁ / b₁)) * (((8 * a₁) ^ (1 / b₁))⁻¹ / 2) :=
        mul_lt_mul_of_pos_left key hpos
    _ = ((8 * a₁) ^ (1 / b₁))⁻¹ * x ^ (-(a₁ / b₁)) / 2 := by ring

/-! ## The answer-reduction step -/

/-- `ε₂ = (ε₁ / (3 σ^{a₂} x^{μ a₂}))^{1/b₂}`. -/
noncomputable def eps2 (a₁ b₁ a₂ b₂ : ℝ) (mu : ℕ) (s x : ℝ) : ℝ :=
  (eps1 a₁ b₁ x / (3 * s ^ a₂ * x ^ ((mu : ℝ) * a₂))) ^ (1 / b₂)

theorem eps2_pos {a₁ b₁ a₂ b₂ : ℝ} {mu : ℕ} {s x : ℝ} (ha₁ : 1 ≤ a₁) (hs : 0 < s)
    (hx : 0 < x) : 0 < eps2 a₁ b₁ a₂ b₂ mu s x := by
  unfold eps2
  have := eps1_pos (b := b₁) ha₁ hx
  have := rpow_pos_of_pos hs a₂
  have := rpow_pos_of_pos hx ((mu : ℝ) * a₂)
  positivity

theorem eps2_le_one {a₁ b₁ a₂ b₂ : ℝ} {mu : ℕ} {s x : ℝ} (ha₁ : 1 ≤ a₁) (hb₁ : 0 < b₁)
    (ha₂ : 1 ≤ a₂) (hb₂ : 0 < b₂) (hs : 1 ≤ s) (hx : 1 ≤ x) :
    eps2 a₁ b₁ a₂ b₂ mu s x ≤ 1 := by
  unfold eps2
  have h0 := eps1_pos (b := b₁) ha₁ (by linarith : 0 < x)
  have h1 := eps1_le_one ha₁ hb₁ hx
  have h2 : 1 ≤ s ^ a₂ := one_le_rpow hs (by linarith)
  have h3 : 1 ≤ x ^ ((mu : ℝ) * a₂) := one_le_rpow hx (by positivity)
  have hden : 0 < 3 * s ^ a₂ * x ^ ((mu : ℝ) * a₂) := by positivity
  refine rpow_le_one (div_nonneg h0.le hden.le) ?_ (by positivity)
  rw [div_le_one hden]
  nlinarith

/-- `ε₂^{b₂} · 3 σ^{a₂} x^{μ a₂} = ε₁`. -/
theorem eps2_rpow {a₁ b₁ a₂ b₂ : ℝ} {mu : ℕ} {s x : ℝ} (ha₁ : 1 ≤ a₁) (hb₂ : 0 < b₂)
    (hs : 0 < s) (hx : 0 < x) :
    eps2 a₁ b₁ a₂ b₂ mu s x ^ b₂ = eps1 a₁ b₁ x / (3 * s ^ a₂ * x ^ ((mu : ℝ) * a₂)) := by
  rw [eps2, ← rpow_mul, one_div, inv_mul_cancel₀ hb₂.ne', rpow_one]
  have := eps1_pos (b := b₁) ha₁ hx
  have := rpow_pos_of_pos hs a₂
  have := rpow_pos_of_pos hx ((mu : ℝ) * a₂)
  positivity

/-- **The answer-reduction step lands inside the introspection margin**: with the margin claim,
`δ₂(ε₂, n) < ε₁`. -/
theorem ar_margin {a₁ b₁ a₂ b₂ : ℝ} {mu : ℕ} {s x : ℝ} (ha₁ : 1 ≤ a₁) (hb₂ : 0 < b₂)
    (hs : 0 < s) (hx : 0 < x)
    (hmargin : s ^ a₂ * x ^ (-((mu : ℝ) * b₂)) < eps1 a₁ b₁ x / 2) :
    s ^ a₂ * (x ^ ((mu : ℝ) * a₂) * eps2 a₁ b₁ a₂ b₂ mu s x ^ b₂ + x ^ (-((mu : ℝ) * b₂))) <
      eps1 a₁ b₁ x := by
  rw [eps2_rpow ha₁ hb₂ hs hx]
  have h1 : 0 < s ^ a₂ := rpow_pos_of_pos hs a₂
  have h2 : 0 < x ^ ((mu : ℝ) * a₂) := rpow_pos_of_pos hx _
  have h3 : s ^ a₂ * (x ^ ((mu : ℝ) * a₂) *
      (eps1 a₁ b₁ x / (3 * s ^ a₂ * x ^ ((mu : ℝ) * a₂)))) = eps1 a₁ b₁ x / 3 := by
    field_simp
  have h0 := eps1_pos (b := b₁) ha₁ hx
  rw [mul_add, h3]
  linarith

/-- **`1/ε₂` is a fixed power of `x`**: `x^{-P} ≤ ε₂` for a universal `P` and `x` past a
threshold, whenever `1 ≤ σ ≤ x^K`. -/
theorem exists_eps2_lower {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 1 ≤ a₁) (hb₁ : 0 < b₁) (ha₂ : 1 ≤ a₂)
    (hb₂ : 0 < b₂) (mu K : ℕ) :
    ∃ P : ℕ, ∃ N : ℕ, ∀ x : ℝ, (N : ℝ) ≤ x → ∀ s : ℝ, 1 ≤ s → s ≤ x ^ (K : ℝ) →
      x ^ (-(P : ℝ)) ≤ eps2 a₁ b₁ a₂ b₂ mu s x := by
  refine ⟨⌈(1 + K * a₂ + mu * a₂ + (1 + a₁) / b₁) / b₂⌉₊, ⌈8 * a₁⌉₊ + 3, fun x hx s hs hsx => ?_⟩
  have hx8 : 8 * a₁ ≤ x := by
    have := Nat.le_ceil (8 * a₁); push_cast at hx; linarith
  have hx3 : (3 : ℝ) ≤ x := by push_cast at hx; linarith
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  -- `1/ε₂ ≤ x^P`
  set E : ℝ := (1 + K * a₂ + mu * a₂ + (1 + a₁) / b₁) / b₂ with hE
  have hE0 : 0 ≤ E := by positivity
  have hP : E ≤ (⌈E⌉₊ : ℝ) := Nat.le_ceil E
  -- the base of `ε₂`, `ε₁ / (3 s^{a₂} x^{μ a₂})`, is at least `x^{-(E b₂)}`
  have hbase : x ^ (-(E * b₂)) ≤ eps1 a₁ b₁ x / (3 * s ^ a₂ * x ^ ((mu : ℝ) * a₂)) := by
    have hs' : s ^ a₂ ≤ x ^ ((K : ℝ) * a₂) := by
      rw [rpow_mul hx0.le]; exact rpow_le_rpow (by linarith) hsx (by linarith)
    have h8 : (8 * a₁) ^ (1 / b₁) ≤ x ^ (1 / b₁) :=
      rpow_le_rpow (by positivity) hx8 (by positivity)
    have hden : 3 * s ^ a₂ * x ^ ((mu : ℝ) * a₂) * (8 * a₁) ^ (1 / b₁) * x ^ (a₁ / b₁) ≤
        x ^ (E * b₂) := by
      have hEb : E * b₂ = 1 + K * a₂ + mu * a₂ + 1 / b₁ + a₁ / b₁ := by
        rw [hE, div_mul_cancel₀ _ hb₂.ne']; ring
      rw [hEb, rpow_add hx0, rpow_add hx0, rpow_add hx0, rpow_add hx0]
      have h3' : (3 : ℝ) ≤ x ^ (1 : ℝ) := by rwa [rpow_one]
      have p1 : 0 ≤ s ^ a₂ := rpow_nonneg (by linarith) _
      have p2 : 0 ≤ x ^ ((mu : ℝ) * a₂) := rpow_nonneg hx0.le _
      have p3 : 0 ≤ (8 * a₁) ^ (1 / b₁) := rpow_nonneg (by positivity) _
      have p4 : 0 ≤ x ^ (a₁ / b₁) := rpow_nonneg hx0.le _
      have p5 : 0 ≤ x ^ ((K : ℝ) * a₂) := rpow_nonneg hx0.le _
      have p6 : 0 ≤ x ^ (1 / b₁) := rpow_nonneg hx0.le _
      have p7 : (0 : ℝ) ≤ x ^ (1 : ℝ) := rpow_nonneg hx0.le _
      have L1 : 3 * s ^ a₂ ≤ x ^ (1 : ℝ) * x ^ ((K : ℝ) * a₂) := mul_le_mul h3' hs' p1 p7
      have L2 : 3 * s ^ a₂ * x ^ ((mu : ℝ) * a₂) ≤
          x ^ (1 : ℝ) * x ^ ((K : ℝ) * a₂) * x ^ ((mu : ℝ) * a₂) :=
        mul_le_mul L1 le_rfl p2 (mul_nonneg p7 p5)
      have L3 : 3 * s ^ a₂ * x ^ ((mu : ℝ) * a₂) * (8 * a₁) ^ (1 / b₁) ≤
          x ^ (1 : ℝ) * x ^ ((K : ℝ) * a₂) * x ^ ((mu : ℝ) * a₂) * x ^ (1 / b₁) :=
        mul_le_mul L2 h8 p3 (mul_nonneg (mul_nonneg p7 p5) p2)
      exact mul_le_mul L3 le_rfl p4 (mul_nonneg (mul_nonneg (mul_nonneg p7 p5) p2) p6)
    have hinv : eps1 a₁ b₁ x = ((8 * a₁) ^ (1 / b₁) * x ^ (a₁ / b₁))⁻¹ := by
      rw [eps1_eq ha₁ hx0, rpow_neg (by positivity), rpow_neg hx0.le, mul_inv]
    have hpos1 : 0 < (8 * a₁) ^ (1 / b₁) * x ^ (a₁ / b₁) := by positivity
    have hpos2 : 0 < 3 * s ^ a₂ * x ^ ((mu : ℝ) * a₂) := by
      have := rpow_pos_of_pos (by linarith : (0:ℝ) < s) a₂
      have := rpow_pos_of_pos hx0 ((mu : ℝ) * a₂)
      positivity
    have hprod : 3 * s ^ a₂ * x ^ ((mu : ℝ) * a₂) * ((8 * a₁) ^ (1 / b₁) * x ^ (a₁ / b₁)) ≤
        x ^ (E * b₂) := by
      calc 3 * s ^ a₂ * x ^ ((mu : ℝ) * a₂) * ((8 * a₁) ^ (1 / b₁) * x ^ (a₁ / b₁))
          = 3 * s ^ a₂ * x ^ ((mu : ℝ) * a₂) * (8 * a₁) ^ (1 / b₁) * x ^ (a₁ / b₁) := by ring
        _ ≤ x ^ (E * b₂) := hden
    rw [hinv, rpow_neg hx0.le]
    calc (x ^ (E * b₂))⁻¹
        ≤ (3 * s ^ a₂ * x ^ ((mu : ℝ) * a₂) * ((8 * a₁) ^ (1 / b₁) * x ^ (a₁ / b₁)))⁻¹ :=
          inv_anti₀ (mul_pos hpos2 hpos1) hprod
      _ = ((8 * a₁) ^ (1 / b₁) * x ^ (a₁ / b₁))⁻¹ / (3 * s ^ a₂ * x ^ ((mu : ℝ) * a₂)) := by
          rw [mul_inv, mul_comm]; exact (div_eq_mul_inv _ _).symm
  -- raise to the power `1/b₂`
  have hfin : x ^ (-E) ≤ eps2 a₁ b₁ a₂ b₂ mu s x := by
    rw [eps2]
    have := rpow_le_rpow (rpow_nonneg hx0.le _) hbase (by positivity : (0:ℝ) ≤ 1 / b₂)
    rwa [← rpow_mul hx0.le, neg_mul, mul_one_div, mul_div_cancel_right₀ _ hb₂.ne'] at this
  refine le_trans ?_ hfin
  exact rpow_le_rpow_of_exponent_le hx1 (by linarith)

/-! ## A universal repetition exponent -/

/-- **A universal repetition exponent** (blueprint `lem:compress-tau`). For the constant `c`
of repetition, a bound `ε ≥ z^{-P}` on the gap and an exponent `β` on the parse length, there
is `τ` such that `exp(-c ε^{13} k / (B + 1)) ≤ 1/2` for all `z ≥ τ`, `k ≥ z^τ` and
`0 ≤ B ≤ z^β`. -/
theorem exists_tau {c : ℝ} (hc : 0 < c) (P beta : ℕ) :
    ∃ tau : ℕ, ∀ z : ℝ, (tau : ℝ) ≤ z → ∀ k : ℝ, z ^ tau ≤ k → ∀ B : ℝ, 0 ≤ B → B ≤ z ^ beta →
      ∀ ε : ℝ, 0 < ε → z ^ (-(P : ℝ)) ≤ ε →
      Real.exp (-(c * ε ^ 13 * k / (B + 1))) ≤ 1 / 2 := by
  refine ⟨13 * P + beta + 1 + ⌈2 / c⌉₊, fun z hz k hk B hB0 hB ε hε hεz => ?_⟩
  have hz2 : 2 / c ≤ z := by
    have := Nat.le_ceil (2 / c); push_cast at hz; linarith
  have hz1 : 1 ≤ z := by
    have : (1 : ℝ) ≤ ((13 * P + beta + 1 + ⌈2 / c⌉₊ : ℕ) : ℝ) := Nat.one_le_cast.2 (by omega)
    linarith
  have hz0 : 0 < z := by linarith
  have hztau : ((13 * P + beta + 1 + ⌈2 / c⌉₊ : ℕ) : ℝ) ≤ z := hz
  -- `ε^13 ≥ z^{-13P}`
  have h13 : z ^ (-(13 * P : ℝ)) ≤ ε ^ 13 := by
    have : (z ^ (-(P : ℝ))) ^ 13 ≤ ε ^ 13 := pow_le_pow_left₀ (rpow_nonneg hz0.le _) hεz 13
    rwa [← rpow_natCast, ← rpow_mul hz0.le, show -(P : ℝ) * (13 : ℕ) = -(13 * P : ℝ) by
      push_cast; ring] at this
  -- `z^τ ≥ z^{13P + β + 1}` and `z^β + 1 ≤ 2 z^β`
  have hnum : z ^ (13 * P + beta + 1) ≤ z ^ (13 * P + beta + 1 + ⌈2 / c⌉₊) :=
    pow_le_pow_right₀ hz1 (by omega)
  have hden : z ^ beta + 1 ≤ 2 * z ^ beta := by
    have : 1 ≤ z ^ beta := one_le_pow₀ hz1
    linarith
  -- the exponent is at least `log 2`
  have hexp : Real.log 2 ≤ c * ε ^ 13 * k / (B + 1) := by
    have hpb : 0 < z ^ beta := pow_pos hz0 _
    have hkey : c * z / 2 ≤ c * ε ^ 13 * k / (B + 1) := by
      rw [le_div_iff₀ (by positivity)]
      have e1 : z ^ (13 * P + beta + 1) = z ^ (13 * P) * z ^ beta * z := by
        rw [pow_add, pow_add, pow_one]
      have e2 : z ^ (-(13 * P : ℝ)) * z ^ (13 * P) = 1 := by
        rw [← rpow_natCast, ← rpow_add hz0]; push_cast; simp
      have h13' : 1 ≤ ε ^ 13 * z ^ (13 * P) := by
        have := mul_le_mul_of_nonneg_right h13 (pow_nonneg hz0.le (13 * P))
        rwa [e2] at this
      calc c * z / 2 * (B + 1) ≤ c * z / 2 * (z ^ beta + 1) := by gcongr
        _ ≤ c * z / 2 * (2 * z ^ beta) := by gcongr
        _ = c * (z ^ beta * z) := by ring
        _ ≤ c * (ε ^ 13 * z ^ (13 * P) * (z ^ beta * z)) := by
            refine mul_le_mul_of_nonneg_left ?_ hc.le
            have := mul_le_mul_of_nonneg_right h13' (by positivity : 0 ≤ z ^ beta * z)
            linarith
        _ = c * ε ^ 13 * z ^ (13 * P + beta + 1) := by rw [e1]; ring
        _ ≤ c * ε ^ 13 * z ^ (13 * P + beta + 1 + ⌈2 / c⌉₊) := by gcongr
        _ ≤ c * ε ^ 13 * k := by gcongr
    have hlog : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    have hcz : 1 ≤ c * z / 2 := by
      rw [div_le_iff₀ hc] at hz2; linarith
    linarith
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num), show (1 / 2 : ℝ)⁻¹ = 2 by norm_num]
  exact (Real.log_le_iff_le_exp (by norm_num)).1 hexp

end MIPRE.Pipeline


