-- Prove2me | Definitions.Def_TaoFivePrimes_VaughanTruncation
-- name    : TaoFivePrimes_VaughanTruncation
-- status  : Definition
-- author  : @Hartmann_Psi
-- created : 2026-09-13T16:11:50.156197+00:00
-- url     : https://prove2.me/theorems/082e4d99-e99e-4dcd-9fa3-d496047b54c3
-- title:
--   Truncation of an arithmetic function at a real cutoff
-- statement:
--   Tao's proof of his variant of Vaughan's identity (Lemma 4.11) begins by splitting both the Möbius function and the von Mangoldt function at a real cutoff:
--   $$\mu \;=\; \mu\mathbf 1_{\le U} + \mu\mathbf 1_{>U},\qquad
--     \Lambda \;=\; \Lambda\mathbf 1_{\le V} + \Lambda\mathbf 1_{>V},$$
--   where $\mathbf 1_{\le U}(n)$ is $1$ when $n\le U$ and $0$ otherwise. This file provides those two truncation operators for an arbitrary real-valued arithmetic function.
--
--   For a real cutoff $U$ and an arithmetic function $f$, `truncLe U f` is the arithmetic function
--   $$n \longmapsto \begin{cases} f(n), & n \le U,\\ 0, & n > U,\end{cases}$$
--   and `truncGt U f` is its complement. Both are again arithmetic functions — they vanish at $0$ because $f$ does — and the file records the two projection `simp` lemmas together with the only structural fact needed downstream, namely that the two pieces reconstruct the original:
--   $$\texttt{truncLe } U\, f + \texttt{truncGt } U\, f = f .$$
--
--   The cutoff is a **real** number rather than a natural one, matching the paper: the parameters $U, V$ in Vaughan's identity are optimised over the reals, and no integrality is ever assumed of them.
--
--   Also provided are `zetaR` and `moebiusR`, the real-valued incarnations of the constant-one function $\zeta$ and of $\mu$, so that all four factors of Vaughan's identity live in the single Dirichlet-convolution ring `ArithmeticFunction ℝ`, in which the identity is an equation between ring elements.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, Section 4, proof of Lemma 4.11: "We split mu = mu 1_{<=U} + mu 1_{>U} and Lambda = Lambda 1_{<=V} + Lambda 1_{>V}, where 1_{<=U}(n) := 1_{n <= U}, and similarly for 1_{>U}, 1_{<=V}, 1_{>V}."

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Truncation of arithmetic functions at a real cutoff

Source: Terence Tao, *Every odd number greater than 1 is the sum of at most five primes*,
https://arxiv.org/abs/1201.6656, Section 4, proof of Lemma 4.11 (the variant of Vaughan's
identity), where the Moebius and von Mangoldt functions are split as
`mu = mu * 1_{<= U} + mu * 1_{> U}` and `Lambda = Lambda * 1_{<= V} + Lambda * 1_{> V}`.

Only the two truncation operators and their structural lemmas live here; the Vaughan
identity itself is a separate theorem.
-/

namespace TaoFivePrimes

/-- `truncLe U f` is the arithmetic function agreeing with `f` on arguments `n` with
`(n : ℝ) ≤ U`, and vanishing elsewhere.  Tao writes this as `f 1_{≤ U}`. -/
noncomputable def truncLe (U : ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if (n : ℝ) ≤ U then f n else 0, by simp⟩

/-- `truncGt U f` is the arithmetic function agreeing with `f` on arguments `n` with
`U < (n : ℝ)`, and vanishing elsewhere.  Tao writes this as `f 1_{> U}`. -/
noncomputable def truncGt (U : ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if U < (n : ℝ) then f n else 0, by simp⟩

@[simp] theorem truncLe_apply (U : ℝ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    truncLe U f n = if (n : ℝ) ≤ U then f n else 0 := rfl

@[simp] theorem truncGt_apply (U : ℝ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    truncGt U f n = if U < (n : ℝ) then f n else 0 := rfl

/-- The two truncations of `f` at `U` add back up to `f`. -/
theorem truncLe_add_truncGt (U : ℝ) (f : ArithmeticFunction ℝ) :
    truncLe U f + truncGt U f = f := by
  ext n
  rw [ArithmeticFunction.add_apply, truncLe_apply, truncGt_apply]
  by_cases h : (n : ℝ) ≤ U
  · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
  · rw [if_neg h, if_pos (not_le.mp h), zero_add]

/-- The real-valued zeta arithmetic function `ζ(n) = 1` for `n ≥ 1`. -/
noncomputable abbrev zetaR : ArithmeticFunction ℝ :=
  ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)

/-- The real-valued Moebius arithmetic function. -/
noncomputable abbrev moebiusR : ArithmeticFunction ℝ :=
  ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)

end TaoFivePrimes


