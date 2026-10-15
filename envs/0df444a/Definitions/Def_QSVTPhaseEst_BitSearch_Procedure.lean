-- Prove2me | Definitions.Def_QSVTPhaseEst_BitSearch_Procedure
-- name    : QSVTPhaseEst_BitSearch_Procedure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:47.435506+00:00
-- url     : https://prove2.me/theorems/187b8efd-5752-45b2-a8b7-0fdb5cf7f9f6
-- title:
--   §V A, (64)–(65), Algorithm 3, Appendix B, pp. 15–17, 27–29 — singular value σ^j(θ), outcome rule with Δ-region, the bit-search recursion for θ, the additional j = 0 iteration and the output
-- statement:
--   This file fixes the objects of *phase estimation by QSVT* (Algorithm 3 of Martyn, Rossi, Tan and Chuang). Throughout, $U$ is a unitary with eigenvector $|u\rangle$, $U|u\rangle = e^{2\pi i\varphi}|u\rangle$, and the phase satisfies $0 \le \varphi < 1$. The procedure runs $n$ iterations $j = n-1, n-2, \dots, 0$ and maintains a binary fraction $\theta = 0.\theta_1\theta_2\ldots$
--
--   1. **Singular value (64).** For $j \in \mathbb N$ and $\theta \in \mathbb R$, the matrix $A_j(\theta) = \tfrac12(I + e^{-2\pi i\theta}U^{2^j})$ has, on $|u\rangle$, the singular value
--   $$\sigma^j(\theta) = \bigl|\cos\bigl(\pi(2^j\varphi - \theta)\bigr)\bigr|.$$
--   2. **Δ-region.** For a width $\Delta$, the closed interval $\bigl[\tfrac1{\sqrt2} - \tfrac\Delta2,\ \tfrac1{\sqrt2} + \tfrac\Delta2\bigr]$, where the phase-estimation polynomial is not a good approximation to the sign function.
--   3. **Outcome rule.** A measured bit $b$ is *admissible* at singular value $s$ if $s < \tfrac1{\sqrt2} - \tfrac\Delta2$ forces $b = 1$ and $s > \tfrac1{\sqrt2} + \tfrac\Delta2$ forces $b = 0$; inside the Δ-region either bit may occur. For $\Delta = 0$ this is the exact sign function $\Theta(\tfrac1{\sqrt2} - s)$ of (66), with either bit allowed at the tie $s = \tfrac1{\sqrt2}$.
--   4. **θ after each iteration.** $\theta_n = 0$ (line 1), and iteration $j$ halves $\theta$ (line 4) and sets its first binary digit to the measured bit $b_j$ (line 8):
--   $$\theta_j = \tfrac12\,\theta_{j+1} + \tfrac12\, b_j \qquad (0 \le j < n).$$
--   5. **Runs.** A run of the loop is a bit sequence $(b_j)$ such that, for every $j < n$, $b_j$ is admissible at $\sigma^j(\theta_{j+1}/2)$. A complete run adds a bit $b_0'$ for the additional $j = 0$ iteration (lines 9–10), admissible at the singular value $\bigl|\cos\bigl(\pi(\varphi/2 - \theta_0/2)\bigr)\bigr|$.
--   6. **Output.** $\theta = b_0' + \theta_0$, i.e. $\theta_0.\theta_1\theta_2\ldots\theta_n$ with units digit $b_0'$.
--
--   These objects carry every statement of the mission: the measurement enters only through the outcome rule, and a theorem about the procedure quantifies over all runs.
--
--   **Formalization Note** Bits are `Bool` (`true` = 1). `thetaAfter n b j` is $\theta_j$, computed by `thetaIter` after $n - j$ completed iterations. The additional $j = 0$ iteration is encoded as Appendix B 1 b (p. 29) analyses it, "identical to the case above, just with the modification that $\varphi_0 = 0$": the general step applied to $0.\varphi_0\varphi_1\ldots = \varphi/2$ with $\theta$ halved. Read literally, line 9 of Algorithm 3 would use $|\cos(\pi(\varphi - \theta_0))|$, under which the paper's own example $\varphi = 0.1110101_2$, $n = 2$ would output $0.00$ instead of $1.00$. The outcome rule is stated in terms of the singular value only and never through a value of $\Theta$; the signs of $\Theta$ printed in (B1)–(B3) and Lemma 12's proof are inconsistent with (66), while the bits (1 iff $\sigma < 1/\sqrt2$) are consistent everywhere.
-- source:
--   Martyn, Rossi, Tan & Chuang, A Grand Unification of Quantum Algorithms, arXiv:2105.02859v5, pp. 15–17, (64)–(66), Algorithm 3 (p. 17), Δ-region (p. 17); Appendix B 1 b, p. 29, paragraph "Furthermore, we must discuss the additional j = 0 iteration" and the tie caveat

import Mathlib

namespace QSVTPhaseEst.BitSearch

/-- (64): `σ^j(θ) = |cos(π(2^j φ − θ))|`, the singular value of `A_j(θ) = ½(I + e^{−2πiθ}U^{2^j})`
on the eigenvector `|u⟩` of `U` with eigenvalue `e^{2πiφ}`. -/
noncomputable def sigma (φ : ℝ) (j : ℕ) (θ : ℝ) : ℝ :=
  |Real.cos (Real.pi * ((2 : ℝ) ^ j * φ - θ))|

/-- The closed Δ-region `[1/√2 − Δ/2, 1/√2 + Δ/2]` (p. 17), where the phase-estimation polynomial
does not approximate the sign function. -/
def InDeltaRegion (Δ s : ℝ) : Prop :=
  1 / Real.sqrt 2 - Δ / 2 ≤ s ∧ s ≤ 1 / Real.sqrt 2 + Δ / 2

/-- Outcome rule for the measured bit `b` at singular value `s`: below the Δ-region the measured
bit is `1` (`true`), above it the bit is `0` (`false`); inside the closed Δ-region either bit may
occur. With `Δ = 0` this is the exact sign function `Θ(1/√2 − s)` of (66), ties at `s = 1/√2`
allowed either way (p. 29). -/
def Admissible (Δ s : ℝ) (b : Bool) : Prop :=
  (s < 1 / Real.sqrt 2 - Δ / 2 → b = true) ∧ (1 / Real.sqrt 2 + Δ / 2 < s → b = false)

/-- The numerical value of a bit: `true ↦ 1`, `false ↦ 0`. -/
noncomputable def bitVal (b : Bool) : ℝ := if b then 1 else 0

/-- `thetaIter n b k` is `θ` after `k` completed loop iterations of Algorithm 3
(iterations `j = n − 1, …, n − k`): `θ = 0` initially (line 1), and iteration `j` halves `θ`
(line 4) and sets its first binary digit to the measured bit `b j` (line 8), i.e.
`θ ← θ/2 + b_j/2`. -/
noncomputable def thetaIter (n : ℕ) (b : ℕ → Bool) : ℕ → ℝ
  | 0 => 0
  | k + 1 => thetaIter n b k / 2 + bitVal (b (n - 1 - k)) / 2

/-- `θ` at the end of iteration `j` of the loop, for `j ≤ n` (`j = n`: before the loop, `θ = 0`).
For `j < n` it satisfies `thetaAfter n b j = thetaAfter n b (j + 1) / 2 + bitVal (b j) / 2`. -/
noncomputable def thetaAfter (n : ℕ) (b : ℕ → Bool) (j : ℕ) : ℝ := thetaIter n b (n - j)

/-- A run of the loop of Algorithm 3 (lines 1–8), i.e. of the algorithm sketch of §V A 1:
at every iteration `j < n` the measured bit `b j` is an admissible outcome for the singular value
`σ^j` evaluated at the halved `θ` (line 4 precedes line 5). -/
def IsLoopRun (Δ φ : ℝ) (n : ℕ) (b : ℕ → Bool) : Prop :=
  ∀ j < n, Admissible Δ (sigma φ j (thetaAfter n b (j + 1) / 2)) (b j)

/-- The singular value of the additional `j = 0` iteration (Algorithm 3, lines 9–10) as analysed
in Appendix B 1 b (p. 29): the general step applied to `0.φ₀φ₁φ₂… = φ/2` with `θ` halved, i.e.
`|cos(π(φ/2 − θ₀/2))|`, where `θ₀` is `θ` at the end of the loop. -/
noncomputable def extraSigma (φ : ℝ) (n : ℕ) (b : ℕ → Bool) : ℝ :=
  sigma (φ / 2) 0 (thetaAfter n b 0 / 2)

/-- A complete run of Algorithm 3: an admissible run of the loop, followed by an admissible
outcome `b₀` of the additional `j = 0` iteration. -/
def IsRun (Δ φ : ℝ) (n : ℕ) (b : ℕ → Bool) (b₀ : Bool) : Prop :=
  IsLoopRun Δ φ n b ∧ Admissible Δ (extraSigma φ n b) b₀

/-- The output `θ = θ₀.θ₁θ₂…θₙ` of Algorithm 3: the units digit `b₀` set by the additional
iteration plus `θ` at the end of the loop. -/
noncomputable def output (n : ℕ) (b : ℕ → Bool) (b₀ : Bool) : ℝ := bitVal b₀ + thetaAfter n b 0

end QSVTPhaseEst.BitSearch


