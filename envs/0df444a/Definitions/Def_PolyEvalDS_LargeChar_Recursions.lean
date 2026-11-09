-- Prove2me | Definitions.Def_PolyEvalDS_LargeChar_Recursions
-- name    : PolyEvalDS_LargeChar_Recursions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:42.917063+00:00
-- url     : https://prove2.me/theorems/af21404a-545a-4f58-bd5e-0f7b49a860ec
-- title:
--   The grid bound $B'$ and the two recursions of the proofs
-- statement:
--   Three real-analytic objects from §3.
--
--   1. The **grid bound** of Proposition 3.2:
--   $$B'=\Bigl\lfloor\exp\bigl(\tfrac1r\ln B+r\ln d+r\ln r\bigr)\Bigr\rfloor.$$
--   2. The **curve recursion** of the proof of Theorem 1.1: $B_0=p$ and
--   $$B_{i+1}=\begin{cases}\exp\bigl(3\sqrt{\ln B_i\ln d}\bigr)&\text{if }\ln B_i\le d,\\ \exp\bigl(3\sqrt{\ln B_i\ln\ln B_i}\bigr)&\text{otherwise.}\end{cases}$$
--   3. The **line recursion** of the proof of Theorem 1.2: $B_0=d^{60}$ and $B_{i+1}=2\sqrt{dB_i}$.
--
--   These drive the recursion bounds of the two main theorems.
--
--   **Formalization Note** The sequences are real-valued, as on the page. `Real.log` is total, but $B_0>1$ and every later term is an exponential of a nonnegative number whenever $p>d^{60}$, so the logarithms in the branches stay meaningful in the milestones that use them.
-- source:
--   Hiroki Okada, Rachel Player, Simon Pohmann, An Algebraic Polynomial Evaluation Datastructure for Fields of Large Characteristic, STOC 2027 submission #463 (October 2026), source.pdf SHA-256 33e2ace7597795eb2f5be3a68d2beb3fd8c69139336faf4559faf1452360646b, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/463.pdf, Proposition 3.2, p. 7; proof of Theorem 1.1, p. 8; proof of Theorem 1.2, p. 10

import Mathlib

namespace PolyEvalDS.LargeChar

/-- The grid bound of Proposition 3.2, p. 7:
`B′ := ⌊exp((1/r) ln B + r ln d + r ln r)⌋`. -/
noncomputable def curveBox (B d r : ℕ) : ℕ :=
  ⌊Real.exp ((1 / (r : ℝ)) * Real.log B + (r : ℝ) * Real.log d + (r : ℝ) * Real.log r)⌋₊

/-- The sequence of the proof of Theorem 1.1, p. 8: `B₀ := p`, and
`B_{i+1} = exp(3√(ln B_i ln d))` if `ln B_i ≤ d`, else `exp(3√(ln B_i ln ln B_i))`. -/
noncomputable def curveSeq (p d : ℕ) : ℕ → ℝ
  | 0 => (p : ℝ)
  | i + 1 =>
    if Real.log (curveSeq p d i) ≤ (d : ℝ) then
      Real.exp (3 * Real.sqrt (Real.log (curveSeq p d i) * Real.log d))
    else
      Real.exp (3 * Real.sqrt (Real.log (curveSeq p d i) * Real.log (Real.log (curveSeq p d i))))

/-- The sequence of the proof of Theorem 1.2, p. 10: `B₀ := d⁶⁰`, `B_{i+1} = 2√(d B_i)`. -/
noncomputable def lineSeq (d : ℕ) : ℕ → ℝ
  | 0 => (d : ℝ) ^ 60
  | i + 1 => 2 * Real.sqrt ((d : ℝ) * lineSeq d i)

end PolyEvalDS.LargeChar


