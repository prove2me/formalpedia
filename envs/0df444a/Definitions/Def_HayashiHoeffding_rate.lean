-- Prove2me | Definitions.Def_HayashiHoeffding_rate
-- name    : HayashiHoeffding_rate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:54.814854+00:00
-- url     : https://prove2.me/theorems/a4e95c48-1427-4519-915d-f0fd299bfcad
-- title:
--   Exponential decreasing rate $\liminf_n -\frac{1}{n}\log p_n$
-- statement:
--   For a sequence $(p_n)_{n \ge 1}$ of nonnegative reals (error probabilities), its **exponential decreasing rate** is
--
--   $$\liminf_{n \to \infty} \frac{-\log p_n}{n} \in [-\infty, +\infty] ,$$
--
--   with $-\log 0 = +\infty$.
--
--   This is the exponent appearing twice in the definition of $B(r|\rho\|\sigma)$, where both limits are lower limits.
--
--   **Formalization Note** The sequence is indexed from $0$, with entry $k$ the value for $n = k+1$ copies, so the $k$-th term is divided by $k + 1$. The logarithm is `elog`, the lower limit `Filter.liminf` in `EReal` (it always exists).
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, "Formulation and main results", p.3

import Mathlib
import Definitions.Def_HayashiHoeffding_elog

open Filter

namespace HayashiHoeffding

/-- The exponential decreasing rate of a sequence of error probabilities:
`liminf_{n→∞} −log p_n / n`, in the extended reals, where the entry `p k` is the probability
for `n = k + 1` copies.

Hayashi, arXiv:quant-ph/0611013v2, "Formulation and main results", p.3, the two expressions
"lim_{n→∞} −log Trρ⊗nT^c_n / n" and "lim_{n→∞} −log Trσ⊗nTn / n" in the definition of
`B(r|ρ‖σ)`; both `lim` are underlined on the page, i.e. lower limits.

**Formalization Note.** Copies are indexed `k ↦ k + 1`, so the `k`-th term is divided by
`k + 1`. The logarithm is `elog` (`log 0 = −∞`), so a vanishing probability contributes `+∞`;
the lower limit is `Filter.liminf` in `EReal` and always exists. -/
noncomputable def rate (p : ℕ → ℝ) : EReal :=
  liminf (fun k : ℕ => -elog (p k) / (((k + 1 : ℕ) : ℝ) : EReal)) atTop

end HayashiHoeffding


