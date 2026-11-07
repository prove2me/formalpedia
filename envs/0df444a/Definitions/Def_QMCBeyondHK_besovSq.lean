-- Prove2me | Definitions.Def_QMCBeyondHK_besovSq
-- name    : QMCBeyondHK_besovSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:56.741035+00:00
-- url     : https://prove2.me/theorems/96cbc197-c9e4-4cc4-8bb7-7cbe535e093c
-- title:
--   Squared Haar–Besov seminorm $\|f\|_B^2$
-- statement:
--   The squared **Haar–Besov seminorm** of $f \in L^2([0,1)^d)$ is
--   $$
--   \|f\|_B^2 := \sum_{j,k} \frac{|\langle f, H_{j,k}\rangle|^2}{\|H_{j,k}\|_2^4},
--   $$
--   the sum running over all Haar indices $(j,k)$, the constant function $H_{0,0} = 1$ included.
--
--   It weights each Haar coefficient by the inverse square of the support volume, so fine-scale oscillation is penalized; the integration-error bounds of the mission are first proved in terms of $\|f_s\|_B^2$.
--
--   **Formalization Note** The index range is that of §2 ($0 \le k_i < 2^{j_i - 1}$ when $j_i \ge 1$, $k_i = 0$ when $j_i = 0$); Definition 2.1 prints $0 \le k_i < 2^{j_i}$, whose extra indices name no Haar function. The sum is an unconditional sum of nonnegative terms in $[0,\infty]$, so a divergent sum is $+\infty$.
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), Definition 2.1, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_QMCBeyondHK_haar

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- The squared Haar–Besov seminorm `‖f‖²_B := ∑_{j,k} |⟨f, H_{j,k}⟩|² / ‖H_{j,k}‖₂⁴`
(arXiv:2609.10921, sha256 bc273e88…, Definition 2.1, p.6, PDF p.8).

**Formalization Note** The sum runs over every Haar index of §2 (`HaarIdx d`), the constant
`H_{0,0}` included; Definition 2.1's printed range `0 ≤ k_i < 2^{j_i}` is read as §2's range
`k_i < 2^{j_i−1}` (`j_i ≥ 1`), `k_i = 0` (`j_i = 0`). The value is an unconditional sum of
nonnegative terms in `ℝ≥0∞`, so a divergent sum is `⊤`, never a junk `0`. -/
noncomputable def besovSq (d : ℕ) (f : (Fin d → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑' H : HaarIdx d, ENNReal.ofReal (l2inner d f (haar H) ^ 2 / haarNormSq H ^ 2)

end QMCBeyondHK


