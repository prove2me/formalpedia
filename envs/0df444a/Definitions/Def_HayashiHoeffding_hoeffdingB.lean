-- Prove2me | Definitions.Def_HayashiHoeffding_hoeffdingB
-- name    : HayashiHoeffding_hoeffdingB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:18:12.291546+00:00
-- url     : https://prove2.me/theorems/8696fdb1-70f2-421a-8413-2f3a9f4e437c
-- title:
--   Hoeffding-type exponent $B(r|\rho\|\sigma)$
-- statement:
--   Let $\rho$, $\sigma$ be density operators on a complex Hilbert space $\mathcal H$ and $r \in \mathbb R$. The optimal exponent of the error probability of the first kind under an exponential constraint of rate $r$ on the error probability of the second kind is
--
--   $$B(r|\rho\|\sigma) := \sup_{\{T_n\}} \left\{ \liminf_{n\to\infty} \frac{-\log \operatorname{Tr} \rho^{\otimes n} T_n^c}{n} \;\middle|\; \liminf_{n\to\infty} \frac{-\log \operatorname{Tr}\sigma^{\otimes n} T_n}{n} \ge r \right\},$$
--
--   where the supremum runs over all sequences of tests $T_n$ on $\mathcal H^{\otimes n}$ ($0 \le T_n \le I$), $T_n^c = I - T_n$, and $-\log 0 = +\infty$. The supremum is taken in $[-\infty, +\infty]$; the feasible set is never empty, since $T_n = 0$ has type-II error $0$.
--
--   **Formalization Note**
--   1. A test sequence is a family $T_k$ on `tensorPow H k` $= \mathcal H^{\otimes (k+1)}$ (copies indexed $k \mapsto k+1$).
--   2. The page prints "$\ge r$" inside the numerator of the constraint; it is read as the constraint $\liminf_n (-\log \operatorname{Tr}\sigma^{\otimes n}T_n)/n \ge r$.
--   3. Both limits are underlined on the page, i.e. lower limits (`rate`).
--   4. Error probabilities are the real parts of `basisOperatorTrace`; the supremum is `sSup` in `EReal`.
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, "Formulation and main results", p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02
import Definitions.Def_HayashiHoeffding_tensorPow
import Definitions.Def_HayashiHoeffding_opTensorPow
import Definitions.Def_HayashiHoeffding_IsTest
import Definitions.Def_HayashiHoeffding_rate

open QAlgorithms.Papers.Independent.Next46.P02

namespace HayashiHoeffding

universe u

/-- The optimal exponent `B(r|ρ‖σ)` of the error probability of the first kind under an
exponential constraint of rate `r` on the error probability of the second kind:
the supremum, over all sequences of tests `{T_n}` on `H^{⊗n}` with
`liminf_n −log Tr σ^{⊗n} T_n / n ≥ r`, of `liminf_n −log Tr ρ^{⊗n} (I − T_n) / n`.

Hayashi, arXiv:quant-ph/0611013v2, "Formulation and main results", p.3:
"B(r|ρ‖σ) def= sup_{Tn} { lim_{n→∞} −log Trρ⊗nT^c_n / n | lim_{n→∞} −log Trσ⊗nTn ≥ r / n }"
(both `lim` underlined, i.e. `lim inf`).

**Formalization Note.**
1. Copies are indexed `k ↦ k + 1`: a test sequence is a family `T k` of tests on
   `tensorPow H k = H^{⊗(k+1)}`, and `ρ^{⊗(k+1)} = opTensorPow ρ k`.
2. The printed constraint has "≥ r" inside the numerator; it is read as
   `liminf_n (−log Tr σ^{⊗n} T_n)/n ≥ r`.
3. Traces are `basisOperatorTrace`; the error probabilities are the real parts of the traces
   (they are real and in `[0,1]` for density operators and tests).
4. The supremum is `sSup` in `EReal` over every feasible test sequence; the set is never empty
   (the zero test has type-II error `0`, of rate `+∞`). -/
noncomputable def hoeffdingB {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ρ σ : H →L[ℂ] H) (r : ℝ) : EReal :=
  sSup {e : EReal | ∃ T : (k : ℕ) → (tensorPow H k →L[ℂ] tensorPow H k),
    (∀ k, IsTest (T k)) ∧
    (r : EReal) ≤ rate (fun k => (basisOperatorTrace (opTensorPow σ k * T k)).re) ∧
    e = rate (fun k => (basisOperatorTrace (opTensorPow ρ k * (1 - T k))).re)}

end HayashiHoeffding


