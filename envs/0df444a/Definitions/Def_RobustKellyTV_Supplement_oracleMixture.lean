-- Prove2me | Definitions.Def_RobustKellyTV_Supplement_oracleMixture
-- name    : RobustKellyTV_Supplement_oracleMixture
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:31:34.249445+00:00
-- url     : https://prove2.me/theorems/ac92cc3c-3154-4720-b5b4-339e530f07b6
-- title:
--   The oracle mixture $B^\Pi_n=\int_{\mathcal A}\prod_{t=1}^n E_U(X_t)\,\Pi(dU)$
-- statement:
--   Work in the finite-alphabet total-variation model: observations take values in $\{1,\dots,d\}$, the null class is $\mathcal P_0=B_{\mathrm{TV}}(P,\epsilon_0)$, and for a probability vector $U$ the pointwise Kelly oracle $E_U=(E_U(1),\dots,E_U(d))$ is the clipped likelihood ratio of eq. (12).
--
--   Let $\Pi$ be a mixing measure on probability vectors and $\mathcal A$ a set of alternatives. The **oracle mixture** is the process
--
--   $$B^\Pi_n:=\int_{\mathcal A}\prod_{t=1}^n E_U(X_t)\,\Pi(dU),\qquad n\ge 0,$$
--
--   which averages, over the prior $\Pi$, the wealth of the oracle bettors that each know one alternative $U$. For $n=0$ the empty product gives $B^\Pi_0=\Pi(\mathcal A)$, which equals $1$ when $\Pi$ is a probability measure carried by $\mathcal A$.
--
--   This is the comparison process of Appendix B: a Bayesian mixture over pointwise oracles, whose regret against the oracle growth rate $\Gamma(S)$ Theorem B.1 bounds by the prior mass of a neighbourhood of $S$.
--
--   **Formalization Note** The observation $X_t$ ($t\ge1$) is coordinate $t-1$ of a sequence $\omega:\mathbb N\to\mathrm{Fin}\,d$. The integral is the Bochner integral over $\mathcal A$; under the assumptions of Appendix B ($\mathcal A\subseteq\mathcal K_{m,\delta}$ compact) the integrand is continuous and bounded on $\mathcal A$, so the integral is the paper's. $E_U$ is the published `RobustKellyTV.oracleE`.
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, Appendix B, eq. (53), p.35

import Mathlib
import Definitions.Def_RobustKellyTV_oracleE

open MeasureTheory

namespace RobustKellyTV.Supplement

variable {d : ℕ}

/-- The **oracle mixture** `B^Π_n = ∫_A ∏_{t=1}^n E_U(X_t) Π(dU)` of A. Saha, A. Ramdas,
*Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis
testing*, arXiv:2611.02130v1, Appendix B, eq. (53), p.35.

`prior` is the mixing measure `Π` on `Fin d → ℝ`, `A` the compact set of alternatives it is
supported on, and `E_U` the published pointwise Kelly oracle `RobustKellyTV.oracleE`.

**Formalization Note.** The paper's observation `X_t` (`t ≥ 1`) is coordinate `t − 1` of
`ω : ℕ → Fin d`, so the product runs over the coordinates `s ∈ {0, …, n − 1}`; the empty product
gives `B^Π_0 = Π(A)`, which is `1` for a probability measure carried by `A`. The integral is the
Bochner integral over `A` with respect to `Π`; under the assumptions of Appendix B
(`A ⊆ K_{m,δ}` compact) the integrand is continuous and bounded on `A` (Lemma A.1), so the integral
is the paper's. -/
noncomputable def oracleMixture (σ : Setting d) (prior : Measure (Fin d → ℝ))
    (A : Set (Fin d → ℝ)) (n : ℕ) (ω : ℕ → Fin d) : ℝ :=
  ∫ U in A, ∏ s ∈ Finset.range n, oracleE σ U (ω s) ∂prior

end RobustKellyTV.Supplement


