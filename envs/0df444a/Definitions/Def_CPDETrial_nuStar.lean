-- Prove2me | Definitions.Def_CPDETrial_nuStar
-- name    : CPDETrial_nuStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:48:44.736415+00:00
-- url     : https://prove2.me/theorems/85a6d278-a6df-4658-a987-9fccb98e5587
-- title:
--   cPDE allocation index $\nu^*_i(\mu^t,\Sigma^t)$ (eq. (EC.8))
-- statement:
--   For costs $c$, sampling variances $\lambda$, an arm $i$ and a belief $(\mu,\Sigma)$, the cPDE allocation index is
--
--   $$
--   \nu^*_i(\mu,\Sigma)=\sup_{T\ge 1}\ \mathbb E\left[-T+\frac{1}{c_i}\max_j\left\{\mu_j+\frac{\Sigma_{i,j}}{\Sigma_{i,i}}Z^{T}_i\right\}\right]-\frac{1}{c_i}\max_j\{\mu_j\},
--   $$
--
--   the supremum being over stopping times $T\ge 1$ of the lookahead observations of arm $i$ (filtration of $Z$), and the expectation under the predictive law of $Z$. It measures, per unit cost of arm $i$, the value of sampling arm $i$ adaptively before selecting an arm, net of the sampling cost. The cPDE policy allocates the next patient to an arm maximizing this index.
--
--   **Formalization Note** This is the paper's (EC.8). Its (15) lacks the term $-\frac1{c_i}\max_j\mu_j$, and its (20) folds the kinks at negative intercept differences onto the positive side; the proof of Theorem 1 uses (EC.8). The supremum runs over stopping times with $T\ge1$, $T<\infty$ a.s., $\mathbb E[T]<\infty$ and an integrable payoff; a stopping time with $\mathbb E[T]=\infty$ has value $-\infty$, so this does not change the supremum. The set of values is nonempty ($T\equiv1$) and bounded above (Lemma EC.1), so Lean's `sSup` is the true supremum.
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. ec3, eq. (EC.8); see also pp. 11–12, eqs. (14), (15), (20)

import Mathlib
import Definitions.Def_CPDETrial_zProc
import Definitions.Def_CPDETrial_zFilt
import Definitions.Def_CPDETrial_idxP
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **The cPDE allocation index `ν*_i(µ^t, Σ^t)`, eq. (EC.8).**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), App. B.4, eq. (EC.8), p. ec3:
"`ν*_i(µ^t,Σ^t) = sup_{T_i≥1} E[ −T_i + (1/c_i) max_j { µ^t_j + (Σ^t_{i,j}/Σ^t_{i,i}) Z^{T_i}_i } | µ^t,Σ^t ] − (1/c_i) max_j{µ^t_j}`".

For costs `c`, sampling variances `lam`, an arm `i` and a belief `(m, S) = (µ^t, Σ^t)`:
the supremum, over stopping times `T ≥ 1` of the lookahead observations of arm `i` (the
filtration `zFilt λ_i S_ii`), of `E[−T + (1/c_i) max_j (m_j + (S_ij/S_ii) Z^T)]`, minus
`(1/c_i) max_j m_j`. The expectation is over the predictive law (`idxP`), under which
`Z^τ = zProc λ_i S_ii τ` has the law (10).

**Formalization Note.**
1. Of the paper's three formulas for `ν*` this is (EC.8), the one the proof of Theorem 1 uses
   (Lemma EC.1). Formula (15) (p. 11) lacks the term `−(1/c_i) max_j µ^t_j` of (7)/(14), and with
   it Theorem 1(ii) would fail; formula (20) (p. 12) folds the kinks at negative `d_(l)` onto the
   positive side, which agrees with (EC.8) for deterministic `T` but not for adaptive `T`. The
   page's "setting `Δ = 0`" is read as `Δ = 1` (the undiscounted case of §3.3).
2. Stopping times are `WithTop ℕ`-valued; the set requires `T ≥ 1`, `T < ∞` a.s., `E[T] < ∞` and
   an integrable payoff. For an admissible `T` with `E[T] = ∞` the expectation is `−∞` (the
   terminal term is integrable since `Z` is bounded in `L²`, Prop. 3), so the restriction does not
   change the supremum. `untopA` (value `0` at `⊤`) is only evaluated on the null set `{T = ⊤}`.
3. `sSup` of a real set is `0` when the set is empty or unbounded above. The set is nonempty
   (`T ≡ 1`) and bounded above (Lemma EC.1), so `sSup` is the true supremum.
4. `⨆ j : Fin M` is the finite maximum for `M ≥ 1` (the paper has `M ≥ 2`). `S_ij / S_ii` is the
   slope `b_j` of (16); `S_ii > 0` along the posterior recursion. -/
noncomputable def nuStar {M : ℕ} (c : Fin M → ℝ) (lam : Fin M → ℝ≥0) (i : Fin M)
    (m : Fin M → ℝ) (S : Matrix (Fin M) (Fin M) ℝ) : ℝ :=
  sSup {v : ℝ | ∃ T : (ℕ → ℝ) → WithTop ℕ,
      IsStoppingTime (zFilt (lam i) (S i i)) T ∧ (∀ ω, (1 : WithTop ℕ) ≤ T ω) ∧
      (∀ᵐ ω ∂idxP, T ω ≠ ⊤) ∧
      Integrable (fun ω => (((T ω).untopA : ℕ) : ℝ)) idxP ∧
      Integrable (fun ω => ⨆ j, (m j + S i j / S i i *
        stoppedValue (fun τ => zProc (lam i) (S i i) τ) T ω)) idxP ∧
      v = ∫ ω, (-(((T ω).untopA : ℕ) : ℝ) + (1 / c i) * ⨆ j, (m j + S i j / S i i *
        stoppedValue (fun τ => zProc (lam i) (S i i) τ) T ω)) ∂idxP}
    - (1 / c i) * ⨆ j, m j

end CPDETrial


