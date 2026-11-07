-- Prove2me | Definitions.Def_CalibeatBandit_pseudoSwapRegret
-- name    : CalibeatBandit_pseudoSwapRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:28.216953+00:00
-- url     : https://prove2.me/theorems/b0ee4591-d922-4a68-9815-1c06003d5803
-- title:
--   Pseudo swap regret $R^{\mathrm{SR},p}_T$
-- statement:
--   For mixed strategies $p_t$ and reward vectors $y_t$, let $g^{\mathrm{SR}}_t(f)=\sum_i p_t(i)\,y_t(f(i))$ be the expected payoff after post-processing by $f\in\Sigma_{\mathcal A}$. The **pseudo swap regret** is
--   $$R^{\mathrm{SR},p}_T=\max_{f\in\Sigma_{\mathcal A}}\sum_{t=1}^T\bigl(g^{\mathrm{SR}}_t(f)-\langle p_t,y_t\rangle\bigr).$$
--   It is the proof device that the analysis bounds before converting to $\mathrm{SR}_T$ by a sampling argument.
--
--   **Formalization Note** Rounds are $0,\dots,T-1$; $\langle p,y\rangle$ is `p ⬝ᵥ y`; the maximum is `Finset.sup'`.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §C.1 (proof of Lemma C.1), p.30 (PDF 30)

import Mathlib

set_option autoImplicit false

namespace CalibeatBandit

open Matrix

/-- **Pseudo swap regret `R^{SR,p}_T`.** For mixed strategies `p_t` and reward vectors `y_t`,
with `g^SR_t(f) = ∑_i p_t(i) y_t(f(i))`,
`R^{SR,p}_T = max_f ∑_{t=1}^T (g^SR_t(f) − ⟨p_t, y_t⟩)`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.1, proof of
Lemma C.1, p.30: "For a fixed post-processing rule f ∈ Σ_𝒜, let the expected payoff after
processing be g^SR_t(f) = ∑_i p_t(i)y_t(f(i)) … define the corresponding swap regret as
R^{a,p}_T := max_f ∑_{t=1}^T (g^a_t(f) − ⟨p_t, y_t⟩)."

**Formalization Note.** Rounds are `0, …, T − 1`; `⟨p, y⟩` is `p ⬝ᵥ y`; the maximum over all
`f : Fin K → Fin K` is `Finset.sup'`. -/
def pseudoSwapRegret {K : ℕ} (T : ℕ) (p y : ℕ → Fin K → ℝ) : ℝ :=
  Finset.univ.sup' ⟨id, Finset.mem_univ _⟩
    (fun f : Fin K → Fin K => ∑ t ∈ Finset.range T, (∑ i, p t i * y t (f i) - p t ⬝ᵥ y t))

end CalibeatBandit


