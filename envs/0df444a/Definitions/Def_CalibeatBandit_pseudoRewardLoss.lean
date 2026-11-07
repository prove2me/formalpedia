-- Prove2me | Definitions.Def_CalibeatBandit_pseudoRewardLoss
-- name    : CalibeatBandit_pseudoRewardLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:32.64792+00:00
-- url     : https://prove2.me/theorems/c3b44adc-2d6c-461b-92be-0e1a7edf6d82
-- title:
--   Pseudo reward loss $R^{\mathrm{Rec},p}_T$
-- statement:
--   For mixed strategies $p_t$, reward vectors $y_t$ and recommended actions $J_t$, let $g^{\mathrm{Rec}}_t(f)=y_t(f(J_t))$. The **pseudo reward loss** is
--   $$R^{\mathrm{Rec},p}_T=\max_{f\in\Sigma_{\mathcal A}}\sum_{t=1}^T\bigl(g^{\mathrm{Rec}}_t(f)-\langle p_t,y_t\rangle\bigr).$$
--
--   **Formalization Note** Rounds are $0,\dots,T-1$; $\langle p,y\rangle$ is `p ⬝ᵥ y`; the maximum is `Finset.sup'`.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §C.1 (proof of Lemma C.1), p.30 (PDF 30)

import Mathlib

set_option autoImplicit false

namespace CalibeatBandit

open Matrix

/-- **Pseudo reward loss `R^{Rec,p}_T`.** For mixed strategies `p_t`, reward vectors `y_t` and
recommended actions `J_t`, with `g^Rec_t(f) = y_t(f(J_t))`,
`R^{Rec,p}_T = max_f ∑_{t=1}^T (g^Rec_t(f) − ⟨p_t, y_t⟩)`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.1, proof of
Lemma C.1, p.30: "g^Rec_t(f) = y_t(f(J_t)), and for a ∈ {SR, Rec} define the corresponding swap
regret as R^{a,p}_T := max_f ∑_{t=1}^T (g^a_t(f) − ⟨p_t, y_t⟩)."

**Formalization Note.** Rounds are `0, …, T − 1`; `⟨p, y⟩` is `p ⬝ᵥ y`; the maximum over all
`f : Fin K → Fin K` is `Finset.sup'`. -/
def pseudoRewardLoss {K : ℕ} (T : ℕ) (p y : ℕ → Fin K → ℝ) (J : ℕ → Fin K) : ℝ :=
  Finset.univ.sup' ⟨id, Finset.mem_univ _⟩
    (fun f : Fin K → Fin K => ∑ t ∈ Finset.range T, (y t (f (J t)) - p t ⬝ᵥ y t))

end CalibeatBandit


