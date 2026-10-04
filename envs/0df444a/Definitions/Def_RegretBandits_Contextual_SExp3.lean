-- Prove2me | Definitions.Def_RegretBandits_Contextual_SExp3
-- name    : RegretBandits_Contextual_SExp3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:10:33.010145+00:00
-- url     : https://prove2.me/theorems/bb7caa37-4cfd-48a7-954d-5fddfea5a061
-- title:
--   S-Exp3: one Exp3 instance per context (proof of Theorem 4.1)
-- statement:
--   Bandits with side information (Section 4.1 of Bubeck and Cesa-Bianchi). Each round $t$ is marked by a context $s_t$ from a finite set $\mathcal S$; the context sequence is arbitrary but fixed. Let $n_s = |\{t \le n : s_t = s\}|$ be the number of the first $n$ rounds marked by $s$.
--
--   The **S-Exp3 forecaster** runs a separate instance of Exp3 (Section 3.1) on each context $s \in \mathcal S$, with learning rate
--   $$\eta_s = \sqrt{\frac{2 \ln K}{n_s K}} .$$
--   At round $t$ it plays $I_t$ drawn from the distribution of the instance of context $s_t$:
--   $$p_{i,t} = \frac{\exp(-\eta_{s_t} \widetilde L^{(s_t)}_{i})}{\sum_{k=1}^K \exp(-\eta_{s_t} \widetilde L^{(s_t)}_{k})},$$
--   where $\widetilde L^{(s)}_i = \sum_{\tau < t,\ s_\tau = s} \widetilde\ell_{i,\tau}$ sums the importance-weighted estimates $\widetilde\ell_{i,\tau} = \frac{\ell_{i,\tau}}{p_{i,\tau}}\mathbb 1_{I_\tau = i}$ over the earlier rounds of the same context. Only the loss of the played arm enters.
--
--   **Formalization Note** Rounds are numbered from $0$. The learning rates are passed as a function $\eta : \mathcal S \to \mathbb R$; `sExp3Rate` is the book's tuning. When $n_s = 0$ the instance of $s$ is never used (and Lean's $x/0 = 0$ makes its rate $0$, which is harmless).
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 44-45, Section 4.1, proof of Theorem 4.1; Exp3 on p. 23

import Mathlib
import Definitions.Def_RegretBandits_Contextual_Protocol

namespace RegretBandits.Contextual

/-- Number of the first `n` rounds marked by context `c`: `n_c = |{t < n : s_t = c}|`
(rounds numbered from `0`). -/
def contextCount {S : Type*} [DecidableEq S] (n : ℕ) (s : ℕ → S) (c : S) : ℕ :=
  ((Finset.range n).filter (fun t => s t = c)).card

/-- The learning rate of the Exp3 instance attached to context `c` in the S-Exp3 forecaster
(Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, proof of Theorem 4.1, p. 44–45, using the tuning of
(3.2)): `η_c = √(2 ln K / (n_c K))`. When `n_c = 0` the instance is never used. -/
noncomputable def sExp3Rate {S : Type*} [DecidableEq S] (K n : ℕ) (s : ℕ → S) (c : S) : ℝ :=
  Real.sqrt (2 * Real.log K / ((contextCount n s c : ℝ) * K))

/-- Cumulative estimated losses of the S-Exp3 forecaster with per-context learning rates `η`,
context sequence `s` and adaptive losses `ℓ`, after the plays `h` of rounds `0, …, t-1`:
`sExp3CumLoss … t h c i = ∑_{τ < t, s_τ = c} ℓ̃_{i,τ}`, where
`ℓ̃_{i,τ} = ℓ_{i,τ} / p_{i,τ} · 1{I_τ = i}` and `p_τ` is the distribution the Exp3 instance of
context `s_τ` used at round `τ`. Only the loss of the played arm enters. -/
noncomputable def sExp3CumLoss {S : Type*} [DecidableEq S] {K : ℕ} (η : S → ℝ) (s : ℕ → S)
    (ℓ : AdaptiveLosses K) : (t : ℕ) → (Fin t → Fin K) → S → Fin K → ℝ
  | 0, _ => fun _ _ => 0
  | t + 1, h => fun c i =>
      let prev := sExp3CumLoss η s ℓ t (Fin.init h)
      if c = s t then
        prev c i + (if h (Fin.last t) = i then
          ℓ t (Fin.init h) i / expWeights (η c) (prev c) i else 0)
      else prev c i

/-- The S-Exp3 forecaster (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, Section 4.1, proof of
Theorem 4.1, p. 44): one instance of Exp3 (Section 3.1, p. 23) per context; at round `t` the arm
is drawn from the exponential-weights distribution of the instance of context `s_t`, with that
instance's learning rate `η (s_t)` and its own cumulative estimated losses. -/
noncomputable def sExp3Rule {S : Type*} [DecidableEq S] {K : ℕ} (η : S → ℝ) (s : ℕ → S)
    (ℓ : AdaptiveLosses K) : PlayRule K :=
  fun t h i => expWeights (η (s t)) (sExp3CumLoss η s ℓ t h (s t)) i

end RegretBandits.Contextual


