-- Prove2me | Definitions.Def_OnlineLearningOCO_Winnow_Winnow
-- name    : OnlineLearningOCO_Winnow_Winnow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:57.681969+00:00
-- url     : https://prove2.me/theorems/e80e71f1-8b6d-4a6c-b6b2-fe5bb7875314
-- title:
--   The Winnow algorithm, its error rounds $\mathcal M$, surrogate $f_t$ and loss vectors $z_t$ (§3.3.2, pp. 172–174; sign of the update corrected)
-- statement:
--   Labels are $y_t\in\{-1,1\}$ and instances are $x_t\in\{0,1\}^d$. **Winnow** with parameter $\eta>0$ maintains a weight vector $w_t\in\mathbb R^d_+$:
--
--   1. initialize $w_1=(1/d,\dots,1/d)$;
--   2. on round $t$, receive $x_t$ and predict $p_t=\operatorname{sign}(2\langle w_t,x_t\rangle-1)$;
--   3. if $y_t(2\langle w_t,x_t\rangle-1)\le0$, update $w_{t+1}[i]=w_t[i]\,e^{2\eta y_tx_t[i]}$ for every $i$; otherwise $w_{t+1}=w_t$.
--
--   The set of **error rounds** is $\mathcal M=\{t: y_t(2\langle w_t,x_t\rangle-1)\le0\}$ (ties count as errors). On these rounds the **surrogate loss** is the hinge loss, and it is zero elsewhere:
--   $$f_t(w)=\mathbf 1_{[t\in\mathcal M]}\bigl[1-y_t(2\langle w,x_t\rangle-1)\bigr]_+ .$$
--   Winnow is unnormalized EG with $\lambda=1/d$ fed the loss vectors
--   $$z_t=\begin{cases}-2y_tx_t,& t\in\mathcal M,\\ 0,& t\notin\mathcal M,\end{cases}$$
--   and $z_t$ is the gradient of $f_t$ at $w_t$ on error rounds. Weights of irrelevant variables are demoted after false positives and weights of active variables are promoted after false negatives.
--
--   **Formalization Note** *Erratum.* The box on p. 173 prints the update $w_{t+1}[i]=w_t[i]e^{-\eta 2y_tx_t[i]}$ and the proof on p. 174 sets $z_t=2y_tx_t$; with that sign the algorithm demotes on a false negative and Theorem 3.10 is false (with $d=2$, $u=(1,0)$, $\eta=1/4$ and $x_t=(1,0)$, $y_t=1$ for all $t$, every round is an error, so $|\mathcal M|=T>8\log 2$ for $T=6$). The gradient of the hinge surrogate at $w_t$ on an error round is $-2y_tx_t$, and the unnormalized-EG step with it is the update above (Littlestone's Winnow); this file uses the corrected sign. Rounds are numbered from $0$: `winnowWeights d η x y 0` is $w_1$. `winnowMargin` is $y_t(2\langle w_t,x_t\rangle-1)$, `winnowMistakes d η x y T` is $\mathcal M\cap\{0,\dots,T-1\}$, `winnowSurrogate` is $f_t$ and `winnowZ` is $z_t$; all of them refer to the run with parameter $\eta$ on the given sequence. The definitions accept any real sequences; the theorems assume $x_t\in\{0,1\}^d$ and $y_t\in\{-1,1\}$.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, pp. 172–173 (§3.3.2, hypothesis class, surrogate f_t, Winnow box), p. 174 (proof of Theorem 3.10: M and z_t); update sign corrected

import Mathlib

namespace OnlineLearningOCO.Winnow

open Finset

/-- The weights of the Winnow algorithm (§3.3.2, p. 173) with parameter `η` on the instances
`x : ℕ → Fin d → ℝ` (in `{0,1}^d`) and labels `y : ℕ → ℝ` (in `{-1, 1}`), rounds numbered from `0`:
`w₀ = (1/d, …, 1/d)`; if `y_t (2⟨w_t, x_t⟩ - 1) ≤ 0` then `w_{t+1}[i] = w_t[i] e^{2η y_t x_t[i]}`,
otherwise `w_{t+1} = w_t`.

Formalization Note: the printed box on p. 173 has `e^{-η 2 y_t x_t[i]}`; that sign is an erratum
(it demotes on a false negative and makes Theorem 3.10 false). The update here is the
unnormalized-EG step with the subgradient `-2 y_t x_t` of the hinge surrogate, i.e. Littlestone's
Winnow. -/
noncomputable def winnowWeights (d : ℕ) (η : ℝ) (x : ℕ → Fin d → ℝ) (y : ℕ → ℝ) :
    ℕ → Fin d → ℝ
  | 0 => fun _ => 1 / (d : ℝ)
  | t + 1 =>
    if y t * (2 * ∑ i, winnowWeights d η x y t i * x t i - 1) ≤ 0 then
      fun i => winnowWeights d η x y t i * Real.exp (2 * η * y t * x t i)
    else winnowWeights d η x y t

/-- The signed margin `y_t (2⟨w_t, x_t⟩ - 1)` of Winnow's weight on round `t`; Winnow errs
(and updates) on round `t` exactly when it is `≤ 0` (p. 172, p. 174). -/
noncomputable def winnowMargin (d : ℕ) (η : ℝ) (x : ℕ → Fin d → ℝ) (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  y t * (2 * ∑ i, winnowWeights d η x y t i * x t i - 1)

/-- The set `M` of rounds among the first `T` (`0, …, T-1`) on which Winnow errs,
`M = {t : y_t (2⟨w_t, x_t⟩ - 1) ≤ 0}` (proof of Theorem 3.10, p. 174). -/
noncomputable def winnowMistakes (d : ℕ) (η : ℝ) (x : ℕ → Fin d → ℝ) (y : ℕ → ℝ) (T : ℕ) :
    Finset ℕ :=
  (range T).filter (fun t => winnowMargin d η x y t ≤ 0)

/-- The surrogate loss of round `t` (p. 173, Theorem 3.10):
`f_t(v) = 1[t ∈ M] [1 - y_t (2⟨v, x_t⟩ - 1)]_+`, where `M` is Winnow's own set of error rounds. -/
noncomputable def winnowSurrogate (d : ℕ) (η : ℝ) (x : ℕ → Fin d → ℝ) (y : ℕ → ℝ) (t : ℕ)
    (v : Fin d → ℝ) : ℝ :=
  if winnowMargin d η x y t ≤ 0 then max 0 (1 - y t * (2 * ∑ i, v i * x t i - 1)) else 0

/-- The linear loss vector `z_t` fed to unnormalized EG by Winnow (proof of Theorem 3.10, p. 174),
with the sign corrected: `z_t = -2 y_t x_t` if `t ∈ M`, and `z_t = 0` otherwise; `z_t` is the
gradient of `f_t` at `w_t` on error rounds. -/
noncomputable def winnowZ (d : ℕ) (η : ℝ) (x : ℕ → Fin d → ℝ) (y : ℕ → ℝ) (t : ℕ) (i : Fin d) :
    ℝ :=
  if winnowMargin d η x y t ≤ 0 then -2 * y t * x t i else 0

end OnlineLearningOCO.Winnow


