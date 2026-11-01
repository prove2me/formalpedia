-- Prove2me | Definitions.Def_NoRegretLastIterate_Strategy
-- name    : NoRegretLastIterate_Strategy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:08.875999+00:00
-- url     : https://prove2.me/theorems/3e8e454d-cc64-4682-a780-74bfd9560117
-- title:
--   Definitions 2.1 and 2.3 — self-agnostic strategies, regret, and the no-regret rate $(r,c)$
-- statement:
--   Rounds are $t=1,2,\dots$. A **self-agnostic** strategy of player 1 (Definition 2.1) is a sequence of maps $f_t:\{0,1\}^{t-1}\to[0,1]$; in round $t$ player 1 plays action 1 with probability $P_t=f_t((J)^{t-1})$, a function of player 2's past actions $J_1,\dots,J_{t-1}$ only. Against a deterministic opponent sequence $J_1,J_2,\dots$ its **regret** after $T$ rounds is
--   $$
--   \mathrm{Reg}_T(J)=\max_{i\in\{0,1\}}\sum_{t=1}^T G(i,J_t)-\sum_{t=1}^T G\big(f_t((J)^{t-1}),J_t\big),
--   $$
--   where $G(p,J_t)$ is the bilinear extension, the expected payoff over player 1's own randomization. The strategy achieves a **uniform no-regret rate** $(r,c)$ (Definition 2.3) if
--   $$
--   \limsup_{T\to\infty}\ \max_{\{J_t\}_{t=1}^T}\ \frac{1}{T^r}\,\mathrm{Reg}_T(J)\le c .
--   $$
--   The rate $r=1/2$ is the best possible and is called **optimal** (pp.7, 10). Player 2's notions are the same with $H$, player 1's actions $I_t$ and the regret $\max_j\sum_t H(I_t,j)-\sum_t H(I_t,g_t((I)^{t-1}))$.
--
--   These are the hypotheses on the players' learning algorithms in every theorem of the mission.
--
--   **Formalization Note** Lean rounds start at $0$: `F n` is the paper's $f_{n+1}$ and sees the opponent's actions of Lean rounds $0,\dots,n-1$. "Rate $(r,c)$ for some finite $c$" is encoded as: there is $c\in\mathbb R$ with $\mathrm{Reg}_T(J)\le c\,T^r$ for all large $T$ and all $J$, which is equivalent because the maximum over $\{0,1\}^T$ is finite; no real `limsup` is used. Player 2's regret is the row-player regret of the transpose $H^{\mathsf T}$.
-- source:
--   Muthukumar, Phade, Sahai, On the Impossibility of Convergence of Mixed Strategies with Optimal No-Regret Learning, arXiv:2012.02125v3, Definition 2.1 p.6, Definition 2.3 p.6, p.7 (optimal rate r = 1/2)

import Mathlib
import Definitions.Def_NoRegretLastIterate_Game

namespace NoRegretLastIterate

open Filter

/-- The indicator of action `1`: `bit 0 = 0`, `bit 1 = 1` (arXiv:2012.02125v3, §2, p.5, where
the realized actions `I`, `J` are indicator random variables of action 1). -/
def bit (b : Fin 2) : ℝ := ((b : ℕ) : ℝ)

/-- arXiv:2012.02125v3, Definition 2.1, p.6: a *self-agnostic* repeated-game strategy for a
player: in every round it maps the opponent's past actions to a mixed strategy in `[0, 1]`
(the probability of playing action 1).

**Formalization Note** Rounds are indexed from `0` in Lean: `F n` is the paper's `f_{n+1}`, and
takes the opponent's actions in Lean rounds `0, …, n − 1` (paper rounds `1, …, n`), so
`F n (J^n)` is the paper's `f_{n+1}((J)^n)`. A strategy is the function `F` together with this
range condition. -/
def IsStrategy (F : (n : ℕ) → (Fin n → Fin 2) → ℝ) : Prop :=
  ∀ n (h : Fin n → Fin 2), F n h ∈ Set.Icc (0 : ℝ) 1

/-- arXiv:2012.02125v3, Definition 2.3, p.6: the regret after `T` rounds of the self-agnostic
strategy `F` of the row player of the payoff matrix `X`, against the (deterministic) opponent
sequence `J`,
`max_{i ∈ {0,1}} Σ_{t=1}^T X(i, J_t) − Σ_{t=1}^T X(f_t((J)^{t−1}), J_t)`,
where `X(p, J_t)` is the bilinear extension, i.e. the expected payoff over the player's own coin.

**Formalization Note** Lean rounds `0, …, T − 1` are the paper's rounds `1, …, T`. Player 2's
regret (with payoff `H(I_t, j)`) is `regret Hᵀ`, since `Hᵀ j i = H i j` and
`ext Hᵀ q (bit i) = ext H (bit i) q`. -/
noncomputable def regret (X : Matrix (Fin 2) (Fin 2) ℝ) (F : (n : ℕ) → (Fin n → Fin 2) → ℝ)
    (T : ℕ) (J : ℕ → Fin 2) : ℝ :=
  max (∑ n ∈ Finset.range T, X 0 (J n)) (∑ n ∈ Finset.range T, X 1 (J n)) -
    ∑ n ∈ Finset.range T, ext X (F n (fun k : Fin n => J k)) (bit (J n))

/-- arXiv:2012.02125v3, Definition 2.3, p.6: the self-agnostic strategy `F` (row player of `X`)
achieves a uniform no-regret rate of `(r, c)` for some finite constant `c`:
`lim sup_{T→∞} max_{{J_t}_{t=1}^T} T^{−r} · Regret_T(J) ≤ c`. With `r = 1/2` this is the
paper's *optimal* no-regret rate (p.7, p.10).

**Formalization Note** Encoded as: there is `c : ℝ` such that for all large `T` and every
opponent sequence `J`, `Regret_T(J) ≤ c · T^r`. This is equivalent to "lim sup ≤ c′ for some
finite `c′`", because the maximum over `{0,1}^T` is a finite maximum and `Regret_T(J)` depends only
on `J_0, …, J_{T−1}`. No real-valued `limsup` is used. -/
def HasRate (X : Matrix (Fin 2) (Fin 2) ℝ) (F : (n : ℕ) → (Fin n → Fin 2) → ℝ) (r : ℝ) :
    Prop :=
  ∃ c : ℝ, ∀ᶠ T : ℕ in atTop, ∀ J : ℕ → Fin 2, regret X F T J ≤ c * (T : ℝ) ^ r

end NoRegretLastIterate


