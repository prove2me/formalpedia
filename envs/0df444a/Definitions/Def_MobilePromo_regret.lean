-- Prove2me | Definitions.Def_MobilePromo_regret
-- name    : MobilePromo_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:52.427763+00:00
-- url     : https://prove2.me/theorems/ff219b2a-191f-48a9-b868-7313c83c0c36
-- title:
--   The law of a path, the expected cost and the regret
-- statement:
--   Under a bid rule $\pi$ and parameter $\gamma$, the next period has no arrival with probability $1-\sum_lq_l$; an arrival from $l$ has probability $q_l$, and it is won with probability $p_l(\gamma_l,b^\pi)$, or $0$ if no bid is placed. The realized cost of a period is $(b^\pi-e)$ if an impression is won and $0$ otherwise. The expected cost over $I$ seasons is the expectation of the sum of these realized costs, and
--
--   $$
--   \mathrm{Regret}(\pi,I;\gamma^{(0)})=\sum_{i=1}^I\mathbb E\bigl[V^\pi_{i,1}(\emptyset;X^\pi_{i,1},\gamma^{(0)})\bigr]-\sum_{i=1}^IV_{i,1}\bigl((W_{i,1},\dots,W_{i,m_i});\gamma^{(0)}\bigr).
--   $$
--
--   This module also gives the expected cost-to-go $V^\pi$ with its recursion from p.15, and the conditional expectation of the squared bid distance that appears in (A-5), both as backward recursions along the history.
--
--   **Formalization Note** A period has finitely many outcomes, so expectations are finite sums over paths. The expected cost is that of §2.3 and the display of p.16. The display on p.15, with its factor $q_l$ next to the realized $d_{i,t}$, is not used, since read literally it counts $q_l$ twice.
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, §2.3, pp.15–16; first line of (4), p.10; (A-5), A7 (PDF 41)

import Mathlib
import Definitions.Def_MobilePromo_Policy

set_option autoImplicit false

namespace MobilePromo

/-- The probability that bid `b` wins an impression from `l`: `0` for no bid (`b = 0`, p.8), and
`p_l(γ_l, b)` otherwise. -/
noncomputable def winProb (M : Model) (γ : M.ParamVec) (l : Fin M.L) (b : ℝ) : ℝ :=
  if b = 0 then 0 else M.p l (γ l) b

/-- The law of the outcome of the next period given the history `h` (SSRN 3523491, pp.7–8): no arrival
with probability `1 - ∑ q`, an arrival from `l` with probability `q_l`, won with probability
`winProb`. -/
noncomputable def stepProb (M : Model) (π : Policy M.L) (γ : M.ParamVec)
    (h : List (Outcome M.L)) : Outcome M.L → ℝ
  | none => 1 - ∑ l, M.q l
  | some (l, true) => M.q l * winProb M γ l (π h l)
  | some (l, false) => M.q l * (1 - winProb M γ l (π h l))

/-- The realized cost of a period, `∑_l (b_{i,t,l} - e) 1{ζ_{i,t} = l} d_{i,t}` (SSRN 3523491, first line
of (4), p.10, without its constant, with the common `e` of p.11). -/
noncomputable def stepCost (M : Model) (π : Policy M.L) (h : List (Outcome M.L)) :
    Outcome M.L → ℝ
  | some (l, true) => π h l - M.e
  | _ => 0

/-- The first `k` outcomes of the path `ω`, in order. -/
def pref {α : Type*} {N : ℕ} (ω : Fin N → α) (k : ℕ) : List α := (List.ofFn ω).take k

/-- The probability of the outcome path `ω` under `π` and `γ`. -/
noncomputable def pathProb (M : Model) (π : Policy M.L) (γ : M.ParamVec) {N : ℕ}
    (ω : Fin N → Outcome M.L) : ℝ :=
  ∏ k : Fin N, stepProb M π γ (pref ω k) (ω k)

/-- The expectation of a function of the outcomes of the first `N` periods, under `π` and `γ`.

**Formalization Note** A period has finitely many outcomes, so this is a finite sum over paths. -/
noncomputable def pathExp (M : Model) (π : Policy M.L) (γ : M.ParamVec) (N : ℕ)
    (F : (Fin N → Outcome M.L) → ℝ) : ℝ :=
  ∑ ω, pathProb M π γ ω * F ω

/-- The expected cost `∑_{i ≤ I} E[V^π_{i,1}(∅; X^π_{i,1}, γ)]` of `π` over `I` seasons of `T` periods
(SSRN 3523491, §2.3, pp.15–16): the expectation of the realized cost. -/
noncomputable def expCost (M : Model) (T : ℕ) (π : Policy M.L) (γ : M.ParamVec) (I : ℕ) : ℝ :=
  pathExp M π γ (I * T) fun ω => ∑ k : Fin (I * T), stepCost M π (pref ω k) (ω k)

/-- `Regret(π, I; γ) = ∑_{i=1}^I E[V^π_{i,1}(∅; X^π_{i,1}, γ)] - ∑_{i=1}^I V_{i,1}((W_{i,1}, …, W_{i,m_i}); γ)`
(SSRN 3523491, p.16).

**Formalization Note** This is the display of p.16, with its expected cost written as `expCost`. The
display on p.15 is not used, because read literally it counts `q_l` twice. -/
noncomputable def regret (M : Model) {T : ℕ} (S : Schedule T) (π : Policy M.L)
    (γ : M.ParamVec) (I : ℕ) : ℝ :=
  expCost M T π γ I - ∑ i : Fin I, V M (S i) γ 1 (S i).W

/-- `∑_l q_l (b^π_{i,t,l} - b*_{i,t,l}(c_i(x̂); γ))²` at the period after the history `h`. -/
noncomputable def squaredGap (M : Model) {T : ℕ} (S : Schedule T) (π : Policy M.L)
    (γ : M.ParamVec) (h : List (Outcome M.L)) : ℝ :=
  ∑ l, M.q l * (π h l - bStarAt M S γ h l) ^ 2

/-- The expected cost-to-go of `π` with `r` periods left after the history `h`
(SSRN 3523491, recursion for `V^π_{i,t}`, p.15; `Vπ (T + 1 - t) (x₁ ++ x̂)` is `V^π_{i,t}(x̂; x₁, γ)`), with
`V^π_{i,T+1} = 0`.

**Formalization Note** The sum over the outcomes of the next period is the three lines of the page,
with `winProb` for `1{c ≥ 1} p_l(γ_l, b)`. -/
noncomputable def Vπ (M : Model) (π : Policy M.L) (γ : M.ParamVec) :
    ℕ → List (Outcome M.L) → ℝ
  | 0, _ => 0
  | r + 1, h => ∑ o : Outcome M.L, stepProb M π γ h o * (stepCost M π h o + Vπ M π γ r (h ++ [o]))

/-- The conditional expectation
`E[∑_{t̂ = t}^T ∑_l q_l (b^π_{i,t̂,l}(x₁, X̂^π_{i,t̂}) - b*_{i,t̂,l}(c_i(X̂^π_{i,t̂}); γ))² | X̂^π_{i,t} = x̂]`
of (A-5) with `r = T + 1 - t` periods left after the history `h = x₁ ++ x̂`, written as a backward recursion
(SSRN 3523491, (A-5), A7, PDF 41). -/
noncomputable def gapToGo (M : Model) {T : ℕ} (S : Schedule T) (π : Policy M.L)
    (γ : M.ParamVec) : ℕ → List (Outcome M.L) → ℝ
  | 0, _ => 0
  | r + 1, h => squaredGap M S π γ h +
      ∑ o : Outcome M.L, stepProb M π γ h o * gapToGo M S π γ r (h ++ [o])

end MobilePromo


