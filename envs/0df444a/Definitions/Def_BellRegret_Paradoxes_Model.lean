-- Prove2me | Definitions.Def_BellRegret_Paradoxes_Model
-- name    : BellRegret_Paradoxes_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:12:37.037271+00:00
-- url     : https://prove2.me/theorems/978b1df0-0ce5-48a8-96e7-7ab143349a6c
-- title:
--   Sec. 2, pp. 970–978 — regret utility u(x, y) = x + f(x − y), simple comparisons (1), Tables II–IV, decreasing concavity, g and the negative exponential
-- statement:
--   This file sets up the model Bell uses in Section 2 to explain four kinds of behaviour regarded as paradoxical.
--
--   **Regret utility.** A decision maker who chooses one alternative and forgoes another evaluates an outcome by the final assets $x$ she obtains and the assets $y$ the foregone alternative would have given in the same state. Section 2 uses the additive form (4) of the paper's representation theorem with a linear value function $v(x)=x$:
--   $$u(x,y)=x+f(x-y),$$
--   where $f:\mathbb R\to\mathbb R$ measures the satisfaction (for $x>y$) or regret (for $x<y$) of the difference.
--
--   **Simple comparisons.** A comparison between alternatives $a$ and $b$ has finitely many states $i$ with probabilities $\pi_i$; in state $i$ the alternatives give final assets $a_i$ and $b_i$. The expected utility of selecting $a$ when $b$ is foregone is
--   $$\mathrm{EU}_\pi(a\,|\,b)=\sum_i \pi_i\,u(a_i,b_i).$$
--   The alternative $a$ is **strictly preferred** to $b$ when $\mathrm{EU}_\pi(b\,|\,a)<\mathrm{EU}_\pi(a\,|\,b)$ (inequality (1) of the paper, for two states), and the two are **indifferent** when $\mathrm{EU}_\pi(a\,|\,b)=\mathrm{EU}_\pi(b\,|\,a)$.
--
--   **The payoff tables.**
--   1. Two states with probabilities $(p,1-p)$. Table II (horse race; state 1 "horse wins"): Bet $=(1-p,\,-p)$, Don't bet $=(0,0)$. Table III (car insurance; state 1 "car damaged"): Insure $=(-p,-p)$, Don't insure $=(-1,0)$.
--   2. Table IV (probabilistic insurance), three states "accident, insurer pays", "accident, insurer does not pay", "no accident" with probabilities $(q/2,\,q/2,\,1-q)$: Self insurance $=(-1,-1,0)$, Full insurance $=(-p,-p,-p)$, Probabilistic insurance $=(-p,-1,-p/2)$.
--
--   **Decreasing concavity.** $f$ is **decreasingly concave** if it is twice differentiable and its second derivative $f''$ is strictly increasing.
--
--   **The function $g$ and the negative exponential.** For $u(x,y)=x+f(x-y)$ the function $g$ of Section 3 is $g(r)=r+f(r)-f(-r)$, and the negative exponential is $f(r)=1-e^{-\gamma r}$.
--
--   These objects carry every statement of Section 2 (i)–(iii) and the exponential example of Section 3.
--
--   **Formalization Note** The page assumes $v$ "approximately linear"; the formalization takes $v(x)=x$ exactly, which is how every display of Section 2 is computed. The probabilities $\pi$ in `Prefers`/`Indiff` are an arbitrary real vector; each theorem instantiates them with the table's probabilities. The paper never defines "decreasingly concave"; its uses ("$f''(x)>f''(-x)$ … and, therefore, if $f$ is decreasingly concave", p. 972; "$f$ having a positive third derivative", p. 976) pin it down as twice differentiable with strictly increasing $f''$. The page's further presumption that $f$ is increasing and concave (p. 976) is not part of the definition. Table IV is encoded with the event "accident" split by whether the insurer pays, each with probability $q/2$.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, pp. 966 and 970–978 (PDF 7, 11–19): inequality (1) (p. 966), form (4) with v linear (p. 970), Table II (p. 971), Table III (p. 972), Table IV (p. 974), g (p. 976), f(r) = 1 − exp(−γr) (p. 978)

import Mathlib

namespace BellRegret.Paradoxes

/-- The regret utility of Bell (1982), additive form (4) with `v` linear, `v(x) = x`
(Sec. 2, p. 970, and every display of Sec. 2, e.g. p. 971 "Using u(x, y) = x + f(x − y)"):
`regretU f x y = x + f (x - y)` is the utility of ending with final assets `x` when the
foregone alternative would have given `y`. -/
def regretU (f : ℝ → ℝ) (x y : ℝ) : ℝ := x + f (x - y)

/-- Expected utility of selecting alternative `a` when alternative `b` is foregone, in a
comparison with finitely many states `Fin n` of probabilities `π i`; in state `i` the two
alternatives give final assets `a i` and `b i` (inequality (1), p. 966). -/
def selectU {n : ℕ} (f : ℝ → ℝ) (π : Fin n → ℝ) (a b : Fin n → ℝ) : ℝ :=
  ∑ i, π i * regretU f (a i) (b i)

/-- `a` is strictly preferred to `b` (inequality (1), p. 966): selecting `a` over `b` has
strictly larger expected regret utility than selecting `b` over `a`. -/
def Prefers {n : ℕ} (f : ℝ → ℝ) (π : Fin n → ℝ) (a b : Fin n → ℝ) : Prop :=
  selectU f π b a < selectU f π a b

/-- `a` and `b` are indifferent: selecting `a` over `b` and selecting `b` over `a` have equal
expected regret utility. -/
def Indiff {n : ℕ} (f : ℝ → ℝ) (π : Fin n → ℝ) (a b : Fin n → ℝ) : Prop :=
  selectU f π a b = selectU f π b a

/-- Two states, the first of probability `p` and the second of probability `1 - p`. -/
def prob2 (p : ℝ) : Fin 2 → ℝ := ![p, 1 - p]

/-- Table II (p. 971), column "Bet": `$(1 − p)` if the horse wins (state 0), `$−p` if it
loses (state 1). -/
def horseBet (p : ℝ) : Fin 2 → ℝ := ![1 - p, -p]

/-- Table II (p. 971), column "Don't Bet": `$0` in both states. -/
def horseNoBet : Fin 2 → ℝ := ![0, 0]

/-- Table III (p. 972), column "Insure": `−$p` if the car is damaged (state 0) and if it is
undamaged (state 1). -/
def carInsure (p : ℝ) : Fin 2 → ℝ := ![-p, -p]

/-- Table III (p. 972), column "Don't Insure": `−$1` if the car is damaged (state 0), `$0`
if it is undamaged (state 1). -/
def carNoInsure : Fin 2 → ℝ := ![-1, 0]

/-- The three states of Table IV (p. 974): state 0 "accident, the insurer pays", state 1
"accident, the insurer does not pay", state 2 "no accident". An accident has probability
`q` and the insurer pays with probability ½ given an accident. -/
noncomputable def prob3 (q : ℝ) : Fin 3 → ℝ := ![q / 2, q / 2, 1 - q]

/-- Table IV (p. 974), "Self Insurance": `−1` on an accident, `0` otherwise. -/
def selfInsurance : Fin 3 → ℝ := ![-1, -1, 0]

/-- Table IV (p. 974), "Full Insurance": `−p` in every state. -/
def fullInsurance (p : ℝ) : Fin 3 → ℝ := ![-p, -p, -p]

/-- Table IV (p. 974), "Probabilistic Insurance": `−p` on an accident when the insurer pays,
`−1` on an accident when it does not pay, `−p/2` when there is no accident. -/
noncomputable def probInsurance (p : ℝ) : Fin 3 → ℝ := ![-p, -1, -p / 2]

/-- `f` is decreasingly concave: twice differentiable with strictly increasing second
derivative (pp. 972 and 976; the paper does not define the term). -/
def DecreasinglyConcave (f : ℝ → ℝ) : Prop :=
  Differentiable ℝ f ∧ Differentiable ℝ (deriv f) ∧ StrictMono (deriv (deriv f))

/-- The function `g` of Lemma 2 for `u(x, y) = x + f(x − y)`: `g(r) = r + f(r) − f(−r)`
(p. 976). -/
def regretG (f : ℝ → ℝ) (r : ℝ) : ℝ := r + f r - f (-r)

/-- The negative exponential `f(r) = 1 − exp(−γr)` (p. 978). -/
noncomputable def negExp (γ : ℝ) (r : ℝ) : ℝ := 1 - Real.exp (-(γ * r))

end BellRegret.Paradoxes


