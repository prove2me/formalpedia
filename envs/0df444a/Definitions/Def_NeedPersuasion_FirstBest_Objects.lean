-- Prove2me | Definitions.Def_NeedPersuasion_FirstBest_Objects
-- name    : NeedPersuasion_FirstBest_Objects
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:53.722653+00:00
-- url     : https://prove2.me/theorems/f307a75b-3999-4321-83fa-1a06c9aaa91f
-- title:
--   Threshold welfare W_i(x), J(x), L(x); the no-information equilibrium π(p); g(x); sm(θ) and ap(θ) as sets of optimal policies
-- statement:
--   This module defines the objects specific to the first-best comparison, on top of the model of the mission.
--
--   1. For a threshold $x\ge0$, $W_L(x)$, $W_H(x)$, $J(x)$, $L(x)$ denote $W_L$, $W_H$, $J$, $L$ of the threshold policy $\pi_x$.
--   2. For $p\in[0,1]$, $\pi(p)$ is the steady state when every low-need user joins with probability $p$ regardless of the queue length:
--   $$\pi_n(p)=(1-\lambda_Lp-\lambda_H)(\lambda_Lp+\lambda_H)^n .$$
--   $p$ is an **equilibrium of the no-information mechanism** ni if $p\in[0,1]$, $\pi(p)$ is an admission policy, and joining with probability $p$ is a best response of a low-need user, whose expected utility from joining is $\sum_n\pi_n(p)u_L(n)$: if $p>0$ this sum is $\ge0$, and if $p<1$ it is $\le0$.
--   3. $g(x)=\sum_{k\in\mathbb N_0}(1-x)x^ku_L(k)$.
--   4. **Finite high-need welfare**: $\sum_k r^ku_H(k)$ converges for every $r\in[0,1)$.
--   5. For a class $S$ and a weight $\theta\in[0,1]$, the set of **optimal** elements of $S$ is: for $\theta\in(0,1)$, all maximizers of $W(\cdot,\theta)$ over $S$; for $\theta=0$, the maximizers of $W_H$ over $S$ that maximize $W_L$ among them; for $\theta=1$, the maximizers of $W_L$ over $S$ that maximize $W_H$ among them. Then
--   $$\mathrm{sm}(\theta)=\text{optimal elements of }\Pi_{SM},\qquad \mathrm{ap}(\theta)=\text{optimal elements of }\Pi_{AP}.$$
--
--   The admission policies in $\mathrm{ap}(\theta)$ are the "first-best" for the weight $\theta$.
--
--   **Formalization Note** $\mathrm{sm}(\theta)$ and $\mathrm{ap}(\theta)$ are sets (footnote 14), and the extremes $\theta\in\{0,1\}$ use the lexicographic refinement of footnote 12. The equilibrium of ni is defined by its best-response condition, not as a closed form. Finite high-need welfare is not stated in the paper: it is the condition under which every $\pi(p)$ with $\lambda_Lp+\lambda_H<1$ has finite welfare, so that the paper's finite-welfare convention does not rule out the equilibrium of ni; it is used only for the existence part of Lemma 4, and it holds, e.g., for linear utilities. The analogous property of $u_L$ follows from Assumption 1.
-- source:
--   arXiv:2005.07253v3, p. 16 (W_i(x), J(x), L(x)); Lemma 4, p. 37 and (b), p. 13 (π(p), ni); Proposition 3(3), p. 18 (g); footnote 12, p. 13 and footnote 14, p. 20 (sm(θ), ap(θ))

import Mathlib
import Definitions.Def_NeedPersuasion_FirstBest_Model

namespace NeedPersuasion.FirstBest

/-- W_L(x) = W_L(π_x), the low-need welfare of the threshold policy x (p. 16). -/
noncomputable def WLx (M : Model) (x : ℝ) : ℝ := WL M (thresholdPolicy M x)

/-- W_H(x) = W_H(π_x), the high-need welfare of the threshold policy x (p. 16). -/
noncomputable def WHx (M : Model) (x : ℝ) : ℝ := WH M (thresholdPolicy M x)

/-- J(x) = J(π_x), the (JOIN) value of the threshold policy x (p. 16). -/
noncomputable def joinValx (M : Model) (x : ℝ) : ℝ := joinVal M (thresholdPolicy M x)

/-- L(x) = L(π_x), the (LEAVE) value of the threshold policy x (p. 16). -/
noncomputable def leaveValx (M : Model) (x : ℝ) : ℝ := leaveVal M (thresholdPolicy M x)

/-- π(p), the steady state when every low-need user joins with probability p regardless of the
queue length (Lemma 4, p. 37; (b), p. 13): π_n(p) = (1 − λ_L p − λ_H)(λ_L p + λ_H)^n. -/
noncomputable def niDist (M : Model) (p : ℝ) : ℕ → ℝ :=
  fun n => (1 - (M.lamL * p + M.lamH)) * (M.lamL * p + M.lamH) ^ n

/-- `p` is a symmetric equilibrium joining probability of the no-information mechanism ni
((b), p. 13; Lemma 4 and its proof, p. 37): p ∈ [0, 1], π(p) is an admission policy, and joining
with probability p is a best response of a low-need user, whose expected utility for joining is
∑_n π_n(p) u_L(n) against the outside option 0: if p > 0 joining is weakly preferred, and if p < 1
leaving is weakly preferred. -/
def IsNIEquilibrium (M : Model) (p : ℝ) : Prop :=
  p ∈ Set.Icc (0 : ℝ) 1 ∧ niDist M p ∈ PiAP M ∧
    (0 < p → 0 ≤ ∑' n, niDist M p n * M.uL n) ∧
    (p < 1 → ∑' n, niDist M p n * M.uL n ≤ 0)

/-- g(x) = ∑_{k ∈ N₀} (1 − x) x^k u_L(k) (Proposition 3(3), p. 18; App. C, p. 42). -/
noncomputable def g (M : Model) (x : ℝ) : ℝ := ∑' k, (1 - x) * x ^ k * M.uL k

/-- Finite high-need welfare under every geometric queue-length law: for every r ∈ [0, 1),
∑_k r^k u_H(k) converges. (The analogous property of u_L follows from Assumption 1.) -/
def FiniteHWelfare (M : Model) : Prop :=
  ∀ r : ℝ, 0 ≤ r → r < 1 → Summable (fun k => r ^ k * M.uH k)

/-- The set of maximizers of W(·, θ) over a class `S` (p. 13). -/
def argmaxW (M : Model) (S : Set (ℕ → ℝ)) (θ : ℝ) : Set (ℕ → ℝ) :=
  {π | π ∈ S ∧ ∀ π' ∈ S, W M θ π' ≤ W M θ π}

/-- Lexicographic maximizers over `S` (footnote 12, p. 13): first maximize `f`, then, among the
maximizers of `f`, maximize `h`. -/
def lexArgmax (S : Set (ℕ → ℝ)) (f h : (ℕ → ℝ) → ℝ) : Set (ℕ → ℝ) :=
  {π | π ∈ S ∧ (∀ π' ∈ S, f π' ≤ f π) ∧ ∀ π' ∈ S, f π' = f π → h π' ≤ h π}

/-- The set of optimal elements of `S` for the weight θ (p. 20 and footnotes 12, 14): for
θ ∈ (0, 1) all maximizers of W(·, θ); for θ = 0, maximize W_H and then W_L; for θ = 1, maximize
W_L and then W_H. -/
noncomputable def optSet (M : Model) (S : Set (ℕ → ℝ)) (θ : ℝ) : Set (ℕ → ℝ) :=
  if θ = 0 then lexArgmax S (WH M) (WL M)
  else if θ = 1 then lexArgmax S (WL M) (WH M)
  else argmaxW M S θ

/-- sm(θ), the set of signaling mechanisms optimal for the weight θ (p. 20, footnote 14). -/
noncomputable def smSet (M : Model) (θ : ℝ) : Set (ℕ → ℝ) := optSet M (PiSM M) θ

/-- ap(θ), the set of admission policies optimal for the weight θ, the "first-best"
(pp. 13, 20, footnote 14). -/
noncomputable def apSet (M : Model) (θ : ℝ) : Set (ℕ → ℝ) := optSet M (PiAP M) θ

end NeedPersuasion.FirstBest


