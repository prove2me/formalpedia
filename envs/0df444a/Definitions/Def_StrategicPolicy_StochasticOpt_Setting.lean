-- Prove2me | Definitions.Def_StrategicPolicy_StochasticOpt_Setting
-- name    : StrategicPolicy_StochasticOpt_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:08.159983+00:00
-- url     : https://prove2.me/theorems/5d8c8fbf-ff63-4215-8a80-65b31b011339
-- title:
--   §2–§4, pp. 3–6 — strategic decision model: policies, best response (5) with (i)–(ii), utility (7), non-strategic utility (2), outcome monotonic costs
-- statement:
--   There are $m$ feature values $x_1,\dots,x_m$, indexed in Lean by $0,\dots,m-1$ (index $k$ is $x_{k+1}$). The data are a feature distribution $p(x)=P(x)$, an outcome probability $q(x)=P(y=1\mid x)$, a constant $\gamma$, and a cost $c(x_i,x_j)$ of changing from $x_i$ to $x_j$.
--
--   1. A **decision policy** is a map $\pi$ with $0\le\pi(x)\le1$ for every $x$; $\pi(x)=\pi(d=1\mid x)$ is the probability of a positive decision, which is also the individual benefit $b(x)=\pi(x)$.
--   2. The **argmax set** of an individual starting at $x_i$ is the set of $x_k$ maximizing $\pi(x_k)-c(x_i,x_k)$, as in (5).
--   3. The **best response** $\mathrm{br}(i)$ is the element of the argmax set with the highest outcome $q$ (standing assumption (ii)); if several maximizers share that outcome, the least index is taken. When all outcomes are distinct this last rule never applies.
--   4. The **strategic utility** (7), regrouped by initial feature, is
--   $$
--   u(\pi,\gamma)=\sum_{i}P(x_i)\,\bigl(P(y=1\mid x_{\mathrm{br}(i)})-\gamma\bigr)\,\pi(x_{\mathrm{br}(i)}).
--   $$
--   5. The **non-strategic utility** is the utility (2) when the feature distribution is not induced by $\pi$ (nobody moves): $u_{\mathrm{NS}}(\pi,\gamma)=\sum_x P(x)\,(P(y=1\mid x)-\gamma)\,\pi(x)$.
--   6. **Standing assumption (i)**: $c(x_i,x_j)>0$ whenever $i\ne j$ and $P(y\mid x_j)\ge P(y\mid x_i)$.
--   7. An **outcome monotonic cost** has $c(x_i,x_i)=0$; for pairwise distinct $i,j,k$, $P(y=1\mid x_i)<P(y=1\mid x_j)<P(y=1\mid x_k)$ holds if and only if $c(x_i,x_j)<c(x_i,x_k)$ and $c(x_j,x_k)<c(x_i,x_k)$; and for $i\ne j$, $P(y=1\mid x_i)>P(y=1\mid x_j)$ holds if and only if $c(x_i,x_j)=0$.
--   8. A policy is **deterministic** if every $\pi(x)$ is $0$ or $1$.
--
--   These objects are the paper's base model, with $P(y\mid x)$ unchanged by best responses. Every statement of the mission is about them.
--
--   **Formalization Note** The best response is computed from $\pi$, $c$ and $q$, never assumed. The zero-cost equivalence of p. 6 is imposed only for distinct pairs, together with $c(x,x)=0$, because at $i=j$ it would forbid free staying. The two small nonemptiness lemmas make the best response well defined for $m\ge1$ (`NeZero m`).
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, pp. 3–6, (2), (3), (5), (7), standing assumptions (i)–(ii) p. 4, outcome monotonic cost p. 6

import Mathlib

namespace StrategicPolicy.StochasticOpt

/-- Decision policies: `π x` is the probability `π(d = 1 | x)` of a positive decision at
feature value `x`, so it lies in `[0, 1]` (p. 3; "0 ≤ π(x_j) ≤ 1", p. 5). -/
def Policies (m : ℕ) : Set (Fin m → ℝ) :=
  {π | ∀ x, π x ∈ Set.Icc (0 : ℝ) 1}

/-- The argmax set of (5): the feature values `k` maximizing `π k - c i k` for an individual
starting at `i` (benefit `b(x) = π(x)`, p. 3). -/
noncomputable def argmaxSet {m : ℕ} (c : Fin m → Fin m → ℝ) (π : Fin m → ℝ) (i : Fin m) :
    Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun k => ∀ l, π l - c i l ≤ π k - c i k)

/-- The maximizers of (5) with the highest outcome `q` (standing assumption (ii), p. 4). -/
noncomputable def tieSet {m : ℕ} (c : Fin m → Fin m → ℝ) (q π : Fin m → ℝ) (i : Fin m) :
    Finset (Fin m) := by
  classical
  exact (argmaxSet c π i).filter (fun k => ∀ l ∈ argmaxSet c π i, q l ≤ q k)

theorem argmaxSet_nonempty {m : ℕ} [NeZero m] (c : Fin m → Fin m → ℝ) (π : Fin m → ℝ)
    (i : Fin m) : (argmaxSet c π i).Nonempty := by
  classical
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m))
    (fun k => π k - c i k) Finset.univ_nonempty
  exact ⟨k, by simpa [argmaxSet] using fun l => hk l (Finset.mem_univ l)⟩

theorem tieSet_nonempty {m : ℕ} [NeZero m] (c : Fin m → Fin m → ℝ) (q π : Fin m → ℝ)
    (i : Fin m) : (tieSet c q π i).Nonempty := by
  classical
  obtain ⟨k, hk, hq⟩ := Finset.exists_max_image (argmaxSet c π i) q (argmaxSet_nonempty c π i)
  exact ⟨k, by simpa [tieSet] using ⟨hk, hq⟩⟩

/-- Best response (5) with tie-break (ii): among the maximizers of `π k - c i k`, the one with
the highest outcome `q`; any remaining tie (only possible when outcomes coincide) goes to the
least index. -/
noncomputable def br {m : ℕ} [NeZero m] (c : Fin m → Fin m → ℝ) (q π : Fin m → ℝ)
    (i : Fin m) : Fin m :=
  (tieSet c q π i).min' (tieSet_nonempty c q π i)

/-- The strategic utility (7), regrouped by the initial feature value `i`. -/
noncomputable def u {m : ℕ} [NeZero m] (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (π : Fin m → ℝ) : ℝ :=
  ∑ i, p i * (q (br c q π i) - γ) * π (br c q π i)

/-- The non-strategic utility: (2) with the feature distribution `P(x)` itself (nobody moves). -/
def uNS {m : ℕ} (p q : Fin m → ℝ) (γ : ℝ) (π : Fin m → ℝ) : ℝ :=
  ∑ x, p x * (q x - γ) * π x

/-- Standing assumption (i), p. 4: moving to a feature value with an outcome at least as high
costs a positive amount. -/
def StandingI {m : ℕ} (q : Fin m → ℝ) (c : Fin m → Fin m → ℝ) : Prop :=
  ∀ i j, i ≠ j → q i ≤ q j → 0 < c i j

/-- Outcome monotonic cost (p. 6), on distinct feature values, with free staying. -/
def OMCost {m : ℕ} (q : Fin m → ℝ) (c : Fin m → Fin m → ℝ) : Prop :=
  (∀ i, c i i = 0) ∧
  (∀ i j k, i ≠ j → j ≠ k → i ≠ k →
    ((q i < q j ∧ q j < q k) ↔ (c i j < c i k ∧ c j k < c i k))) ∧
  (∀ i j, i ≠ j → (q j < q i ↔ c i j = 0))

/-- A deterministic policy takes only the values `0` and `1`. -/
def IsDeterministic {m : ℕ} (π : Fin m → ℝ) : Prop :=
  ∀ x, π x = 0 ∨ π x = 1

end StrategicPolicy.StochasticOpt


