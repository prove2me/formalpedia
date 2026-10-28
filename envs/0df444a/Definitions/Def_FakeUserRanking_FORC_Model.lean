-- Prove2me | Definitions.Def_FakeUserRanking_FORC_Model
-- name    : FakeUserRanking_FORC_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:18.968479+00:00
-- url     : https://prove2.me/theorems/e6edd7bd-ce10-4203-9a52-da0308b9f874
-- title:
--   §3, pp. 10–13 — cascade customers with exit probabilities, the adaptive fake entity with budget F, trajectories, expected real clicks and regret (2)
-- statement:
--   This file fixes the online ranking model of §3 of Golrezaei, Manshadi, Schneider and Sekar.
--
--   **Instance.** A platform displays $n$ products. Product $i$ has click probability $\mu_i\in[0,1]$, and after a non-click at position $j\le n-1$ a real customer leaves with probability $q_j\in[0,1]$. A **ranking** $\pi$ is a bijection from positions to products: $\pi(j)=i$ means product $i$ is at position $j$, and $\pi^{-1}(i)$ is the position of product $i$. The gap between products is
--   $$\Delta_{j,i}=\mu_j-\mu_i \qquad (3).$$
--
--   **Real customers (cascade model).** A real customer examines positions $1,2,\dots$ in turn. At position $j$ she clicks $\pi(j)$ with probability $\mu_{\pi(j)}$ and leaves; otherwise she leaves with probability $q_j$ (always, at the last position) or moves on. The platform observes $c_t$: the last examined position and whether its product was clicked. With $\mathrm{reach}(j)=\prod_{r<j}(1-q_r)\prod_{r<j}(1-\mu_{\pi(r)})$, the observation law is
--   $$\Pr[\text{click at } j]=\mathrm{reach}(j)\,\mu_{\pi(j)},\qquad \Pr[\text{no click, exit after } j]=\mathrm{reach}(j)\,(1-\mu_{\pi(j)})\,q_j ,$$
--   with $q_n:=1$.
--
--   **Fake users.** In each round the fake entity's policy maps the history $\mathcal H_{t-1}=\{(\pi_s,f_s,c_s)\}_{s<t}$ (rankings, fake indicators, observations) to a probability distribution over: a real user; a fake user who clicks product $i$ (and exits at its position); or a fake user who clicks nothing and exits after position $e$. The **fakeness budget** $F$ means $\sum_t f_t\le F$ on every realization: once $F$ rounds of the history were fake, the policy puts all mass on a real user.
--
--   **Algorithms and runs.** A randomized algorithm draws, in each round, an internal label $\ell\in\{1,\dots,L\}$ with probabilities depending on its own past (labels and observations, never the fake indicators) and displays a ranking that is a function of that past and $\ell$. A $T$-round run is a trajectory of (label, user action, observation) triples; its probability is the product over rounds of the label probability, the policy's probability of the action given $\mathcal H_{t-1}$, and the probability of the observation (the cascade law for a real user, a point mass for a fake one). Expectations and probabilities are the corresponding finite sums.
--
--   **Reward and regret.** $\mathcal C_{r,t}=1$ when the user of round $t$ is real and clicks. The regret (2) of an algorithm against a policy $\mathbf P$ is
--   $$\mathrm{Reg}_T(\mathbf P)=\mathbb E_{\mathcal H_T(\pi^\star)}\Big[\sum_{t=1}^T\mathcal C_{r,t}(\pi^\star)\Big]-\mathbb E_{\mathcal H_T(\pi_t)}\Big[\sum_{t=1}^T\mathcal C_{r,t}(\pi_t)\Big],$$
--   where $\pi^\star(i)=i$ and both runs face the same policy $\mathbf P$. The event $\mathcal A_{r,t}(\pi_t(j)=i)$ of Lemma 1 is: product $i$ is at position $j$ in round $t$, the user is real, and she does not exit before position $j$.
--
--   These are the objects in which Theorem 3 and its lemmas are stated.
--
--   **Formalization Note.** Products and positions are `Fin n` (0-based). An observation is `Fin n × Bool` (last examined position, clicked?), in bijection with the consistent pairs of $(\{\varnothing\}\cup[n])\times[n]$. `q` is a function on `Fin n` whose value at the last position is unused. The policy is `List (PubStep n) → PMF (Action n)`; its weights enter through `PMF.toReal`. `regret` is defined for a fixed policy; the supremum over policies in (2) is expressed in the theorems by quantifying over every policy within budget.
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, pp. 10–13, §3, (1)–(3); p. 20, Lemma 1 (event A); p. 47, App. C.1

import Mathlib

namespace FakeUserRanking.FORC

open scoped BigOperators

/-- A problem instance (§3, p. 10). Products and positions are `Fin n`, 0-based: Lean product `i`
is paper product `i + 1`, Lean position `j` is paper position `j + 1`.
`μ i` is the click probability of product `i`; `q j` is the probability that a real customer who
does not click at position `j` exits there (paper `q_{j+1}`). The value `q` at the last position is
never used: after the last position the customer always leaves. -/
structure Instance (n : ℕ) where
  μ : Fin n → ℝ
  μ_mem : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1
  q : Fin n → ℝ
  q_mem : ∀ j, q j ∈ Set.Icc (0 : ℝ) 1

/-- The gap `Δ_{j,i} = μ_j − μ_i` of (3), p. 13. -/
def gap {n : ℕ} (inst : Instance n) (j i : Fin n) : ℝ := inst.μ j - inst.μ i

/-- What the platform observes in a round (p. 12): the last examined position and whether the
product at that position was clicked. A click at position `j` means exit at `j` (p. 11), so the
clicked product is `π j`; this is the paper's `c_t ∈ ({∅} ∪ [n]) × [n]` restricted to consistent
pairs. -/
abbrev Obs (n : ℕ) := Fin n × Bool

/-- Probability that a real customer facing ranking `π` reaches position `j` (App. C.1, p. 47):
she did not click and did not exit at any earlier position. `π r` is the product at position `r`. -/
def reach {n : ℕ} (inst : Instance n) (π : Equiv.Perm (Fin n)) (j : Fin n) : ℝ :=
  (∏ r ∈ Finset.Iio j, (1 - inst.q r)) * ∏ r ∈ Finset.Iio j, (1 - inst.μ (π r))

/-- The law of a real customer's observation under ranking `π` (cascade model, p. 10):
she clicks at position `j` with probability `reach j · μ_{π j}`; she examines position `j`, does not
click and leaves with probability `reach j · (1 − μ_{π j}) · q_j` (with exit probability `1` at the
last position). -/
def realW {n : ℕ} (inst : Instance n) (π : Equiv.Perm (Fin n)) : Obs n → ℝ
  | (j, true) => reach inst π j * inst.μ (π j)
  | (j, false) => reach inst π j * (1 - inst.μ (π j)) * (if (j : ℕ) + 1 < n then inst.q j else 1)

/-- A user's type and action (p. 11): `none` is a real user; `some (Sum.inl i)` is a fake user
who clicks product `i` (and so exits at its position); `some (Sum.inr e)` is a fake user who clicks
nothing and exits after position `e`. -/
abbrev Action (n : ℕ) := Option (Fin n ⊕ Fin n)

/-- The observation produced by a fake user's action under ranking `π`. -/
def fakeObs {n : ℕ} (π : Equiv.Perm (Fin n)) : Fin n ⊕ Fin n → Obs n
  | Sum.inl i => (π.symm i, true)
  | Sum.inr e => (e, false)

/-- One entry `(π_s, f_s, c_s)` of the history `H_t` (p. 12): ranking, fake indicator,
observation. -/
abbrev PubStep (n : ℕ) := Equiv.Perm (Fin n) × Bool × Obs n

/-- The fake entity's adaptive randomized policy (p. 11): it maps the history `H_{t−1}` (the list
of past triples `(π_s, f_s, c_s)`, oldest first) to a probability distribution over this round's
action. It sees neither the current ranking nor the platform's internal randomness. -/
abbrev Adversary (n : ℕ) := List (PubStep n) → PMF (Action n)

/-- Fakeness budget `F` (p. 11, p. 52): once `F` rounds of the history were fake, every later user
is real. Equivalently, `∑_t f_t ≤ F` on every realization. -/
def WithinBudget {n : ℕ} (F : ℕ) (P : Adversary n) : Prop :=
  ∀ h : List (PubStep n), F ≤ (h.filter (fun s => s.2.1)).length → P h = PMF.pure none

/-- A randomized ranking algorithm with internal labels `Fin L`. In each round it draws a label
`ℓ` with probability `w h ℓ`, where `h` is its own past (labels and observations, oldest first),
and displays the ranking `rank h ℓ`. It never sees whether a user was fake (the platform observes
only `H^o_t`, p. 12). -/
structure Alg (n L : ℕ) where
  w : List (Fin L × Obs n) → Fin L → ℝ
  rank : List (Fin L × Obs n) → Fin L → Equiv.Perm (Fin n)

/-- One round of a run: the algorithm's label, the user's action, the observation. -/
abbrev Step (n L : ℕ) := Fin L × Action n × Obs n

variable {n L T : ℕ}

/-- The algorithm's own view of the first `t` rounds of a trajectory. -/
def algHist (τ : Fin T → Step n L) (t : ℕ) : List (Fin L × Obs n) :=
  ((List.ofFn τ).take t).map (fun s => (s.1, s.2.2))

/-- The ranking `π_s` displayed in round `s`. -/
def ranking (A : Alg n L) (τ : Fin T → Step n L) (s : Fin T) : Equiv.Perm (Fin n) :=
  A.rank (algHist τ s) (τ s).1

/-- The history `H_t` of the first `t` rounds: triples `(π_s, f_s, c_s)`. -/
def pubHist (A : Alg n L) (τ : Fin T → Step n L) (t : ℕ) : List (PubStep n) :=
  (List.ofFn (fun s : Fin T => (ranking A τ s, (τ s).2.1.isSome, (τ s).2.2))).take t

/-- Probability of observation `o` given the user's action, under ranking `π`. -/
def obsW (inst : Instance n) (π : Equiv.Perm (Fin n)) : Action n → Obs n → ℝ
  | none, o => realW inst π o
  | some a, o => if o = fakeObs π a then 1 else 0

/-- Weight of round `s` of a trajectory: label draw × adversary's action law × observation law. -/
def stepW (inst : Instance n) (P : Adversary n) (A : Alg n L) (τ : Fin T → Step n L) (s : Fin T) :
    ℝ :=
  A.w (algHist τ s) (τ s).1 * (P (pubHist A τ s) (τ s).2.1).toReal *
    obsW inst (ranking A τ s) (τ s).2.1 (τ s).2.2

/-- Probability of a whole `T`-round trajectory. -/
def trajW (inst : Instance n) (P : Adversary n) (A : Alg n L) (T : ℕ) (τ : Fin T → Step n L) : ℝ :=
  ∏ s : Fin T, stepW inst P A τ s

/-- Expectation over the `T`-round run of algorithm `A` against policy `P` on instance `inst`. -/
def expect (inst : Instance n) (P : Adversary n) (A : Alg n L) (T : ℕ)
    (g : (Fin T → Step n L) → ℝ) : ℝ :=
  ∑ τ : Fin T → Step n L, trajW inst P A T τ * g τ

open Classical in
/-- Probability of an event of the run. -/
noncomputable def prob (inst : Instance n) (P : Adversary n) (A : Alg n L) (T : ℕ)
    (E : (Fin T → Step n L) → Prop) : ℝ :=
  expect inst P A T (fun τ => if E τ then 1 else 0)

/-- `C_{r,t} = 1` iff the user of the round is real and clicks (p. 12). -/
def realClick (s : Step n L) : ℝ := if s.2.1 = none ∧ s.2.2.2 = true then 1 else 0

/-- Total reward `∑_t C_{r,t}(π_t)`: the number of real clicks. -/
def reward (τ : Fin T → Step n L) : ℝ := ∑ s : Fin T, realClick (τ s)

/-- The comparator that always displays `π⋆ = id` (p. 12; optimal because `μ` is decreasing). -/
def optAlg (n : ℕ) : Alg n 1 := ⟨fun _ _ => 1, fun _ _ => 1⟩

/-- Regret (2), p. 12, of algorithm `A` against a fixed policy `P`: both runs face the same `P`. -/
def regret (inst : Instance n) (P : Adversary n) (A : Alg n L) (T : ℕ) : ℝ :=
  expect inst P (optAlg n) T reward - expect inst P A T reward

/-- The event `A_{r,t}(π_t(j) = i)` (Lemma 1, p. 20): product `i` is at position `j` in round `t`,
the user is real, and she does not exit before position `j`. -/
def feedbackEvent (A : Alg n L) (τ : Fin T → Step n L) (t : Fin T) (j i : Fin n) : Prop :=
  ranking A τ t j = i ∧ (τ t).2.1 = none ∧ j ≤ (τ t).2.2.1

end FakeUserRanking.FORC


