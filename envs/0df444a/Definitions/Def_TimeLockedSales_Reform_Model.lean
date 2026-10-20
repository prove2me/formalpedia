-- Prove2me | Definitions.Def_TimeLockedSales_Reform_Model
-- name    : TimeLockedSales_Reform_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:58.992085+00:00
-- url     : https://prove2.me/theorems/f5932c59-db89-4c9a-9adb-5697e384507c
-- title:
--   §§3–4, pp. 7–18 — finite-message sales campaign model, Bayesian response (2), revenue (3), reformulations (9) and (11)
-- statement:
--   A campaign has $T$ successive customers, a fixed price $p$, an unknown binary product value $V$, a prior $v_0=\Pr(V=1)$, and private binary signals of precision $q$. The standing ranges are $p\in(0,1)$, $q\in(1/2,1]$, and $v_0\in[0,1]$. A policy gives a probability distribution over a finite message set after each history of earlier messages and purchase decisions.
--
--   Customer $t$ buys exactly when the conditional value of the product given her message and signal reaches the price:
--   $$a_t=1\quad\Longleftrightarrow\quad \mathbb E[V\mid S_t,m_t,\sigma]\ge p.$$
--   Indifference leads to purchase. The model constructs the joint law of product value and proprietary history recursively using this rule. It defines the expected revenue $p\sum_{t=1}^T\Pr(a_t=1)$ and its attainable values over all such policies.
--
--   It also defines the two thresholds $v^*$ and $v^{**}$ of (5), obedient three-message recommendation policies, the net purchase position $N$ of (7), the posterior $v_n$ of (8), the optimistic-signal chance $u_n$, the feasible sets and objectives of (9) and LP (11), and the recovery map (10). These objects give a common, reusable statement layer for the reduction to a linear program.
--
--   **Formalization Note.** Boolean `true` denotes a valuable product, an optimistic signal, and a purchase, respectively. Histories of length $t$ belong to customer $t+1$. The finite-message reading makes every policy law a finite sum. Bayesian response uses a joint-probability inequality, avoiding division on null events. Obedience is required only on signal–message pairs of positive probability. The posterior $v_n$ uses a two-sided product formula that remains meaningful at $q=1$. State probabilities in (9) are explicitly nonnegative, as their probabilistic meaning requires. Variables outside $n\in\{-(T-1),\ldots,T-1\}$ are zero, including the boundary terms in (N) and (11).
-- source:
--   Küçükgül, Özer & Wang, Engineering social learning: information design of time-locked sales campaigns for online platforms, submission manuscript (Nov. 2019; published Management Science 2022, doi:10.1287/mnsc.2021.4151), pp. 7–18, §§3–4, (1)–(11)

import Mathlib

namespace TimeLockedSales.Reform
open Classical

/-- Parameters of the finite time-locked sales campaign. -/
structure Params where
  T : ℕ
  p : ℝ
  q : ℝ
  v0 : ℝ

/-- The price, signal precision, and prior ranges of Section 3. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.p ∧ P.p < 1 ∧ (1 / 2 : ℝ) < P.q ∧ P.q ≤ 1 ∧ 0 ≤ P.v0 ∧ P.v0 ≤ 1

noncomputable def vStar (P : Params) : ℝ :=
  P.p * (1 - P.q) / (P.p * (1 - P.q) + (1 - P.p) * P.q)

noncomputable def vStarStar (P : Params) : ℝ :=
  P.p * P.q / (P.p * P.q + (1 - P.p) * (1 - P.q))

/-- The parameter region used after Proposition 1. -/
def Params.Region (P : Params) : Prop :=
  vStar P ≤ P.v0 ∧ P.v0 < vStarStar P

/-- `true` means the product is valuable. -/
def prior (P : Params) (v : Bool) : ℝ :=
  if v then P.v0 else 1 - P.v0

/-- `true` means an optimistic private signal. -/
def sigLik (P : Params) (v s : Bool) : ℝ :=
  if s = v then P.q else 1 - P.q

/-- A finite-message information policy, conditional on each proprietary history. -/
structure InfoPolicy (M : Type) [Fintype M] where
  σ : (t : ℕ) → (Fin t → M × Bool) → M → ℝ
  nonneg : ∀ t h m, 0 ≤ σ t h m
  sum_one : ∀ t h, ∑ m, σ t h m = 1

/-- Bayesian purchase rule (2), expressed without dividing by a possibly null event. -/
def buysAt (P : Params) {M : Type} [Fintype M] (σ : InfoPolicy M)
    (t : ℕ) (w : Bool → (Fin t → M × Bool) → ℝ) (s : Bool) (m : M) : Prop :=
  P.p * (∑ v : Bool, ∑ h, w v h * σ.σ t h m * sigLik P v s) ≤
    ∑ h, w true h * σ.σ t h m * sigLik P true s

/-- Joint probability of the value and the first `t` message-decision pairs. -/
noncomputable def law (P : Params) {M : Type} [Fintype M] (σ : InfoPolicy M) :
    (t : ℕ) → Bool → (Fin t → M × Bool) → ℝ
  | 0, v, _ => prior P v
  | t + 1, v, h =>
      law P σ t v (Fin.init h) * σ.σ t (Fin.init h) (h (Fin.last t)).1 *
        ∑ s : Bool,
          if (buysAt P σ t (law P σ t) s (h (Fin.last t)).1 ↔
              (h (Fin.last t)).2 = true) then sigLik P v s else 0

/-- The probability that customer `t+1` receives a given message. -/
noncomputable def msgProb (P : Params) {M : Type} [Fintype M]
    (σ : InfoPolicy M) (t : ℕ) (m : M) : ℝ :=
  ∑ v : Bool, ∑ h, law P σ t v h * σ.σ t h m

/-- The joint probability of the next customer's signal and message. -/
noncomputable def signalMsgProb (P : Params) {M : Type} [Fintype M]
    (σ : InfoPolicy M) (t : ℕ) (s : Bool) (m : M) : ℝ :=
  ∑ v : Bool, ∑ h, law P σ t v h * σ.σ t h m * sigLik P v s

/-- The value posterior conditional on a positive-probability message. -/
noncomputable def msgPosterior (P : Params) {M : Type} [Fintype M]
    (σ : InfoPolicy M) (t : ℕ) (m : M) : ℝ :=
  (∑ h, law P σ t true h * σ.σ t h m) / msgProb P σ t m

/-- The probability that customer `t+1` buys, using the endogenous rule (2). -/
noncomputable def purchaseProb (P : Params) {M : Type} [Fintype M]
    (σ : InfoPolicy M) (t : ℕ) : ℝ :=
  ∑ v : Bool, ∑ h, law P σ t v h *
    ∑ m, σ.σ t h m *
      ∑ s : Bool, if buysAt P σ t (law P σ t) s m then sigLik P v s else 0

/-- Expected platform revenue in (3). -/
noncomputable def revenue (P : Params) {M : Type} [Fintype M]
    (σ : InfoPolicy M) : ℝ :=
  P.p * ∑ t ∈ Finset.range P.T, purchaseProb P σ t

/-- Revenues from all finite-message information policies with Bayesian customer response. -/
def AchievableRevenue (P : Params) : Set ℝ :=
  {J | ∃ (M : Type) (_ : Fintype M) (σ : InfoPolicy M), J = revenue P σ}

/-- A recommendation policy is obeyed on each signal-message pair that occurs. -/
def IsObedient (P : Params) (σ : InfoPolicy SignType) : Prop :=
  ∀ t < P.T, ∀ m : SignType, ∀ s : Bool,
    0 < signalMsgProb P σ t s m →
      (buysAt P σ t (law P σ t) s m ↔ (m = 1 ∨ (m = 0 ∧ s = true)))

/-- Net purchase position (7): only neutral recommendations change it. -/
def netPos {t : ℕ} (h : Fin t → SignType × Bool) : ℤ :=
  ∑ i, if (h i).1 = 0 then (if (h i).2 then 1 else -1) else 0

/-- Posterior (8), written without negative powers of a zero base. -/
noncomputable def vN (P : Params) (n : ℤ) : ℝ :=
  if 0 ≤ n then
    P.v0 * P.q ^ n.toNat /
      (P.v0 * P.q ^ n.toNat + (1 - P.v0) * (1 - P.q) ^ n.toNat)
  else
    P.v0 * (1 - P.q) ^ (-n).toNat /
      (P.v0 * (1 - P.q) ^ (-n).toNat + (1 - P.v0) * P.q ^ (-n).toNat)

/-- Chance of an optimistic signal at net position `n`. -/
noncomputable def uN (P : Params) (n : ℤ) : ℝ :=
  P.q * vN P n + (1 - P.q) * (1 - vN P n)

/-- The paper's range `-(T-1), …, T-1`; empty when `T = 0`. -/
noncomputable def pos (P : Params) : Finset ℤ :=
  Finset.Icc (-((P.T : ℤ) - 1)) ((P.T : ℤ) - 1)

/-- Feasibility of (9): (R), probabilities and boundaries in (N), and the four IC inequalities. -/
def Feasible9 (P : Params) (r : ℕ → ℤ → SignType → ℝ)
    (z : ℕ → ℤ → ℝ) : Prop :=
  (∀ t ∈ Finset.Icc 1 P.T, ∀ n ∈ pos P,
    (∀ i, 0 ≤ r t n i) ∧ ∑ i, r t n i = 1) ∧
  (∀ t ∈ Finset.Icc 1 P.T, ∀ n, 0 ≤ z t n) ∧
  (∀ t ∈ Finset.Icc 1 P.T, ∀ n, n ∉ pos P → z t n = 0) ∧
  (∀ n ∈ pos P, z 1 n = if n = 0 then 1 else 0) ∧
  (∀ t ∈ Finset.Icc 2 P.T, ∀ n ∈ pos P,
    z t n = (r (t-1) n 1 + r (t-1) n (-1)) * z (t-1) n +
      uN P (n-1) * r (t-1) (n-1) 0 * z (t-1) (n-1) +
      (1 - uN P (n+1)) * r (t-1) (n+1) 0 * z (t-1) (n+1)) ∧
  (∀ t ∈ Finset.Icc 1 P.T,
    0 ≤ ∑ n ∈ pos P, (vN P n - vStarStar P) * z t n * r t n 1 ∧
    (∑ n ∈ pos P, (vN P n - vStarStar P) * z t n * r t n 0) ≤ 0 ∧
    0 ≤ ∑ n ∈ pos P, (vN P n - vStar P) * z t n * r t n 0 ∧
    (∑ n ∈ pos P, (vN P n - vStar P) * z t n * r t n (-1)) ≤ 0)

/-- Objective of (9). -/
noncomputable def obj9 (P : Params) (r : ℕ → ℤ → SignType → ℝ)
    (z : ℕ → ℤ → ℝ) : ℝ :=
  P.p * ∑ t ∈ Finset.Icc 1 P.T, ∑ n ∈ pos P,
    z t n * (r t n 1 + uN P n * r t n 0)

/-- Feasibility of the linear program (11). Outside `pos P`, variables are zero. -/
def FeasibleLP (P : Params) (y : ℕ → ℤ → SignType → ℝ) : Prop :=
  (∀ t ∈ Finset.Icc 1 P.T, ∀ n i, 0 ≤ y t n i) ∧
  (∀ t ∈ Finset.Icc 1 P.T, ∀ n i, n ∉ pos P → y t n i = 0) ∧
  (∀ t ∈ Finset.Icc 1 P.T,
    0 ≤ ∑ n ∈ pos P, (vN P n - vStarStar P) * y t n 1 ∧
    (∑ n ∈ pos P, (vN P n - vStar P) * y t n (-1)) ≤ 0 ∧
    (∑ n ∈ pos P, (vN P n - vStarStar P) * y t n 0) ≤ 0 ∧
    0 ≤ ∑ n ∈ pos P, (vN P n - vStar P) * y t n 0) ∧
  (∀ t ∈ Finset.Icc 2 P.T, ∀ n ∈ pos P,
    (∑ i, y t n i) = y (t-1) n 1 + y (t-1) n (-1) +
      uN P (n-1) * y (t-1) (n-1) 0 +
      (1 - uN P (n+1)) * y (t-1) (n+1) 0) ∧
  (∀ n ∈ pos P, (∑ i, y 1 n i) = if n = 0 then 1 else 0)

/-- Objective of (11). -/
noncomputable def objLP (P : Params) (y : ℕ → ℤ → SignType → ℝ) : ℝ :=
  P.p * ∑ t ∈ Finset.Icc 1 P.T, ∑ n ∈ pos P,
    (y t n 1 + uN P n * y t n 0)

/-- The first recovery identity in (10). -/
def zOf (y : ℕ → ℤ → SignType → ℝ) (t : ℕ) (n : ℤ) : ℝ :=
  ∑ i, y t n i

/-- The second recovery identity in (10), including any (R)-vector at zero mass. -/
def Recovers (P : Params) (y r : ℕ → ℤ → SignType → ℝ) : Prop :=
  ∀ t ∈ Finset.Icc 1 P.T, ∀ n ∈ pos P,
    (0 < zOf y t n → ∀ i, r t n i = y t n i / zOf y t n) ∧
    (zOf y t n = 0 → (∀ i, 0 ≤ r t n i) ∧ ∑ i, r t n i = 1)

end TimeLockedSales.Reform


