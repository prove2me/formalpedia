-- Prove2me | Definitions.Def_QueueBandit_QUCB_Algorithm1
-- name    : QueueBandit_QUCB_Algorithm1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:12.465602+00:00
-- url     : https://prove2.me/theorems/81e5efcf-ec55-41e0-acd0-3446cc0fb58d
-- title:
--   Algorithm 1 (Q-UCB), p. 15 — UCB1 with forced exploration, the queues Q_u, regeneration time B_u(t), queue-regret Ψ_u(t), events ℰ₁, ℰ₂
-- statement:
--   This module defines the scheduling algorithm Q-UCB (Algorithm 1, p. 15) on the switch of the `Model` module, and the quantities used in its analysis (§8.2).
--
--   **History and indices.** After $t-1$ slots the scheduler knows the scheduled matchings $\kappa(s)$ and the services $S_u(s)=R_{u\kappa_u(s)}(s)$ observed on the scheduled links, $s\le t-1$. For each link let $N_{uk}(t)$ be the number of slots $s\le t-1$ with $\kappa_u(s)=k$, let $\hat\mu_{uk}(t)$ be the mean of the services observed on that link, and
--   $$\mathrm{UCB}_{uk}(t)=\hat\mu_{uk}(t)+\sqrt{\frac{\log^2 t}{2N_{uk}(t)}}.$$
--
--   **Q-UCB.** Fix a family $\mathcal X=\{X_0,\dots,X_{K-1}\}$ of matchings covering every edge of the complete bipartite graph. In slot $t$:
--
--   1. if $\mathsf E(t)=1$ (*explore*), schedule $X_{J_t}$, a uniformly random member of $\mathcal X$;
--   2. otherwise (*exploit*), choose for every queue $\hat k_u(t)\in\arg\max_k\mathrm{UCB}_{uk}(t)$, an unsampled server ($N_{uk}(t)=0$, index $+\infty$) if there is one, and schedule a matching $\kappa(t)\in\arg\min_{\kappa\in\mathcal M}\sum_u\mathbb 1\{\kappa_u\neq\hat k_u(t)\}$.
--
--   Ties in both choices are broken by arbitrary rules, given as functions of the slot and the history; a `QUCBRule` bundles $\mathcal X$ and the two rules, and every theorem holds for every such rule.
--
--   **Derived quantities.** The queue $Q_u(t)=(Q_u(t-1)+A_u(t)-S_u(t))^+$; the exploit indicator $\mathsf I_{uk}(t)=\mathbb 1\{\mathsf E(t)=0,\ \kappa_u(t)=k\}$; the time since the last empty instant
--   $$B_u(t)=\min\{s\ge0:\ Q_u(t-s)=0\}\quad(\text{and }B_u(t)=t\text{ if there is no such }s\le t);$$
--   the **queue-regret** $\Psi_u(t)=\mathbb E[Q_u(t)-Q^*_u(t)]$; for $\beta>1$, $w(t)=t^{1-1/\beta}$, $v'_u(t)=\frac{6K}{\epsilon_u}w(t)$ and $v_u(t)=\frac{24}{\epsilon_u^2}\log t+\frac{60K}{\epsilon_u}\frac{v'_u(t)\log^2t}{t}$; and the events
--   $$\mathcal E_1=\Big\{\sum_{w(t)<l\le t}\ \sum_{u}\sum_{k\neq k^*_u}\mathsf I_{uk}(l)=0\Big\},\qquad \mathcal E_2=\Big\{\sum_{l=1}^t\mathsf E(l)\le Kw(t)\Big\}.$$
--
--   **Formalization Note** $N_{uk}(t)$ counts the slots $1,\dots,t-1$, the number of samples averaged in $\hat\mu_{uk}(t)$; the page's $T_{uk}(t-1)$ is read this way (paper.md slip 2). The rule "unsampled first" is UCB1's convention for $N=0$, which the page leaves open. The sum over $w(t)<l\le t$ ranges over natural numbers $l$ (`Finset.Ioc ⌊w t⌋₊ t`). $B_u(t)=t$ when queue $u$ was never empty on $[0,t]$, a case the page leaves undefined (slip 7). Tie-breaking rules are deterministic functions of the slot and the history.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 14, §4.2.1 (ℳ, 𝒳); p. 15, Table 2 and Algorithm 1; p. 16, Theorem 5 (w, v′, v); p. 25, ℰ₁; p. 29, B_u(t); p. 30, ℰ₂

import Mathlib
import Definitions.Def_QueueBandit_QUCB_Model

namespace QueueBandit.QUCB

open MeasureTheory

variable {U K : ℕ}

/-- The scheduler's information after `n` slots: entry `i` records slot `i + 1`, namely the
scheduled matching `κ(i + 1)` and the observed services `S_u(i + 1) = R_{u κ_u(i+1)}(i + 1)`. -/
abbrev Hist (U K n : ℕ) := Fin n → Matching U K × (Fin U → ℕ)

/-- `N_uk`: the number of recorded slots in which server `k` was assigned to queue `u`. -/
def Hist.count {n : ℕ} (h : Hist U K n) (u : Fin U) (k : Fin K) : ℕ :=
  (Finset.univ.filter fun i => (h i).1.1 u = k).card

/-- The total service observed on link `(u, k)` over the recorded slots. -/
def Hist.served {n : ℕ} (h : Hist U K n) (u : Fin U) (k : Fin K) : ℕ :=
  ∑ i, if (h i).1.1 u = k then (h i).2 u else 0

/-- The empirical mean `μ̂_uk` of the observed services of link `(u, k)`. -/
noncomputable def Hist.muHat {n : ℕ} (h : Hist U K n) (u : Fin U) (k : Fin K) : ℝ :=
  (h.served u k : ℝ) / h.count u k

/-- The UCB index `μ̂_uk + √(log² t / (2 N_uk))` used at time slot `t`. -/
noncomputable def Hist.ucbIndex {n : ℕ} (t : ℕ) (h : Hist U K n) (u : Fin U) (k : Fin K) : ℝ :=
  h.muHat u k + Real.sqrt (Real.log t ^ 2 / (2 * h.count u k))

/-- `k̂` is a UCB1 choice for queue `u` at slot `t = n + 1` given the history `h` of the first `n`
slots: an unsampled server if there is one (index `+∞`), otherwise a maximizer of the UCB index. -/
def IsUCBChoice {n : ℕ} (h : Hist U K n) (u : Fin U) (khat : Fin K) : Prop :=
  ((∃ k, h.count u k = 0) → h.count u khat = 0) ∧
  ((∀ k, h.count u k ≠ 0) → ∀ k, h.ucbIndex (n + 1) u k ≤ h.ucbIndex (n + 1) u khat)

/-- The number of queues on which a matching `κ` disagrees with a server vector `khat`. -/
def hamming (κ : Matching U K) (khat : Fin U → Fin K) : ℕ :=
  (Finset.univ.filter fun u => κ.1 u ≠ khat u).card

/-- `κ ∈ argmin_{κ' ∈ ℳ} Σ_u 1{κ'_u ≠ k̂_u}`: a Hamming projection of `k̂` onto the matchings. -/
def IsHammingProjection (khat : Fin U → Fin K) (κ : Matching U K) : Prop :=
  ∀ κ' : Matching U K, hamming κ khat ≤ hamming κ' khat

/-- `𝒳 = {X 0, …, X (K−1)}` covers every edge of the complete bipartite graph. (With `U ≤ K`
this forces the `K` matchings to be pairwise edge-disjoint, hence distinct.) -/
def IsCovering (X : Fin K → Matching U K) : Prop := ∀ u k, ∃ j, (X j).1 u = k

/-- A specification of Q-UCB (Algorithm 1, p. 15): the explore family `𝒳` and the arbitrary
tie-breaking rules of the UCB argmax (`sel`) and of the Hamming projection (`proj`), both
deterministic functions of the slot and the history. -/
structure QUCBRule (U K : ℕ) where
  X : Fin K → Matching U K
  covering : IsCovering X
  sel : (n : ℕ) → Hist U K n → Fin U → Fin K
  sel_spec : ∀ n (h : Hist U K n) u, IsUCBChoice h u (sel n h u)
  proj : (n : ℕ) → Hist U K n → (Fin U → Fin K) → Matching U K
  proj_spec : ∀ n (h : Hist U K n) khat, IsHammingProjection khat (proj n h khat)

namespace QUCBRule

/-- Slot `t = n + 1` of Q-UCB given the history `h` of the first `n` slots: explore (schedule
`X J_t`) if `E(t) = 1`, else exploit (Hamming projection of the UCB choices); returns the scheduled
matching and the observed services. -/
noncomputable def step (A : QUCBRule U K) (I : Instance U K) (n : ℕ) (h : Hist U K n) (ω : Ω U K) :
    Matching U K × (Fin U → ℕ) :=
  let κ := if explore (n + 1) ω = 1 then A.X (ω.2 (n + 1)).2.2.2 else A.proj n h (A.sel n h)
  (κ, fun u => I.R u (κ.1 u) (n + 1) ω)

/-- The history of the first `n` slots along the sample point `ω`. -/
noncomputable def hist (A : QUCBRule U K) (I : Instance U K) : (n : ℕ) → Ω U K → Hist U K n
  | 0, _ => Fin.elim0
  | n + 1, ω => Fin.snoc (α := fun _ => Matching U K × (Fin U → ℕ)) (A.hist I n ω)
      (A.step I n (A.hist I n ω) ω)

/-- The matching `κ(t)` scheduled in slot `t ≥ 1`. -/
noncomputable def kappa (A : QUCBRule U K) (I : Instance U K) (t : ℕ) (ω : Ω U K) : Matching U K :=
  (A.step I (t - 1) (A.hist I (t - 1) ω) ω).1

/-- The service offered to queue `u` in slot `t`: `S_u(t) = R_{u κ_u(t)}(t)`. -/
noncomputable def S (A : QUCBRule U K) (I : Instance U K) (u : Fin U) (t : ℕ) (ω : Ω U K) : ℕ :=
  I.R u ((A.kappa I t ω).1 u) t ω

/-- The queue `Q_u` under Q-UCB: `Q_u(0)` from `ω`, `Q_u(t) = (Q_u(t−1) + A_u(t) − S_u(t))⁺`. -/
noncomputable def Q (A : QUCBRule U K) (I : Instance U K) (u : Fin U) : ℕ → Ω U K → ℕ
  | 0, ω => ω.1 u
  | t + 1, ω => A.Q I u t ω + I.A u (t + 1) ω - A.S I u (t + 1) ω

/-- `I_uk(t)`: server `k` is assigned to queue `u` in slot `t` through Exploit. -/
noncomputable def exploit (A : QUCBRule U K) (I : Instance U K) (u : Fin U) (k : Fin K) (t : ℕ)
    (ω : Ω U K) : ℕ :=
  if explore t ω = 0 ∧ (A.kappa I t ω).1 u = k then 1 else 0

open scoped Classical in
/-- `B_u(t) = min{s ≥ 0 : Q_u(t − s) = 0}`, the time since queue `u` was last empty, and `t` if
queue `u` has not been empty at any time in `[0, t]`. -/
noncomputable def B (A : QUCBRule U K) (I : Instance U K) (u : Fin U) (t : ℕ) (ω : Ω U K) : ℕ :=
  if h : ∃ s, s ≤ t ∧ A.Q I u (t - s) ω = 0 then Nat.find h else t

/-- The queue-regret `Ψ_u(t) = 𝔼[Q_u(t) − Q*_u(t)]`. -/
noncomputable def Psi (A : QUCBRule U K) (I : Instance U K) (u : Fin U) (t : ℕ) : ℝ :=
  ∫ ω, ((A.Q I u t ω : ℝ) - (I.Qstar u t ω : ℝ)) ∂I.P

end QUCBRule

/-- `w(t) = t^{1 − 1/β}`. -/
noncomputable def w (β : ℝ) (t : ℕ) : ℝ := (t : ℝ) ^ (1 - 1 / β)

/-- `v′_u(t) = (6K/ε_u) w(t)`. -/
noncomputable def Instance.vPrime (I : Instance U K) (β : ℝ) (u : Fin U) (t : ℕ) : ℝ :=
  6 * K / I.eps u * w β t

/-- `v_u(t) = (24/ε_u²) log t + (60K/ε_u) v′_u(t) log² t / t`. -/
noncomputable def Instance.v (I : Instance U K) (β : ℝ) (u : Fin U) (t : ℕ) : ℝ :=
  24 / I.eps u ^ 2 * Real.log t + 60 * K / I.eps u * (I.vPrime β u t * Real.log t ^ 2 / t)

/-- `ℰ₁ = {Σ_{w(t) < l ≤ t} Σ_u Σ_{k ≠ k*_u} I_uk(l) = 0}`: no sub-optimal exploit schedule in
the slots `l ∈ ℕ` with `w(t) < l ≤ t`. -/
def QUCBRule.E1 (A : QUCBRule U K) (I : Instance U K) (β : ℝ) (t : ℕ) : Set (Ω U K) :=
  {ω | ∑ l ∈ Finset.Ioc ⌊w β t⌋₊ t, ∑ u, ∑ k ∈ Finset.univ.filter (fun k => k ≠ I.kstar u),
      A.exploit I u k l ω = 0}

/-- `ℰ₂ = {Σ_{l=1}^t E(l) ≤ K w(t)}`. -/
def E2 (β : ℝ) (t : ℕ) : Set (Ω U K) :=
  {ω | ((∑ l ∈ Finset.Icc 1 t, explore l ω : ℕ) : ℝ) ≤ K * w β t}

end QueueBandit.QUCB


