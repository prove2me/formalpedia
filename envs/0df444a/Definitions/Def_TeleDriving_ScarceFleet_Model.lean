-- Prove2me | Definitions.Def_TeleDriving_ScarceFleet_Model
-- name    : TeleDriving_ScarceFleet_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:26.400474+00:00
-- url     : https://prove2.me/theorems/0a9ae8fc-9836-452b-be5f-88759e642276
-- title:
--   §3, pp. 11–14, 22 — ρ (1), π_{m,n} (2)–(3), SL(m, n), Assumptions 1–2, the size restriction, the regimes, the rate (4), m_λ
-- statement:
--   A ride-hailing platform runs $m$ vehicles that are driven remotely by $n \le m$ tele-drivers. Trip requests arrive as a Poisson process of rate $\lambda > 0$; a request that finds every driver busy is lost. When $q$ customers are in service (waiting for pick-up or riding), each trip ends at the state-dependent exponential rate $\mu(m, q)$, a function of a real $q \in [1, m]$. The number of customers in service is a birth–death chain with birth rate $\lambda$ and death rate $q\mu(m,q)$ in state $q$, truncated at $n$. With
--   $$\rho(q) = \frac{\lambda}{q\,\mu(m,q)} \qquad (1)$$
--   its stationary distribution is
--   $$\pi_{m,n}(0) = \Big[1 + \sum_{i=1}^{n} \prod_{k=1}^{i} \rho(k)\Big]^{-1}, \qquad \pi_{m,n}(q) = \pi_{m,n}(0) \prod_{k=1}^{q} \rho(k), \quad 0 \le q \le n, \qquad (2)\text{–}(3)$$
--   and the **service level**, the long-run fraction of demand served, is $SL(m,n) = 1 - \pi_{m,n}(n)$.
--
--   The file also fixes the standing assumptions of the paper:
--
--   1. **Assumption 1** (p. 11): $s > 0$ (the expected trip time between two uniform locations) and $\mu(m, q) > 0$ on $[1, m]$; $\mu(m,q)$ is strictly increasing in $m$ and non-increasing in $q$; strictly concave in $q$ on $[1,m]$; $\mu(m,q) \to 1/s$ as $m \to \infty$; and $\mu(m,m)$ does not depend on $m \ge 1$.
--   2. **Assumption 2** (p. 11): there is $\bar m > 0$ such that for every $m \ge \bar m$ the trip-completion rate $q\mu(m,q)$ strictly increases on $[1, \hat q]$ and strictly decreases on $[\hat q, m]$ for some turning point $\hat q \in (1, m)$.
--   3. **The size restriction** (p. 13): $m \ge \bar m$ and $\lambda > \max\{1/s, \max_{q \in \{1,\dots,\bar m\}} q\mu(\bar m, q)\}$.
--   4. **The regimes**: supply-limited ($m < \gamma_1(\lambda)$), read as $\rho(q) > 1$ for all $q \in [1, m]$ (Lemma 3(i)); supply-rich ($m > \gamma_2(\lambda)$), read as $\lambda < m\mu(m,m)$.
--
--   It also defines the rate (4) of §3.3, $\mu(m,q) = [s/\sqrt{m-q+1} + s]^{-1}$, the fleet size $m_\lambda = \lfloor \alpha\lambda s \rfloor$ and $\max_{1 \le n \le m} SL(m,n)/SL(m,m)$, which the later missions of the series use.
--
--   These are the objects every result of the paper is stated about.
--
--   **Formalization Note** $\mu$ is a function $\mathbb N \times \mathbb R \to \mathbb R$ whose values matter only for $q \in [1, m]$. Positivity of $\mu$ and $s > 0$ are implicit on the page (a rate and a trip time) and are written into Assumption 1. "Decreasing in $q$" is read non-strictly (AntitoneOn); "first increases then decreases" is a strict turning point inside $(1, m)$. The paper defines $\gamma_1(\lambda), \gamma_2(\lambda)$ as real roots in $m$; the regimes are encoded by the characterizations the proofs use. $\pi_{m,n}(q)$ is meaningful for $q \le n$ and $SL(m,n)$ for $n \le m$. The product is empty at $i = 0$, so $\pi_{m,0}(0) = 1$ and $SL(m,0) = 0$.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), pp. 11–14 and 22, Assumptions 1–2, (1)–(4), the size restriction of §3.1 (p. 13), Lemma 3 (p. 37)

import Mathlib

namespace TeleDriving.ScarceFleet

/-- ρ(q) = λ / (q µ(m, q)), (1), p. 12. `mu m q` is the service rate µ(m, q) with m vehicles (a natural
number) and q customers in service; q is real, as in Lemma 3 (p. 37), and meaningful for q ∈ [1, m]. -/
noncomputable def rho (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m : ℕ) (q : ℝ) : ℝ :=
  lam / (q * mu m q)

/-- The product ∏_{k=1}^{i} ρ(k) of (2)–(3), p. 12; it equals 1 at i = 0 (empty product). -/
noncomputable def weight (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m i : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 i, rho mu lam m (k : ℝ)

/-- π_{m,n}(q), (2)–(3), p. 12: the stationary probability of q customers in service with m vehicles and
n remote drivers, for 0 ≤ q ≤ n. -/
noncomputable def piMN (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m n q : ℕ) : ℝ :=
  weight mu lam m q / (1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i)

/-- The service level SL(m, n) = 1 − π_{m,n}(n), p. 12. -/
noncomputable def SL (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m n : ℕ) : ℝ :=
  1 - piMN mu lam m n n

/-- Assumption 1, p. 11, for a rate defined for q ∈ [1, m], with the positivity of a service rate (implicit
on the page): s > 0; µ > 0; (1) µ(m, q) strictly increasing in m and decreasing in q; (2) strictly concave
in q; (3) µ(m, q) → 1/s as m → ∞; (4) µ(m, m) invariant in m. -/
def Assumption1 (mu : ℕ → ℝ → ℝ) (s : ℝ) : Prop :=
  0 < s ∧
  (∀ m : ℕ, ∀ q ∈ Set.Icc (1 : ℝ) m, 0 < mu m q) ∧
  (∀ (m m' : ℕ) (q : ℝ), 1 ≤ q → q ≤ m → m < m' → mu m q < mu m' q) ∧
  (∀ m : ℕ, AntitoneOn (mu m) (Set.Icc (1 : ℝ) m)) ∧
  (∀ m : ℕ, StrictConcaveOn ℝ (Set.Icc (1 : ℝ) m) (mu m)) ∧
  (∀ q : ℝ, 1 ≤ q → Filter.Tendsto (fun m : ℕ => mu m q) Filter.atTop (nhds (1 / s))) ∧
  (∀ m m' : ℕ, 1 ≤ m → 1 ≤ m' → mu m (m : ℝ) = mu m' (m' : ℝ))

/-- Assumption 2, p. 11: there is m̄ > 0 such that for m ≥ m̄, q ↦ q µ(m, q) first increases, then
decreases on [1, m]. -/
def Assumption2 (mu : ℕ → ℝ → ℝ) (mbar : ℕ) : Prop :=
  0 < mbar ∧ ∀ m : ℕ, mbar ≤ m → ∃ qhat ∈ Set.Ioo (1 : ℝ) m,
    StrictMonoOn (fun q : ℝ => q * mu m q) (Set.Icc 1 qhat) ∧
    StrictAntiOn (fun q : ℝ => q * mu m q) (Set.Icc qhat (m : ℝ))

/-- The size restriction of p. 13: m ≥ m̄ and λ > max{1/s, max_{q ∈ {1,…,m̄}} q µ(m̄, q)}. -/
def StandingSize (mu : ℕ → ℝ → ℝ) (s : ℝ) (mbar m : ℕ) (lam : ℝ) : Prop :=
  mbar ≤ m ∧ 1 / s < lam ∧ ∀ q ∈ Finset.Icc 1 mbar, (q : ℝ) * mu mbar (q : ℝ) < lam

/-- The supply-limited regime m < γ₁(λ), in the form of Lemma 3(i), p. 37: ρ(q) > 1 for 1 ≤ q ≤ m. -/
def IsSupplyLimited (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m : ℕ) : Prop :=
  ∀ q ∈ Set.Icc (1 : ℝ) m, 1 < rho mu lam m q

/-- The supply-rich regime m > γ₂(λ), in the form of the proof of Lemma 3, item (2), p. 37:
ρ(m, m) < 1, i.e. λ < m µ(m, m). -/
def IsSupplyRich (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m : ℕ) : Prop :=
  lam < (m : ℝ) * mu m (m : ℝ)

/-- The rate (4), p. 14 (used in §3.3): µ(m, q) = [s/√(m − q + 1) + s]⁻¹. -/
noncomputable def muBesbes (s : ℝ) (m : ℕ) (q : ℝ) : ℝ :=
  1 / (s / Real.sqrt ((m : ℝ) - q + 1) + s)

/-- m_λ = ⌊αλs⌋, §3.3, p. 22. -/
noncomputable def mLam (alpha s lam : ℝ) : ℕ :=
  ⌊alpha * lam * s⌋₊

/-- max_{n ∈ {1,…,m}} SL(m, n)/SL(m, m) of Theorems 2.A–2.B, p. 22 (`Fin m` index n ↦ n + 1; the empty
supremum at m = 0 is 0 and never matters, since m_λ → ∞). -/
noncomputable def maxSLRatio (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m : ℕ) : ℝ :=
  ⨆ n : Fin m, SL mu lam m ((n : ℕ) + 1) / SL mu lam m m

end TeleDriving.ScarceFleet


