-- Prove2me | Definitions.Def_RiskExposure_RingComplete_Model
-- name    : RiskExposure_RingComplete_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:27.670032+00:00
-- url     : https://prove2.me/theorems/3092f1ca-8a52-4805-a8c0-a3ed93c93db2
-- title:
--   §2, Definitions 1–3, (1)–(5), pp. 5–14 — regular interbank network, ring Θ^R and complete Θ^C, greatest payment equilibrium d*, expected profit, equilibrium, cross-subsidy D_i, Pr(m failed), K_i(ω)
-- statement:
--   This file sets up Shu's model of $N$ banks in a **regular** interbank network, together with the two networks of Definition 3 and the quantities used to compare them.
--
--   **Networks.** A regular network is given by a share matrix $\Theta=[\theta_{ij}]$, a common total interbank liability $\bar d>0$ and a common deposit $v>0$: bank $j$ owes bank $i$ the face value $\theta_{ij}\bar d$. Definition 3 introduces, with banks indexed $0,\dots,N-1$,
--   $$\Theta^R_{ij}=\begin{cases}1 & j\equiv i-1 \pmod N\\ 0&\text{otherwise,}\end{cases}\qquad \Theta^C=\frac{1}{N-1}\big(\mathbb 1_{N,N}-I_N\big).$$
--   In the **ring** $\Theta^R$ each bank is owed only by its upstream neighbour $i-1$; in the **complete** network $\Theta^C$ every bank holds an equal share of every other bank's debt.
--
--   **States and clearing.** Each bank $i$ chooses a project $Z_i$, which pays $Z_i$ on success and $0$ on failure; a state is $\omega\in\{s,f\}^N$ and the cash flow is $e_i(\omega_i,Z_i)=Z_i$ if $\omega_i=s$ and $0$ otherwise. A **payment equilibrium** (Definition 1, (2)) is a vector $d$ with
--   $$d_i=\Big\{\min\Big[\sum_j\theta_{ij}d_j+e_i(\omega_i,Z_i)-v,\ \bar d\Big]\Big\}^+\quad\text{for all } i,$$
--   where $x^+=\max\{x,0\}$. The payment equilibrium $d^*(\omega;Z)$ used throughout is the **greatest** solution of this system.
--
--   **Profits and equilibrium.** Bank $i$'s profit is $\Pi_i(\omega;Z)=\big(\sum_j\theta_{ij}d^*_j+e_i-v-d^*_i\big)^+$ (3). Projects succeed independently, bank $j$ with probability $P(Z_j)$, so
--   $$\mathbb E[\Pi_i]=\sum_{\omega\in\{s,f\}^N}\Pi_i(\omega;Z)\prod_j\Pr(\omega_j).$$
--   Bank $i$'s **best responses** to $Z_{-i}$ are the maximizers of $\mathbb E[\Pi_i]$ over its own choice $Z_i\in[\underline Z,\overline Z]$ (4), and a **risk-taking equilibrium** (Definition 2) is a profile $Z^*$ in which every $Z^*_i$ is a best response to $Z^*_{-i}$.
--
--   **The distortion.** Bank $i$'s expected cross-subsidy (5) is
--   $$\mathcal D_i(Z_{-i})=\sum_{\omega_{-i}}\Big(\bar d-\sum_j\theta_{ij}d^*_j(\omega^{i=s})\Big)\Pr(\omega_{-i}),$$
--   where $\omega^{i=s}$ appends bank $i$'s success to $\omega_{-i}$.
--
--   **Ingredients of the closed forms.** With $q$ the common success probability of the other banks, $\Pr(m\text{ banks failed})=\binom{N-1}{m}(1-q)^m q^{N-1-m}$ (p. 14). The ring weight is $\binom{N-2-l}{N-2-m}\big/\binom{N-1}{m}$ for $m\le N-2$; for $m=N-1$ it is $1$ at $l=N-1$ and $0$ otherwise. Finally $K_i(\omega)=\min\{o\ge0:\omega_{i-o}=s\}$ (indices mod $N$) is the number of consecutive failed banks met going upstream from $i$, counting $i$ itself, before the first successful bank (I.14). The number of consecutive failed upstream neighbours of $i$ is $K_{i-1}(\omega)$.
--
--   These objects are shared by every statement of the mission: the two clearing vectors, the two closed forms of $\mathcal D_i$, their comparison, and Proposition 4.
--
--   **Formalization Note.** Banks are `Fin N`; the state is `ω : Fin N → Bool` with `true` meaning success. The paper's general model has bilateral face values $\bar d_{ij}$; on a regular network $\bar d_{ij}=\theta_{ij}\bar d$, $\bar d_j=\bar d$ and $v_j=v$, which is the specialization encoded here (`clear θ dbar v`). $d^*$ is `sSup` of the solutions of (2) lying in the box $[0,\bar d]^N$, which contains every solution; for $\theta\ge0$ and $\bar d\ge0$ this supremum is itself a solution and the greatest one (Knaster–Tarski). The paper's Lemma 1 asserts only generic uniqueness, so a selection is needed; the greatest one coincides with the unique one whenever (2) has a single solution. `bestResponse` fixes coordinate $i$ with `Function.update` and requires the choice to lie in $[\underline Z,\overline Z]$. `ringWeight` at $m=N-1$ replaces the printed binomial with lower index $-1$. `runLength` returns the junk value $N$ when no bank succeeds; every statement using it assumes some bank succeeds. `upRun ω i` is `runLength` of the upstream neighbour.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), pp. 5–9, Definition 1, (1)–(5); p. 8, Definition 2; p. 13, Definition 3; p. 14, Pr(m banks failed) and the D^R weights; Internet Appendix p. 16, K_i(ω) in (I.14)

import Mathlib

namespace RiskExposure.RingComplete

open Finset

/-- The ring network `Θ^R` of Definition 3 (p. 13), 0-indexed: `θ_ij = 1` exactly when
`j ≡ i − 1 (mod N)`, i.e. bank `i` is owed by its upstream neighbour `i − 1` (row 1 of `Θ^R` has
its `1` in column `N`, row `i ≥ 2` in column `i − 1`), and `θ_ij = 0` otherwise. -/
def thetaRing (N : ℕ) (i j : Fin N) : ℝ :=
  if (j : ℕ) = ((i : ℕ) + N - 1) % N then 1 else 0

/-- The complete network `Θ^C = (𝟙_{N,N} − I_N)/(N − 1)` of Definition 3 (p. 13). -/
noncomputable def thetaComplete (N : ℕ) (i j : Fin N) : ℝ :=
  if i = j then 0 else 1 / ((N : ℝ) - 1)

/-- The realized cash flow `e_i(ω_i, Z_i)` of (1): `Z_i` if bank `i`'s project succeeds
(`ω i = true`, the paper's `ω_i = s`) and `0` if it fails (`ω i = false`, `ω_i = f`). -/
def cash {N : ℕ} (ω : Fin N → Bool) (Z : Fin N → ℝ) (i : Fin N) : ℝ :=
  if ω i then Z i else 0

/-- The right-hand side of (2) in a regular network with share matrix `θ`, common total
interbank liability `d̄` and common deposit `v`:
`{min[∑_j θ_ij d_j + e_i(ω_i, Z_i) − v, d̄]}^+`. -/
def clear {N : ℕ} (θ : Fin N → Fin N → ℝ) (dbar v : ℝ) (ω : Fin N → Bool) (Z : Fin N → ℝ)
    (d : Fin N → ℝ) (i : Fin N) : ℝ :=
  max (min (∑ j, θ i j * d j + cash ω Z i - v) dbar) 0

/-- `d` solves the payment-equilibrium system (2) of Definition 1 in state `ω` under the risk
vector `Z`. -/
def IsPaymentEq {N : ℕ} (θ : Fin N → Fin N → ℝ) (dbar v : ℝ) (ω : Fin N → Bool) (Z : Fin N → ℝ)
    (d : Fin N → ℝ) : Prop :=
  ∀ i, d i = clear θ dbar v ω Z d i

/-- The payment equilibrium `d*(ω; Z)`: the greatest solution of (2), taken as the
(componentwise) supremum of all solutions `d` with `0 ≤ d_i ≤ d̄` (every solution of (2) lies in
this box when `d̄ ≥ 0`). -/
noncomputable def paymentEq {N : ℕ} (θ : Fin N → Fin N → ℝ) (dbar v : ℝ) (ω : Fin N → Bool)
    (Z : Fin N → ℝ) : Fin N → ℝ :=
  sSup {d : Fin N → ℝ | (∀ i, 0 ≤ d i ∧ d i ≤ dbar) ∧ IsPaymentEq θ dbar v ω Z d}

/-- Bank `i`'s profit (3): `(∑_j θ_ij d*_j + e_i − v − d*_i)^+`. -/
noncomputable def profit {N : ℕ} (θ : Fin N → Fin N → ℝ) (dbar v : ℝ) (ω : Fin N → Bool)
    (Z : Fin N → ℝ) (i : Fin N) : ℝ :=
  max (∑ j, θ i j * paymentEq θ dbar v ω Z j + cash ω Z i - v - paymentEq θ dbar v ω Z i) 0

/-- `Pr(ω) = ∏_j Pr(ω_j)` with `Pr(ω_j = s) = P(Z_j)`, `Pr(ω_j = f) = 1 − P(Z_j)` (independent
projects, p. 7). -/
def stateProb {N : ℕ} (P : ℝ → ℝ) (Z : Fin N → ℝ) (ω : Fin N → Bool) : ℝ :=
  ∏ j, if ω j then P (Z j) else 1 - P (Z j)

/-- Expected profit `E[Π_i(ω; Z)] = ∑_{ω ∈ {s,f}^N} Π_i(ω; Z) · Pr(ω)` (p. 7). -/
noncomputable def expProfit {N : ℕ} (θ : Fin N → Fin N → ℝ) (dbar v : ℝ) (P : ℝ → ℝ)
    (Z : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∑ ω, profit θ dbar v ω Z i * stateProb P Z ω

/-- Bank `i`'s best-response set (4): the maximizers over `y ∈ [Z̲, Z̄]` of
`E[Π_i(ω; y, Z_{−i})]`. Only `Z_{−i}` matters, since coordinate `i` is overwritten. -/
def bestResponse {N : ℕ} (θ : Fin N → Fin N → ℝ) (dbar v : ℝ) (P : ℝ → ℝ) (Zlo Zhi : ℝ)
    (Z : Fin N → ℝ) (i : Fin N) : Set ℝ :=
  {z | z ∈ Set.Icc Zlo Zhi ∧ ∀ y ∈ Set.Icc Zlo Zhi,
    expProfit θ dbar v P (Function.update Z i y) i ≤ expProfit θ dbar v P (Function.update Z i z) i}

/-- A risk-taking equilibrium (Definition 2, p. 8) with `d*` the greatest payment equilibrium:
every bank's choice `Z_i` lies in `[Z̲, Z̄]` and maximizes its expected profit given `Z_{−i}`. -/
def IsEquilibrium {N : ℕ} (θ : Fin N → Fin N → ℝ) (dbar v : ℝ) (P : ℝ → ℝ) (Zlo Zhi : ℝ)
    (Z : Fin N → ℝ) : Prop :=
  ∀ i, Z i ∈ bestResponse θ dbar v P Zlo Zhi Z i

/-- The cross-subsidy (5):
`D_i(Z_{−i}) = ∑_{ω_{−i}} (d̄ − ∑_j θ_ij d*_j(ω^{i=s})) · Pr(ω_{−i})`, written as a sum over the
states `ω` with `ω i = true` and `Pr(ω_{−i}) = ∏_{j ≠ i} Pr(ω_j)`. -/
noncomputable def distortion {N : ℕ} (θ : Fin N → Fin N → ℝ) (dbar v : ℝ) (P : ℝ → ℝ)
    (Z : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω : Fin N → Bool => ω i = true),
    (dbar - ∑ j, θ i j * paymentEq θ dbar v ω Z j) *
      ∏ j ∈ univ.erase i, (if ω j then P (Z j) else 1 - P (Z j))

/-- `Pr(m banks failed) = C(N−1, m) (1 − q)^m q^{N−1−m}` (p. 14), with `q = P(Z_{−i})` the
common success probability of the other `N − 1` banks. -/
def prFail (N m : ℕ) (q : ℝ) : ℝ :=
  ((N - 1).choose m : ℝ) * (1 - q) ^ m * q ^ (N - 1 - m)

/-- The weight `C(N−2−l, N−2−m) / C(N−1, m)` of the ring formula (p. 14; (I.15)). For `m = N − 1`
(all other banks fail) the printed binomial has lower index `−1`; there the weight is `1` at
`l = N − 1` and `0` otherwise. -/
noncomputable def ringWeight (N m l : ℕ) : ℝ :=
  if m + 2 ≤ N then ((N - 2 - l).choose (N - 2 - m) : ℝ) / ((N - 1).choose m : ℝ)
  else if l = N - 1 then 1 else 0

/-- The bank `o` steps upstream of `i` in the ring: index `(i − o) mod N`. -/
def upstream {N : ℕ} (i : Fin N) (o : ℕ) : Fin N :=
  ⟨((i : ℕ) + N - o % N) % N, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- `K_i(ω) = min{o : ω_{i−o} = s}` ((I.14)): the number of consecutive failed banks met going
upstream from `i` (counting `i` itself) before the first successful bank. It is `0` when `i`
succeeds. When no bank succeeds the minimum does not exist and the value is the junk `N`; every
statement using `runLength` assumes some bank succeeds. -/
noncomputable def runLength {N : ℕ} (ω : Fin N → Bool) (i : Fin N) : ℕ := by
  classical
  exact if h : ∃ o, ω (upstream i o) = true then Nat.find h else N

/-- The number of consecutive failed upstream neighbours of bank `i` before the first successful
bank: `K_{i−1}(ω)`, the run length of the upstream neighbour `i − 1`. -/
noncomputable def upRun {N : ℕ} (ω : Fin N → Bool) (i : Fin N) : ℕ :=
  runLength ω (upstream i 1)

end RiskExposure.RingComplete


