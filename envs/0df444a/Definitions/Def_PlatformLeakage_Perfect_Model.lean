-- Prove2me | Definitions.Def_PlatformLeakage_Perfect_Model
-- name    : PlatformLeakage_Perfect_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:49.359974+00:00
-- url     : https://prove2.me/theorems/03ded984-f0b1-4182-a280-e3d3685eefd9
-- title:
--   §3, pp. 7–16 — on-demand platform with an off-platform option: queue-joining demand, provider fees and participation, platform payout ratios, and the closed forms g1, g2, K̂, ω*, a, b
-- statement:
--   This file sets up the perfect-information model of He, Savin, Goh and Teo for an on-demand service platform whose providers may also serve customers off the platform.
--
--   **Primitives.** There are two provider types $j\in\{h,l\}$. Type $j$ has a population of $N^j$ providers, customers value its service at $v^j$, and each $j$-type provider has an opportunity cost rate $K^j$. Every provider serves at rate $\mu$; customers pay a waiting cost $c$ per unit time; $c_s^2$ is the squared coefficient of variation of service durations and $\phi:=(1+c_s^2)/2$; $\Lambda$ is the aggregate customer arrival rate; and $R_o\ge 0$ is the extra cost (counterparty risk) a customer bears when transacting off the platform.
--
--   **Standing assumptions.** Every statement of the mission assumes $N^j\ge 1$, $v^j>0$, $K^j\ge 0$, $K^h\ge K^l$, $\mu>0$, $c>0$, $c_s^2\ge 0$, $R_o\ge 0$, and the supply-constrained assumption (1)
--   $$\Lambda > (N^h+N^l)\mu.$$
--
--   **Customers.** With waiting times (2)–(3), $W_p(C,\lambda)=\frac{\lambda}{C(\mu-\lambda)}\phi$ for an on-platform queue of $C$ providers and $W_o(1,\lambda)=\frac{\lambda}{\mu-\lambda}\phi$ for a single off-platform provider, a demand rate $\lambda$ is an equilibrium (5) for an on-platform queue of $C$ $j$-type providers charging $q$ if either $C\ge1$, $v^j>q$, $0\le\lambda<\mu$ and $v^j-q-cW_p(C,\lambda)=0$, or ($C=0$ or $v^j\le q$) and $\lambda=0$; off the platform the condition is $0\le\lambda<\mu$ and $v^j-q-cW_o(1,\lambda)-R_o=0$ if $v^j>q+R_o$, and $\lambda=0$ otherwise. The demand functions are the closed forms (16)–(17),
--   $$\lambda^j_p(C,q)=\mu\frac{C(v^j-q)^+}{c\phi+C(v^j-q)^+},\qquad \lambda^j_o(q)=\mu\frac{(v^j-q-R_o)^+}{c\phi+(v^j-q-R_o)^+}.$$
--
--   **Providers.** The off-platform utility rate is $U^j_o=\sup_{q\ge0}q\lambda^j_o(q)-K^j$ (problem (6) and (7)). With $n$ $j$-type providers on the platform charging a common fee, the on-platform utility rate at payout ratio $\omega$ is $U^j_p(\omega,n)=\omega\sup_{\zeta\ge0}\zeta\lambda^j_p(n,\zeta)-K^j$ ((9)–(10)), and the on-platform fee $Q^j_p(n)$ is a maximizer of $\zeta\lambda^j_p(n,\zeta)$ over $\zeta\ge0$. A pair $(N^j_p,N^j_o)$ of nonnegative integers is a provider participation equilibrium (Definition 1, (12)) at $\omega$ if $N^j_p+N^j_o\le N^j$ and
--   1. if $N^j_p>0$: $U^j_p(\omega,N^j_p)\ge (U^j_o)^+$;
--   2. if $N^j_o>0$: $U^j_o\ge (U^j_p(\omega,N^j_p))^+$ and $U^j_p(\omega,N^j_p+1)<U^j_o$;
--   3. if $N^j_p+N^j_o<N^j$: $U^j_p(\omega,N^j_p+1)<0$ and $U^j_o<0$.
--
--   The *selected* equilibrium (p. 16) is one whose on-platform head count is largest among all equilibria at $\omega$, and $N^j_p(\omega)$ denotes that head count.
--
--   **Platform.** The profit rate (14) is
--   $$\Pi(\omega^h,\omega^l)=\sum_{j=h,l}N^j_p(\omega^j)\big((1-\omega^j)Q^j_p(N^j_p(\omega^j))-R_o\big)\lambda^j_p\big(N^j_p(\omega^j),Q^j_p(N^j_p(\omega^j))\big),$$
--   and a payout pair is optimal if it maximizes $\Pi$ over $[0,1]^2$ (15).
--
--   **Closed forms.** $g_1(n,v)=\frac{nv+c\phi-c\phi\sqrt{1+nv/(c\phi)}}{n}$ and $g_2(n,v)=\frac{c\mu\phi}{n}\big(\sqrt{1+nv/(c\phi)}-1\big)^2$ (18); $\widehat K^j=\max\{K^j,g_2(1,(v^j-R_o)^+)\}$ (21); $\omega^{j*}$ of (23); and the end-points of the leakage interval of Proposition 3,
--   $$a^j=v^j+c\phi\Big(1-\Big(\big(1-\sqrt{\tfrac{N^j-1}{N^j}}\big)\sqrt{1+\tfrac{N^jv^j}{c\phi}}+\sqrt{\tfrac{N^j-1}{N^j}}\Big)^2\Big),\qquad b^j=v^j+c\phi\Big(1-\Big(1+\sqrt{\tfrac{K^j}{c\phi\mu}}\Big)^2\Big).$$
--
--   These objects are the vocabulary of Lemmas 1–2, Propositions 1–3 and the two steps (A9) of the proof of Proposition 3.
--
--   **Formalization Note** The demand rates are defined by the closed forms (16)–(17); the paper defines them as the unique solutions of (5), and Lemma 1 (a milestone) states exactly that equivalence. The utilities are defined through suprema of the revenue, not through $g_2$, so Lemma 2 has content. The fee $Q^j_p(n)$ is a revenue maximizer chosen by `Classical.epsilon` (for $\omega>0$ this is the argmax of (9); at $\omega=0$ (9) does not pin the fee). The printed first line of (12) also requires $U^j_o<U^j_p(\omega,N^j_p-1)$; that clause is dropped, because with it all-on equilibria fail at the paper's own optimal payout ratio, contradicting Proposition 1, whose proof uses only $U^j_p(\omega,N^j)\ge(U^j_o)^+$. Equilibria are stated per type, since (12) never couples the types. The off-platform clause "$n^j_o\ge1$" of (5) is dropped: the off-platform demand function is that of an existing off-platform provider. The positive part in $\widehat K^j$ keeps $g_2$ on its domain $\mathbb R^2_+$. The standing positivity assumptions other than $K^h\ge K^l$, $R_o\ge0$ and (1) are implicit in the paper (rates, costs, a positive population).
-- source:
--   He, Savin, Goh & Teo, Off-Platform Threats in On-Demand Services, SSRN working paper 3550646 (PDF of 2021-03-25), pp. 10–18 (PDF 10–18), §3, (1)–(15), Definitions 1–2, (16)–(18), (21), (23), Proposition 3 (a^j, b^j)

import Mathlib

namespace PlatformLeakage.Perfect

/-- The two provider types: high quality `h` and low quality `l`. -/
inductive PType
  | h
  | l
  deriving DecidableEq

/-- The primitives of the perfect-information model (§3): the population `N j` of `j`-type providers,
their service valuation `v j` (the paper's `v^j`) and opportunity cost rate `K j` (`K^j`), the service
rate `mu` (µ), the customers' waiting cost `c`, the squared coefficient of variation `cs2` (`c_s²`) of
service durations, the aggregate demand rate `Lam` (Λ) and the counterparty risk `Ro` (`R_o`). -/
structure Params where
  N : PType → ℕ
  v : PType → ℝ
  K : PType → ℝ
  mu : ℝ
  c : ℝ
  cs2 : ℝ
  Lam : ℝ
  Ro : ℝ

/-- φ := (1 + c_s²)/2 (p. 11). -/
noncomputable def Params.phi (P : Params) : ℝ := (1 + P.cs2) / 2

/-- The standing assumptions of §3: a positive population of each type (`1 ≤ N j`), positive
valuations, nonnegative opportunity costs with `K^h ≥ K^l` (p. 12), positive service rate and waiting
cost, nonnegative SCV, nonnegative counterparty risk (p. 11), and the supply-constrained assumption
(1) `Λ > Nµ` with `N = N^h + N^l` (p. 10). -/
def Params.Std (P : Params) : Prop :=
  (∀ j, 1 ≤ P.N j ∧ 0 < P.v j ∧ 0 ≤ P.K j) ∧ P.K .l ≤ P.K .h ∧
  0 < P.mu ∧ 0 < P.c ∧ 0 ≤ P.cs2 ∧ 0 ≤ P.Ro ∧
  ((P.N .h + P.N .l : ℕ) : ℝ) * P.mu < P.Lam

/-- (2): expected waiting time in an on-platform queue of `C` providers with demand rate `lam`. -/
noncomputable def Wp (P : Params) (C : ℕ) (lam : ℝ) : ℝ := lam / ((C : ℝ) * (P.mu - lam)) * P.phi

/-- (3): expected waiting time at a single off-platform provider with demand rate `lam`. -/
noncomputable def Wo (P : Params) (lam : ℝ) : ℝ := lam / (P.mu - lam) * P.phi

/-- (5), on-platform line: `lam` is an equilibrium demand rate for a queue of `C` `j`-type providers
charging the fee `q` (with stability `lam < µ`, p. 11). -/
def IsEqDemandP (P : Params) (j : PType) (C : ℕ) (q lam : ℝ) : Prop :=
  if 1 ≤ C ∧ q < P.v j then 0 ≤ lam ∧ lam < P.mu ∧ P.v j - q - P.c * Wp P C lam = 0
  else lam = 0

/-- (5), off-platform line: `lam` is an equilibrium demand rate for an off-platform `j`-type provider
charging the fee `q` (with stability `lam < µ`, p. 11). -/
def IsEqDemandO (P : Params) (j : PType) (q lam : ℝ) : Prop :=
  if q + P.Ro < P.v j then 0 ≤ lam ∧ lam < P.mu ∧ P.v j - q - P.c * Wo P lam - P.Ro = 0
  else lam = 0

/-- The on-platform demand rate `λ^j_p(C, q)` in the closed form (16); Lemma 1 states that it is the
unique solution of (5). -/
noncomputable def demandP (P : Params) (j : PType) (C : ℕ) (q : ℝ) : ℝ :=
  P.mu * ((C : ℝ) * max (P.v j - q) 0 / (P.c * P.phi + (C : ℝ) * max (P.v j - q) 0))

/-- The off-platform demand rate `λ^j_o(q)` in the closed form (17); Lemma 1 states that it is the
unique solution of (5). -/
noncomputable def demandO (P : Params) (j : PType) (q : ℝ) : ℝ :=
  P.mu * (max (P.v j - q - P.Ro) 0 / (P.c * P.phi + max (P.v j - q - P.Ro) 0))

/-- The optimal value of the off-platform fee problem (6) before subtracting `K^j`:
the supremum over fees `q ≥ 0` of the revenue rate `q λ^j_o(q)`. -/
noncomputable def offValue (P : Params) (j : PType) : ℝ :=
  sSup ((fun q : ℝ => q * demandO P j q) '' Set.Ici 0)

/-- The optimal value of the on-platform fee problem (9) before scaling by `ω` and subtracting `K^j`:
the supremum over fees `ζ ≥ 0` of the revenue rate `ζ λ^j_p(n, ζ)` with `n` providers sharing the fee. -/
noncomputable def onValue (P : Params) (j : PType) (n : ℕ) : ℝ :=
  sSup ((fun ζ : ℝ => ζ * demandP P j n ζ) '' Set.Ici 0)

/-- (7): the off-platform utility rate `U^j_o`. -/
noncomputable def Uo (P : Params) (j : PType) : ℝ := offValue P j - P.K j

/-- (10): the on-platform utility rate `U^j_p(ω, n)` when `n` `j`-type providers are on the platform. -/
noncomputable def Up (P : Params) (j : PType) (ω : ℝ) (n : ℕ) : ℝ := ω * onValue P j n - P.K j

/-- The symmetric on-platform fee `Q^j_p(n)`: a fee `ζ ≥ 0` maximizing the revenue rate
`ζ λ^j_p(n, ζ)` over `ζ ≥ 0` (for `ω > 0` exactly the argmax of (9)). Chosen by `Classical.epsilon`;
Lemma 2 shows the maximizer exists and is unique for `n ≥ 1`. -/
noncomputable def feeP (P : Params) (j : PType) (n : ℕ) : ℝ :=
  Classical.epsilon (fun ζ : ℝ =>
    0 ≤ ζ ∧ ∀ ζ' : ℝ, 0 ≤ ζ' → ζ' * demandP P j n ζ' ≤ ζ * demandP P j n ζ)

/-- Definition 1 (12), for one type `j` at payout ratio `ω`: `Np` providers on the platform and `No`
off it form a provider participation equilibrium. The printed clause `U^j_o < U^j_p(ω, Np − 1)` of the
first line of (12) is not included (see the Formalization Note). -/
def IsPartEq (P : Params) (j : PType) (ω : ℝ) (Np No : ℕ) : Prop :=
  Np + No ≤ P.N j ∧
  (0 < Np → max (Uo P j) 0 ≤ Up P j ω Np) ∧
  (0 < No → max (Up P j ω Np) 0 ≤ Uo P j ∧ Up P j ω (Np + 1) < Uo P j) ∧
  (Np + No < P.N j → Up P j ω (Np + 1) < 0 ∧ Uo P j < 0)

/-- The selected equilibrium (p. 16): a participation equilibrium with the largest number of
on-platform providers among all participation equilibria at `ω`. -/
def IsSelectedEq (P : Params) (j : PType) (ω : ℝ) (Np No : ℕ) : Prop :=
  IsPartEq P j ω Np No ∧ ∀ Np' No' : ℕ, IsPartEq P j ω Np' No' → Np' ≤ Np

open Classical in
/-- `N^j_p(ω)`: the largest on-platform head count `n ≤ N^j` that is part of a participation
equilibrium at `ω` (the selection of p. 16); `0` if there is none. -/
noncomputable def selNp (P : Params) (j : PType) (ω : ℝ) : ℕ :=
  Nat.findGreatest (fun n => ∃ no : ℕ, IsPartEq P j ω n no) (P.N j)

/-- The `j`-type summand of the platform's profit rate (14) at payout ratio `ω`, with the selected
on-platform head count `N^j_p(ω)` and fee `Q^j_p(N^j_p(ω))`. -/
noncomputable def profitTerm (P : Params) (j : PType) (ω : ℝ) : ℝ :=
  (selNp P j ω : ℝ) * ((1 - ω) * feeP P j (selNp P j ω) - P.Ro) *
    demandP P j (selNp P j ω) (feeP P j (selNp P j ω))

/-- (14): the platform's expected profit rate `Π(ω^h, ω^l)`. -/
noncomputable def profit (P : Params) (ω : PType → ℝ) : ℝ :=
  profitTerm P .h (ω .h) + profitTerm P .l (ω .l)

/-- (15): `ω` is an optimal payout pair, i.e. it lies in `[0,1]²` and maximizes `Π` over `[0,1]²`. -/
def IsOptimalPayout (P : Params) (ω : PType → ℝ) : Prop :=
  (∀ j, ω j ∈ Set.Icc (0 : ℝ) 1) ∧
  ∀ ω' : PType → ℝ, (∀ j, ω' j ∈ Set.Icc (0 : ℝ) 1) → profit P ω' ≤ profit P ω

/-- (18): `g1(n, v) = (nv + cφ − cφ√(1 + nv/(cφ)))/n`. -/
noncomputable def g1 (P : Params) (n v : ℝ) : ℝ :=
  (n * v + P.c * P.phi - P.c * P.phi * Real.sqrt (1 + n * v / (P.c * P.phi))) / n

/-- (18): `g2(n, v) = (cµφ/n)(√(1 + nv/(cφ)) − 1)²`. -/
noncomputable def g2 (P : Params) (n v : ℝ) : ℝ :=
  P.c * P.mu * P.phi / n * (Real.sqrt (1 + n * v / (P.c * P.phi)) - 1) ^ 2

/-- (21): `K̂^j = max{K^j, g2(1, (v^j − R_o)⁺)}`. -/
noncomputable def Khat (P : Params) (j : PType) : ℝ :=
  max (P.K j) (g2 P 1 (max (P.v j - P.Ro) 0))

/-- (23): the payout ratio `ω^{j*}` of Proposition 2. -/
noncomputable def omegaStar (P : Params) (j : PType) : ℝ :=
  if Khat P j ≤ P.c * P.phi * P.mu / (P.N j : ℝ) *
        (Real.sqrt (1 + (P.N j : ℝ) * P.v j / (P.c * P.phi)) - 1) ^ 2 -
      P.mu * P.Ro * (1 - Real.sqrt (P.c * P.phi / (P.c * P.phi + (P.N j : ℝ) * P.v j)))
  then Khat P j / g2 P (P.N j) (P.v j)
  else 0

/-- Proposition 3: the lower end-point `a^j` of the leakage interval. -/
noncomputable def leakLo (P : Params) (j : PType) : ℝ :=
  P.v j + P.c * P.phi *
    (1 - ((1 - Real.sqrt (((P.N j : ℝ) - 1) / (P.N j : ℝ))) *
            Real.sqrt (1 + (P.N j : ℝ) * P.v j / (P.c * P.phi)) +
          Real.sqrt (((P.N j : ℝ) - 1) / (P.N j : ℝ))) ^ 2)

/-- Proposition 3: the upper end-point `b^j` of the leakage interval. -/
noncomputable def leakHi (P : Params) (j : PType) : ℝ :=
  P.v j + P.c * P.phi * (1 - (1 + Real.sqrt (P.K j / (P.c * P.phi * P.mu))) ^ 2)

end PlatformLeakage.Perfect


