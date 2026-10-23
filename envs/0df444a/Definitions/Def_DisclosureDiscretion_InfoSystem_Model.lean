-- Prove2me | Definitions.Def_DisclosureDiscretion_InfoSystem_Model
-- name    : DisclosureDiscretion_InfoSystem_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:02:43.0416+00:00
-- url     : https://prove2.me/theorems/364e9c85-90da-4091-92e4-51af15035ecc
-- title:
--   §2–§3, pp. 7–25 — CEO/union/market disclosure game: systems N, P, D, union threshold k/t, prices, D-subgame equilibrium, expected prices
-- statement:
--   This file sets up the model of Arya and Ramanan, *Endogenizing Discretion in Disclosures*.
--
--   A firm's cash flow $c$ is uniformly distributed on $[0,\bar c]$. A labor union observes every public signal about $c$; if it bargains, it costs the union $k>0$ and transfers an expected fraction $t\in(0,1)$ of the cash flow to the employees. The firm's owner-CEO chooses an information system $I\in\{N,P,D\}$: under $N$ nothing is learned; under $P$ the system learns $c$ with probability $p\in(0,1)$ and publishes it; under $D$ the CEO privately learns $c$ with probability $p$ and then chooses whether to disclose it truthfully. The public signal is $s\in\{c,\phi\}$, where $\phi$ denotes silence. The **standing assumptions** (pp. 8–9) are
--   $$0<t<1,\qquad k>0,\qquad 0<p<1,\qquad \bar c>\frac{k}{t(1-t)}.$$
--
--   By Lemma 1 the union bargains when $E[c\mid I,s]>k/t$, does not when $E[c\mid I,s]<k/t$, and bargains with any probability $q\in[0,1]$ at equality; by Lemma 2 the stock price is $\wp(I,s)=[q(1-t)+1-q]\,E[c\mid I,s]$. The file defines:
--
--   1. the **disclosure price** $V(c)=c$ if $c\le k/t$ and $V(c)=(1-t)c$ if $c>k/t$;
--   2. the **silence price** $[q(1-t)+1-q]\,x$, where $x=c^\phi=E[c\mid D,\phi]$;
--   3. the informed CEO's **nondisclosure set** at silence price $P$: $\mathrm{ND}=\{c\in[0,\bar c]: V(c)<P\}$ (she discloses iff $\wp(D,c)\ge\wp(D,\phi)$);
--   4. the **value of silence** given a nondisclosure set $S$ (equations (1)–(4)):
--   $$\frac{(1-p)\,\bar c/2+p\int_S c\,dc/\bar c}{1-p+p\,|S|/\bar c};$$
--   5. a **$D$-subgame equilibrium** $(x,q)$: $q\in[0,1]$, $q=1$ if $x>k/t$, $q=0$ if $x<k/t$, and $x$ equals the value of silence of the nondisclosure set at the silence price of $(x,q)$;
--   6. the CEO's **expected prices** $E[\wp(N,s)]$, $E[\wp(P,s)]$ and, at a $D$-subgame profile $(x,q)$, $E[\wp(D,s)]=(1-p)P+p\int_0^{\bar c}\max(V(c),P)\,dc/\bar c$ with $P$ the silence price;
--   7. the paper's closed forms $c_1^\phi$, $k_{1A}$, $k_{1B}$ (Proposition 1), $c^\phi_{2A}$, $k_{2A}$ (Proposition 2), $c^\phi_{2B}$, $k_{2B}$ (Proposition 3) and $q_{2C}$ (Proposition 4), exactly as printed;
--   8. the predicate that the printed $k_{2B}$ is defined ($t\ne1/2$ and $(1-p)[1-2t+(1-p)t^2]\ge0$), and the predicate that discretion is optimal, $E[\wp(D,s)]>E[\wp(N,s)]$ and $E[\wp(D,s)]>E[\wp(P,s)]$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The parameter $t=\lambda t'$ of the paper enters only through $t\in(0,1)$, so $\lambda$ and $t'$ do not appear. The uniform prior is encoded by Lebesgue integrals over subsets of $[0,\bar c]$ divided by $\bar c$. Ties follow the paper: no bargaining after a disclosed $c=k/t$ and under $N$/$P$ silence at $E[c]=k/t$ (Propositions 5–6); disclosure at indifference (p. 16). The union's mixing probability $q$ is part of the $D$-subgame equilibrium.
-- source:
--   Arya & Ramanan, Endogenizing discretion in disclosures, authors' manuscript (SSRN 3935991, June 2022), pp. 7–25 (PDF 9–27), §2–§3, Lemmas 1–2, equations (1)–(4), Propositions 1–7

import Mathlib

namespace DisclosureDiscretion.InfoSystem

/-! Arya and Ramanan, *Endogenizing Discretion in Disclosures*, authors' manuscript
(SSRN 3935991, June 2022), §2 (pp. 7–10), Lemmas 1–2 (p. 11), §3.1 (pp. 12–22),
Propositions 5–7 (pp. 23–25).

Cash flow `c` is uniform on `[0, cbar]`. A union that bargains takes the expected fraction
`t = λ t'` of the cash flow at cost `k`. The CEO installs an information system
`I ∈ {N, P, D}`; under `P` and `D` the system learns `c` with probability `p`. Under `D` the
CEO, when informed, decides whether to disclose `c`. The stock price is
`℘(I, s) = E[payoff | I, s]` given the union's response (Lemmas 1–2). The uniform prior
is written as Lebesgue integrals over subsets of `[0, cbar]` divided by `cbar`. -/

open MeasureTheory

/-- The paper's standing assumptions (§2, pp. 8–9): `t ∈ (0, 1)` (since `t = λ t'` with
`0 < λ ≤ 1`, `0 < t' < 1`), `k > 0`, `p ∈ (0, 1)`, and `cbar > k / [t(1 - t)]`. -/
structure Standing (cbar t p k : ℝ) : Prop where
  t_pos : 0 < t
  t_lt_one : t < 1
  k_pos : 0 < k
  p_pos : 0 < p
  p_lt_one : p < 1
  cbar_large : k / (t * (1 - t)) < cbar

/-- Lemma 2 at a disclosed signal `s = c`: the price is `c` if `c ≤ k / t` (the union does
not bargain, Prop. 6(b) tie convention) and `(1 - t) c` if `c > k / t`. -/
noncomputable def discPrice (t k c : ℝ) : ℝ := if c ≤ k / t then c else (1 - t) * c

/-- Lemma 2 at silence `s = φ`: the price `[q(1 - t) + 1 - q] x` when the market's estimate
of the cash flow is `x = c^φ` and the union bargains with probability `q`. -/
def silencePrice (t x q : ℝ) : ℝ := (q * (1 - t) + 1 - q) * x

/-- Under `I = D`, the informed CEO's nondisclosure set when the silence price is `P`: she
discloses iff `℘(D, c) ≥ ℘(D, φ)` (p. 16), so she withholds exactly the
`c ∈ [0, cbar]` with `discPrice t k c < P`. -/
def ndSet (cbar t k P : ℝ) : Set ℝ := {c | c ∈ Set.Icc 0 cbar ∧ discPrice t k c < P}

/-- Bayes' rule for the value of silence, equations (1)–(4): given the nondisclosure set
`S ⊆ [0, cbar]`, `E[c | D, φ]` is
`([1 - p] cbar / 2 + p ∫_S c dc / cbar) / (1 - p + p |S| / cbar)`. -/
noncomputable def silenceValue (cbar p : ℝ) (S : Set ℝ) : ℝ :=
  ((1 - p) * (cbar / 2) + p * (∫ c in S, c) / cbar) /
    (1 - p + p * (volume S).toReal / cbar)

/-- An equilibrium of the `I = D` subgame, described by the market's estimate `x = c^φ` of
the cash flow under silence and the union's bargaining probability `q` under silence:
`q` is a best response of the union to `x` (Lemma 1), and `x` is Bayes-consistent with the
CEO's best-response nondisclosure set at the silence price (equations (1)–(4)). -/
def IsDEquilibrium (cbar t p k x q : ℝ) : Prop :=
  0 ≤ q ∧ q ≤ 1 ∧ (k / t < x → q = 1) ∧ (x < k / t → q = 0) ∧
    x = silenceValue cbar p (ndSet cbar t k (silencePrice t x q))

/-- `E[℘(N, s)]`: under `N` the signal is always `φ`, `E[c] = cbar / 2`, and the union
bargains iff `cbar / 2 > k / t` (Prop. 5; no bargaining at equality). -/
noncomputable def expPriceN (cbar t k : ℝ) : ℝ :=
  if k / t < cbar / 2 then (1 - t) * (cbar / 2) else cbar / 2

/-- `E[℘(P, s)]`: with probability `1 - p` the signal is `φ` and the price is as under `N`;
with probability `p` the cash flow `c` is published and priced at `discPrice t k c`
(Prop. 6). -/
noncomputable def expPriceP (cbar t p k : ℝ) : ℝ :=
  (1 - p) * expPriceN cbar t k + p * (∫ c in Set.Icc 0 cbar, discPrice t k c) / cbar

/-- `E[℘(D, s)]` at the `D`-subgame profile `(x, q)`: the uninformed CEO (probability
`1 - p`) is silent and gets the silence price; the informed CEO gets the larger of the
disclosure price and the silence price, which is her best response. -/
noncomputable def expPriceD (cbar t p k x q : ℝ) : ℝ :=
  (1 - p) * silencePrice t x q +
    p * (∫ c in Set.Icc 0 cbar, max (discPrice t k c) (silencePrice t x q)) / cbar

/-- `c₁^φ = [√(1 - p) - (1 - p)] cbar / p` (Proposition 1). -/
noncomputable def c1phi (cbar p : ℝ) : ℝ := (Real.sqrt (1 - p) - (1 - p)) * cbar / p

/-- `k_{1A} = t [1 - t] c₁^φ` (Proposition 1). -/
noncomputable def k1A (cbar t p : ℝ) : ℝ := t * (1 - t) * c1phi cbar p

/-- `k_{1B} = t c₁^φ / (1 - t)` (Proposition 1). -/
noncomputable def k1B (cbar t p : ℝ) : ℝ := t * c1phi cbar p / (1 - t)

/-- `c_{2A}^φ` (Proposition 2):
`(√([(1-p)t cbar - kp]² + p[2 - t²][(1-p)(t cbar)² - k²p]) - [(1-p)t cbar - kp]) / (p t [2 - t²])`. -/
noncomputable def c2Aphi (cbar t p k : ℝ) : ℝ :=
  (Real.sqrt (((1 - p) * t * cbar - k * p) ^ 2 +
      p * (2 - t ^ 2) * ((1 - p) * (t * cbar) ^ 2 - k ^ 2 * p)) -
    ((1 - p) * t * cbar - k * p)) / (p * t * (2 - t ^ 2))

/-- `k_{2A} = t cbar [√((1 - p)(1 - p t²)) - (1 - p)] / (p [1 - t²])` (Proposition 2). -/
noncomputable def k2A (cbar t p : ℝ) : ℝ :=
  t * cbar * (Real.sqrt ((1 - p) * (1 - p * t ^ 2)) - (1 - p)) / (p * (1 - t ^ 2))

/-- `c_{2B}^φ` (Proposition 3):
`(1-t)/(p t [2-4t+t²]) · (√([1-t]²[(1-p)t cbar - kp]² + p[2-4t+t²][(1-p)(t cbar)² - k²p])
 - [1-t][(1-p)t cbar - kp])`. -/
noncomputable def c2Bphi (cbar t p k : ℝ) : ℝ :=
  (1 - t) / (p * t * (2 - 4 * t + t ^ 2)) *
    (Real.sqrt ((1 - t) ^ 2 * ((1 - p) * t * cbar - k * p) ^ 2 +
        p * (2 - 4 * t + t ^ 2) * ((1 - p) * (t * cbar) ^ 2 - k ^ 2 * p)) -
      (1 - t) * ((1 - p) * t * cbar - k * p))

/-- `k_{2B} = Min{ t[1-t] cbar [√([1-p][1-2t+(1-p)t²]) - (1-p)(1-t)] / (p[1-2t]), k_{1B} }`
(Proposition 3), exactly as printed. The first term is meaningful only for `t ≠ 1/2` and
`(1 - p)[1 - 2t + (1 - p)t²] ≥ 0`; statements using `k2B` assume this. -/
noncomputable def k2B (cbar t p : ℝ) : ℝ :=
  min (t * (1 - t) * cbar *
      (Real.sqrt ((1 - p) * (1 - 2 * t + (1 - p) * t ^ 2)) - (1 - p) * (1 - t)) /
      (p * (1 - 2 * t)))
    (k1B cbar t p)

/-- `q_{2C} = 1/(2[1-t]+t²) · (1 - (1-t)/(t k) · √(2[1-t]k² + t cbar[2k - t cbar][2(1-t)+t²][1-p]/p))`
(Proposition 4). -/
noncomputable def q2C (cbar t p k : ℝ) : ℝ :=
  1 / (2 * (1 - t) + t ^ 2) *
    (1 - (1 - t) / (t * k) *
      Real.sqrt (2 * (1 - t) * k ^ 2 +
        t * cbar * (2 * k - t * cbar) * (2 * (1 - t) + t ^ 2) * (1 - p) / p))

/-- The guard under which the printed formula for `k_{2B}` is defined: `t ≠ 1/2` and
`(1 - p)[1 - 2t + (1 - p)t²] ≥ 0`. -/
def K2BDefined (t p : ℝ) : Prop :=
  t ≠ 1 / 2 ∧ 0 ≤ (1 - p) * (1 - 2 * t + (1 - p) * t ^ 2)

/-- Discretionary disclosure is optimal at the `D`-subgame equilibrium `(x, q)`: the
expected price under `D` strictly exceeds those under `N` and under `P`. -/
def DOptimal (cbar t p k x q : ℝ) : Prop :=
  expPriceN cbar t k < expPriceD cbar t p k x q ∧ expPriceP cbar t p k < expPriceD cbar t p k x q

end DisclosureDiscretion.InfoSystem


