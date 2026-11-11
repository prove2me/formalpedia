-- Prove2me | Definitions.Def_ConcurrentStochasticApprox_Approx_PowerSeries
-- name    : ConcurrentStochasticApprox_Approx_PowerSeries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:43:56.017844+00:00
-- url     : https://prove2.me/theorems/5cc7233a-9226-469c-82d4-76e9bb210852
-- title:
--   §5.1 — power-series numbers $F(\ell,B)$, $D(\ell,B)$, relative distance, patience and truncation
-- statement:
--   A **power-series number** is a finite list of signed powers of two $\pm2^{-a_1}\pm\dots\pm2^{-a_k}$ with exponents $a_i\in\mathbb N_0$; the list represents the rational number given by its sum. Repeated exponents and cancellations are allowed. The set
--   $$F(\ell,B)=\Big\{\sum_{i=1}^k\pm2^{-a_i}\ \Big|\ k\le\ell,\ a_i\in\mathbb N_0,\ a_i<2^B\Big\}$$
--   consists of the numbers with a representation of at most $\ell$ terms whose exponents are written with $B$ bits, and $F_+(\ell,B)=F(\ell,B)\cap[0,\infty)$. For distributions on $[t]=\{1,\dots,t\}$, $D(\ell,B)$ is the set of $\mu\in\Delta([t])$ with $\mu(i)\in F_+(\ell,B)$ for all $i$.
--
--   The **relative distance** of $x,x'>0$ is $\mathrm{rel}(x,x')=\max(x/x',x'/x)-1$; moreover $\mathrm{rel}(0,0)=0$ and $\mathrm{rel}(x,0)=\mathrm{rel}(0,x)=\infty$ for $x>0$. For distributions, $\mathrm{rel}(\mu,\mu')=\max_i\mathrm{rel}(\mu(i),\mu'(i))$. The **support** of $\mu$ is $\{i\mid\mu(i)>0\}$, its **patience** is $\mathrm{Patience}(\mu)=\max\{1/\mu(i)\mid i\in\mathrm{supp}(\mu)\}$, and the patience of a stationary strategy is the maximum over states.
--
--   **Truncation.** For $x\in(0,1]$, write its binary expansion (the finite one when it exists) and let $\mathrm{Trunc}_\ell(x)$ keep its first $\ell$ digits starting from the first nonzero digit.
--
--   The file also fixes the binary encoding of a power-series list: every term is written as its sign bit followed by its exponent in binary.
--
--   **Formalization Note** A representation is a `List (Bool × ℕ)` (`true` = minus sign). Relative distance takes values in `ℝ≥0∞`. The $i$-th binary digit of $x$ is $\lfloor 2^i x\rfloor \bmod 2$, for $i\ge0$ ($i=0$ is the units digit). For a dyadic rational this is the terminating expansion, so $\mathrm{Trunc}_\ell(1)=1$. These formulas are only used on the source's domains ($x\in(0,1]$, nonnegative probabilities).
-- source:
--   Ali Asadi, Krishnendu Chatterjee, The Computational Complexity of Concurrent Stochastic Games: Exact Value and Approximation, STOC 2027 submission #285 (October 2026), SHA-256 5cff187cf6b230b3bdfe540f2832f824d1ddb6acb43239fbf469d37c43b0d461, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/285.pdf, §3.1 patience (printed p. 6, PDF p. 8), §5.1 (printed pp. 11–13, PDF pp. 13–15): definition of F(ℓ,B), F₊, rel, D(ℓ,B), Lemma 5.3 statement of Trunc

import Mathlib
import Definitions.Def_ConcurrentStochasticApprox_Approx_Game
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding

/-!
# Power-series numbers, relative distance, patience and truncation

Asadi–Chatterjee, STOC 2027 submission #285, §3.1 (patience, printed p. 6) and §5.1
(printed pp. 11–14).

A power-series number is a finite list of signed terms `(-1)^b 2^{-a}` with `a ∈ ℕ₀`, stored as
`(b, a) : Bool × ℕ` (`b = true` is a minus sign). The list represents the rational sum of its
terms; repeated exponents and cancellations are allowed. `F(ℓ, B)` is the set of values of lists
with at most `ℓ` terms whose exponents satisfy `a < 2^B`.
-/

open Finset

noncomputable section

namespace ConcurrentStochasticApprox.Approx

/-- A power-series representation: a list of signed terms `(-1)^b 2^{-a}`. -/
abbrev PSNum := List (Bool × ℕ)

/-- The real number represented by a power-series list. -/
def psVal (x : PSNum) : ℝ := (x.map fun p => (if p.1 then (-1 : ℝ) else 1) * (1 / 2 : ℝ) ^ p.2).sum

/-- The same number, computed exactly in `ℚ`. -/
def psValQ (x : PSNum) : ℚ := (x.map fun p => (if p.1 then (-1 : ℚ) else 1) * (1 / 2 : ℚ) ^ p.2).sum

/-- The list has at most `ℓ` terms and every exponent is `< 2^B` (written with `B` bits). -/
def InF (ℓ B : ℕ) (x : PSNum) : Prop := x.length ≤ ℓ ∧ ∀ p ∈ x, p.2 < 2 ^ B

/-- `F(ℓ, B) = {∑_{i=1}^k ±2^{-a_i} | k ≤ ℓ, a_i ∈ ℕ₀, a_i < 2^B}` (printed p. 11). -/
def F (ℓ B : ℕ) : Set ℝ := {v | ∃ x : PSNum, InF ℓ B x ∧ psVal x = v}

/-- `F₊(ℓ, B) = F(ℓ, B) ∩ [0, ∞)`. -/
def Fplus (ℓ B : ℕ) : Set ℝ := F ℓ B ∩ Set.Ici 0

/-- `D(ℓ, B)`: probability distributions on `Fin t` all of whose probabilities lie in
`F₊(ℓ, B)` (printed p. 13). -/
def Dset (t ℓ B : ℕ) : Set (Fin t → ℝ) := {μ | IsDist μ ∧ ∀ i, μ i ∈ Fplus ℓ B}

/-- Relative distance (printed p. 13): `rel(x, x') = max(x/x', x'/x) - 1` for positive `x, x'`,
`rel(0, 0) = 0`, and `rel(x, 0) = rel(0, x) = ∞` for `x > 0`. Values in `ℝ≥0∞`. -/
def rel (x x' : ℝ) : ENNReal :=
  if x = 0 ∧ x' = 0 then 0
  else if x = 0 ∨ x' = 0 then ⊤
  else ENNReal.ofReal (max (x / x') (x' / x) - 1)

/-- Relative distance of distributions: the maximum over coordinates. -/
def relDist {t : ℕ} (μ μ' : Fin t → ℝ) : ENNReal := ⨆ i, rel (μ i) (μ' i)

/-- The support `supp(μ) = {i | μ(i) > 0}`. -/
def supp {t : ℕ} (μ : Fin t → ℝ) : Set (Fin t) := {i | 0 < μ i}

/-- `Patience(μ) = max {1/μ(x) | x ∈ supp(μ)}` (printed p. 6). -/
def patience {t : ℕ} (μ : Fin t → ℝ) : ℝ := sSup ((fun i => 1 / μ i) '' supp μ)

/-- The patience of a stationary strategy: the maximum over states. -/
def patienceStat {n t : ℕ} (π : Fin n → Dist t) : ℝ := sSup (Set.range fun s => patience (π s).1)

/-- The `i`-th binary digit of `x` (weight `2^{-i}`; digit `0` is the units digit). For dyadic `x`
this is the digit of the finite expansion. -/
def binDigit (x : ℝ) (i : ℕ) : ℕ := (⌊(2 : ℝ) ^ i * x⌋).toNat % 2

/-- The index of the first nonzero binary digit of `x > 0`. -/
def firstOne (x : ℝ) : ℕ := sInf {i | binDigit x i = 1}

/-- `Trunc_ℓ(x)`: keep the first `ℓ` binary digits of `x`, starting from the first nonzero digit,
using the finite binary expansion when it exists (Lemma 5.3, printed p. 13). -/
def trunc (ℓ : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.Ico (firstOne x) (firstOne x + ℓ), (binDigit x i : ℝ) * (1 / 2 : ℝ) ^ i

open NetworkEquilibriumCLS.LinearNash in
/-- Binary encoding of a power-series list: each term is its sign bit followed by the binary
(self-delimiting) exponent. -/
def encPS (x : PSNum) : List Bool := encList (fun p => p.1 :: encNat p.2) x

end ConcurrentStochasticApprox.Approx


