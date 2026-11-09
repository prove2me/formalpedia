-- Prove2me | Definitions.Def_HypergraphUnreliability_FPRAS_RationalApprox
-- name    : HypergraphUnreliability_FPRAS_RationalApprox
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:51.653369+00:00
-- url     : https://prove2.me/theorems/5c695f98-2b2c-4181-892c-2d1162cb5507
-- title:
--   Exact rational approximations of logarithm and exponential, and the parameter searches
-- statement:
--   These are the rational operations of the algorithm.
--
--   1. **Logarithm** (proof of Lemma 7.1). For integers $0<A<B$ and $\eta>0$, take $j$ with $2^j\le B/A<2^{j+1}$, put $y=B/(2^jA)$, and with $z=(x-1)/(x+1)$ let
--   $$L_J(x)=2\sum_{i<J}\frac{z^{2i+1}}{2i+1}.$$
--   With the least $J\ge1$ satisfying $3(j+1)9^{-J}\le\eta$, the value is $jL_J(2)+L_J(y)$.
--   2. **Exponential** (proof of Lemma 9.3). $q_0=1$ if $\Lambda=0$. Otherwise $k=\max\{1,\lceil\Lambda\rceil\}$, $x=\Lambda/k$, the least $t\ge1$ with $1/(t+1)!\le\varepsilon/(1024k)$ is taken, and $q_0=\bigl(\sum_{j\le t}(-x)^j/j!\bigr)^k$.
--   3. **Parameter searches.** The least positive odd $r$ with $2^{-r}\le\delta$, and the least $q\ge1$ with $2^q\ge v$.
--
--   **Formalization Note** The searches are written with `sInf` on $\mathbb N$. Each set is nonempty for the parameters of the algorithm ($\eta,\varepsilon,\delta>0$), so `sInf` is the minimum and the junk value $0$ is not met.
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Proof of Lemma 7.1, p. 8; proof of Lemma 9.3, p. 15; (7.5), p. 10; §8, p. 11

import Mathlib

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

/-- The partial sum `L_J(x) = 2 ∑_{i<J} z^{2i+1} / (2i+1)`, `z = (x-1)/(x+1)` (proof of Lemma 7.1,
p. 8). -/
def logSeries (J : ℕ) (x : ℚ) : ℚ :=
  2 * ∑ i ∈ Finset.range J, ((x - 1) / (x + 1)) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℚ)

/-- The lower approximation `T′ = j L_J(2) + L_J(y)` to `log(B/A)` from the proof of Lemma 7.1, p. 8:
`2^j ≤ B/A < 2^{j+1}`, `y = B/(2^j A)`, and `J ≥ 1` is the least integer with
`3 (j+1) 9^{-J} ≤ η`. (`η > 0` makes that set nonempty, so `sInf` is its minimum.) -/
def logLower (A B : ℕ) (η : ℚ) : ℚ :=
  let j : ℕ := Nat.log 2 (B / A)
  let y : ℚ := (B : ℚ) / (2 ^ j * A)
  let J : ℕ := sInf {J : ℕ | 1 ≤ J ∧ 3 * ((j : ℚ) + 1) / 9 ^ J ≤ η}
  (j : ℚ) * logSeries J 2 + logSeries J y

/-- The rational approximation `q₀` to `e^{-Λ}` from the proof of Lemma 9.3, p. 15: `q₀ = 1` when
`Λ = 0`; otherwise `k = max{1, ⌈Λ⌉}`, `x = Λ/k`, `t ≥ 1` is the least integer with
`1/(t+1)! ≤ ε/(1024 k)`, and `q₀ = (∑_{j≤t} (-x)^j/j!)^k`. -/
def expApprox (Λ ε : ℚ) : ℚ :=
  if Λ = 0 then 1
  else
    let k : ℕ := max 1 ⌈Λ⌉₊
    let x : ℚ := Λ / k
    let t : ℕ := sInf {t : ℕ | 1 ≤ t ∧ (1 : ℚ) / ((t + 1).factorial : ℕ) ≤ ε / (1024 * k)}
    (∑ j ∈ Finset.range (t + 1), (-x) ^ j / ((j.factorial : ℕ) : ℚ)) ^ k

/-- The least positive odd integer `r` with `2^{-r} ≤ δ` (§8, p. 11). -/
def oddBatchCount (δ : ℚ) : ℕ :=
  sInf {r : ℕ | Odd r ∧ (1 / 2 : ℚ) ^ r ≤ δ}

/-- The least integer `q ≥ 1` with `2^q ≥ v` ((7.5), p. 10, and (9.9), p. 14). -/
def bitWidth (v : ℚ) : ℕ :=
  sInf {q : ℕ | 1 ≤ q ∧ v ≤ 2 ^ q}

end HypergraphUnreliability.FPRAS


