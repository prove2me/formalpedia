-- Prove2me | Definitions.Def_MinorityDynamics_Chain
-- name    : MinorityDynamics_Chain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:15:51.398215+00:00
-- url     : https://prove2.me/theorems/3bb336b7-5414-401d-a591-d8e22bdef0db
-- title:
--   Minority chain, auxiliary chain and chain with sources; p, q, a, b, c, f, ℓ, I∗, K, D, H, S
-- statement:
--   Fix odd $n$ and $k$ and write $L=\ln n$ and $P_s(p)=\binom ns p^s(1-p)^{n-s}$. The module defines the objects of §§2–3 and §8.1:
--
--   1. $p(x)=\Pr\big(\mathrm{Bin}(k,x)\in\{1,\dots,\tfrac{k-1}2\}\cup\{k\}\big)$ (2.1) and $q(x)=\Pr\big(\mathrm{Bin}(k,x)\ge\tfrac{k+1}2\big)$ (2.2).
--   2. $a=1-2^{-1/k}$, $b=1-e^{-L/k}$, $c$ with $q(c)=1/n$, the central interval $I_*=[b,c]$ and the inner interval $I_*^{\mathrm{in}}=[\tfrac32b,\tfrac23c]$.
--   3. The map (2.4)
--   $$f(x)=\begin{cases}1-(1-x)^k,&0\le x<a,\\(1-x)^k,&a\le x<b,\\0,&b\le x\le c,\\q(x),&c<x\le 1/2,\end{cases}$$
--   its lower branch $f_\ell(x)=1-(1-x)^k$ and the inverse lower branch $\ell(y)=1-(1-y)^{1/k}$.
--   4. $K=k/L^{21/20}$, $D=L/\ln k$, the state space $\Omega=\{0,\tfrac1n,\dots,\tfrac{n-1}{2n}\}$, $\mathcal H=\Omega\cap([0,K/n]\cup I_*)$ and $\mathcal S=\Omega\setminus\mathcal H$.
--   5. The **minority chain**: given $X_t=x$, $Z\sim\mathrm{Bin}(n,p(x))$ and $X_{t+1}=\min\{Z,n-Z\}/n$.
--   6. The **auxiliary chain**: given $X'_t=x$, $R_{t+1}\sim\mathrm{Bin}(n,f(x))$ and $X'_{t+1}=\min\{R_{t+1},n-R_{t+1}\}/n$; its state is the unfolded count $R_t$.
--   7. The **chain with $\varrho$ sources** on $\Omega_\varrho=\{(x,\sigma)\in\Omega\times\{0,1\}:\varrho\sigma/n\le x\le(n-\varrho(1-\sigma))/n\}$: given $(x,\sigma)$, $Z\sim\varrho\sigma+\mathrm{Bin}(n-\varrho,p(x))$, $X_{t+1}=\min\{Z,n-Z\}/n$, $\sigma_{t+1}=\sigma$ if $Z<n/2$ and $1-\sigma$ if $Z>n/2$.
--   8. The law of $\beta+\mathrm{Bin}(n-\varrho,p)$ (Lemma 8.2).
--
--   These are the chains on which every lemma of the paper is stated; the minority chain is the exact image of the agent-level dynamics (§2.1, §8.1).
--
--   **Formalization Note** States are minority counts $s=nx\in\{0,\dots,n\}$ (`Fin (n+1)`), with $\Omega$ the counts $s$ with $2s<n$. $c$ is the least $x\in[0,1/2]$ with $q(x)\ge1/n$; for $n\ge2$ and odd $k$ it is the solution of $q(c)=1/n$ (a proved sanity check shows $q(c)=1/n$ and $0<a<b<c<1/2$ for $n\ge3$, $k\ge8L$). $f$ tests $x<a$, then $x<b$, then $x\le c$, which is (2.4) on $[0,1/2]$ when $a<b<c$. Orientation $1$ is `true`.
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), §2.1, pp.10–11, (2.1); §2.2, pp.11–12, (2.2)–(2.4); §3, p.13; §4.1, p.14 (P_s(p)); §7.2, p.38 (I∗^in); §8.1, p.41 (Ω_ϱ, the actual chain with sources); Lemma 8.2, p.42

import Mathlib

set_option autoImplicit false

namespace MinorityDynamics

open Classical

/-- The **binomial probability** `P_s(p) = Pr(Bin(n, p) = s) = C(n, s) pˢ (1 − p)^{n−s}`
(Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC
2027 submission), §4.1, p.14 = PDF p.16).

**Formalization Note** For `s > n` the binomial coefficient is `0`, so the value is `0` although
`n − s` is truncated in `ℕ`. -/
noncomputable def binomPMF (n : ℕ) (p : ℝ) (s : ℕ) : ℝ :=
  (n.choose s : ℝ) * p ^ s * (1 - p) ^ (n - s)

/-- The **adoption probability** (2.1) (manuscript, §2.1, p.10 = PDF p.12):
`p(x) = Pr(Bin(k, x) ∈ {1, …, (k−1)/2} ∪ {k})`, the probability that an agent adopts the current
minority opinion when the minority fraction is `x`.

**Formalization Note** `(k − 1)/2` is natural-number division; for odd `k` (the paper's standing
assumption) it is exact. -/
noncomputable def pAdopt (k : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), if (1 ≤ j ∧ j ≤ (k - 1) / 2) ∨ j = k then binomPMF k x j else 0

/-- The **majority-sample probability** (2.2) (manuscript, §2.2, p.11 = PDF p.13):
`q(x) = Pr(Bin(k, x) ≥ (k + 1)/2)`, for `x ∈ [0, 1/2]`.

**Formalization Note** `(k + 1)/2` is natural-number division, exact for odd `k`. -/
noncomputable def qMaj (k : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), if (k + 1) / 2 ≤ j then binomPMF k x j else 0

/-- `L = ln n` (manuscript, §2.2, p.11), natural logarithm. -/
noncomputable def logN (n : ℕ) : ℝ := Real.log n

/-- `a = 1 − 2^{−1/k}` (manuscript, §2.2, p.11), the solution of `1 − (1 − a)^k = (1 − a)^k`. -/
noncomputable def aPt (k : ℕ) : ℝ := 1 - (2 : ℝ) ^ (-(1 : ℝ) / k)

/-- `b = 1 − e^{−L/k}` (manuscript, §2.2, p.11), the solution of `(1 − b)^k = 1/n`. -/
noncomputable def bPt (n k : ℕ) : ℝ := 1 - Real.exp (-(logN n) / k)

/-- `c`, defined by `q(c) = 1/n` (manuscript, §2.2, p.11: "Function q is strictly increasing on
[0, 1/2], with endpoint values 0 and 1/2, so c is well-defined").

**Formalization Note** `c` is the least `x ∈ [0, 1/2]` with `q(x) ≥ 1/n`. Since `q` is continuous
and strictly increasing on `[0, 1/2]` with `q(0) = 0` and `q(1/2) = 1/2` (odd `k`), for `n ≥ 2`
this is the unique solution of `q(c) = 1/n` in `[0, 1/2]`. -/
noncomputable def cPt (n k : ℕ) : ℝ :=
  sInf {x : ℝ | x ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ 1 / (n : ℝ) ≤ qMaj k x}

/-- The **central interval** `I∗ = [b, c]` (manuscript, §2.2, p.11). -/
noncomputable def Istar (n k : ℕ) : Set ℝ := Set.Icc (bPt n k) (cPt n k)

/-- The **inner central interval** `I∗^in = [3b/2, 2c/3]` (manuscript, §7.2, p.38 = PDF p.40). -/
noncomputable def IstarIn (n k : ℕ) : Set ℝ := Set.Icc (3 / 2 * bPt n k) (2 / 3 * cPt n k)

/-- The **lower branch** `f_ℓ(x) = 1 − (1 − x)^k` (manuscript, (2.4), p.12 = PDF p.14). -/
noncomputable def fLow (k : ℕ) (x : ℝ) : ℝ := 1 - (1 - x) ^ k

/-- The **middle branch** `f_m(x) = (1 − x)^k` (manuscript, (2.4), p.12). -/
noncomputable def fMid (k : ℕ) (x : ℝ) : ℝ := (1 - x) ^ k

/-- The **deterministic map** `f : [0, 1/2] → [0, 1/2]` of (2.4) (manuscript, §2.2, p.12 = PDF
p.14):
`f(x) = 1 − (1 − x)^k` for `0 ≤ x < a`, `(1 − x)^k` for `a ≤ x < b`, `0` for `b ≤ x ≤ c`, and
`q(x)` for `c < x ≤ 1/2`.

**Formalization Note** The cases are tested in the order `x < a`, `x < b`, `x ≤ c`, else; on
`[0, 1/2]` with `a < b < c` (which holds for `k ≥ 8L`, p.12) this is exactly (2.4). The map is
only evaluated at minority fractions `x ∈ [0, 1/2]`. -/
noncomputable def fMap (n k : ℕ) (x : ℝ) : ℝ :=
  if x < aPt k then fLow k x
  else if x < bPt n k then fMid k x
  else if x ≤ cPt n k then 0
  else qMaj k x

/-- The **inverse lower branch** `ℓ(y) = 1 − (1 − y)^{1/k}`, `y ∈ [0, 1/2]` (manuscript, §2.2,
p.12). -/
noncomputable def ell (k : ℕ) (y : ℝ) : ℝ := 1 - (1 - y) ^ ((1 : ℝ) / k)

/-- `K = k / L^{21/20}` (manuscript, §3, p.13 = PDF p.15), a real count threshold. -/
noncomputable def KK (n k : ℕ) : ℝ := (k : ℝ) / logN n ^ ((21 : ℝ) / 20)

/-- `D = L / ln k` (manuscript, §3, p.13). -/
noncomputable def DD (n k : ℕ) : ℝ := logN n / Real.log k

/-- The **state space** `Ω = {0, 1/n, …, (n − 1)/(2n)}` of the minority chain (manuscript, §2.1,
p.10), as minority counts: `s ∈ Fin (n + 1)` with `2s < n`, i.e. `s ≤ (n − 1)/2`; the state is the
fraction `x = s/n`. -/
def InOmega (n : ℕ) (s : Fin (n + 1)) : Prop := 2 * (s : ℕ) < n

/-- `H = Ω ∩ ([0, K/n] ∪ I∗)` (manuscript, §3, p.13 = PDF p.15), as a set of counts. -/
noncomputable def Hset (n k : ℕ) : Set (Fin (n + 1)) :=
  {s | InOmega n s ∧ (((s : ℕ) : ℝ) / n ≤ KK n k / n ∨ ((s : ℕ) : ℝ) / n ∈ Istar n k)}

/-- The surviving states `S = Ω \ H` (manuscript, §3, p.13), as a set of counts. -/
noncomputable def Sset (n k : ℕ) : Set (Fin (n + 1)) :=
  {s | InOmega n s ∧ s ∉ Hset n k}

/-- The law of the **folded** count `min{Z, n − Z}` for `Z ∼ Bin(n, p)` (manuscript, §2.1, p.11:
"We call the map z ↦ min{z, 1 − z} folding"): `foldedLaw n p s'` is `Pr(min{Z, n − Z} = s')`. -/
noncomputable def foldedLaw (n : ℕ) (p : ℝ) (s' : ℕ) : ℝ :=
  ∑ z ∈ Finset.range (n + 1), if min z (n - z) = s' then binomPMF n p z else 0

/-- The **minority chain** (the actual chain without sources), manuscript §2.1, p.11 = PDF p.13:
"Given Xt = x, let Z count the agents holding the current minority opinion after the next update.
Then, Z ∼ Bin(n, p(x)), Xt+1 = min{Z, n − Z}/n." As a transition matrix on minority counts
`s = nx`: `actualKernel n k s s' = Pr(min{Z, n − Z} = s')` with `Z ∼ Bin(n, p(s/n))`.

**Formalization Note** States are counts in `Fin (n + 1)`; only those in `Ω` (`2s < n`) are
reached from `Ω`, and every statement starts the chain in `Ω`. -/
noncomputable def actualKernel (n k : ℕ) (s s' : Fin (n + 1)) : ℝ :=
  foldedLaw n (pAdopt k (((s : ℕ) : ℝ) / n)) s'

/-- The minority fraction `min{R, n − R}/n` encoded by an unfolded count `R`. -/
noncomputable def foldFrac (n : ℕ) (R : Fin (n + 1)) : ℝ := (min (R : ℕ) (n - R) : ℝ) / n

/-- The **auxiliary chain** with its unfolded count (manuscript, §2.2, p.12 = PDF p.14): "Given
X′t = x, sample R_{t+1} ∼ Bin(n, f(x)), X′_{t+1} = min{R_{t+1}, n − R_{t+1}}/n." The state is the
unfolded count `R_t`, and `X′_t = min{R_t, n − R_t}/n` (`foldFrac`): `auxKernel n k R R'` is
`Pr(R_{t+1} = R')` given `R_t = R`, namely `P_{R'}(f(X′_t))`.

**Formalization Note** The chain started at `x = s/n ∈ Ω` starts at `R₀ = s`. -/
noncomputable def auxKernel (n k : ℕ) (R R' : Fin (n + 1)) : ℝ :=
  binomPMF n (fMap n k (foldFrac n R)) R'

/-- The law of `X′_{t+1}` (as a count) given `X′_t = s/n` for the auxiliary chain: the folded law
of `Bin(n, f(s/n))` (manuscript, §2.2, p.12). -/
noncomputable def auxFoldedKernel (n k : ℕ) (s s' : Fin (n + 1)) : ℝ :=
  foldedLaw n (fMap n k (((s : ℕ) : ℝ) / n)) s'

/-- The **feasible states with ϱ sources** (manuscript, §8.1, p.41 = PDF p.43):
`Ω_ϱ = {(x, σ) ∈ Ω × {0, 1} : ϱσ/n ≤ x ≤ (n − ϱ(1 − σ))/n}`, as pairs (minority count `s = nx`,
orientation `σ`), with orientation 1 encoded as `true`. -/
def OmegaRho (n ϱ : ℕ) : Set (Fin (n + 1) × Bool) :=
  {p | InOmega n p.1 ∧ (if p.2 then ϱ else 0) ≤ (p.1 : ℕ) ∧
    (p.1 : ℕ) + (if p.2 then 0 else ϱ) ≤ n}

/-- The **actual chain with ϱ sources** (manuscript, §8.1, p.41 = PDF p.43): "Conditional on
(Xt, σt) = (x, σ), let Z count the agents holding the current minority opinion after the update.
… Then Z ∼ ϱσ + Bin(n − ϱ, p(x)), Xt+1 = min{Z, n − Z}/n, σt+1 = σ if Z < n/2, 1 − σ if
Z > n/2." As a transition matrix on pairs (minority count, orientation):
`sourceKernel n k ϱ (s, σ) (s', σ')` is the probability that, with `Z = ϱσ + J`,
`J ∼ Bin(n − ϱ, p(s/n))`, one has `min{Z, n − Z} = s'` and the new orientation is `σ'`.

**Formalization Note** Orientation 1 is `true`; `ϱσ` is `ϱ` if `σ = true` and `0` otherwise. For
odd `n` the case `Z = n/2` does not occur. At consensus (`Z = 0` or `Z = n`) this rule gives
orientation 0 whenever `ϱ ≥ 1`, as stated on p.41. -/
noncomputable def sourceKernel (n k ϱ : ℕ) (st st' : Fin (n + 1) × Bool) : ℝ :=
  ∑ j ∈ Finset.range (n - ϱ + 1),
    binomPMF (n - ϱ) (pAdopt k (((st.1 : ℕ) : ℝ) / n)) j *
      (if min ((if st.2 then ϱ else 0) + j) (n - ((if st.2 then ϱ else 0) + j)) = (st'.1 : ℕ) ∧
          (if 2 * ((if st.2 then ϱ else 0) + j) < n then st.2 else !st.2) = st'.2
        then 1 else 0)

/-- The law of `Z = β + Bin(n − ϱ, p)` (manuscript, Lemma 8.2, p.42 = PDF p.44):
`Pr(Z = r) = P_{r−β}(p)` over `n − ϱ` trials if `r ≥ β`, and `0` otherwise. -/
noncomputable def shiftBinomPMF (n ϱ β : ℕ) (p : ℝ) (r : ℕ) : ℝ :=
  if β ≤ r then binomPMF (n - ϱ) p (r - β) else 0

end MinorityDynamics


