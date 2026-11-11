-- Prove2me | Definitions.Def_IIDMultiItem_TwoPoint_Counts
-- name    : IIDMultiItem_TwoPoint_Counts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:56:36.614983+00:00
-- url     : https://prove2.me/theorems/9bbfb079-0ea3-40f3-aba7-6a47ee59d39c
-- title:
--   Two-point values: types as sets, all-low items, exclusive counts, ϕ_{c,r} (3.1), reserves (3.2), the value (3.6) and ϖ_{c,r}
-- statement:
--   Throughout Section 3, $F=p\,\delta_a+q\,\delta_b$ with $0<a<b$, $0<p<1$, $q=1-p$ and $\Delta=b-a$. A type is identified with the set $S\subseteq[m]$ of items valued high: its values are $t_j(S)=a+\Delta\,\mathbf 1\{j\in S\}$ and its probability is $f(S)=p^{m-|S|}q^{|S|}$. A profile is $S=(S_1,\dots,S_n)$.
--
--   At a profile $S$ the **all-low items** are $L=[m]\setminus\bigcup_i S_i$, $c=|L|$; $E_i=S_i\setminus\bigcup_{\ell\ne i}S_\ell$ is the set of items only buyer $i$ reports high, $e_i=|E_i|$ is her **exclusive count**, and $e^*=\max_i e_i$. For $c\ge1$, $r\ge0$,
--   $$\phi_{c,r}=a-\Delta\,\frac{\Pr[R>r]}{c\,\Pr[R=r]},\qquad R\sim\mathrm{Bin}(c+r,q),\tag{3.1}$$
--   and $\phi_{0,r}=0$. The **reserves** are $\theta_0=0$ and, for $d\ge1$,
--   $$\theta_d=\min\big(\{k\in\{0,\dots,d-1\}:\phi_{d-k,k}>0\}\cup\{d\}\big).\tag{3.2}$$
--   The value
--   $$mb(1-p^n)+\mathbb E_S\big[c\,[\phi_{c,e^*}]_+\big],\qquad [z]_+=\max\{z,0\},\tag{3.6}$$
--   takes the expectation over $S_1,\dots,S_n$ independent with mass function $f$. For §B.4, $\varpi_{c,r}=\Pr[|L|=c,\ e^*=r]$, and the truncated exponential polynomial $\sum_{k=0}^{K-1}(\pi w)^k/k!$ gives $E_r(w)=\sum_{k=0}^{r}(\pi_1w)^k/k!$ with $K=r+1$ and $E_{-1}=0$ with $K=0$.
--
--   **Formalization Note.** Types are `Finset (Fin m)`; `setVal a b S j` $=t_j(S)$, `setPmf p m S` $=f(S)$, `twoPoint a b p m` is the two-point type space. `allLow`, `numLow`, `excl`, `exclCount`, `maxExcl` are $L$, $c$, $E_i$, $e_i$, $e^*$ ($e^*=0$ when $n=0$). `binPmf N q k` $=\binom Nk q^k(1-q)^{N-k}$, `binGt`, `binGe` are $\Pr[R>r]$, $\Pr[R\ge r]$; `phi a b p c r` is (3.1) with $q=1-p$; `reserveStar a b p d : ℤ` is (3.2) (at $d=0$ the formula gives $0=\theta_0$). `revFormula a b p n m` is (3.6), `lowMaxProb p n m c r` is $\varpi_{c,r}$, `expTrunc π K` the truncated exponential polynomial.
-- source:
--   Liu, Liu, Wang, Optimal Multi-Item Auctions with I.I.D. Values, arXiv:2610.11051 (held version, PDF of 2026-11-03, sha256 983080a4…), p. 13 (PDF 15), §3 and §3.1, (3.1)–(3.2); p. 14 (PDF 16), (3.6); pp. 38–39 (PDF 40–41), §B.4

import Mathlib
import Definitions.Def_IIDMultiItem_TwoPoint_Model

open scoped BigOperators

/-!
# Two-point values: types as sets, all-low items, exclusive counts, `ϕ_{c,r}`, reserves, (3.6)

Liu, Liu, Wang, *Optimal Multi-Item Auctions with I.I.D. Values*, arXiv:2610.11051 (held version,
PDF of 2026-11-03, sha256 983080a4…), §3 opening, §3.1 (3.1)–(3.2), p. 13; Theorem 3.3 (3.6),
p. 14; §B.4, pp. 38–39.

`F = p δ_a + q δ_b` with `0 < a < b`, `0 < p < 1`, `q = 1 − p`, `∆ = b − a`. A type is the set
`S ⊆ [m]` of items valued high (`Finset (Fin m)`): `t_j(S) = a + ∆ 1{j ∈ S}` and
`f(S) = p^{m−|S|} q^{|S|}`. A profile is `S : Fin n → Finset (Fin m)`.
-/

namespace IIDMultiItem.TwoPoint

/-- `f(S) = p^{m−|S|} q^{|S|}` with `q = 1 − p`: the probability that a buyer values exactly the
items of `S` high. -/
def setPmf (p : ℝ) (m : ℕ) (S : Finset (Fin m)) : ℝ :=
  p ^ (m - S.card) * (1 - p) ^ S.card

/-- `t_j(S) = a + ∆ 1{j ∈ S}`, `∆ = b − a`: the value for item `j` of the type `S`. -/
def setVal (a b : ℝ) {m : ℕ} (S : Finset (Fin m)) (j : Fin m) : ℝ :=
  a + (b - a) * (if j ∈ S then 1 else 0)

/-- The two-point type space: types are subsets `S ⊆ [m]`, `t_j(S) = a + (b − a) 1{j ∈ S}`,
`f(S) = p^{m−|S|} (1 − p)^{|S|}`. -/
def twoPoint (a b p : ℝ) (m : ℕ) : TypeSpace (Finset (Fin m)) m where
  val S j := setVal a b S j
  pmf S := setPmf p m S

variable {n m : ℕ}

/-- The all-low items `L = [m] \ ⋃_i S_i`. -/
def allLow (S : Fin n → Finset (Fin m)) : Finset (Fin m) :=
  Finset.univ \ Finset.univ.biUnion S

/-- `c = |L|`. -/
def numLow (S : Fin n → Finset (Fin m)) : ℕ := (allLow S).card

/-- `E_i = S_i \ ⋃_{ℓ ≠ i} S_ℓ`, the items that only buyer `i` reports high. -/
def excl (S : Fin n → Finset (Fin m)) (i : Fin n) : Finset (Fin m) :=
  S i \ (Finset.univ.erase i).biUnion S

/-- The exclusive count `e_i = |E_i|`. -/
def exclCount (S : Fin n → Finset (Fin m)) (i : Fin n) : ℕ := (excl S i).card

/-- `e* = max_i e_i` (`0` when `n = 0`). -/
def maxExcl (S : Fin n → Finset (Fin m)) : ℕ := Finset.univ.sup (exclCount S)

/-- `Pr[R = k]` for `R ∼ Bin(N, q)`. -/
noncomputable def binPmf (N : ℕ) (q : ℝ) (k : ℕ) : ℝ :=
  (N.choose k : ℝ) * q ^ k * (1 - q) ^ (N - k)

/-- `Pr[R > r]` for `R ∼ Bin(N, q)`. -/
noncomputable def binGt (N : ℕ) (q : ℝ) (r : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (N + 1)).filter (fun k => r < k), binPmf N q k

/-- `Pr[R ≥ r]` for `R ∼ Bin(N, q)`. -/
noncomputable def binGe (N : ℕ) (q : ℝ) (r : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (N + 1)).filter (fun k => r ≤ k), binPmf N q k

/-- (3.1): for `c ≥ 1`, `ϕ_{c,r} = a − ∆ Pr[R > r] / (c Pr[R = r])` with `R ∼ Bin(c + r, q)`,
`q = 1 − p`, `∆ = b − a`; and `ϕ_{0,r} = 0`. -/
noncomputable def phi (a b p : ℝ) (c r : ℕ) : ℝ :=
  if c = 0 then 0
  else a - (b - a) * binGt (c + r) (1 - p) r / ((c : ℝ) * binPmf (c + r) (1 - p) r)

/-- The reserves (3.2): `θ_0 = 0` and, for `d ≥ 1`,
`θ_d = min({k ∈ {0, …, d − 1} : ϕ_{d−k,k} > 0} ∪ {d})`. (The formula at `d = 0` gives `0`.) -/
noncomputable def reserveStar (a b p : ℝ) (d : ℕ) : ℤ :=
  (((insert d ((Finset.range d).filter (fun k => 0 < phi a b p (d - k) k))).min'
    (Finset.insert_nonempty _ _) : ℕ) : ℤ)

/-- The value (3.6): `m b (1 − p^n) + E_S[c [ϕ_{c,e*}]_+]`, the expectation over profiles with
`S_1, …, S_n` independent of mass function `f`. -/
noncomputable def revFormula (a b p : ℝ) (n m : ℕ) : ℝ :=
  m * b * (1 - p ^ n) +
    ∑ S : Fin n → Finset (Fin m), (∏ i, setPmf p m (S i)) *
      ((numLow S : ℝ) * max (phi a b p (numLow S) (maxExcl S)) 0)

/-- `ϖ_{c,r} = Pr[|L| = c, e* = r]` (§B.4). -/
noncomputable def lowMaxProb (p : ℝ) (n m c r : ℕ) : ℝ :=
  ∑ S : Fin n → Finset (Fin m),
    if numLow S = c ∧ maxExcl S = r then ∏ i, setPmf p m (S i) else 0

/-- `∑_{k=0}^{K-1} (π w)^k / k!`, so that `E_r(w) = expTrunc π (r + 1)` and `E_{−1} = expTrunc π 0
= 0` (§B.4). -/
noncomputable def expTrunc (π : ℝ) (K : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range K, Polynomial.C (π ^ k / (k.factorial : ℝ)) * Polynomial.X ^ k

end IIDMultiItem.TwoPoint


