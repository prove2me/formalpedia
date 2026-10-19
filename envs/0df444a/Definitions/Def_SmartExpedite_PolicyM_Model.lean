-- Prove2me | Definitions.Def_SmartExpedite_PolicyM_Model
-- name    : SmartExpedite_PolicyM_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:48.568434+00:00
-- url     : https://prove2.me/theorems/49770e31-41ab-4d9a-b23a-4b67fbcf2eff
-- title:
--   Policy-M occupancy, thresholds, routing, rates, and product weights
-- statement:
--   The supply system has $K$ numbered service nodes, with state $n=(n_1,\ldots,n_K)\in\mathbb N^K$. The occupancy of a segment is
--
--   $$n[a,b]=\sum_{l=a}^{b}n_l.$$
--
--   A policy parameter array $u=(u_{ij})_{0\le i<j\le K}$ has nonnegative extended-integer entries, is nondecreasing in $j$ and nonincreasing in $i$, and satisfies $u_{iK}=\infty$. Assumption A imposes the paper's triangle and supermodular inequalities. The admissible set is $S_M(u)=\{n:n[k+1,l]\le u_{kl}\text{ for }0\le k<l\le K\}$.
--
--   A demand arrival and each enabled service completion follow the paper's Policy-M routing rules. Their rates are determined by the demand rate $\lambda$ and node rates $\mu_k$. The product weight is $w(n)=\prod_{k=1}^K(\lambda/\mu_k)^{n_k}$, its normalizer is $G(u)=\sum_{n\in S_M(u)}w(n)$, and the candidate law is $\pi_M(n)=\mathbf1_{S_M(u)}(n)w(n)/G(u)$.
--
--   The definition also provides the source's routing sets $R_i,E_{ij}$ and its proof sets $A_m,B_m,C_m,D_m,E_i,F_i$. These shared definitions let the closure, indicator, and balance claims use one model.
--
--   **Formalization Note** The entries of $u$ use $\mathbb N\cup\{\infty\}$ because the source requires infinite terminal thresholds. Node indices in formulas remain one-based. The normalizing sum is a countable sum; its convergence and positivity are conclusions of Theorem 1.
-- source:
--   Song, Xiao, Zhang & Zipkin, Smart policies for multi-source inventory systems and general tandem queues with order tracking and expediting, SSRN 3702068 (version of September 28, 2020), pp. 14–18, 34–36, (5), (7), (11), (12), §4, Assumption A, (A-16)–(A-21)

import Mathlib

noncomputable section

namespace SmartExpedite.PolicyM

/-- The occupancy of paper node `l`, with node numbers starting at one. -/
def occ {K : ℕ} (n : Fin K → ℕ) (l : ℕ) : ℕ :=
  if h : 1 ≤ l ∧ l ≤ K then n ⟨l - 1, by omega⟩ else 0

/-- Equation (5): occupancy of the segment from node `a` through node `b`. -/
def seg {K : ℕ} (n : Fin K → ℕ) (a b : ℕ) : ℕ :=
  ∑ l ∈ Finset.Icc a b, occ n l

/-- The unit vector at paper node `l`. -/
def ev (K l : ℕ) : Fin K → ℕ :=
  fun j => if j.val + 1 = l then 1 else 0

/-- The policy parameters on p. 15: nondecreasing in the destination, nonincreasing
in the origin, and infinite at destination `K`. The type `ℕ∞` implements the
nonnegative entries and the paper's infinite entries together. -/
def IsPolicyParam (K : ℕ) (u : ℕ → ℕ → ℕ∞) : Prop :=
  (∀ i j, i < j → j < K → u i j ≤ u i (j + 1)) ∧
  (∀ i j, 0 < i → i < j → j ≤ K → u i j ≤ u (i - 1) j) ∧
  (∀ i, i < K → u i K = ⊤)

/-- Assumption A, p. 17: triangle inequalities and supermodularity. -/
def AssumptionA (K : ℕ) (u : ℕ → ℕ → ℕ∞) : Prop :=
  (∀ k i j, k < i → i < j → j ≤ K → u k j ≤ u k i + u i j) ∧
  (∀ k i j l, k < i → i < j → j < l → l ≤ K →
    u i j + u k l ≤ u k j + u i l)

/-- Equation (11): the admissible state set. -/
def SM (K : ℕ) (u : ℕ → ℕ → ℕ∞) : Set (Fin K → ℕ) :=
  {n | ∀ k l, k < l → l ≤ K → (seg n (k + 1) l : ℕ∞) ≤ u k l}

/-- Equation (7), including the stated empty-max convention. -/
def arrNode (K : ℕ) (u : ℕ → ℕ → ℕ∞) (n : Fin K → ℕ) : ℕ :=
  let S := (Finset.Icc 1 K).filter (fun k => u 0 k ≤ (seg n 1 k : ℕ∞))
  if h : S.Nonempty then S.max' h + 1 else 1

/-- Policy-M's routing rule on pp. 16–17. The range is empty for `m = K - 1`,
so the destination is `K`, as required by `r_{K-1,K}(n) = 1`. -/
def expNode (K : ℕ) (u : ℕ → ℕ → ℕ∞) (m : ℕ) (n : Fin K → ℕ) : ℕ :=
  let S := (Finset.Icc (m + 1) (K - 1)).filter
    (fun k => u m k ≤ (seg n (m + 1) k : ℕ∞))
  if h : S.Nonempty then S.max' h + 1 else m + 1

/-- The transition rate from `a` to `b` under the paper's arrival and service
clocks. A service completion at an empty node is disabled. -/
def rate (K : ℕ) (u : ℕ → ℕ → ℕ∞) (lam : ℝ) (mu : ℕ → ℝ)
    (a b : Fin K → ℕ) : ℝ :=
  (if b = a + ev K (arrNode K u a) then lam else 0) +
  (∑ m ∈ Finset.Icc 1 (K - 1),
    if 0 < occ a m ∧ b = a - ev K m + ev K (expNode K u m a)
    then mu m else 0) +
  (if 0 < occ a K ∧ b = a - ev K K then mu K else 0)

/-- The sum of enabled event-clock rates in state `a`. -/
def outRate (K : ℕ) (lam : ℝ) (mu : ℕ → ℝ) (a : Fin K → ℕ) : ℝ :=
  lam + ∑ k ∈ Finset.Icc 1 K, if 0 < occ a k then mu k else 0

/-- The unnormalized product weight in equation (12). -/
def weight (K : ℕ) (lam : ℝ) (mu : ℕ → ℝ) (n : Fin K → ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 K, (lam / mu k) ^ occ n k

/-- The normalizing sum `G(u)` of equation (12). -/
def normG (K : ℕ) (u : ℕ → ℕ → ℕ∞) (lam : ℝ)
    (mu : ℕ → ℝ) : ℝ :=
  ∑' n : Fin K → ℕ, (SM K u).indicator (weight K lam mu) n

/-- Equation (12), extended by zero outside `S_M(u)`. -/
def piM (K : ℕ) (u : ℕ → ℕ → ℕ∞) (lam : ℝ)
    (mu : ℕ → ℝ) (n : Fin K → ℕ) : ℝ :=
  (SM K u).indicator (weight K lam mu) n / normG K u lam mu

/-- States in `S_M(u)` where an arriving order is routed to node `i` (p. 34).
The page displays `R_i = {n : n[1,i-1] = u_{0,i-1} and
n[1,j] < u_{0j} for j = i,...,K-1}` for the nonempty maximum case.
At `i=1` the operational rule (7) supplies the explicit empty-max
fallback; no undefined `u_{0,0}` is read. -/
def Rset (K : ℕ) (u : ℕ → ℕ → ℕ∞) (i : ℕ) : Set (Fin K → ℕ) :=
  {n | n ∈ SM K u ∧ arrNode K u n = i}

/-- States in `S_M(u)` where a service completion at node `m` routes to `j`
(pp. 34–35); service requires an item at node `m`. The page displays:
`E_{m,m+1} = {n : n[m+1,l] < u_{ml} for l=m+1,...,K-1}`;
for `m+2 ≤ j < K`, `E_{mj} = {n : n[m+1,j-1] ≥ u_{m,j-1}` and
`n[m+1,l] < u_{ml} for l=j,...,K-1}`;
for `j=K`, `E_{mK} = {n : n[m+1,K-1] ≥ u_{m,K-1}}`.
Here the displayed conditions are intersected with `S_M(u)` and with the
enabled-service condition. -/
def Eset (K : ℕ) (u : ℕ → ℕ → ℕ∞) (m j : ℕ) : Set (Fin K → ℕ) :=
  {n | n ∈ SM K u ∧ 0 < occ n m ∧ expNode K u m n = j}

/-- Set `A_m` in (A-16), pp. 35–36: `n ∈ S_M(u)`, `n_i>0`,
`n[m+1,i-1]=u_{m,i-1}`, and `n[k+1,l]<u_{kl}` for
`k=0,...,m-1`, `l=m+1,...,i-1`. -/
def Aset (K : ℕ) (u : ℕ → ℕ → ℕ∞) (i m : ℕ) : Set (Fin K → ℕ) :=
  {n | n ∈ SM K u ∧ 0 < occ n i ∧
    (seg n (m + 1) (i - 1) : ℕ∞) = u m (i - 1) ∧
    ∀ k ∈ Finset.Icc 0 (m - 1), ∀ l ∈ Finset.Icc (m + 1) (i - 1),
      (seg n (k + 1) l : ℕ∞) < u k l}

/-- Set `B_m` in (A-17), pp. 35–36: `n ∈ S_M(u)`, `n_i>0`,
`n[m+1,i-1]=u_{m,i-1}`, and `n[k+1,i-1]≤u_{k,i-1}-1`
for `k=0,...,m-1`. -/
def Bset (K : ℕ) (u : ℕ → ℕ → ℕ∞) (i m : ℕ) : Set (Fin K → ℕ) :=
  {n | n ∈ SM K u ∧ 0 < occ n i ∧
    (seg n (m + 1) (i - 1) : ℕ∞) = u m (i - 1) ∧
    ∀ k ∈ Finset.Icc 0 (m - 1), (seg n (k + 1) (i - 1) : ℕ∞) < u k (i - 1)}

/-- Set `C_m` in (A-18), p. 36: `n ∈ S_M(u)` and
`n[k+1,l]≤u_{kl}-1` for `k=0,...,m-1`, `l=m+1,...,i-2`. -/
def Cset (K : ℕ) (u : ℕ → ℕ → ℕ∞) (i m : ℕ) : Set (Fin K → ℕ) :=
  {n | n ∈ SM K u ∧
    ∀ k ∈ Finset.Icc 0 (m - 1), ∀ l ∈ Finset.Icc (m + 1) (i - 2),
      (seg n (k + 1) l : ℕ∞) < u k l}

/-- Set `D_m` in (A-19), p. 36: `n ∈ S_M(u)`, `n_i>0`,
`n[m+1,i-1]=u_{m,i-1}`, and `n[k+1,m]<u_{km}`
for `k=0,...,m-1`. -/
def Dset (K : ℕ) (u : ℕ → ℕ → ℕ∞) (i m : ℕ) : Set (Fin K → ℕ) :=
  {n | n ∈ SM K u ∧ 0 < occ n i ∧
    (seg n (m + 1) (i - 1) : ℕ∞) = u m (i - 1) ∧
    ∀ k ∈ Finset.Icc 0 (m - 1), (seg n (k + 1) m : ℕ∞) < u k m}

/-- Set `E_i` in (A-20), p. 36: `n ∈ S_M(u)`, `n_i>0`, and
`n[k+1,i-1]<u_{k,i-1}` for `k=0,...,i-2`. -/
def Eiset (K : ℕ) (u : ℕ → ℕ → ℕ∞) (i : ℕ) : Set (Fin K → ℕ) :=
  {n | n ∈ SM K u ∧ 0 < occ n i ∧
    ∀ k ∈ Finset.Icc 0 (i - 2), (seg n (k + 1) (i - 1) : ℕ∞) < u k (i - 1)}

/-- Set `F_i` in (A-21), p. 36: `n ∈ S_M(u)`, `n_i>0`, and
`n[1,i-1]=u_{0,i-1}`. -/
def Fset (K : ℕ) (u : ℕ → ℕ → ℕ∞) (i : ℕ) : Set (Fin K → ℕ) :=
  {n | n ∈ SM K u ∧ 0 < occ n i ∧
    (seg n 1 (i - 1) : ℕ∞) = u 0 (i - 1)}

end SmartExpedite.PolicyM


