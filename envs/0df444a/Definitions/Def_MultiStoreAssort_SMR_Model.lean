-- Prove2me | Definitions.Def_MultiStoreAssort_SMR_Model
-- name    : MultiStoreAssort_SMR_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:38.302369+00:00
-- url     : https://prove2.me/theorems/6e0fddf0-ca77-4760-ab2a-4c864093ed66
-- title:
--   §3, (1), (SMR), (2), (SQR), (3), (A.1), PDF pp. 8–11, 33 — the multi-store SMR/SQR models, the single-store problem, revenue-ordered sets, S̃ and S*_M(c)
-- statement:
--   This file sets up the multi-store assortment model of Liu, Chen, Liu and Wan.
--
--   A seller operates $m$ stores and sells $n$ substitutable products. Product $k$ has revenue $r_k$ and attraction value $v_k=\exp(u_k)>0$; the outside option has attraction value $1$. A customer first visits store $i$ (a fraction $\lambda_i$ of customers does so). An **assortment profile** is $\mathbf S=(S_1,\dots,S_m)$, where $S_i\subseteq\{1,\dots,n\}$ is the set offered in store $i$, and $\bar S=S_1\cup\dots\cup S_m$. Buying product $k$ from store $j$ after visiting store $i$ costs the customer a utility discount $c_{ij}^k\ge 0$ (with $c_{ii}^k=0$). The effective discount for product $k$ is
--   $$c_i^k(\mathbf S)=\min_{j\in\{l\,:\,k\in S_l\}} c_{ij}^k,$$
--   and $c_i^k(\mathbf S)=\infty$ if no store offers $k$.
--
--   The file defines the following objects.
--   1. `discFactor c S i k` $=\exp(-c_i^k(\mathbf S))$. It equals $0$ when no store offers $k$.
--   2. `Sbar S` $=\bar S$.
--   3. `pM`, the **simultaneous recommendation (SMR)** choice probabilities (1). With $D_i(\mathbf S)=1+\sum_{l\in S_i}v_l+\sum_{l\in\bar S\setminus S_i}v_l e^{-c_i^l(\mathbf S)}$,
--   $$p^M_{ik}(\mathbf S)=\begin{cases}v_k/D_i(\mathbf S), & k\in S_i,\\ v_k e^{-c_i^k(\mathbf S)}/D_i(\mathbf S), & k\in\bar S\setminus S_i,\\ 0, & \text{otherwise.}\end{cases}$$
--   4. `storeRevM` $=\sum_k r_k p^M_{ik}(\mathbf S)$ and the (SMR) objective `revM` $=\sum_i\lambda_i\sum_k r_k p^M_{ik}(\mathbf S)$.
--   5. `pQ`, the **sequential recommendation (SQR)** choice probabilities (2): $v_k/(1+\sum_{l\in S_i}v_l)$ for $k\in S_i$, $v_k e^{-c_i^k(\mathbf S)}/\big((1+\sum_{l\in S_i}v_l)D_i(\mathbf S)\big)$ for $k\in\bar S\setminus S_i$, and $0$ otherwise. `revQ` is the (SQR) objective $\sum_i\lambda_i\sum_k r_k p^Q_{ik}(\mathbf S)$.
--   6. `single r v S` $=\sum_{k\in S}r_kv_k/(1+\sum_{k\in S}v_k)$, the objective of the single-store problem (3), $R^*=\max_S$ of this quantity.
--   7. `prefixSet n j` $=\{1,\dots,j\}$. `IsRevenueOrdered S` holds when $S=\{1,\dots,k\}$ for some $k\in[n]$, so a revenue-ordered set is nonempty.
--   8. `IsOptSingle r v S` says $S$ is optimal for (3). `IsStilde r v S` says $S$ is $\tilde S$: the smallest revenue-ordered optimal solution of (3).
--   9. `revA1 r v S₂ β S₁` is store 1's revenue in the two-store problem (A.1) when store 2 offers $S_2$, written in terms of the discount factors $\beta_k=e^{-c^k}\in[0,1]$:
--   $$R(S_1,\mathbf c)=\frac{\sum_{k\in S_1}r_kv_k+\sum_{k\in S_2\setminus S_1}r_kv_k\beta_k}{1+\sum_{k\in S_1}v_k+\sum_{k\in S_2\setminus S_1}v_k\beta_k}.$$
--   10. `IsSstarM r v S₂ β S` says $S$ is $S^*_M(\mathbf c)$: a revenue-ordered optimal solution of (A.1) with the fewest elements among revenue-ordered optima.
--
--   These objects are the common model of the four missions on this paper: Theorem 1 and Theorem 5(a) (SMR), Theorems 2–4 (SQR), Proposition 7 (the half-approximation) and the pricing model of Theorem 6 are all stated in terms of them.
--
--   **Formalization Note.** Products are `Fin n`, so the paper's product $k$ is index $k-1$; stores are `Fin m`. The attraction values $v_k$ are the primitive parameters instead of the utilities $u_k$. Because $\exp$ is decreasing, `discFactor` is the largest factor $e^{-c_{ij}^k}$ over the stores $j$ offering $k$, which equals $e^{-\min_j c_{ij}^k}$; over the empty set of stores it is $0=e^{-\infty}$. In (A.1), $\mathbf c\in[0,\infty]^n$ is encoded by $\beta=e^{-\mathbf c}\in[0,1]^n$: $c^k=\infty$ becomes $\beta_k=0$, and $\mathbf c\ge\tilde{\mathbf c}$ becomes $\beta\le\tilde\beta$ pointwise. $\tilde S$ and $S^*_M(\mathbf c)$ are predicates, not chosen objects. `single` is the published `ChoiceCDLP.MNL.mnlObjective v r 1 S`, whose denominator is written $\sum_{k\in S}v_k+1$.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF pp. 8–11, §3, (1), (SMR), (2), (SQR), (3); PDF p. 33 (Online Supplement p. 1), (A.1), S*_M(c)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective

namespace MultiStoreAssort.SMR

open Finset

variable {m n : ℕ}

/-- `exp(−c_i^k(S))` of p. 9, with `c_i^k(S) = min_{j ∈ {l | k ∈ S_l}} c_{ij}^k`, and `c_i^k(S) = ∞`
(factor `0`) if no store offers `k`. Since `exp` is decreasing, `exp(−min_j c_{ij}^k)` is the largest
factor `exp(−c_{ij}^k)` over the stores `j` that offer `k`; the supremum over the empty set of
stores is `0 = exp(−∞)`. -/
noncomputable def discFactor (c : Fin m → Fin m → Fin n → ℝ) (S : Fin m → Finset (Fin n))
    (i : Fin m) (k : Fin n) : ℝ :=
  ((Finset.univ.filter (fun j => k ∈ S j)).sup (fun j => (Real.exp (-(c i j k))).toNNReal) : NNReal)

/-- The union `S̄ = S_1 ∪ ⋯ ∪ S_m` of the offered products (p. 8). -/
def Sbar (S : Fin m → Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.sup S

/-- The denominator `1 + Σ_{l∈S_i} v_l + Σ_{l∈S̄∖S_i} v_l exp(−c_i^l(S))` of (1) for store `i`. -/
noncomputable def denomM (v : Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (i : Fin m) : ℝ :=
  1 + ∑ l ∈ S i, v l + ∑ l ∈ Sbar S \ S i, v l * discFactor c S i l

/-- (1), p. 9: the SMR choice probability `p^M_{ik}(S)` of product `k` for a customer visiting
store `i`. -/
noncomputable def pM (v : Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (i : Fin m) (k : Fin n) : ℝ :=
  if k ∈ S i then v k / denomM v c S i
  else if k ∈ Sbar S \ S i then v k * discFactor c S i k / denomM v c S i
  else 0

/-- Store `i`'s SMR revenue `Σ_{k=1}^n r_k p^M_{ik}(S)`. -/
noncomputable def storeRevM (r v : Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (i : Fin m) : ℝ :=
  ∑ k, r k * pM v c S i k

/-- The (SMR) objective, p. 10: `Σ_{i=1}^m λ_i Σ_{k=1}^n r_k p^M_{ik}(S)`. -/
noncomputable def revM (lam : Fin m → ℝ) (r v : Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) : ℝ :=
  ∑ i, lam i * storeRevM r v c S i

/-- (2), p. 10: the SQR choice probability `p^Q_{ik}(S)`. -/
noncomputable def pQ (v : Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (i : Fin m) (k : Fin n) : ℝ :=
  if k ∈ S i then v k / (1 + ∑ l ∈ S i, v l)
  else if k ∈ Sbar S \ S i then
    v k * discFactor c S i k / ((1 + ∑ l ∈ S i, v l) * denomM v c S i)
  else 0

/-- The (SQR) objective, p. 11: `Σ_{i=1}^m λ_i Σ_{k=1}^n r_k p^Q_{ik}(S)`. -/
noncomputable def revQ (lam : Fin m → ℝ) (r v : Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) : ℝ :=
  ∑ i, lam i * ∑ k, r k * pQ v c S i k

/-- The single-store objective of (3), p. 11: `Σ_{k∈S} r_k v_k / (1 + Σ_{k∈S} v_k)`, i.e. the
published MNL objective with no-purchase weight `1`. -/
noncomputable def single (r v : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ChoiceCDLP.MNL.mnlObjective v r 1 S

/-- The paper's `{1, 2, …, j}`: products with 0-based index `< j`. -/
def prefixSet (n j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun k => k.val < j)

/-- A revenue-ordered assortment (p. 11): `S = {1, 2, …, k}` for some `k ∈ [n]` (so nonempty). -/
def IsRevenueOrdered (S : Finset (Fin n)) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ n ∧ S = prefixSet n j

/-- `S` is an optimal solution of (3). -/
def IsOptSingle (r v : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ T, single r v T ≤ single r v S

/-- `S` is `S̃` (p. 11): the smallest revenue-ordered optimal solution of (3). -/
def IsStilde (r v : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  IsRevenueOrdered S ∧ IsOptSingle r v S ∧
    ∀ T, IsRevenueOrdered T → IsOptSingle r v T → S.card ≤ T.card

/-- (A.1), Online Supplement p. 1: store 1's revenue `R(S_1, c)` when store 2 offers `S2`, written
with the discount factors `β_k = exp(−c^k) ∈ [0, 1]` (`β_k = 0` encodes `c^k = ∞`):
`(Σ_{k∈S_1} r_k v_k + Σ_{k∈S_2∖S_1} r_k v_k β_k) / (1 + Σ_{k∈S_1} v_k + Σ_{k∈S_2∖S_1} v_k β_k)`. -/
noncomputable def revA1 (r v : Fin n → ℝ) (S2 : Finset (Fin n)) (β : Fin n → ℝ)
    (S1 : Finset (Fin n)) : ℝ :=
  (∑ k ∈ S1, r k * v k + ∑ k ∈ S2 \ S1, r k * v k * β k) /
    (1 + ∑ k ∈ S1, v k + ∑ k ∈ S2 \ S1, v k * β k)

/-- `S` is `S*_M(c)` (Online Supplement p. 1): a revenue-ordered optimal solution of (A.1) with the
fewest elements among revenue-ordered optimal solutions. -/
def IsSstarM (r v : Fin n → ℝ) (S2 : Finset (Fin n)) (β : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  IsRevenueOrdered S ∧ (∀ T, revA1 r v S2 β T ≤ revA1 r v S2 β S) ∧
    ∀ T, IsRevenueOrdered T → (∀ U, revA1 r v S2 β U ≤ revA1 r v S2 β T) → S.card ≤ T.card

end MultiStoreAssort.SMR


