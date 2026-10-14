-- Prove2me | Definitions.Def_MultiStoreAssort_SQR_Model
-- name    : MultiStoreAssort_SQR_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:16.967708+00:00
-- url     : https://prove2.me/theorems/edf8eab6-89ef-4cc6-b3ab-e51b7fce6a8b
-- title:
--   §3, (2), (SQR), (3), (8), PDF pp. 8–17 — the sequential recommendation model, its objective, homogeneous discounts, the single-store problem, revenue-ordered sets and S̃
-- statement:
--   This file sets up the **sequential recommendation (SQR) model** of multi-store assortment planning of Liu, Chen, Liu and Wan.
--
--   A seller operates $m$ stores and sells $n$ substitutable products. A fraction $\lambda_i$ of the customers visits store $i$. Product $k$ has revenue $r_k$ and attraction value $v_k = e^{u_k} > 0$; the outside option has attraction $1$. A profile $\mathbf S = (S_1,\dots,S_m)$ lists the assortment $S_i$ of every store, and $\bar S = S_1\cup\dots\cup S_m$. A customer who visits store $i$ and buys product $k$ from store $j$ incurs a utility discount $c_{ij}^k \ge 0$, with $c_{ii}^k = 0$, and
--   $$
--   c_i^k(\mathbf S)=\min_{j:\,k\in S_j} c_{ij}^k \quad(\text{and } c_i^k(\mathbf S)=\infty \text{ if no store offers } k).
--   $$
--
--   The definitions are:
--
--   1. `discFactor c S i k` $= e^{-c_i^k(\mathbf S)}$, with $e^{-\infty}=0$.
--   2. `Sbar S` $=\bar S$, `Vs v S` $= V(S)=\sum_{k\in S} v_k$, `Ws r v S` $= W(S)=\sum_{k\in S} r_k v_k$.
--   3. `pQ v c S i k`, the SQR choice probability (2):
--   $$
--   p^Q_{ik}(\mathbf S)=\begin{cases}\dfrac{v_k}{1+\sum_{l\in S_i}v_l}, & k\in S_i,\\[3mm]
--   \dfrac{v_k e^{-c_i^k(\mathbf S)}}{\big(1+\sum_{l\in S_i}v_l\big)\big(1+\sum_{l\in S_i}v_l+\sum_{l\in\bar S\setminus S_i}v_l e^{-c_i^l(\mathbf S)}\big)}, & k\in \bar S\setminus S_i,\\[3mm]
--   0, & \text{otherwise.}\end{cases}
--   $$
--   4. `revQ lam r v c S` $=\sum_{i=1}^m \lambda_i\sum_{k=1}^n r_k\,p^Q_{ik}(\mathbf S)$, the objective of (SQR), and `IsOptQ` says that a profile maximizes it over all profiles.
--   5. `UnivHomog c c0`: $c_{ij}^k = c$ with $c>0$ for all $i\ne j$ and $k$ (universally homogeneous discounts, p. 14). `StoreWiseHomog c cs`: $c_{ij}^k = c_i > 0$ for all $i\ne j$ and $k$ (store-wise homogeneous discounts, p. 17).
--   6. `single r v S` $=\sum_{k\in S} r_kv_k\big/\big(1+\sum_{k\in S}v_k\big)$, the single-store problem (3); `IsOptSingle` says that $S$ maximizes it.
--   7. `IsRevenueOrdered S`: $S=\{1,2,\dots,k\}$ for some $k\in[n]$ (so $S$ is nonempty). `IsStilde r v S`: $S$ is the smallest revenue-ordered optimal solution of (3), the paper's $\tilde S$.
--   8. `rev8 r v β S₂ S₁`, the objective of problem (8):
--   $$
--   R(S_1)=\frac{W(S_1)}{1+V(S_1)}+\frac{\beta\,W(S_2\setminus S_1)}{\big(1+V(S_1)\big)\big(1+V(S_1)+\beta V(S_2\setminus S_1)\big)},
--   $$
--   and `IsRevOrderedWithin S₂ S₁`: $S_1$ consists of the products of $S_2$ below some index, i.e. it is revenue-ordered within the products of $S_2$ (possibly empty).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Products are `Fin n` and stores `Fin m`; the paper's product $k$ is index $k-1$, so product $1$ (the highest revenue, since $r_1>\dots>r_n$) is index $0$. The attraction values $v_k$ are the primitive data instead of the utilities $u_k$. The factor $e^{-c_i^k(\mathbf S)}$ is computed as the largest factor $e^{-c_{ij}^k}$ over the stores $j$ that offer $k$, which equals $e^{-\min_j c_{ij}^k}$ because $\exp$ is decreasing, and is $0$ when no store offers $k$. "Optimal" always means a global maximizer over all profiles (ties allowed); $\tilde S$ is a predicate, not a chosen element.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF pp. 8–11, §3, (2), (SQR), (3); PDF p. 14 (universally homogeneous), p. 15 (V, W, β), p. 16 (8), p. 17 (store-wise homogeneous); PDF p. 35, Lemma B.2

import Mathlib
import Definitions.Def_MultiStoreAssort_SMR_Model

namespace MultiStoreAssort.SQR

variable {m n : ℕ}

/-- `V(S) = ∑_{k ∈ S} v_k` (p. 15). -/
noncomputable def Vs (v : Fin n → ℝ) (S : Finset (Fin n)) : ℝ := ∑ k ∈ S, v k

/-- `W(S) = ∑_{k ∈ S} r_k v_k` (p. 15). -/
noncomputable def Ws (r v : Fin n → ℝ) (S : Finset (Fin n)) : ℝ := ∑ k ∈ S, r k * v k

/-- `S` is an optimal solution of (SQR): a global maximizer over all assortment profiles (ties allowed). -/
def IsOptQ (lam : Fin m → ℝ) (r v : Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) : Prop :=
  ∀ S' : Fin m → Finset (Fin n), MultiStoreAssort.SMR.revQ lam r v c S' ≤ MultiStoreAssort.SMR.revQ lam r v c S

/-- Universally homogeneous utility discounts (p. 14): `c_{ij}^k = c` with `c > 0` for `i ≠ j`. -/
def UnivHomog (c : Fin m → Fin m → Fin n → ℝ) (c0 : ℝ) : Prop :=
  0 < c0 ∧ ∀ i j k, i ≠ j → c i j k = c0

/-- Store-wise homogeneous utility discounts (p. 17): `c_{ij}^k = c_i > 0` for `i ≠ j`. -/
def StoreWiseHomog (c : Fin m → Fin m → Fin n → ℝ) (cs : Fin m → ℝ) : Prop :=
  (∀ i, 0 < cs i) ∧ ∀ i j k, i ≠ j → c i j k = cs i

/-- The single-store objective of (3): `∑_{k ∈ S} r_k v_k / (1 + ∑_{k ∈ S} v_k)`. -/
noncomputable def single (r v : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  (∑ k ∈ S, r k * v k) / (1 + ∑ k ∈ S, v k)

/-- `S` is optimal for the single-store problem (3). -/
def IsOptSingle (r v : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ T : Finset (Fin n), single r v T ≤ single r v S

/-- (8): store 1's revenue `R(S₁)` with `S₂` fixed and `β = exp(−c)`. -/
noncomputable def rev8 (r v : Fin n → ℝ) (β : ℝ) (S2 S1 : Finset (Fin n)) : ℝ :=
  Ws r v S1 / (1 + Vs v S1) +
    β * Ws r v (S2 \ S1) / ((1 + Vs v S1) * (1 + Vs v S1 + β * Vs v (S2 \ S1)))

/-- "Revenue-ordered (within the products in `S₂`)" (Lemma B.2): `S₁` consists of the products of `S₂`
with index below some threshold, i.e. a (possibly empty) initial segment of `S₂` in the revenue order. -/
def IsRevOrderedWithin (S2 S1 : Finset (Fin n)) : Prop :=
  ∃ j : ℕ, S1 = S2.filter (fun k => k.val < j)

end MultiStoreAssort.SQR


