-- Prove2me | Definitions.Def_MultiStoreAssort_Pricing_Model
-- name    : MultiStoreAssort_Pricing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:14.852586+00:00
-- url     : https://prove2.me/theorems/26c97595-79f9-4d7c-9bf0-6e0a76bc9515
-- title:
--   §8, (13)–(15), PDF pp. 28–29 — multistore joint assortment and pricing under SMR and SQR, and the single-store MNL pricing problem
-- statement:
--   This file sets up the joint assortment and pricing model of Liu, Chen, Liu and Wan (§3 and §8).
--
--   A seller runs $m$ stores $i\in[m]$ and sells $n$ substitutable products $k\in\mathcal N=[n]$. A fraction $\lambda_i\ge 0$ of the customers (with $\sum_i\lambda_i=1$) visits store $i$. Store $i$ offers an assortment $S_i\subseteq\mathcal N$; the profile is $\mathbf S=(S_1,\dots,S_m)$ and $\bar S=S_1\cup\dots\cup S_m$. Prices are decisions: $p_{ik}\in\mathbb R$ is the price of product $k$ in store $i$, and $\mathbf P=(p_{ik})$. A customer who visits store $i$ and buys product $k$ in store $j$ at store $j$'s price has deterministic utility
--   $$u_{ij}^k(\mathbf P)=\alpha_{ik}-\beta_{ik}\,p_{jk}-c_{ij}^k,$$
--   where $\alpha_{ik}$ and $\beta_{ik}$ are the intrinsic utility and price sensitivity of product $k$ for store-$i$ customers and $c^k_{ij}$ is the utility discount for buying from another store.
--
--   1. **Own-store attraction.** $v_{ik}=\exp(\alpha_{ik}-\beta_{ik}p_{ik})$.
--   2. **Best other store.** A selection $l$ is a *best-store rule* for $(\mathbf S,\mathbf P)$ if for every store $i$ and every $k\in\bar S\setminus S_i$, the store $l(i,k)$ offers $k$ and maximizes $u^k_{ij}(\mathbf P)$ over the stores $j$ with $k\in S_j$ (the paper's $l=\arg\max_{\{j\mid k\in S_j\}}\alpha_{ik}-\beta_{ik}p_{jk}-c^k_{ij}$; ties may be broken arbitrarily).
--   3. **Other-store attraction and price.** With $l=l(i,k)$: $\tilde v_{ik}(\mathbf S)=\exp(\alpha_{ik}-\beta_{ik}p_{lk}-c^k_{il})$ and $\tilde p_{ik}(\mathbf S)=p_{lk}$.
--   4. **The SMR objective (13).**
--   $$R^M(\mathbf S,\mathbf P)=\sum_{i=1}^m\lambda_i\cdot\frac{\sum_{k\in S_i}p_{ik}v_{ik}+\sum_{k\in\bar S\setminus S_i}\tilde p_{ik}(\mathbf S)\tilde v_{ik}(\mathbf S)}{1+\sum_{k\in S_i}v_{ik}+\sum_{k\in\bar S\setminus S_i}\tilde v_{ik}(\mathbf S)}.$$
--   5. **The SQR objective (15).**
--   $$R^Q(\mathbf S,\mathbf P)=\sum_{i=1}^m\lambda_i\left(\frac{\sum_{k\in S_i}p_{ik}v_{ik}}{1+\sum_{k\in S_i}v_{ik}}+\frac{\sum_{k\in\bar S\setminus S_i}\tilde p_{ik}(\mathbf S)\tilde v_{ik}(\mathbf S)}{\bigl(1+\sum_{k\in S_i}v_{ik}\bigr)\bigl(1+\sum_{k\in S_i}v_{ik}+\sum_{k\in\bar S\setminus S_i}\tilde v_{ik}(\mathbf S)\bigr)}\right).$$
--   6. **The single-store problem (14).** For parameters $(\alpha_k)$, $(\beta_k)$, an assortment $S$ and prices $(p_k)$,
--   $$R_{14}(S,p)=\frac{\sum_{k\in S}p_k\exp(\alpha_k-\beta_kp_k)}{1+\sum_{k\in S}\exp(\alpha_k-\beta_kp_k)}.$$
--   7. **The markup equation.** $\theta$ solves $\theta=\sum_{k\in\mathcal N}e^{\hat\alpha_k-\beta_k\theta}$ with $\hat\alpha_k=\alpha_k-\log\beta_k-1$.
--
--   These are the objects of Theorem 6 and Proposition 9 of the paper.
--
--   **Formalization Note** Stores are `Fin m` and products `Fin n` (the paper's product $k$ is index $k-1$). $\bar S$ is `Finset.univ.sup S`. The selection $l$ is a function argument constrained by the predicate `IsBestStore`; it is never chosen by `Classical.choose`, so every statement about (13) or (15) holds for every tie-breaking. $\tilde v$, $\tilde p$ are defined for all $(i,k)$ but only enter the objectives for $k\in\bar S\setminus S_i$, where `IsBestStore` makes $l(i,k)$ a store offering $k$. The selection $l$ is an explicit argument of `rev13` and `rev15`. Production costs are zero, as on the page. `IsTheta` is a predicate; its solution exists and is unique when all $\beta_k>0$ (a separate milestone). Every denominator is $1$ plus a sum of exponentials, hence positive.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF pp. 8–9 (§3 model), PDF p. 28 (§8.1, (13), (14), θ*), PDF p. 29 (§8.2, (15))

import Mathlib
import Definitions.Def_MultiStoreAssort_SMR_Model

namespace MultiStoreAssort.Pricing
open Finset

variable {m n : ℕ}

/-- The deterministic utility `α_{ik} − β_{ik} p_{jk} − c_{ij}^k` that a customer who visits store `i`
derives from buying product `k` in store `j` at store `j`'s price `p_{jk}` (p. 28). The intrinsic utility
`α_{ik}` and price sensitivity `β_{ik}` are those of the visiting customer's store `i`. -/
def util (α β : Fin m → Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ) (P : Fin m → Fin n → ℝ)
    (i j : Fin m) (k : Fin n) : ℝ :=
  α i k - β i k * P j k - c i j k

/-- `l` is a store-selection rule realizing p. 28's
`l = arg max_{j | k ∈ S_j} α_{ik} − β_{ik} p_{jk} − c_{ij}^k`: for every store `i` and every product
`k ∈ S̄ \ S_i`, the store `l i k` offers `k` and gives the store-`i` customer the largest utility among
all stores offering `k`. Ties may be broken arbitrarily; the value of `l` outside `S̄ \ S_i` is
irrelevant. -/
def IsBestStore (α β : Fin m → Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ) (P : Fin m → Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (l : Fin m → Fin n → Fin m) : Prop :=
  ∀ i k, k ∈ MultiStoreAssort.SMR.Sbar S \ S i →
    k ∈ S (l i k) ∧ ∀ j, k ∈ S j → util α β c P i j k ≤ util α β c P i (l i k) k

/-- `v_{ik} = exp(α_{ik} − β_{ik} p_{ik})` (p. 28). -/
noncomputable def vP (α β : Fin m → Fin n → ℝ) (P : Fin m → Fin n → ℝ) (i : Fin m) (k : Fin n) : ℝ :=
  Real.exp (α i k - β i k * P i k)

/-- `ṽ_{ik}(𝐒) = exp(α_{ik} − β_{ik} p_{lk} − c_{il}^k)` with `l = l i k` (p. 28). -/
noncomputable def vTilde (α β : Fin m → Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (P : Fin m → Fin n → ℝ) (l : Fin m → Fin n → Fin m) (i : Fin m) (k : Fin n) : ℝ :=
  Real.exp (util α β c P i (l i k) k)

/-- `p̃_{ik}(𝐒) = p_{lk}` with `l = l i k` (p. 28). -/
def pTilde (P : Fin m → Fin n → ℝ) (l : Fin m → Fin n → Fin m) (i : Fin m) (k : Fin n) : ℝ :=
  P (l i k) k

/-- Store `i`'s expected revenue in (13) (SMR):
`(Σ_{k∈S_i} p_{ik} v_{ik} + Σ_{k∈S̄\S_i} p̃_{ik} ṽ_{ik}) / (1 + Σ_{k∈S_i} v_{ik} + Σ_{k∈S̄\S_i} ṽ_{ik})`. -/
noncomputable def storeRev13 (α β : Fin m → Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (P : Fin m → Fin n → ℝ) (l : Fin m → Fin n → Fin m) (i : Fin m) : ℝ :=
  (∑ k ∈ S i, P i k * vP α β P i k + ∑ k ∈ MultiStoreAssort.SMR.Sbar S \ S i, pTilde P l i k * vTilde α β c P l i k) /
    (1 + ∑ k ∈ S i, vP α β P i k + ∑ k ∈ MultiStoreAssort.SMR.Sbar S \ S i, vTilde α β c P l i k)

/-- The objective `R^M(𝐒, 𝐏)` of the joint SMR problem (13) (p. 28). -/
noncomputable def rev13 (lam : Fin m → ℝ) (α β : Fin m → Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (P : Fin m → Fin n → ℝ) (l : Fin m → Fin n → Fin m) : ℝ :=
  ∑ i, lam i * storeRev13 α β c S P l i

/-- Store `i`'s expected revenue in (15) (SQR):
`Σ_{k∈S_i} p_{ik} v_{ik} / (1 + Σ_{k∈S_i} v_{ik})
  + Σ_{k∈S̄\S_i} p̃_{ik} ṽ_{ik} / ((1 + Σ_{k∈S_i} v_{ik}) (1 + Σ_{k∈S_i} v_{ik} + Σ_{k∈S̄\S_i} ṽ_{ik}))`. -/
noncomputable def storeRev15 (α β : Fin m → Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (P : Fin m → Fin n → ℝ) (l : Fin m → Fin n → Fin m) (i : Fin m) : ℝ :=
  (∑ k ∈ S i, P i k * vP α β P i k) / (1 + ∑ k ∈ S i, vP α β P i k) +
    (∑ k ∈ MultiStoreAssort.SMR.Sbar S \ S i, pTilde P l i k * vTilde α β c P l i k) /
      ((1 + ∑ k ∈ S i, vP α β P i k) *
        (1 + ∑ k ∈ S i, vP α β P i k + ∑ k ∈ MultiStoreAssort.SMR.Sbar S \ S i, vTilde α β c P l i k))

/-- The objective `R^Q(𝐒, 𝐏)` of the joint SQR problem (15) (p. 29). -/
noncomputable def rev15 (lam : Fin m → ℝ) (α β : Fin m → Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (P : Fin m → Fin n → ℝ) (l : Fin m → Fin n → Fin m) : ℝ :=
  ∑ i, lam i * storeRev15 α β c S P l i

/-- The objective of the single-store joint assortment and pricing problem (14) (p. 28), for
intrinsic utilities `a = (α_k)`, price sensitivities `b = (β_k)`, assortment `S` and prices `p`:
`Σ_{k∈S} p_k exp(α_k − β_k p_k) / (1 + Σ_{k∈S} exp(α_k − β_k p_k))`. -/
noncomputable def rev14 (a b : Fin n → ℝ) (S : Finset (Fin n)) (p : Fin n → ℝ) : ℝ :=
  (∑ k ∈ S, p k * Real.exp (a k - b k * p k)) / (1 + ∑ k ∈ S, Real.exp (a k - b k * p k))

/-- `θ` solves `θ = Σ_{k∈𝒩} exp(α̂_k − β_k θ)` with `α̂_k = α_k − log β_k − 1` (p. 28). -/
def IsTheta (a b : Fin n → ℝ) (θ : ℝ) : Prop :=
  θ = ∑ k, Real.exp ((a k - Real.log (b k) - 1) - b k * θ)

end MultiStoreAssort.Pricing


