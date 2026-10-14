-- Prove2me | Definitions.Def_MultiStoreAssort_Approx_Model
-- name    : MultiStoreAssort_Approx_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:07.072108+00:00
-- url     : https://prove2.me/theorems/79ac123c-b462-4e72-a393-0df2fbc4f264
-- title:
--   §3, §7.1, (3), (10), (SQR-heter), (D.1), PDF pp. 8–11, 23, 46 — multi-store sequential recommendation with store-specific attraction values
-- statement:
--   This file sets up the multi-store assortment model of Liu, Chen, Liu and Wan under **sequential recommendation (SQR)** in the **heterogeneous case**, where the same product may have different attraction values in different stores.
--
--   A seller runs $m$ stores and sells $n$ products. A fraction $\lambda_i$ of the customers first visits store $i$. Product $k$ has revenue $r_k$, and in store $i$ it has attraction value $v_{ik}=\exp(u_{ik})>0$; the outside option has attraction value $1$. A customer who first visits store $i$ but buys product $k$ from store $j$ suffers a utility discount $c^k_{ij}\ge 0$, with $c^k_{ii}=0$. A decision is a profile $\boldsymbol S=(S_1,\dots,S_m)$ of assortments, with union $\bar S=S_1\cup\dots\cup S_m$. The definitions are:
--
--   1. The **discount factor** $\exp(-c^k_i(\boldsymbol S))$, where $c^k_i(\boldsymbol S)=\min_{j\in\{l\,:\,k\in S_l\}}c^k_{ij}$, and $c^k_i(\boldsymbol S)=\infty$ (factor $0$) when no store offers $k$.
--   2. The union $\bar S$.
--   3. The **single-store revenue** of an assortment $S$ with attraction values $v$,
--   $$
--   R(S)=\frac{\sum_{k\in S}r_kv_k}{1+\sum_{k\in S}v_k},
--   $$
--   the objective of problem (3) and, with $v=v_{i\cdot}$, of store $i$'s problem (D.1).
--   4. **Revenue-ordered** assortments $\{1,2,\dots,k\}$ with $k\in[n]$ (so nonempty), an **optimal solution** of the single-store problem (a maximizer of $R$ over all assortments), and $\tilde S$, the smallest revenue-ordered optimal solution (p. 11).
--   5. The SQR choice probability (10): a customer who first visits store $i$ buys $k$ with probability
--   $$
--   p^Q_{ik}(\boldsymbol S)=\begin{cases}\dfrac{v_{ik}}{1+\sum_{l\in S_i}v_{il}} & k\in S_i,\\[3mm] \dfrac{v_{ik}\exp(-c^k_i(\boldsymbol S))}{\bigl(1+\sum_{l\in S_i}v_{il}\bigr)\bigl(1+\sum_{l\in S_i}v_{il}+\sum_{l\in\bar S\setminus S_i}v_{il}\exp(-c^l_i(\boldsymbol S))\bigr)} & k\in\bar S\setminus S_i,\\[3mm] 0 & \text{otherwise.}\end{cases}
--   $$
--   6. The objective of (SQR-heter), $\sum_{i=1}^m\lambda_i\sum_{k=1}^n r_k\,p^Q_{ik}(\boldsymbol S)$.
--
--   These objects are the model of every statement of this mission: the heuristic that offers each store its single-store optimum $\tilde S_i$ is evaluated with the (SQR-heter) objective, cross-selling included.
--
--   **Formalization Note.** Products are `Fin n` and the paper's product $k$ is index $k-1$; stores are `Fin m`. Attraction values $v_{ik}$ are taken as the primitive data instead of the utilities $u_{ik}$. The discount factor is written as the largest $\exp(-c^k_{ij})$ over the offering stores, which equals $\exp(-\min_j c^k_{ij})$ because $\exp$ is decreasing; the supremum of the empty family is $0$, the paper's $c=\infty$ convention. The single-store revenue is the published `ChoiceCDLP.MNL.mnlObjective v r 1 S`. $\tilde S$ is a predicate, not a chosen term. The standing assumptions ($\lambda\ge0$, $\sum\lambda_i=1$, $r_1>\dots>r_n$, $v>0$, $c\ge0$, $c_{ii}=0$) are hypotheses of each theorem, not part of the definitions.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF pp. 8–11, §3, (3); PDF p. 23, §7.1, (10), (SQR-heter); PDF p. 46, (D.1)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MultiStoreAssort_SMR_Model

namespace MultiStoreAssort.Approx

open Finset

variable {m n : ℕ}

/-- (10), p. 23: the SQR choice probability of product `k` for a customer who first visits store `i`,
in the heterogeneous case with store-specific attraction values `v i k`. -/
noncomputable def pQh (v : Fin m → Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (i : Fin m) (k : Fin n) : ℝ :=
  if k ∈ S i then v i k / (1 + ∑ l ∈ S i, v i l)
  else if k ∈ MultiStoreAssort.SMR.Sbar S \ S i then
    v i k * MultiStoreAssort.SMR.discFactor c S i k /
      ((1 + ∑ l ∈ S i, v i l) *
        (1 + ∑ l ∈ S i, v i l + ∑ l ∈ MultiStoreAssort.SMR.Sbar S \ S i, v i l * MultiStoreAssort.SMR.discFactor c S i l))
  else 0

/-- The objective of (SQR-heter), p. 23: `∑_{i=1}^m λ_i ∑_{k=1}^n r_k p^Q_{ik}(S)`. -/
noncomputable def revQh (lam : Fin m → ℝ) (r : Fin n → ℝ) (v : Fin m → Fin n → ℝ)
    (c : Fin m → Fin m → Fin n → ℝ) (S : Fin m → Finset (Fin n)) : ℝ :=
  ∑ i, lam i * ∑ k, r k * pQh v c S i k

end MultiStoreAssort.Approx


