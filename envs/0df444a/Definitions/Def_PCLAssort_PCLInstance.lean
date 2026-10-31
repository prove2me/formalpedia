-- Prove2me | Definitions.Def_PCLAssort_PCLInstance
-- name    : PCLAssort_PCLInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:20.780245+00:00
-- url     : https://prove2.me/theorems/a08715cc-4c29-4984-941b-7f1cec012b25
-- title:
--   An instance of the paired combinatorial logit model
-- statement:
--   An instance of the paired combinatorial logit (PCL) model with $n$ products consists of
--
--   1. revenues $r_i\ge 0$ and preference weights $v_i\ge 0$ for the products $i\in[n]$;
--   2. the preference weight $v_0>0$ of the no-purchase option;
--   3. a dissimilarity parameter $\gamma_{ij}\in(0,1]$ for each nest, an ordered pair $(i,j)$ with $i\neq j$.
--
--   The set of nests is $M=\{(i,j)\mid i\ne j\}$. A customer first picks a nest or the no-purchase option, then a product of the nest.
--
--   **Formalization Note** Products are `Fin n`. The page writes $\gamma_{ij}\in[0,1]$ and does not restrict $v_0$; $\gamma_{ij}>0$ is needed for $v_i^{1/\gamma_{ij}}$ to be defined, and $v_0>0$ for the fixed point of $g(\cdot)/v_0$ (p.792) to make sense.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §2, p.789 (PDF p.5)

import Mathlib

namespace PCLAssort

/-- An instance of the paired combinatorial logit (PCL) model (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §2, p.789): products
`[n] = {1, …, n}`, each product `i` with a revenue `r_i ≥ 0` and a preference weight `v_i ≥ 0`, the
no-purchase weight `v_0`, and for each nest, an ordered pair `(i, j)` with `i ≠ j`, a dissimilarity
parameter `γ_ij`.

**Formalization Note.** Products are `Fin n` (paper product `i` is index `i − 1`). Two readings of
the page are built in: `v_0 > 0` (the page only names `v_0`; the paper divides by it, "fixed point
of `g(·)/v_0`", p.792), and `γ_ij ∈ (0, 1]` instead of `[0, 1]` (the weight `v_i^{1/γ_ij}` is
undefined at `γ_ij = 0`). The values `γ i i` are not used. -/
structure PCLInstance (n : ℕ) where
  /-- revenues `r_i` -/
  r : Fin n → ℝ
  /-- preference weights `v_i` -/
  v : Fin n → ℝ
  /-- no-purchase preference weight `v_0` -/
  v0 : ℝ
  /-- dissimilarity parameters `γ_ij` of the nests `(i, j)`, `i ≠ j` -/
  γ : Fin n → Fin n → ℝ
  r_nonneg : ∀ i, 0 ≤ r i
  v_nonneg : ∀ i, 0 ≤ v i
  v0_pos : 0 < v0
  γ_pos : ∀ i j, i ≠ j → 0 < γ i j
  γ_le_one : ∀ i j, i ≠ j → γ i j ≤ 1

end PCLAssort


