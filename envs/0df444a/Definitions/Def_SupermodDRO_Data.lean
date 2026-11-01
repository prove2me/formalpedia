-- Prove2me | Definitions.Def_SupermodDRO_Data
-- name    : SupermodDRO_Data
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:31:45.271382+00:00
-- url     : https://prove2.me/theorems/b34a7ba2-b2f4-4e1e-a2c0-3773086d6d1e
-- title:
--   Data of the two-stage DRO problem (2) with the scenario-wise ambiguity set (3)
-- statement:
--   The data of the model are: the first-stage cost $a\in\mathbb R^l$ and the feasible set $\mathcal X\subseteq\mathbb R^l$ (an arbitrary set); the second-stage data $b,W,U,V,v^0$ of (1); the scenario data $R\in\mathbb R^{s\times K}$, $\nu\in\mathbb R^s$ of $\mathcal Q$; and for every scenario $k\in[K]$ the vectors $\mu^k,\delta^k,\underline z^k,\overline z^k\in\mathbb R^n$. The second-stage cost $g(x,z)$ of the data is the value of (1).
--
--   **Formalization Note** $[K]$ and $[n]$ are indexed from $0$. The structure carries no assumptions; they are collected in `Assumptions`.
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), §2.1, pp.6–7

import Mathlib
import Definitions.Def_SupermodDRO_secondStageCost

namespace SupermodDRO

/-- **The data of the two-stage DRO problem (2) with the scenario-wise ambiguity set (3).**
Long, Qi & Zhang, *Supermodularity in Two-Stage Distributionally Robust Optimization*, author
manuscript (June 2022), §2.1, pp.6–7:
* first stage: the cost vector `a ∈ ℝˡ` and the feasible set `𝒳 ⊆ ℝˡ` (any set) of (2);
* second stage (1): `b ∈ ℝᵐ`, `W ∈ ℝ^{r×l}`, `U ∈ ℝ^{r×m}`, `V ∈ ℝ^{r×n}`, `v⁰ ∈ ℝʳ`;
* scenario probabilities: `R ∈ ℝ^{s×K}`, `ν ∈ ℝˢ`, defining `𝒬 = {q | Rq ≤ ν, q ≥ 0}`;
* for each scenario `k ∈ [K]`: the mean `µᵏ`, the MAD bounds `δᵏ`, and the support bounds
  `z̲ᵏ, z̄ᵏ ∈ ℝⁿ`.

**Formalization Note** `[K]` and `[n]` are `Fin K` and `Fin n` (0-based). The structure carries no
assumptions; they are `SupermodDRO.Assumptions`. -/
structure Data (l m r n K s : ℕ) where
  a : Fin l → ℝ
  X : Set (Fin l → ℝ)
  b : Fin m → ℝ
  W : Matrix (Fin r) (Fin l) ℝ
  U : Matrix (Fin r) (Fin m) ℝ
  V : Matrix (Fin r) (Fin n) ℝ
  v0 : Fin r → ℝ
  R : Matrix (Fin s) (Fin K) ℝ
  ν : Fin s → ℝ
  μ : Fin K → Fin n → ℝ
  δ : Fin K → Fin n → ℝ
  zl : Fin K → Fin n → ℝ
  zu : Fin K → Fin n → ℝ

/-- The second-stage cost `g(x, z)` of (1) for the data `D`. -/
noncomputable def Data.g {l m r n K s : ℕ} (D : Data l m r n K s) (x : Fin l → ℝ)
    (z : Fin n → ℝ) : EReal :=
  secondStageCost D.W D.U D.V D.v0 D.b x z

end SupermodDRO


