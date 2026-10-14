-- Prove2me | Definitions.Def_BudgetedAffine_Budget_Rescaling
-- name    : BudgetedAffine_Budget_Rescaling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:11.042245+00:00
-- url     : https://prove2.me/theorems/2af6f574-dd33-4974-a9b0-bc43213bdb93
-- title:
--   Sec. 3.3, (3.6)–(3.7) — the rescaled covering data d̂, B̂ and dual feasibility for (3.7)
-- statement:
--   The rescaled covering problem used in the proof of the structural result (Lemma 3.3). Let $B\in\mathbb R^{m\times n}_+$, $d\in\mathbb R^n_+$, $\mathcal J\subseteq[m]$, weights $w_i$ and numbers $\eta,\gamma$ be given. For each column $j$ let $M_j=\max_{k\in\mathcal J}(w_kB_{kj})$ and define
--   $$\hat d_j=\frac{d_j}{\eta\gamma\,M_j},\qquad \hat B_{ij}=\frac{w_iB_{ij}}{M_j}\quad(i\in\mathcal J),$$
--   with $\hat B_{ij}=0$ for $i\notin\mathcal J$. For $\mathcal W\subseteq\mathcal J$ the rescaled covering problem (3.6) is
--   $$\hat z(\mathcal W)=\min_{y\ge0}\Big\{\hat d^Ty\ :\ \hat By\ge\sum_{i\in\mathcal W}w_ie_i\Big\},$$
--   which is the covering value of (3.2) with data $(\hat B,\hat d)$ and requirement $\sum_{i\in\mathcal W}w_ie_i$. A vector $z$ is **feasible for the packing problem (3.7)**
--   $$\hat\Delta_{\mathcal J}=\max_{z\ge0}\Big\{\sum_{i\in\mathcal J}w_iz_i\ :\ \sum_{i\in\mathcal J}\hat B_{ij}z_i\le\hat d_j\ \ \forall j\in[n]\Big\}$$
--   when $z_i\ge0$ for $i\in\mathcal J$ and every column constraint holds.
--
--   **Formalization Note** $M_j$ is a supremum over the finite set $\mathcal J$ (equal to $0$ when $\mathcal J=\emptyset$). For a column with $M_j=0$ Lean's division by zero gives $\hat d_j=\hat B_{ij}=0$; under $w_i>0$ on $\mathcal J$ such a column has $B_{ij}=0$ for all $i\in\mathcal J$ and cannot cover any row of $\mathcal J$, so this convention does not change any covering value over $\mathcal W\subseteq\mathcal J$.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Sec. 3.3, definitions of d̂, B̂ and (3.6), p. 12, (3.7), p. 12

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model

namespace BudgetedAffine.Budget

open Matrix

/-- `max_{k ∈ J} (w_k B_kj)` for column `j` (a supremum over the finite set `J`; it is `0`
when `J = ∅`). -/
noncomputable def colMax {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ)
    (J : Finset (Fin m)) (j : Fin n) : ℝ :=
  ⨆ k : J, w k * B k j

/-- `d̂ⱼ = dⱼ / (η γ · max_{k ∈ J} (w_k B_kj))` of Sec. 3.3 (Lean's `x / 0 = 0` gives `0`
for a column with `max_{k ∈ J} (w_k B_kj) = 0`). -/
noncomputable def dHat {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
    (w : Fin m → ℝ) (J : Finset (Fin m)) (η γ : ℝ) : Fin n → ℝ :=
  fun j => d j / (η * γ * colMax B w J j)

/-- `B̂ᵢⱼ = wᵢ Bᵢⱼ / max_{k ∈ J} (w_k B_kj)` for `i ∈ J` (rows outside `J` are `0`). -/
noncomputable def BHat {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ)
    (J : Finset (Fin m)) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => if i ∈ J then w i * B i j / colMax B w J j else 0

/-- The requirement vector `∑_{i ∈ W} wᵢ eᵢ` of (3.6). -/
def wIndic {m : ℕ} (w : Fin m → ℝ) (W : Finset (Fin m)) : Fin m → ℝ :=
  fun i => if i ∈ W then w i else 0

/-- Feasibility for the packing problem (3.7):
`z_i ≥ 0` for `i ∈ J` and `∑_{i ∈ J} B̂ᵢⱼ zᵢ ≤ d̂ⱼ` for every column `j`. -/
def DualFeasible {m n : ℕ} (Bh : Matrix (Fin m) (Fin n) ℝ) (dh : Fin n → ℝ)
    (J : Finset (Fin m)) (z : Fin m → ℝ) : Prop :=
  (∀ i ∈ J, 0 ≤ z i) ∧ ∀ j, ∑ i ∈ J, Bh i j * z i ≤ dh j

end BudgetedAffine.Budget


