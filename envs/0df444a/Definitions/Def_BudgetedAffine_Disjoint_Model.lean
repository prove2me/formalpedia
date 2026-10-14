-- Prove2me | Definitions.Def_BudgetedAffine_Disjoint_Model
-- name    : BudgetedAffine_Disjoint_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T21:16:03.975008+00:00
-- url     : https://prove2.me/theorems/1822ff21-ce66-48d6-9a7a-6aa743bfa407
-- title:
--   (4.1) — partition of [m] into blocks and the disjoint constrained budgeted set
-- statement:
--   **Disjoint constrained budgeted sets (4.1).** Let $S_1,\dots,S_L$ be a **partition** of $[m]=\{1,\dots,m\}$: pairwise disjoint sets whose union is $[m]$. For weights $w_{\ell i}$ ($\ell\in[L]$, $i\in[m]$), the disjoint constrained budgeted set is
--   $$\mathcal U=\Big\{h\in[0,1]^m\ :\ \sum_{i\in S_\ell}w_{\ell i}h_i\le 1\ \ \forall \ell\in[L]\Big\}.$$
--   It is the Cartesian product of $L$ budget of uncertainty sets, one on each block, and generalizes the single budget set (1.2) (the case $L=1$). It is the uncertainty set of every statement of this mission; the two-stage problem (1.1), the values $z_{AR}$, $z_{Aff}$ and the covering value (3.2) are the shared definitions of this series.
--
--   **Formalization Note** Vectors are functions on `Fin m` with the componentwise order; Lean index $i$ is the paper's $i+1$, and Lean block $\ell$ is the paper's $\ell+1$. The partition predicate allows empty blocks, which only add the constraint $0\le1$ and leave $\mathcal U$ unchanged. The hypotheses $w_{\ell i}\in[0,1]$ and that $S$ is a partition are not part of the definitions; each theorem states them.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, (4.1) p. 14

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model

namespace BudgetedAffine.Disjoint

open Matrix

/-- `S₁, …, S_L` is a partition of `[m]`: the blocks are pairwise disjoint and cover every
index (empty blocks are allowed). -/
def IsPartition {m L : ℕ} (S : Fin L → Finset (Fin m)) : Prop :=
  (∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (S ℓ) (S ℓ')) ∧ ∀ i, ∃ ℓ, i ∈ S ℓ

/-- The disjoint constrained budgeted set (4.1):
`{h ∈ [0,1]ᵐ | ∑_{i ∈ S_ℓ} w_{ℓi} hᵢ ≤ 1 for every ℓ}`. -/
def disjointBudgetSet {m L : ℕ} (S : Fin L → Finset (Fin m)) (w : Fin L → Fin m → ℝ) :
    Set (Fin m → ℝ) :=
  {h | (∀ i, 0 ≤ h i ∧ h i ≤ 1) ∧ ∀ ℓ, ∑ i ∈ S ℓ, w ℓ i * h i ≤ 1}

end BudgetedAffine.Disjoint


