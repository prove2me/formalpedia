-- Prove2me | Definitions.Def_DynamicOnlineLP_DLA_Supplement_MultiInstance
-- name    : DynamicOnlineLP_DLA_Supplement_MultiInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:07:15.370901+00:00
-- url     : https://prove2.me/theorems/fe9e9fa3-4573-4570-a542-219435fa6944
-- title:
--   Instance of the general online LP (3): reward vectors, consumption blocks, offline optimum over the simplex
-- statement:
--   An **instance of the general online linear program (3)** consists of $n$ arrivals, $m$ resources and $k$ options per arrival, with reward vectors $f_t\in\mathbb R^k$, $f_t\ge0$, consumption vectors $g_{it}\in[0,1]^k$ and a right-hand side $b\in\mathbb R^m$. With $K=\{x\in\mathbb R^k:x\ge0,\ e^{\top}x\le1\}$, its offline optimum is
--
--   $$\mathrm{OPT}=\max\Big\{\sum_{t=1}^nf_t^{\top}x_t:\ \sum_{t=1}^ng_{it}^{\top}x_t\le b_i\ (i=1,\dots,m),\ \ x_t\in K\ (t=1,\dots,n)\Big\}.$$
--
--   The instance is in general position when the set of all $n$ arrivals is. For a permutation $\sigma$, the block $(f_{\sigma(t)},g_{1\sigma(t)},\dots,g_{m\sigma(t)})$ arrives as a whole at time $t$; the $k$ options of one arrival are never separated.
--
--   This is the multidimensional model of the paper, whose special case $k=1$ is the online LP (2).
--
--   **Formalization Note** The benchmark ranges over all fractional points of $K$, not only its vertices. Arrival times are 0-based. The right-hand side is unrestricted in the structure; theorems that use the optimum assume $b\ge0$.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 877, Eq. (3) and Assumptions 1–2

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_SimplexPackingLP
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_SurplusRule
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_GeneralPosition

namespace DynamicOnlineLP.DLA.Supplement

/-- An instance of the general online LP (3): `n` blocks, block `t` carrying a reward vector
`f_t ∈ ℝ^k`, `f_t ≥ 0`, and consumption vectors `g_{ti} ∈ [0,1]^k` for the `m` resources, and a
right-hand side `b ∈ ℝ^m`. -/
structure MultiInstance (m n k : ℕ) where
  f : Fin n → Fin k → ℝ
  g : Fin n → Fin m → Fin k → ℝ
  b : Fin m → ℝ
  f_nonneg : ∀ (t : Fin n) (j : Fin k), 0 ≤ f t j
  g_nonneg : ∀ (t : Fin n) (i : Fin m) (j : Fin k), 0 ≤ g t i j
  g_le_one : ∀ (t : Fin n) (i : Fin m) (j : Fin k), g t i j ≤ 1

/-- `OPT`: the value of the offline LP (3)/(15) over all fractional decisions in the simplex. -/
noncomputable def MultiInstance.OPT {m n k : ℕ} (I : MultiInstance m n k) : ℝ :=
  blockOptValue (Finset.univ : Finset (Fin n)) I.f I.g I.b

/-- General position of the whole input. -/
def MultiInstance.GeneralPosition {m n k : ℕ} (I : MultiInstance m n k) : Prop :=
  BlockGeneralPositionOn (Finset.univ : Finset (Fin n)) I.f I.g

/-- Reward vectors in arrival order `σ`: block `σ t` arrives as a whole at 0-based time `t`. -/
def MultiInstance.arrF {m n k : ℕ} (I : MultiInstance m n k) (σ : Equiv.Perm (Fin n)) :
    Fin n → Fin k → ℝ :=
  fun t => I.f (σ t)

/-- Consumption blocks in arrival order `σ`. -/
def MultiInstance.arrG {m n k : ℕ} (I : MultiInstance m n k) (σ : Equiv.Perm (Fin n)) :
    Fin n → Fin m → Fin k → ℝ :=
  fun t => I.g (σ t)

end DynamicOnlineLP.DLA.Supplement


