-- Prove2me | Definitions.Def_PigeonholeDesign_Upper_Supplement_Clusters
-- name    : PigeonholeDesign_Upper_Supplement_Clusters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:59:40.880459+00:00
-- url     : https://prove2.me/theorems/61e63651-0a49-4607-a9bc-3fe7773e4faa
-- title:
--   §6.3.3, pp. 27–28 — clustered arrival sequences $\bigcup_{n\le N}\mathcal C(v_n,T^{-\gamma})$ and Theorem 10's pigeonholes
-- statement:
--   Let there be $p$ continuous covariates and no discrete ones, so covariates lie in $[0,1]^p$. For a centre $v\in[0,1]^p$ and $\gamma>0$, the **cluster**
--   $$\mathcal C(v,T^{-\gamma})=\{u:\ \|u-v\|_\infty\le\tfrac12T^{-\gamma}\}$$
--   is the cube of edge $T^{-\gamma}$ centred at $v$ (p. 27). An arrival sequence $x=(x_1,\dots,x_T)$ is **clustered with $N$ clusters of diameter $T^{-\gamma}$** if there are centres $v_1,\dots,v_N\in[0,1]^p$ with
--   $$x_t\in\bigcup_{n=1}^N\mathcal C(v_n,T^{-\gamma})\qquad\text{for every }t.$$
--
--   For Theorem 10 (p. 28) the paper sets $\zeta=\frac1p+\frac{p-1}p\gamma$ and uses the grid pigeonholes $\{[0,c^\zeta T^{-\zeta}),[c^\zeta T^{-\zeta},2c^\zeta T^{-\zeta}),\dots,[1-c^\zeta T^{-\zeta},1]\}^p$ with $c>1$. The number of cells per axis is $m=\lceil c^{-\zeta}T^{\zeta}\rceil$, so every cell has edge $1/m\le c^\zeta T^{-\zeta}$.
--
--   These objects describe arrival sequences concentrated near a few unknown points, where an online design can do much better than in the worst case.
--
--   **Formalization Note** `IsClustered N γ x` bundles the box constraint $x_t\in[0,1]^p$ with the existence of centres `v : Fin N → Fin p → ℝ` in $[0,1]^p$ such that every $x_t$ is within $T^{-\gamma}/2$ of some centre in every coordinate. Arrival sequences live in `MultiDim.Cov 0 p` (no discrete coordinates). `zeta p γ` is $\zeta$ and `clusterCells c ζ T` is $\lceil c^{-\zeta}T^\zeta\rceil$, the ceiling reading of the printed cell edge used by the published Theorem 9; the pigeonholes are the published `MultiDim.gridHole (clusterCells c ζ T)`, whose last cell on each axis is closed.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. 27 (definition of C(v, T^{-γ}) and clustered sequences) and p. 28, Theorem 10 (ζ and the pigeonholes)

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting

namespace PigeonholeDesign.Upper.Supplement

/-- §6.3.3, p. 27: with `p` continuous and no discrete coordinates, an arrival sequence
`x : Fin T → [0,1]^p` is clustered with `N` clusters of diameter `T^{-γ}` if there are centres
`v₁, …, v_N ∈ [0,1]^p` such that every `x_t` lies in some cube
`C(v_n, T^{-γ}) = {u : ‖u - v_n‖_∞ ≤ T^{-γ}/2}`. -/
def IsClustered {p T : ℕ} (N : ℕ) (γ : ℝ) (x : Fin T → PigeonholeDesign.MultiDim.Cov 0 p) :
    Prop :=
  (∀ t j, x t (Sum.inr j) ∈ Set.Icc (0 : ℝ) 1) ∧
    ∃ v : Fin N → Fin p → ℝ, (∀ n j, v n j ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ t, ∃ n, ∀ j, |x t (Sum.inr j) - v n j| ≤ (T : ℝ) ^ (-γ) / 2

/-- Theorem 10, p. 28: the exponent `ζ = 1/p + (p-1)/p · γ`. -/
noncomputable def zeta (p : ℕ) (γ : ℝ) : ℝ := 1 / (p : ℝ) + ((p : ℝ) - 1) / p * γ

/-- Theorem 10's cells per axis: the pigeonholes `[0, c^ζ T^{-ζ}), …, [1 - c^ζ T^{-ζ}, 1]` read with
`m = ⌈c^{-ζ} T^{ζ}⌉` cells, so that each cell has edge `1/m ≤ c^ζ T^{-ζ}`. -/
noncomputable def clusterCells (c ζ : ℝ) (T : ℕ) : ℕ := ⌈c ^ (-ζ) * (T : ℝ) ^ ζ⌉₊

end PigeonholeDesign.Upper.Supplement


