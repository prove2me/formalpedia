-- Prove2me | Definitions.Def_GeoQAC_lmv
-- name    : GeoQAC_lmv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:53.433863+00:00
-- url     : https://prove2.me/theorems/ddf33c73-f6b8-447a-b97f-ba95f38a8733
-- title:
--   Local measurement variance $\Gamma(\rho)$
-- statement:
--   The **local measurement variance** of a state $\rho$ on the grid $\Lambda=[w]\times[h]$ is
--   $$
--   \Gamma(\rho)=\max_{\mathcal R,(H_i),(c_i)} \mathrm{Var}_\rho\Big(\sum_{i=1}^m c_i H_i\Big).
--   $$
--   The maximum ranges over families $\mathcal R=\{R_1,\dots,R_m\}$ of nonempty regions $R_i\subseteq\Lambda$, each connected in the two-dimensional nearest-neighbour graph, with pairwise disjoint column projections $I(R_i)$; Hermitian contractions $H_i$ (Hermitian, operator norm at most $1$) supported on $R_i$; and real coefficients with $\sum_i c_i^2=1$.
--
--   $\Gamma$ measures correlations between measurements on column-separated regions. Product states have $\Gamma\le 1$, cat states have $\Gamma\ge n/w$, and one layer of a 2D-QAC circuit increases $\Gamma$ by at most a factor $O(w^3)$; this potential drives the width lower bounds.
--
--   **Formalization Note** The norm is the L2 operator (spectral) norm. The maximum is written as the real supremum of the set of attained variances. On a pure state this set is bounded above by $h$ and nonempty on a nonempty grid (both proved in a sanity check), so the supremum is the least upper bound; on the empty grid $\Gamma=0$.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Definition 3.2, p.14

import Mathlib
import Definitions.Def_GeoQAC_Pos
import Definitions.Def_GeoQAC_IsSupportedOn
import Definitions.Def_GeoQAC_var

namespace GeoQAC

open scoped Matrix.Norms.L2Operator

/-!
# Local measurement variance `Γ`

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), Definition 3.2, p.14:
`Γ(ρ) = max Var_ρ(∑_{i=1}^m c_i H_i)`, the maximum over families `R = {R_1, …, R_m}` of nonempty
connected regions with pairwise disjoint column projections `I(R_i)`; Hermitian contractions `H_i`
supported on `R_i`; and real coefficients with `∑_i c_i² = 1`.

**Formalization Note.**
* `‖·‖` is the L2 operator (spectral) norm on matrices (`Matrix.Norms.L2Operator`); a Hermitian
  contraction is a Hermitian matrix of operator norm `≤ 1` (§2.2, p.10).
* "Supported on `R_i`" is `IsSupportedOn` (`H_i = K ⊗ I`).
* The maximum is written as the real supremum `sSup` of the set of attained variances. For a state
  `ρ` this set is bounded above (`Var ≤ (∑|c_i|)² ≤ m ≤ h`), so `sSup` is its least upper bound; it
  is empty only when the grid is empty (then `Γ = 0`, the variance of every observable on the
  one-dimensional space being `0` anyway). Γ is defined for every density matrix `ρ`; for a pure
  state it is applied to `ObliviousRSP.pureState ψ`.
-/

variable {w h : ℕ}

/-- The values `Var_ρ(∑_i c_i H_i)` over admissible families (Definition 3.2, p.14). -/
def lmvSet (ρ : Matrix (Pos w h → Bool) (Pos w h → Bool) ℂ) : Set ℝ :=
  {t | ∃ (m : ℕ) (R : Fin m → Finset (Pos w h))
      (H : Fin m → Matrix (Pos w h → Bool) (Pos w h → Bool) ℂ) (c : Fin m → ℝ),
      (∀ i, IsConnectedRegion (R i)) ∧
      Pairwise (fun i j => Disjoint (colProj (R i)) (colProj (R j))) ∧
      (∀ i, (H i).IsHermitian ∧ ‖H i‖ ≤ 1 ∧ IsSupportedOn (R i) (H i)) ∧
      ∑ i, c i ^ 2 = 1 ∧
      t = var ρ (∑ i, (c i : ℂ) • H i)}

/-- The local measurement variance `Γ(ρ)` of a state on the grid `[w] × [h]`
(Definition 3.2, p.14). -/
noncomputable def lmv (ρ : Matrix (Pos w h → Bool) (Pos w h → Bool) ℂ) : ℝ :=
  sSup (lmvSet ρ)

end GeoQAC


