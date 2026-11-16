-- Prove2me | Definitions.Def_BeyondConvexity_APTAS_Supplement_LevelValidity
-- name    : BeyondConvexity_APTAS_Supplement_LevelValidity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:13:26.964906+00:00
-- url     : https://prove2.me/theorems/9d4982be-6fac-4b28-8262-391c181c68b8
-- title:
--   Dimensional level-separated partition validity
-- statement:
--   Use the published raw level/scale lists, with one level index per occurrence and a nonempty scale list indexed $0,\ldots,J$. Fix $\alpha=2^{-K}$ for an integer $K>0$ and $0<\beta,\gamma<1$. All scales are real, $s_0=1$ and $0<s_j\le1$. Every occurrence at level $j$ satisfies
--
--   $$\beta s_j<D(P),\qquad j\ge1\Longrightarrow D(P)\le\alpha s_j,$$
--
--   and $s_{j+1}=\gamma s_j$ for $1\le j<J$. Diameter is Euclidean in dimension $d$. There is no upper-diameter bound at the root, no geometric-decay requirement on the root transition, and no nonempty-level requirement. Empty input and $J=0$ are included. This defines only Definition 4, with none of Section 3's additional preprocessing conclusions.
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), Definition 4, printed p.6 / PDF p.7; Section 7, printed p.16 / PDF p.17

import Definitions.Def_BeyondConvexity_APTAS_Supplement_PolyhedralRegion
import Definitions.Def_BeyondConvexity_APTAS_LevelPartition

noncomputable section

namespace BeyondConvexity.APTAS.Supplement

/-- Definition 4 with Euclidean d-dimensional diameter. The raw partition and
scalar helpers are the published geometry-independent data, not planar Valid. -/
def LevelValid {d : ℕ} (p : LevelPartition ℝ) (I : Instance d) (α β γ : ℝ) : Prop :=
  PositiveDyadic α ∧ 0 < β ∧ β < 1 ∧ 0 < γ ∧ γ < 1 ∧
  p.scales ≠ [] ∧ p.levels.length = I.length ∧ p.scale 0 = 1 ∧
  (∀ j ≤ p.J, 0 < p.scale j ∧ p.scale j ≤ 1) ∧
  (∀ i : Fin I.length, p.level i ≤ p.J ∧
    β * p.scale (p.level i) < (I.get i).diameter ∧
    (1 ≤ p.level i → (I.get i).diameter ≤ α * p.scale (p.level i))) ∧
  ∀ j, 1 ≤ j → j < p.J → p.scale (j + 1) = γ * p.scale j

end BeyondConvexity.APTAS.Supplement


