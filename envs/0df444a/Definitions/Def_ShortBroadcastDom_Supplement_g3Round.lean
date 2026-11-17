-- Prove2me | Definitions.Def_ShortBroadcastDom_Supplement_g3Round
-- name    : ShortBroadcastDom_Supplement_g3Round
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:42:11.421198+00:00
-- url     : https://prove2.me/theorems/59a35406-f21c-4979-b627-e701ae8836b1
-- title:
--   The rounding of App. G.3: $W$, $R$, $h$, $H$, $U$, the requests and $D$
-- statement:
--   With $F,Z,K,c$ as in the transformation of App. G.3, let $x\in[0,1]^K$, extended by zero outside $K$. With open neighbourhoods $N(\cdot)$, the rounding is
--
--   $$
--   \begin{aligned}
--   W&=\{v\in B: x_v>2/3\}, & R&=Z\setminus N(W), & h(v)&=|N(v)\cap R|,\\
--   H&=\{v\in K\setminus W: h(v)\ge3\}, & Y&=R\cap N(H), & U&=R\setminus Y.
--   \end{aligned}
--   $$
--
--   Every vertex of $U$ without a neighbour in $F$ requests its neighbour of smallest identifier, and $D$ is the union of $W\cup H$ and the requested vertices. The algorithm outputs $F\cup D$. The cost of $x$ is $\mathcal C(x)=\sum_{v\in K}c(v)x_v$.
--
--   **Formalization Note** A vertex $v$ is requested by $u$ when $v$ is a neighbour of $u$ whose identifier is at most that of every neighbour of $u$; with distinct identifiers this is the neighbour of smallest identifier. $D$ depends on the identifiers.
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), App. G.3, p.97 (PDF p.100)

import Mathlib
import Definitions.Def_ShortBroadcastDom_Supplement_g3Sel

namespace ShortBroadcastDom.Supplement

/-! The rounding of App. G.3, p.97 (PDF 100) of Amiri, Siebertz, Wawrzyniak, *Paying for Fractional
Error* (arXiv:2611.02057, sha256 prefix f4dc98d2): "Let x ∈ [0, 1]^K be a feasible fractional
solution, extended by zero outside K. The rounding is the rule of Section F.1 with Π = B, threshold
t = 2/3, and three in place of n0 in Step 2, except that a demand with a neighbor in F requests
nothing in Step 3: W = {v ∈ B : xv > 2/3}, R = Z \ N(W), h(v) = |N(v) ∩ R|,
H = {v ∈ K \ W : h(v) ≥ 3}, Y = R ∩ N(H), U = R \ Y. Every vertex of U without a neighbor in F
requests its neighbor of smallest identifier, and D is the union of W ∪ H and the requested
vertices. The output is F ∪ D." Here `N(·)` is the open neighbourhood. -/

open Classical in
/-- Step 1: `W = {v ∈ B : x_v > 2/3}`. -/
noncomputable def g3W {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) : Finset V :=
  (branchSet G).filter fun v => 2 / 3 < x v

open Classical in
/-- `R = Z \ N(W)`: the demands without a neighbour in `W` (a vertex of `W` may lie in `R`). -/
noncomputable def g3R {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) : Finset V :=
  (g3Z G).filter fun r => ∀ w ∈ g3W G x, ¬ G.Adj r w

/-- `h(v) = |N(v) ∩ R|`. -/
noncomputable def g3h {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) (v : V) : ℕ :=
  (G.neighborFinset v ∩ g3R G x).card

open Classical in
/-- Step 2: `H = {v ∈ K \ W : h(v) ≥ 3}`. -/
noncomputable def g3H {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) : Finset V :=
  (g3K G \ g3W G x).filter fun v => 3 ≤ g3h G x v

open Classical in
/-- `U = R \ Y` with `Y = R ∩ N(H)`: the remaining demands without a neighbour in `H`. -/
noncomputable def g3U {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) : Finset V :=
  (g3R G x).filter fun r => ∀ v ∈ g3H G x, ¬ G.Adj r v

open Classical in
/-- Step 3: the requested vertices. Every `u ∈ U` without a neighbour in `F` requests its neighbour
of smallest identifier.

**Formalization Note** `v` is requested by `u` iff `v` is a neighbour of `u` and `id v ≤ id w` for
every neighbour `w` of `u`; with injective identifiers this is the unique neighbour of smallest
identifier. -/
noncomputable def g3Req {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (id : V → ℕ) (x : V → ℝ) : Finset V :=
  Finset.univ.filter fun v => ∃ u ∈ g3U G x, (∀ f ∈ g3F G, ¬ G.Adj u f) ∧ G.Adj u v ∧
    ∀ w, G.Adj u w → id v ≤ id w

/-- **The rounded set `D` of App. G.3**: `W ∪ H` and the requested vertices (the algorithm outputs
`F ∪ D`). It depends on the identifiers through the requests. -/
noncomputable def g3D {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (id : V → ℕ) (x : V → ℝ) : Finset V :=
  g3W G x ∪ g3H G x ∪ g3Req G id x

/-- The cost `C(x) = ∑_{v ∈ K} c(v) x_v` (p.96). -/
noncomputable def g3CostOf {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) : ℝ :=
  ∑ v ∈ g3K G, g3Cost G v * x v

end ShortBroadcastDom.Supplement


