-- Prove2me | Definitions.Def_ShortBroadcastDom_firstSel
-- name    : ShortBroadcastDom_firstSel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:43.877614+00:00
-- url     : https://prove2.me/theorems/7e934178-2e41-4cfb-b417-a973acd6be6b
-- title:
--   First selection of the integer case: defects $B$, $F=V\setminus N_G[B]$, $R_0=V\setminus N_G[F]$, costs $c(v)=b-|N_G(v)\cap F|$
-- statement:
--   Let $d=2a$ be an integer and $b=d+1$. A vertex is a **defect** if its degree differs from $d$; let $B$ be the set of defects. The first selection is
--
--   $$
--   F=V(G)\setminus N_G[B],
--   $$
--
--   the vertices that have degree $d$ and all of whose neighbours have degree $d$. The remaining demands are $R_0=V(G)\setminus N_G[F]$, every vertex outside $F$ is a candidate, and a candidate $v\notin F$ gets the cost
--
--   $$
--   c(v)=b-|N_G(v)\cap F|,
--   $$
--
--   the budget left after paying one unit per neighbour in $F$. The rounding rule of §7.1 is then applied in $G$ with candidate set $V(G)\setminus F$, demands $R_0$, costs $c$ and $a=d/2$.
--
--   **Formalization Note** The cost is computed in $\mathbb R$, so no truncated subtraction occurs; it is only read on candidates $v\notin F$.
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §7.2, p.45 (PDF p.48)

import Mathlib
import Definitions.Def_ShortBroadcastDom_closedNbhd
import Definitions.Def_ShortBroadcastDom_RoundingData

namespace ShortBroadcastDom

/-- The defects `B = {v : deg_G(v) ≠ d}` for the integer `d = 2a` (§7.2, p.45, PDF 48: "Let B be
the set of defects, the vertices of degree different from d"). -/
def defects {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) : Finset V :=
  Finset.univ.filter fun v => G.degree v ≠ d

/-- **The first selection of the integer case**, §7.2, p.45 (PDF 48) of Amiri, Siebertz,
Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix f4dc98d2):
"Assume first that d = 2a is an integer … Select F = V(G) \ N_G[B]." A vertex is in `F` exactly
when it and all its neighbours have degree `d`. -/
def firstSel {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) : Finset V :=
  Finset.univ.filter fun v => ∀ u ∈ defects G d, v ∉ closedNbhd G u

/-- The remaining demands `R₀ = V(G) \ N_G[F]` (§7.2, p.45): the vertices neither in `F` nor
adjacent to it. -/
def remDemands {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) : Finset V :=
  Finset.univ.filter fun v => ∀ u ∈ firstSel G d, v ∉ closedNbhd G u

/-- The candidate costs `c(v) = b − |N_G(v) ∩ F|` with `b = d + 1` (§7.2, p.45: "c(v) = b −
|N_G(v) ∩ F| (v ∉ F)").

**Formalization Note** The cost is computed in `ℝ`, so no truncated subtraction occurs; it is
used only on candidates `v ∉ F` (its value on `F` is irrelevant). -/
noncomputable def selCost {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) (v : V) : ℝ :=
  ((d : ℝ) + 1) - ((G.neighborFinset v ∩ firstSel G d).card : ℝ)

/-- The rounding data of the integer case, §7.2, p.46 (PDF 49): "we use the rounding rule in G
with C = V(G) \ F", demands `R₀`, the costs `c` of `selCost`, and `a = d/2` (so `b = d + 1`), for
a fractional vector `x` on `V(G) \ F`. -/
noncomputable def selRounding {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) (x : V → ℝ) : RoundingData V where
  a := (d : ℝ) / 2
  C := Finset.univ \ firstSel G d
  R0 := remDemands G d
  c := selCost G d
  x := x

end ShortBroadcastDom


