-- Prove2me | Definitions.Def_MaxEntOCRS_schemeLaw
-- name    : MaxEntOCRS_schemeLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:34:53.83121+00:00
-- url     : https://prove2.me/theorems/03fd6019-6034-48a9-87d6-682ade280ccd
-- title:
--   Law of the scheme's matching after an arrival order $\sigma$
-- statement:
--   Starting from a matching drawn from $\mu$, the simulate-then-replace scheme processes the edges of an arrival order $\sigma = (e_1, e_2, \ldots)$ one at a time. This is the law of its matching after all of $\sigma$ has arrived, obtained by composing the one-step law transforms. When $\sigma$ lists every edge once, it is the law of the output, the set of edges accepted at their arrival; the selection probability of $e$ is the marginal of $e$ under this law.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_schemeStep

namespace MaxEntOCRS

/-- The law of the matching held by the simulate-then-replace scheme (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4) after the
edges of the arrival order `σ` have arrived, starting from a matching drawn from `μ`. When `σ`
lists every edge once, this is the law of the output (the set of edges accepted at their
arrival), and the selection probability of `e` is its edge marginal. -/
noncomputable def schemeLaw {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ) (μ : Finset E → ℝ)
    (σ : List E) : Finset E → ℝ :=
  σ.foldl (fun p e => schemeStep G x μ e p) μ

end MaxEntOCRS


