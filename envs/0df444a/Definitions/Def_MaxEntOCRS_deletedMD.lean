-- Prove2me | Definitions.Def_MaxEntOCRS_deletedMD
-- name    : MaxEntOCRS_deletedMD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:32:32.176451+00:00
-- url     : https://prove2.me/theorems/de91f04b-11df-4c79-8bd7-1c2fb49561b3
-- title:
--   Monomer–dimer measure of $G' = G - u - v$
-- statement:
--   The monomer–dimer measure of $G' = G - u - v$, viewed on the edge sets of $G$: a matching $M$ of $G$ covering neither $u$ nor $v$ has probability $Z(G')^{-1}\prod_{e\in M} t_e$, and every other edge set has probability $0$.
--
--   **Formalization Note** This is the same measure as on the induced subgraph on $V \setminus \{u, v\}$, encoded without a subgraph type.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 3, p.5

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_mdWeight
import Definitions.Def_MaxEntOCRS_Covers
import Definitions.Def_MaxEntOCRS_deletedPartitionFn

namespace MaxEntOCRS

open Classical in
/-- The monomer–dimer measure of `G′ = G − u − v` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §3, p.5: "Let M′ be drawn from the
monomer–dimer measure of G′").

**Formalization Note** Encoded as the monomer–dimer weight restricted to the matchings of `G`
that cover neither `u` nor `v`, normalized by `Z(G′)`; this is the same measure as on the
induced subgraph on `V ∖ {u, v}`. -/
noncomputable def deletedMD {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (u v : V) : Finset E → ℝ :=
  fun M => (if ¬ Covers G M u ∧ ¬ Covers G M v then mdWeight G t M else 0) /
    deletedPartitionFn G t u v

end MaxEntOCRS


