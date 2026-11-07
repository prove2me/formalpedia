-- Prove2me | Definitions.Def_AvgPHETH_S2P
-- name    : AvgPHETH_S2P
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:31:04.531139+00:00
-- url     : https://prove2.me/theorems/cd6f7ca3-6b5b-4501-af67-2432eb3a09cf
-- title:
--   The class $\mathrm{S}_2\cdot\mathrm{P}^A$
-- statement:
--   $L\in\mathrm{S}_2\cdot\mathrm{P}^A$ if there are a predicate $B\in\mathrm{P}^A$ and a polynomial $p$ such that for every input $x$,
--
--   $$x\in L\implies\exists u\,\forall v\;B(x,u,v)=1,\qquad x\notin L\implies\exists v\,\forall u\;B(x,u,v)=0,$$
--
--   with $u,v\in\{0,1\}^{p(|x|)}$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.2, p.15 (PDF 17)

import Mathlib
import Definitions.Def_AvgPHETH_PolyPredO

namespace AvgPHETH

/-- `L ∈ S₂ · P^A` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.2, p.15 (PDF 17)): there are a predicate `B ∈ P^A` and a polynomial `p` such
that for every input `x`, `x ∈ L ⟹ ∃u ∀v B(x, u, v) = 1` and `x ∉ L ⟹ ∃v ∀u B(x, u, v) = 0`, with
`u, v ∈ {0,1}^{p(|x|)}`. -/
def S2P (A L : Set (List Bool)) : Prop :=
  ∃ (B : List (List Bool) → Prop) (p : Polynomial ℕ), PolyPredO A 3 B ∧ ∀ x : List Bool,
    (x ∈ L → ∃ u : List Bool, u.length = p.eval x.length ∧
      ∀ v : List Bool, v.length = p.eval x.length → B [x, u, v]) ∧
    (x ∉ L → ∃ v : List Bool, v.length = p.eval x.length ∧
      ∀ u : List Bool, u.length = p.eval x.length → ¬ B [x, u, v])

end AvgPHETH


