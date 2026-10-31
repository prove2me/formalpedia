-- Prove2me | Definitions.Def_KingTerrain_NPHard_PlanarSAT
-- name    : KingTerrain_NPHard_PlanarSAT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T23:51:44.355724+00:00
-- url     : https://prove2.me/theorems/a9796a51-becf-4e88-adab-87461f2468ed
-- title:
--   PLANAR 3-SAT with a variable cycle
-- statement:
--   A formula records a natural number of variables and a list of signed clauses in the shared Boolean CNF syntax. Well-formedness requires exactly three literal occurrences per clause and variable indices within range. Repeated occurrences are not prohibited. The variable labels specify the cyclic order.
--
--   The formula graph has one vertex for each variable, one for each clause, incidence edges for either polarity of an occurring variable, and the variable-cycle edges. It is planar when it has a crossing-free drawing by simple continuous arcs in the real plane, with distinct vertex positions and no vertex in an edge interior. No rectilinearity, uniform clause polarity or satisfiability certificate is hidden in planarity. For fewer than three variables the simple-graph cycle convention discards loops and repeated edges.
--
--   A binary code records the variable count, clause count, clause lengths and signed literal indices. The planar-SAT language contains precisely well-formed, planar, satisfiable formula codes; other words are rejected. Satisfiability is the shared ordinary Boolean assignment predicate, independent of the drawing.
-- source:
--   King and Krohn, Terrain Guarding is NP-Hard, DOI 10.1137/100791506, supplied PDF dated October 20, 2009, PDF p.2, Definition 1.

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace KingTerrain.NPHard

/-- Variable labels specify their cyclic order; the clauses use the shared signed CNF syntax. -/
structure Formula where
  vars : ℕ
  clauses : CookPvsNP.CNF

/-- Three literal occurrences per clause, with all variable indices in range. -/
def Formula.WellFormed (F : Formula) : Prop :=
  ∀ C ∈ F.clauses, C.length = 3 ∧ ∀ l ∈ C, l.2 < F.vars

/-- Directed data whose symmetric irreflexive closure is the formula graph.
Variables come first, then clause vertices. The cycle is not omitted. -/
def Formula.graphRelation (F : Formula)
    (u v : Fin (F.vars + F.clauses.length)) : Prop :=
  (u.val < F.vars ∧ v.val < F.vars ∧
    (u.val + 1 = v.val ∨ (u.val + 1 = F.vars ∧ v.val = 0))) ∨
  (u.val < F.vars ∧ F.vars ≤ v.val ∧
    ∃ l ∈ F.clauses.getD (v.val - F.vars) [], l.2 = u.val)

def Formula.graph (F : Formula) : SimpleGraph (Fin (F.vars + F.clauses.length)) :=
  SimpleGraph.fromRel F.graphRelation

/-- Actual crossing-free continuous-arc planarity of the graph including the variable cycle. -/
def Formula.Planar (F : Formula) : Prop :=
  WilliamsonShmoys.HasPlanarDrawingOn F.graph

/-- Binary counts, clause lengths and signed variable indices; no embedding or assignment is encoded. -/
def formulaCode (F : Formula) : List Bool :=
  OptimalQueuingComplexity.Restless.encNat F.vars ++
    OptimalQueuingComplexity.Restless.encNat F.clauses.length ++
    F.clauses.flatMap (fun C => OptimalQueuingComplexity.Restless.encNat C.length ++
      C.flatMap (fun l => l.1 :: OptimalQueuingComplexity.Restless.encNat l.2))

/-- Definition 1: ordinary satisfiability restricted by formula-graph planarity. -/
def planarSATLanguage : CookPvsNP.Lang Bool :=
  {w | ∃ F : Formula, w = formulaCode F ∧ F.WellFormed ∧ F.Planar ∧
    F.clauses.Satisfiable}

end KingTerrain.NPHard


