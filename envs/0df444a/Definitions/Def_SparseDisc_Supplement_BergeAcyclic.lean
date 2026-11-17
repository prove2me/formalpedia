-- Prove2me | Definitions.Def_SparseDisc_Supplement_BergeAcyclic
-- name    : SparseDisc_Supplement_BergeAcyclic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:02:26.739847+00:00
-- url     : https://prove2.me/theorems/78eaca1e-2857-43fb-b42f-053e370295a5
-- title:
--   Berge-acyclic support pattern
-- statement:
--   A support pattern is **Berge-acyclic** when its bundle incidence graph is a forest.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Definition 2.3, p.12

import Mathlib
import Definitions.Def_SparseDisc_Supplement_incidenceGraph

namespace SparseDisc.Supplement

/-- A support family is **Berge-acyclic** when its bundle incidence graph is a forest
(Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission
manuscript (sha256 0f09ec60…25b81), Definition 2.3, p.12). -/
def BergeAcyclic {V ι : Type} [Fintype V] [DecidableEq V] [Fintype ι]
    (U : V → Finset ι) : Prop :=
  (incidenceGraph U).IsAcyclic

end SparseDisc.Supplement


