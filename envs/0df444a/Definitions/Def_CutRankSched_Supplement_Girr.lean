-- Prove2me | Definitions.Def_CutRankSched_Supplement_Girr
-- name    : CutRankSched_Supplement_Girr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:49:14.553135+00:00
-- url     : https://prove2.me/theorems/6eabe925-7893-46c7-97fd-61306b2e7e1d
-- title:
--   The irredundant constraint graph $G_{\mathrm{irr}}=U(D_{\mathrm{cov}})\cup X^\circ$
-- statement:
--   The **irredundant constraint graph** is
--   $$
--   G_{\mathrm{irr}} = U(D_{\mathrm{cov}})\cup X^\circ ,
--   $$
--   the simple graph on the events whose edges are the pairs joined by an arc of the transitive reduction $D_{\mathrm{cov}}$ (in either direction) together with the residual edges.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.4, p.5

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Residual
import Definitions.Def_CutRankSched_Supplement_Dcov

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- The irredundant constraint graph `G_irr = U(D_cov) ∪ X°` (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.4, p.5): the underlying
undirected graph of the transitive reduction `D_cov`, together with the residual edges. -/
def Girr (I : Instance) : SimpleGraph (Fin I.n) :=
  SimpleGraph.fromRel fun i j => Dcov I i j ∨ Residual I i j

end Supplement

end CutRankSched


