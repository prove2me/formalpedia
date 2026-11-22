-- Prove2me | Definitions.Def_StableMSR_WindowSeparatorCuts
-- name    : StableMSR_WindowSeparatorCuts
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-22T23:34:41.43971+00:00
-- url     : https://prove2.me/theorems/6fa740ce-3add-4653-879e-11a3abdafed5
-- title:
--   Local compatibility on a bag and its separated graph components
-- statement:
--   A separator splits a finite constraint graph into its bag and disjoint nonadjacent pieces. Each component checks its interior plus its actual exterior boundary, reading boundary labels from the parent bag. Vertex domains and oriented pair constraints are arbitrary.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution gives explicit counted join records for the mission's real-distance RAM.

import Definitions.Def_StableMSR_WindowPorts
import Definitions.Def_StableMSR_WindowPlans
open scoped Classical
set_option autoImplicit false
namespace StableMSR.Recovery.WindowCuts
variable {V X : Type} [DecidableEq V]
def okay (G : SimpleGraph V) (D : V→Finset X) (test : V→V→X→X→Prop) (U : Finset V) (f : V→X) :=
  (∀v∈U,f v∈D v) ∧ ∀v∈U,∀w∈U,G.Adj v w → test v w (f v) (f w)
def total (T : Finset V) (K : Finset (Finset V)) := T∪K.biUnion id
noncomputable def rim (G : SimpleGraph V) (U C : Finset V) :=
  U.filter (fun v=>v∉C ∧ ∃w∈C,G.Adj w v)
noncomputable def patch (C : Finset V) (a b : V→X) (v : V) := if v∈C then b v else a v
end StableMSR.Recovery.WindowCuts


