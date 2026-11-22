-- Prove2me | Definitions.Def_StableMSR_WindowJoinTemplates
-- name    : StableMSR_WindowJoinTemplates
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-22T22:38:07.030633+00:00
-- url     : https://prove2.me/theorems/70366396-edb7-44b7-a5b0-1cac0690c166
-- title:
--   Uncompressed bag productions and their rectangular size
-- statement:
--   A raw derivation chooses a bag label, agrees across both separators, and adds the local and two child contributions. The template slot count ranges over all triples of potential labels and both child counts before any filtering.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix A.6 (tree-decomposition dynamic programming over regional windows), in the mission’s real-distance RAM model.

import Definitions.Def_StableMSR_WindowJoins
import Definitions.Def_StableMSR_WindowPlans
open StableMSR.Recovery StableMSR.Recovery.TreeDP
set_option autoImplicit false
namespace StableMSR.Recovery.WindowJoins
/-- Uncompressed bag derivations retain every feasible local combination through the count cap. -/
inductive Raw {V X : Type} [DecidableEq V] (cap : ℕ) : Plan V X→(V→X)→ℕ→ℝ→Prop where
  | leaf (d : BagData V X) (a : V→X) : a∈d.choices → d.valid a → d.count a≤ cap →
      Raw cap (.leaf d) a (d.count a) (d.weight a)
  | join (d : BagData V X) {L R : Plan V X} (a b c : V→X) {i j : ℕ} {s t : ℝ} :
      a∈d.choices → d.valid a → AgreeOn (d.bag∩L.root.bag) a b → AgreeOn (d.bag∩R.root.bag) a c →
      Raw cap L b i s → Raw cap R c j t → d.count a+i+j≤ cap →
      Raw cap (.branch d L R) a (d.count a+i+j) (d.weight a+s+t)
/-- Number of rectangular production slots before checking any separator, count, or optimization predicate. -/
def templateSlots {V X : Type} (cap : ℕ) : Plan V X→ℕ
  | .leaf d=>d.choices.card
  | .branch d L R=>d.choices.card*L.root.choices.card*R.root.choices.card*(cap+1)^2+
    templateSlots cap L+templateSlots cap R
end StableMSR.Recovery.WindowJoins


