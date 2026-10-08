-- Prove2me | Definitions.Def_OnlineStochMatching_SuggestedMatching_Cut
-- name    : OnlineStochMatching_SuggestedMatching_Cut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:47:36.00698+00:00
-- url     : https://prove2.me/theorems/7f7796b3-f416-42e6-b094-297decccb1b3
-- title:
--   Canonical residual reachability cut
-- statement:
--   For a selected integral maximum flow $M$, its canonical cut places an advertiser or impression type on the source side when it is reachable from the source in the residual network. The residual steps relevant to this reachability are source-to-unsaturated-advertiser, advertiser-to-type along an unused edge, and type-to-advertiser along a selected edge. Write $A_T$ for the advertisers outside the reachable side and $I_S$ for the reachable types.
--
--   $$A_T=\{a:\text{$a$ is not residual-reachable}\},\qquad I_S=\{i:\text{$i$ is residual-reachable}\}.$$
--
--   These sets are the paper's guide for bounding the optimum of each realized graph.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 5, §4.1, Bounding OPT

import Definitions.Def_OnlineStochMatching_SuggestedMatching_Instance

namespace OnlineStochMatching.SuggestedMatching

variable {A I : Type} [Fintype A] [Fintype I]

/-- Residual reachability among the source, advertisers and types after sending
the integral flow represented by `M`. -/
noncomputable def ResidualStep (inst : Instance A I) (M : Finset (A × I)) :
    Option (A ⊕ I) → Option (A ⊕ I) → Prop
  | none, some (.inl a) => by classical exact (M.filter fun (p : A × I) => p.1 = a).card = 0
  | some (.inl a), some (.inr i) => (a, i) ∈ inst.E ∧ (a, i) ∉ M
  | some (.inr i), some (.inl a) => (a, i) ∈ M
  | _, _ => False

def adInSourceSide (inst : Instance A I) (M : Finset (A × I)) (a : A) : Prop :=
  Relation.ReflTransGen (ResidualStep inst M) none (some (.inl a))

def typeInSourceSide (inst : Instance A I) (M : Finset (A × I)) (i : I) : Prop :=
  Relation.ReflTransGen (ResidualStep inst M) none (some (.inr i))

/-- Advertisers across the canonical residual reachability cut. -/
noncomputable def adsInSinkSide (inst : Instance A I) (M : Finset (A × I)) : Finset A := by
  classical
  exact Finset.univ.filter fun a => ¬ adInSourceSide inst M a

/-- Impression types on the source side of the canonical residual cut. -/
noncomputable def typesInSourceSide (inst : Instance A I) (M : Finset (A × I)) : Finset I := by
  classical
  exact Finset.univ.filter fun i => typeInSourceSide inst M i

end OnlineStochMatching.SuggestedMatching


