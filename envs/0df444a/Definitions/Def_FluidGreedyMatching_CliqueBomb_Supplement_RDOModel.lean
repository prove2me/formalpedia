-- Prove2me | Definitions.Def_FluidGreedyMatching_CliqueBomb_Supplement_RDOModel
-- name    : FluidGreedyMatching_CliqueBomb_Supplement_RDOModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:11:57.781192+00:00
-- url     : https://prove2.me/theorems/0b6d624f-0dd6-4bc2-9533-cecf94eafdea
-- title:
--   RDO expectations and worst-case ratios
-- statement:
--   Let $G$ be a finite simple graph on $V$ and let $\pi_v$ be a fixed strict total preference order for every vertex $v$. Use the published conditional uniform-actor process, choosing the least active neighbor in $\pi_v$, and let $p_{G,\pi}(M)$ be its terminal matching law. Define
--   $$
--   E_{\rm RDO}(G,\pi)=\sum_M p_{G,\pi}(M)|M|,\qquad
--   r_{\rm RDO}(G,\pi)=\frac{E_{\rm RDO}(G,\pi)}{\nu(G)}.
--   $$
--   Here $\nu(G)$ is the published maximum matching number. The general RDO approximation ratio is the infimum of $r_{\rm RDO}(G,\pi)$ over all finite graphs and all fixed profiles with $\nu(G)>0$. The bipartite RDO ratio restricts this set to 2-colorable graphs. The bipartite MRG ratio uses the same graph restriction and the published MRG expectation. Each infimum set is nonempty (it contains the ratio of a single edge) and bounded in $[0,1]$.
--
--   This layer reuses the operational graph and sampling model; it adds the RDO expectation and the two graph-class restrictions. A structural order constructor pulls back the lexicographic order on (class tier, index, class tag) along an injective labeling. Smaller ranks mean more preferred vertices. Empty graphs have zero expectation and default ratio zero, and are excluded from every worst-case infimum by $\nu>0$.
-- source:
--   Sayan Mukherjee, Fluid Limits and Upper Bounds for Randomized Greedy Matching, STOC 2027 submission #492 (October 2026), §2, pp. 5–6; §2.1, p. 6; Table 1, p. 4

import Mathlib
import Definitions.Def_FluidGreedyMatching_CliqueBomb_MRGModel

set_option autoImplicit false

namespace FluidGreedyMatching.CliqueBomb.Supplement

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- §2.1: the published conditional uniform-actor process, with a fixed preference profile.
The sum is finite and smaller elements in each actor's order are preferred. -/
def rdoExpectedSize (G : SimpleGraph V) (π : V → LinearOrder V) : ℝ :=
  ∑ M : Finset (Sym2 V), ((outputLaw G (some π)) M).toReal * (M.card : ℝ)

def rdoExpectedRatio (G : SimpleGraph V) (π : V → LinearOrder V) : ℝ :=
  rdoExpectedSize G π / matchingNumber G

/-- §2, pp. 5–6: infimum over all finite graphs and all fixed profiles, with ν > 0.
The defining set contains K₂'s ratio and is bounded in [0,1]. -/
def rdoApproximationRatio : ℝ :=
  sInf {r : ℝ | ∃ (N : ℕ) (G : SimpleGraph (Fin N))
    (π : Fin N → LinearOrder (Fin N)),
    0 < matchingNumber G ∧ r = rdoExpectedRatio G π}

def rdoBipartiteApproximationRatio : ℝ :=
  sInf {r : ℝ | ∃ (N : ℕ) (G : SimpleGraph (Fin N))
    (π : Fin N → LinearOrder (Fin N)),
    G.Colorable 2 ∧ 0 < matchingNumber G ∧ r = rdoExpectedRatio G π}

def mrgBipartiteApproximationRatio : ℝ :=
  sInf {r : ℝ | ∃ (N : ℕ) (G : SimpleGraph (Fin N)),
    G.Colorable 2 ∧ 0 < matchingNumber G ∧ r = expectedRatio G}

/-- Structural order constructor: class tier first, then index, then class tag.
The last coordinate only orders distinct classes assigned the same tier. -/
@[instance_reducible] def orderByTier {W : Type} (code : W → ℕ × ℕ) (hinj : Function.Injective code)
    (tier : ℕ → ℕ) : LinearOrder W :=
  LinearOrder.lift'
    (fun v => (toLex (tier (code v).1, toLex ((code v).2, (code v).1)) :
      ℕ ×ₗ (ℕ ×ₗ ℕ))) (by
        intro v w h
        apply hinj
        have hc := congrArg (fun z : ℕ ×ₗ (ℕ ×ₗ ℕ) => (ofLex (ofLex z).2).2) h
        have hi := congrArg (fun z : ℕ ×ₗ (ℕ ×ₗ ℕ) => (ofLex (ofLex z).2).1) h
        exact Prod.ext hc hi)

end
end FluidGreedyMatching.CliqueBomb.Supplement


