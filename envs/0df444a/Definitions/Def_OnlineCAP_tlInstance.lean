-- Prove2me | Definitions.Def_OnlineCAP_tlInstance
-- name    : OnlineCAP_tlInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:01.893125+00:00
-- url     : https://prove2.me/theorems/6a8d3392-f6cc-47be-a596-9ace1517e98e
-- title:
--   Online weighted TL-rectangle hitting set
-- statement:
--   **Online TL-rectangle hitting set** (Problem 1.9). A finite point set $P\subseteq\mathbb R^2$ with costs $c_p$ is given. In each step a TL shape $S=R_L\cup R_T$ arrives, and the algorithm irrevocably buys points so that the purchased set $F\subseteq P$ hits every shape so far; the goal is to keep $\sum_{p\in F}c_p$ small (the unweighted problem: $c\equiv1$).
--
--   As an instance of online hitting set: the ground set is $P$, the costs are $c$, the admissible requests are the TL shapes, and the points hitting a shape are its points.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Problem 1.9, p.5

import Mathlib
import Definitions.Def_OnlineCAP_IsLeftless
import Definitions.Def_OnlineCAP_IsTopless
import Definitions.Def_OnlineCAP_IsTLShape
import Definitions.Def_OnlineCAP_OnlineHSInstance

namespace OnlineCAP

/-- **Online (weighted) TL-rectangle hitting set.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Problem 1.9, p.5 (PDF p.5): "We are given
a finite point set P ⊆ R2. In each time step, a shape S ⊆ R2 arrives to be hit where S = RL ∪ RT
… Upon each arrival, we may irrevocably purchase points to maintain a set F ⊆ P which hits all
shapes which have arrived so far. … In the weighted case, each point has an associated
non-negative cost cp and the goal is to minimize the total cost of F."

The ground set is the point set `P`, the cost of a point `p` is `c p`, the admissible requests
are the TL shapes, and the points hitting a shape `S` are the points of `S`. The unweighted
problem is `c ≡ 1`. -/
def tlInstance (P : Finset (ℝ × ℝ)) (c : ℝ × ℝ → ℝ) :
    OnlineHSInstance (ℝ × ℝ) (Set (ℝ × ℝ)) where
  G := P
  c := c
  ok := IsTLShape
  cov := fun S => S

end OnlineCAP


