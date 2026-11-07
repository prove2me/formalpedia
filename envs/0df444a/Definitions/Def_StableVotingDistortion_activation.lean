-- Prove2me | Definitions.Def_StableVotingDistortion_activation
-- name    : StableVotingDistortion_activation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:46.416571+00:00
-- url     : https://prove2.me/theorems/468db2a8-8034-4d6e-902b-6619a3394a9c
-- title:
--   The activation of an attacker: $g$ at a random copy's rank
-- statement:
--   For an attacker $a$, the paper's $g(\mathrm{rank}_v(a;D))$ uses a uniformly random point of $a$'s interval. With $r=\mathrm{rank}_v(a;D)$ the left boundary, its expected value is
--   $$\begin{cases}\dfrac1{D(a)}\displaystyle\int_r^{r+D(a)}g(u)\,du,&D(a)>0,\\[2mm] g(r),&D(a)=0.\end{cases}$$
--
--   For each voter, $\sum_a D(a)$ times this value equals $\int_0^1 g$, which is what makes this the rank of a random copy.
--
--   **Formalization Note** The guard tests $D(a)=0$ and takes the printed zero-mass value, so a zero-mass candidate is not given the junk value of $1/0$.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §3, p.8; §6.1, p.22

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_leftRank

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

/-- The value the paper writes `g(rank_v(a; D))` for an attacker `a`: the rank is a uniformly random
point of `a`'s interval, so with `r` the left boundary this is `(1/D(a)) ∫_r^{r + D(a)} g` when
`D(a) ≠ 0`, and `g(r)` when `D(a) = 0`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §3, p.8: "Instead of using the left boundary, we use a uniformly random point in a's
interval, corresponding to a random copy of a. Overloading the notation, we still write rank_v(a; D)
for the attacker's rank." See also §6.2, p.22: "A candidate outside the support of D that sits at
rank r has score −ϕ(r)".

**Formalization Note.** The integral is of `g` on a subinterval of `[0, 1]` when `D` is a lottery. The
guard `D a = 0` selects the printed zero-mass value, not the junk value of `0⁻¹`. -/
noncomputable def activation {V C : Type} [Fintype C] (g : ℝ → ℝ) (E : Election V C)
    (D : C → ℝ) (v : V) (a : C) : ℝ :=
  if D a = 0 then g (leftRank E D v a)
  else (D a)⁻¹ * ∫ r in (leftRank E D v a)..(leftRank E D v a + D a), g r

end StableVotingDistortion


