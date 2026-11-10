-- Prove2me | Definitions.Def_TwoConnSS_SuccB
-- name    : TwoConnSS_SuccB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:47:33.660991+00:00
-- url     : https://prove2.me/theorems/0de7fc1a-750e-4d4a-9ddd-fb475fa4bdde
-- title:
--   Successful exchanges of Algorithm B
-- statement:
--   Let $L(S)$ be the 2EC blocks of $S$ that are neither 4-cycles nor 5-cycles, $W_B(S) = \sum_{B \in L(S)} |V(B)|^2$, and $s_B(S)$ the number of 2EC blocks that are 4-cycles or 5-cycles (including those inside complex components). A step from $S$ to $S'$ is a **successful exchange of Algorithm B** if:
--
--   1. $S'$ is a canonical 2-edge-cover for Algorithm B;
--   2. every 4-cycle component of $S'$ is primitive (relative to $S_0$);
--   3. every block of $L(S)$ lies inside a block of $L(S')$;
--   4. $\mathrm{cost}_B(S') \le \mathrm{cost}_B(S)$;
--   5. $\phi_B = (-W_B, s_B, \mathrm{br})$ strictly decreases lexicographically: $W_B$ increases; or $W_B$ is unchanged and $s_B$ decreases; or both are unchanged and $\mathrm{br}$ decreases.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §8.1.2, pp.38–39, display (14)

import Mathlib
import Definitions.Def_TwoConnSS_costB
import Definitions.Def_TwoConnSS_IsCanonB
import Definitions.Def_TwoConnSS_Primitive

namespace TwoConnSS

open Classical

variable {V : Type*} [Fintype V]

/-- `L(S)`: the 2EC blocks of `S` that are neither 4-cycles nor 5-cycles (p.38). -/
noncomputable def Lbl (S : Finset (Sym2 V)) : Finset (Finset V) :=
  (blocks S).filter fun B => ¬ IsCycleBlock S B 4 ∧ ¬ IsCycleBlock S B 5

/-- `W_B(S) = Σ_{B ∈ L(S)} |V(B)|²` (p.39). -/
noncomputable def WB (S : Finset (Sym2 V)) : ℕ :=
  ∑ B ∈ Lbl S, B.card ^ 2

/-- `s_B(S)`: the number of 2EC blocks that are 4-cycles or 5-cycles, including blocks inside
complex components (p.39). -/
noncomputable def sB (S : Finset (Sym2 V)) : ℕ :=
  ((blocks S).filter fun B => IsCycleBlock S B 4 ∨ IsCycleBlock S B 5).card

/-- `ϕ_B(S') < ϕ_B(S)` for `ϕ_B = (−W_B, s_B, br)` in lexicographic order: display (14), p.39. -/
def LexB (S S' : Finset (Sym2 V)) : Prop :=
  WB S < WB S' ∨ (WB S' = WB S ∧ sB S' < sB S) ∨ (WB S' = WB S ∧ sB S' = sB S ∧ br S' < br S)

/-- **A successful exchange of Algorithm B** from `S` to `S'`.
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), p.39: "a successful exchange
produces a canonical cover for Algorithm r, satisfies the preservation requirements above, and obeys
costr(S′) ≤ costr(S), ϕr(S′) < ϕr(S)"; p.38: "For Algorithm B, the same requirement holds for
B ∈ L(S) with B′ ∈ L(S′)", and every 4-cycle component remains primitive.

`SuccB G S₀ S S'` bundles: `S'` canonical for B (which includes a component with at least ten
vertices), every 4-cycle component of `S'` primitive, every block of `L(S)` inside a block of
`L(S')`, `cost_B(S') ≤ cost_B(S)` and `ϕ_B(S') < ϕ_B(S)`. Also defined here: `L(S)`, `W_B`, `s_B`
and `LexB`. -/
def SuccB (G : SimpleGraph V) (S₀ S S' : Finset (Sym2 V)) : Prop :=
  IsCanonB G S' ∧ Primitive S₀ S' ∧ (∀ B ∈ Lbl S, ∃ B' ∈ Lbl S', B ⊆ B') ∧
  costB S' ≤ costB S ∧ LexB S S'

end TwoConnSS


