-- Prove2me | Definitions.Def_MCPoise_WitnessFor
-- name    : MCPoise_WitnessFor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:29:06.876091+00:00
-- url     : https://prove2.me/theorems/30768c7b-5c65-4902-8bb8-31741d193618
-- title:
--   A subgraph certifying a guess L of the optimal value
-- statement:
--   A subgraph $H \subseteq G$ **certifies** the value $L$ when $H$ connects every demand, $\Delta(H) \le L$, and $\mathrm{dist}_H(s_i, t_i) \le L$ for every $i$.
--
--   An optimal solution certifies its own poise, since both summands of the poise are at most the poise. This is all that the existence proof takes from the optimal solution.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Appendix B, p.35; p.6

import Mathlib
import Definitions.Def_MCPoise_Inst
import Definitions.Def_MCPoise_maxDeg
import Definitions.Def_MCPoise_Connects

namespace MCPoise

/-- **`H` certifies the guess `L`.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Appendix B, p.35: "Fix an optimal solution H⋆ ⊆ G. Since its poise is L, ... we have ∆(H⋆) ≤ L and
dist_{H⋆}(s_i, t_i) ≤ L for every i ∈ [k]."

`H` is a connecting subgraph of `G` with maximum degree at most `L` and with every demand at distance at most `L`.

**Formalization Note.** The source's `L` is "the value of the optimal solution", which it guesses (p.6). An optimal `H⋆`
certifies its own poise, since degree and distance are each at most the poise, so a statement for every certified `L` covers
`L = OPT`. -/
def WitnessFor (I : Inst) (L : ℕ) (H : SimpleGraph (Fin I.n)) : Prop :=
  H ≤ I.graph ∧ Connects I H ∧ maxDeg H ≤ L ∧ ∀ i, H.dist (I.s i) (I.t i) ≤ L

end MCPoise


