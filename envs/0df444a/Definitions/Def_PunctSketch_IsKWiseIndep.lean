-- Prove2me | Definitions.Def_PunctSketch_IsKWiseIndep
-- name    : PunctSketch_IsKWiseIndep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:59.934478+00:00
-- url     : https://prove2.me/theorems/2c36c1c9-9cfe-4d88-9ca6-2f2e47305f2d
-- title:
--   $w$-wise independent coins
-- statement:
--   A family of Boolean random variables on a uniform finite space is $w$-wise independent when, for every set of at most $w$ indices and every pattern of values, the probability of the pattern equals the product of the marginal probabilities.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.3, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_PunctSketch_coinProb

namespace PunctSketch

/-- **`w`-wise independent coins.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.3, p.19: "an O(k)-wise independent hash function". For
every at most `w` indices and every pattern, the probability of the pattern is the product of the
marginals. -/
def IsKWiseIndep {ι Ω : Type*} [Fintype Ω] (X : ι → Ω → Bool) (w : ℕ) : Prop :=
  ∀ (S : Finset ι) (b : ι → Bool), S.card ≤ w →
    coinProb (fun ω => ∀ i ∈ S, X i ω = b i) = ∏ i ∈ S, coinProb (fun ω => X i ω = b i)

end PunctSketch


