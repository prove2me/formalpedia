-- Prove2me | Definitions.Def_AvoidPlast_Supplement_HitsTargeted
-- name    : AvoidPlast_Supplement_HitsTargeted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:13:52.738988+00:00
-- url     : https://prove2.me/theorems/36cc2366-3c5f-47de-a98c-846428b9c177
-- title:
--   The targeted hitting property (Definition 7.1)
-- statement:
--   $H$ hits $D$ with error $\varepsilon$ if for every sufficiently large $n$ and every $x\in\{0,1\}^n$ with $\Pr_{r\in\{0,1\}^{m(n)}}[D(x,r)=1]\ge\varepsilon$, every accepting path of $H(x)$ outputs a list containing some $w$ with $D(x,w)=1$. A targeted hitting-set generator against a class $\mathcal D$ hits every $D\in\mathcal D$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 7.1, p.39 (PDF p.41)

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_Supplement_blockOf

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The targeted hitting property with error `ε` against one procedure `D(x, r)` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728),
Definition 7.1, p.39): for every sufficiently large `n` and every `x ∈ {0,1}^n` with
`Pr_{r ∈ {0,1}^{m(n)}}[D(x, r) = 1] ≥ ε`, every accepting path of `H(x)` outputs a list containing
some `w` with `D(x, w) = 1`. -/
def HitsTargeted (H : Machine 2) (a : ℕ) (L m : ℕ → ℕ) (Dpred : List Bool → List Bool → Prop)
    (ε : ℝ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∀ x : List Bool, x.length = n →
    ε ≤ prob (m n) (fun r => Dpred x r) →
    ∀ w : List Bool, w.length ≤ a * (n ^ a + 1) → Accepts H ![x, w] →
      ∃ i < L n, Dpred x (blockOf (output H ![x, w]) (m n) i)

end AvoidPlast.Supplement


