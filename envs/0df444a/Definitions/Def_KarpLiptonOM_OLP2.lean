-- Prove2me | Definitions.Def_KarpLiptonOM_OLP2
-- name    : KarpLiptonOM_OLP2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:37.180217+00:00
-- url     : https://prove2.me/theorems/c4839a44-967c-4e86-ab76-b1381a586bf4
-- title:
--   $\mathrm{OL}^{\mathrm P}_2$: oblivious $\mathrm L^{\mathrm P}_2$ (Definition A.2.9)
-- statement:
--   A language $L$ is in $\mathrm{OL}^{\mathrm P}_2$ if $L \in \mathrm L^{\mathrm P}_2$ via some $V, p$ such that for every $n$ there are strings $y_n, z_n$ with
--   $$
--   \min{\prec_x} = 1y_n \ \text{ for all } x \in L \cap \{0,1\}^n, \qquad \min{\prec_x} = 0z_n \ \text{ for all } x \in \{0,1\}^n \setminus L .
--   $$
--   The minimum depends on the input only through its membership bit.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definition A.2.9, p.23

import Mathlib
import Definitions.Def_KarpLiptonOM_PolyPred3
import Definitions.Def_KarpLiptonOM_IsStrictLinearOn
import Definitions.Def_KarpLiptonOM_IsMinOn

namespace KarpLiptonOM

/-- `L ∈ OL₂^P` (Definition A.2.9, Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.23): `L ∈ L₂^P` via some `V, p` such that for every `n`
there are strings `y_n, z_n` with `min ≺ₓ = 1y_n` for all `x ∈ L ∩ {0,1}ⁿ` and `min ≺ₓ = 0z_n` for all
`x ∈ {0,1}ⁿ ∖ L`. -/
def OLP2 : Set (Set (List Bool)) :=
  {L | ∃ (p : Polynomial ℕ) (V : List Bool → List Bool → List Bool → Prop), PolyPred3 V ∧
    (∀ n, 1 ≤ p.eval n) ∧
    (∀ x : List Bool, IsStrictLinearOn (p.eval x.length) (V x) ∧
      ∀ μ, IsMinOn (p.eval x.length) (V x) μ →
        (x ∈ L → μ.head? = some true) ∧ (x ∉ L → μ.head? = some false)) ∧
    ∀ n : ℕ, ∃ y z : List Bool, ∀ x : List Bool, x.length = n →
      ∀ μ, IsMinOn (p.eval n) (V x) μ → (x ∈ L → μ = true :: y) ∧ (x ∉ L → μ = false :: z)}

end KarpLiptonOM


