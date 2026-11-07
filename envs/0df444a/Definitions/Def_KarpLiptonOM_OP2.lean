-- Prove2me | Definitions.Def_KarpLiptonOM_OP2
-- name    : KarpLiptonOM_OP2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:22.986187+00:00
-- url     : https://prove2.me/theorems/39630415-3726-44e2-a819-e4c8693640e0
-- title:
--   $\mathrm{O}_2^{\mathrm P}$: oblivious symmetric alternation (Definition A.2.2)
-- statement:
--   A language $L$ is in $\mathrm O^{\mathrm P}_2$ if there are polynomials $a, b$ and a polynomial-time predicate $V$ such that for every $x$,
--   $$
--   x \in L \Rightarrow \exists y \in \{0,1\}^{a(|x|)}\, \forall z \in \{0,1\}^{b(|x|)}\; V(x, y, z) = 1, \qquad
--   x \notin L \Rightarrow \exists z \in \{0,1\}^{b(|x|)}\, \forall y \in \{0,1\}^{a(|x|)}\; V(x, y, z) = 0,
--   $$
--   (such $y$ and $z$ are **irrefutable certificates**), and moreover for every $n$ there are $y_n$ and $z_n$ that are irrefutable for all $x \in L \cap \{0,1\}^n$ and for all $x \in \{0,1\}^n \setminus L$, respectively. Without the last condition this is $\mathrm S^{\mathrm P}_2$.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definition A.2.2, p.21

import Mathlib
import Definitions.Def_KarpLiptonOM_PolyPred3

namespace KarpLiptonOM

/-- `L ∈ OP₂` (Definition A.2.2, Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.21, the language version of prOP₂ [CR06]): polynomials
`a, b` and a polynomial-time `V` such that for every `x`, `x ∈ L ⇒ ∃y ∈ {0,1}^{a(|x|)} ∀z ∈ {0,1}^{b(|x|)}
V(x, y, z) = 1` and `x ∉ L ⇒ ∃z ∀y V(x, y, z) = 0`, and moreover for every `n` there are `y_n` and `z_n`
that are irrefutable for all `x ∈ L ∩ {0,1}ⁿ` and all `x ∈ {0,1}ⁿ ∖ L`, respectively. -/
def OP2 : Set (Set (List Bool)) :=
  {L | ∃ (a b : Polynomial ℕ) (V : List Bool → List Bool → List Bool → Prop), PolyPred3 V ∧
    (∀ x : List Bool,
      (x ∈ L → ∃ y : List Bool, y.length = a.eval x.length ∧
        ∀ z : List Bool, z.length = b.eval x.length → V x y z) ∧
      (x ∉ L → ∃ z : List Bool, z.length = b.eval x.length ∧
        ∀ y : List Bool, y.length = a.eval x.length → ¬ V x y z)) ∧
    ∀ n : ℕ, ∃ y z : List Bool, y.length = a.eval n ∧ z.length = b.eval n ∧
      ∀ x : List Bool, x.length = n →
        (x ∈ L → ∀ z' : List Bool, z'.length = b.eval n → V x y z') ∧
        (x ∉ L → ∀ y' : List Bool, y'.length = a.eval n → ¬ V x y' z)}

end KarpLiptonOM


