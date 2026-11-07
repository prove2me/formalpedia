-- Prove2me | Definitions.Def_KarpLiptonOM_ONP
-- name    : KarpLiptonOM_ONP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:10.648437+00:00
-- url     : https://prove2.me/theorems/4fa4b838-d703-4748-b7dd-f876ccc1b24c
-- title:
--   ONP: NP with input-oblivious witnesses (Definition A.2.3)
-- statement:
--   A language $L$ is in $\mathrm{ONP}$ if there are a polynomial $p$, a polynomial-time predicate $V$ and strings $w_n \in \{0,1\}^{p(n)}$, the **oblivious witnesses**, such that for every $n$ and every $x \in \{0,1\}^n$:
--   1. if $x \in L$, then $V(x, w_n) = 1$;
--   2. if $x \notin L$, then $V(x, w) = 0$ for all $w \in \{0,1\}^{p(n)}$.
--
--   One witness serves all yes-instances of a given length.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definition A.2.3, p.21

import Mathlib
import Definitions.Def_KarpLiptonOM_PolyPred2

namespace KarpLiptonOM

/-- `L ∈ ONP` (Definition A.2.3, Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.21): a polynomial `p`, a polynomial-time predicate `V` and
**oblivious witnesses** `w_n ∈ {0,1}^{p(n)}` such that for every `x ∈ {0,1}ⁿ`, `x ∈ L` implies
`V(x, w_n) = 1`, and `x ∉ L` implies `V(x, w) = 0` for all `w ∈ {0,1}^{p(n)}`. -/
def ONP : Set (Set (List Bool)) :=
  {L | ∃ (p : Polynomial ℕ) (V : List Bool → List Bool → Prop) (w : ℕ → List Bool),
    PolyPred2 V ∧ (∀ n, (w n).length = p.eval n) ∧ ∀ x : List Bool,
      (x ∈ L → V x (w x.length)) ∧
      (x ∉ L → ∀ w' : List Bool, w'.length = p.eval x.length → ¬ V x w')}

end KarpLiptonOM


