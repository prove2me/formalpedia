-- Prove2me | Definitions.Def_XOSMax_Supplement_alg5
-- name    : XOSMax_Supplement_alg5
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:32:50.619069+00:00
-- url     : https://prove2.me/theorems/4bbb35ff-422c-4b34-a014-823cd3f9b180
-- title:
--   Algorithm 5 for finding all maximal cliques
-- statement:
--   For $\ell=1,2,\ldots$, Algorithm 5 enumerates the $\ell$-subsets $X$ satisfying $f(X)=\sum_{v\in X}f(v)$, greedily adds every element preserving this equality, collects the resulting sets, and stops at the first level at which the family has exactly $\ell$ members.
--
--   The program uses only the enumeration and value-oracle answers; in particular, it is not given the XOS width.
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Algorithm 5, p.9

import Mathlib
import Definitions.Def_XOSMax_OracleProg

namespace XOSMax.Supplement

open XOSMax OracleProg

variable {E : Type} [DecidableEq E]

/-- Query and sum the singleton values of the elements in a list. -/
noncomputable def singletonSum : List E → OracleProg E ℝ
  | [] => pure 0
  | v :: rest => do
      let a ← ask {v}
      let b ← singletonSum rest
      tick
      pure (a + b)

/-- Test the equality `f(X) = ∑ v∈X, f(v)` from Line 3 of Algorithm 5. -/
noncomputable def isAlg5Seed (X : Finset E) : OracleProg E Bool := do
  let a ← ask X
  let b ← singletonSum X.toList
  tick
  pure (a = b)

/-- One iteration of Lines 6–7 of Algorithm 5. -/
noncomputable def alg5GrowStep (X : Finset E) (u : E) : OracleProg E (Finset E) := do
  tick
  if u ∈ X then
    pure X
  else
    let a ← ask (insert u X)
    let b ← ask X
    let c ← ask {u}
    tick
    if a = b + c then pure (insert u X) else pure X

/-- Greedily expand one seed as in Lines 5–7 of Algorithm 5. -/
noncomputable def alg5Grow (L : List E) (X : Finset E) : OracleProg E (Finset E) :=
  L.foldlM alg5GrowStep X

/-- Process all cardinality-`ℓ` candidates in Lines 3–8, adding their grown sets to the family
accumulated at earlier levels. -/
noncomputable def alg5Level (L : List E) (ℓ : ℕ) (initial : Finset (Finset E)) :
    OracleProg E (Finset (Finset E)) := do
  (L.toFinset.powersetCard ℓ).toList.foldlM (fun family X => do
    tick
    if ← isAlg5Seed X then
      let VX ← alg5Grow L X
      pure (insert VX family)
    else
      pure family) initial

/-- The outer loop of Algorithm 5, stopping at the first level whose returned family has size
exactly that level. -/
noncomputable def alg5Loop (L : List E) :
    Finset (Finset E) → List ℕ → OracleProg E (Finset (Finset E))
  | family, [] => pure family
  | family, ℓ :: rest => do
      let family' ← alg5Level L ℓ family
      tick
      if family'.card = ℓ then pure family' else alg5Loop L family' rest

/-- **Algorithm 5:** enumerate additive seeds of increasing size, greedily expand them, and stop
when the resulting family has the current size (Filmus, Kawase, Kobayashi & Yamaguchi,
arXiv:1811.09045v3, Algorithm 5, p.9).

**Formalization Note** The source's unbounded loop is supplied with levels `1,…,2^n`. The family
persists across levels and contains distinct subsets of the `n`-element ground set, so these levels
include its eventual cardinality; under Lemma 15's hypotheses the proof gives the sharper stopping
level at most `k`. The program takes neither `k` nor a representation. -/
noncomputable def alg5 (L : List E) : OracleProg E (Finset (Finset E)) :=
  alg5Loop L ∅ ((List.range (2 ^ L.length)).map (· + 1))

end XOSMax.Supplement


