-- Prove2me | Definitions.Def_RvsCert_C1
-- name    : RvsCert_C1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:59.382583+00:00
-- url     : https://prove2.me/theorems/fc3ff174-7ed5-4279-93d2-091fd360965d
-- title:
--   1-certificate complexity $C_1(f)$
-- statement:
--   For a Boolean function $f$ on a finite set of bit positions,
--   $$
--   C_1(f)=\max_{x\,:\,f(x)=1} C_x(f),
--   $$
--   the largest certificate complexity of a 1-input ($0$ when $f$ has no 1-input). Lemma 2 of the paper bounds it by $\mathrm{UC}_1(f)=O(n\log n)$.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Lemma 2, p.2 (standard notion)

import Mathlib
import Definitions.Def_RvsCert_certAt

namespace RvsCert

/-- **1-certificate complexity** `C1(f)` (standard, [BdW02]; used in Lemma 2, p.2 of
Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): the maximum, over inputs `x` with `f x = true`, of the least size of a
certificate for `x`.

**Formalization Note.** A `Finset.sup` over all inputs of `if f x = true then certAt f x else 0`;
it is `0` when `f` has no 1-input. -/
noncomputable def C1 {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool) : ℕ :=
  Finset.univ.sup fun x => if f x = true then certAt f x else 0

end RvsCert


